'use strict';

const http = require('node:http');
const net = require('node:net');
const dgram = require('node:dgram');
const dns = require('node:dns').promises;
const crypto = require('node:crypto');
const { domainToASCII } = require('node:url');

const MAX_WS_BYTES = 2 * 1024 * 1024;
const MAX_PENDING_BYTES = 3 * 1024 * 1024;
const MAX_TCP_QUEUE_BYTES = 2 * 1024 * 1024;
const MAX_UDP_BYTES = 65507;
const MAX_CHANNEL_FRAME_BYTES = 65535;
const MAX_CHANNEL_SESSIONS = 32;
const MAX_UDP_PACKETS_PER_SECOND = 150;
const MAX_WS_CLIENTS = 32;
const IDLE_MS = 5 * 60 * 1000;
const IP_DENY_4 = new net.BlockList();
const IP_DENY_6 = new net.BlockList();

for (const [ip, prefix] of [
  ['0.0.0.0', 8], ['10.0.0.0', 8], ['100.64.0.0', 10],
  ['127.0.0.0', 8], ['169.254.0.0', 16], ['172.16.0.0', 12],
  ['192.0.0.0', 24], ['192.0.2.0', 24], ['192.168.0.0', 16],
  ['198.18.0.0', 15], ['198.51.100.0', 24], ['203.0.113.0', 24],
  ['224.0.0.0', 4], ['240.0.0.0', 4],
]) IP_DENY_4.addSubnet(ip, prefix, 'ipv4');
for (const [ip, prefix] of [
  ['::', 128], ['::1', 128], ['::ffff:0:0', 96],
  ['fc00::', 7], ['fe80::', 10], ['ff00::', 8],
  ['2001:db8::', 32], ['2001::', 32], ['2002::', 16],
  ['64:ff9b::', 96],
]) IP_DENY_6.addSubnet(ip, prefix, 'ipv6');

function isPublicIp(address, family = net.isIP(address)) {
  return (family === 4 || family === 6) &&
    !(family === 4 ? IP_DENY_4.check(address, 'ipv4') : IP_DENY_6.check(address, 'ipv6'));
}

async function resolvePublic(host) {
  const family = net.isIP(host);
  const list = family ? [{ address: host, family }] : await dns.lookup(host, { all: true });
  const match = list.find(item => isPublicIp(item.address, item.family));
  if (!match) throw new Error('No permitted public destination');
  return match;
}

function parseAddress(buffer, start) {
  if (buffer.length < start + 3) return null;
  const port = buffer.readUInt16BE(start);
  const type = buffer[start + 2];
  let offset = start + 3;
  let host;
  if (type === 1) {
    if (buffer.length < offset + 4) return null;
    host = [...buffer.subarray(offset, offset + 4)].join('.');
    offset += 4;
  } else if (type === 2) {
    if (buffer.length < offset + 1) return null;
    const length = buffer[offset++];
    if (!length || buffer.length < offset + length) {
      if (!length) throw new Error('Invalid domain length');
      return null;
    }
    host = domainToASCII(buffer.toString('utf8', offset, offset + length));
    offset += length;
    if (!host || host.length > 253 || /[\x00-\x20/\\]/.test(host)) {
      throw new Error('Invalid domain');
    }
  } else if (type === 3) {
    if (buffer.length < offset + 16) return null;
    const words = [];
    for (let i = 0; i < 16; i += 2) words.push(buffer.readUInt16BE(offset + i).toString(16));
    host = words.join(':');
    offset += 16;
  } else {
    throw new Error(`Unsupported address type ${type}`);
  }
  if (!port) throw new Error('Invalid destination port');
  return { host, port, offset };
}

function ipv6Bytes(ip) {
  let parts = ip.toLowerCase().split('::');
  if (parts.length > 2) throw new Error('Invalid IPv6');
  const expand = x => x ? x.split(':').map(v => parseInt(v, 16)) : [];
  const left = expand(parts[0]);
  const right = parts.length === 2 ? expand(parts[1]) : [];
  const missing = 8 - left.length - right.length;
  if (missing < 0 || (parts.length === 1 && missing !== 0)) throw new Error('Invalid IPv6');
  const words = [...left, ...Array(missing).fill(0), ...right];
  const out = Buffer.alloc(16);
  words.forEach((v, i) => out.writeUInt16BE(v, i * 2));
  return out;
}

function encodeAddress(host, port) {
  const family = net.isIP(host);
  const head = Buffer.alloc(2);
  head.writeUInt16BE(port);
  if (family === 4) return Buffer.concat([
    head, Buffer.from([1]), Buffer.from(host.split('.').map(Number)),
  ]);
  if (family === 6) return Buffer.concat([head, Buffer.from([3]), ipv6Bytes(host)]);
  const domain = Buffer.from(host, 'utf8');
  if (!domain.length || domain.length > 255) throw new Error('Invalid encoded domain');
  return Buffer.concat([head, Buffer.from([2, domain.length]), domain]);
}

function parseSessionHeader(buffer, uuidBytes) {
  if (buffer.length < 18) return null;
  if (buffer[0] !== 0) throw new Error('Unsupported protocol version');
  if (!crypto.timingSafeEqual(buffer.subarray(1, 17), uuidBytes)) {
    throw new Error('Invalid credentials');
  }
  if (buffer[17] !== 0) throw new Error('Unsupported session options');
  if (buffer.length < 19) return null;
  const command = buffer[18];
  if (command === 3) return { command, payload: buffer.subarray(19) };
  if (command !== 1 && command !== 2) throw new Error(`Unsupported command ${command}`);
  const target = parseAddress(buffer, 19);
  if (!target) return null;
  return { command, host: target.host, port: target.port, payload: buffer.subarray(target.offset) };
}

function channelFrame(id, status, data, address) {
  const opt = data && data.length ? 1 : 0;
  const header = Buffer.alloc(4);
  header.writeUInt16BE(id);
  header[2] = status;
  header[3] = opt;
  const meta = address ? Buffer.concat([
    header, Buffer.from([2]), encodeAddress(address.host, address.port),
  ]) : header;
  const prefix = Buffer.alloc(2);
  prefix.writeUInt16BE(meta.length);
  if (!opt) return Buffer.concat([prefix, meta]);
  const size = Buffer.alloc(2);
  size.writeUInt16BE(data.length);
  return Buffer.concat([prefix, meta, size, data]);
}

function start() {
  const { WebSocket, WebSocketServer } = require('ws');
  const uuid = (process.env.UUID || '').trim().toLowerCase();
  const port = Number(process.env.PORT || process.env.SERVER_PORT || 5000);
  const host = process.env.HOST || '0.0.0.0';
  const path = process.env.WS_PATH || '/';
  if (!/^[\da-f]{8}-[\da-f]{4}-[1-8][\da-f]{3}-[89ab][\da-f]{3}-[\da-f]{12}$/.test(uuid)) {
    throw new Error('Set a valid UUID environment variable');
  }
  if (!Number.isInteger(port) || port < 1 || port > 65535) throw new Error('Invalid PORT');
  if (!path.startsWith('/')) throw new Error('WS_PATH must start with /');
  const uuidBytes = Buffer.from(uuid.replaceAll('-', ''), 'hex');

  const httpServer = http.createServer((req, res) => {
    res.writeHead(req.url === '/' ? 200 : 404, {
      'Content-Type': 'text/plain; charset=utf-8',
      'Cache-Control': 'no-store',
    });
    res.end(req.url === '/' ? 'OK\n' : 'Not found\n');
  });
  const wss = new WebSocketServer({ noServer: true, maxPayload: MAX_WS_BYTES, perMessageDeflate: false });
  httpServer.on('upgrade', (request, socket, head) => {
    let pathname;
    try { pathname = new URL(request.url, 'http://localhost').pathname; }
    catch { socket.destroy(); return; }
    if (pathname !== path || wss.clients.size >= MAX_WS_CLIENTS) {
      socket.end('HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\n');
      return;
    }
    wss.handleUpgrade(request, socket, head, ws => wss.emit('connection', ws));
  });

  wss.on('connection', ws => {
    const state = {
      mode: 'header', pending: Buffer.alloc(0), closed: false,
      lastSeen: Date.now(), directTcp: null, tcpQueue: [], tcpQueuedBytes: 0,
      tcpReady: false, directUdp: null, sessions: new Map(),
      udpWindow: Date.now(), udpSentInWindow: 0,
    };
    const idleTimer = setInterval(() => {
      if (Date.now() - state.lastSeen > IDLE_MS) shutdown();
      for (const [id, s] of state.sessions) {
        if (s.kind === 'udp' && Date.now() - s.lastSeen > IDLE_MS) {
          closeSession(s);
          state.sessions.delete(id);
        }
      }
    }, 30000);
    idleTimer.unref();

    function send(bytes, cb) {
      if (state.closed || ws.readyState !== WebSocket.OPEN) return false;
      if (ws.bufferedAmount > MAX_PENDING_BYTES) { shutdown(); return false; }
      ws.send(bytes, { binary: true }, err => {
        if (err) shutdown();
        if (cb) cb(err);
      });
      return true;
    }

    function closeSession(session) {
      if (!session || session.closed) return;
      session.closed = true;
      if (session.socket) session.socket.destroy();
      if (session.sockets) for (const sock of session.sockets.values()) {
        try { sock.close(); } catch {}
      }
    }

    function shutdown() {
      if (state.closed) return;
      state.closed = true;
      clearInterval(idleTimer);
      if (state.directTcp) state.directTcp.destroy();
      if (state.directUdp) closeSession(state.directUdp);
      for (const s of state.sessions.values()) closeSession(s);
      state.sessions.clear();
      if (ws.readyState === WebSocket.OPEN || ws.readyState === WebSocket.CONNECTING) ws.terminate();
    }

    function reject(err) {
      console.warn('Rejected connection:', err.message || err);
      shutdown();
    }

    function rateLimitedUdp() {
      const now = Date.now();
      if (now - state.udpWindow >= 1000) {
        state.udpWindow = now;
        state.udpSentInWindow = 0;
      }
      return ++state.udpSentInWindow > MAX_UDP_PACKETS_PER_SECOND;
    }

    function newUdpSession(id, target, direct) {
      return { kind: 'udp', id, target, direct, sockets: new Map(),
        allowed: new Set(), closed: false, lastSeen: Date.now() };
    }

    function udpSocket(session, family) {
      let sock = session.sockets.get(family);
      if (sock) return sock;
      sock = dgram.createSocket(family === 4 ? 'udp4' : 'udp6');
      session.sockets.set(family, sock);
      sock.on('error', () => {
        try { sock.close(); } catch {}
        session.sockets.delete(family);
      });
      sock.on('message', (payload, rinfo) => {
        if (state.closed || session.closed) return;
        if (!session.allowed.has(`${rinfo.address}|${rinfo.port}`)) return;
        state.lastSeen = session.lastSeen = Date.now();
        if (session.direct) {
          const size = Buffer.alloc(2);
          size.writeUInt16BE(payload.length);
          send(Buffer.concat([size, payload]));
        } else {
          send(channelFrame(session.id, 2, payload, {
            host: rinfo.address, port: rinfo.port,
          }));
        }
      });
      return sock;
    }

    async function sendUdp(session, payload, target) {
      if (state.closed || session.closed || rateLimitedUdp()) return;
      if (!payload.length || payload.length > MAX_UDP_BYTES) return;
      try {
        const { address, family } = await resolvePublic(target.host);
        if (state.closed || session.closed) return;
        const sock = udpSocket(session, family);
        session.allowed.add(`${address}|${target.port}`);
        if (session.allowed.size > 256) { reject(new Error('Too many remote endpoints')); return; }
        sock.send(payload, target.port, address, err => {
          if (err && !state.closed) console.warn('Datagram delivery failed:', err.code || err.message);
        });
        state.lastSeen = session.lastSeen = Date.now();
      } catch (err) {
        if (!state.closed) console.warn('Datagram destination rejected:', err.message);
      }
    }

    function directTcpData(data) {
      if (!data.length || state.closed) return;
      if (!state.tcpReady) {
        state.tcpQueuedBytes += data.length;
        if (state.tcpQueuedBytes > MAX_TCP_QUEUE_BYTES) throw new Error('Stream pending buffer exceeded');
        state.tcpQueue.push(data);
      } else if (state.directTcp && !state.directTcp.destroyed) {
        if (state.directTcp.writableLength > MAX_TCP_QUEUE_BYTES) throw new Error('Stream write buffer exceeded');
        state.directTcp.write(data);
      }
    }

    async function openDirectTcp(target, firstData) {
      if (firstData.length) directTcpData(firstData);
      try {
        const dest = await resolvePublic(target.host);
        if (state.closed) return;
        const sock = net.createConnection({ host: dest.address, family: dest.family, port: target.port });
        state.directTcp = sock;
        sock.setTimeout(IDLE_MS, () => sock.destroy());
        sock.on('connect', () => {
          if (state.closed) return;
          state.tcpReady = true;
          send(Buffer.from([0, 0]));
          for (const chunk of state.tcpQueue) sock.write(chunk);
          state.tcpQueue.length = 0;
          state.tcpQueuedBytes = 0;
        });
        sock.on('data', chunk => {
          state.lastSeen = Date.now();
          if (ws.bufferedAmount > MAX_TCP_QUEUE_BYTES) sock.pause();
          send(chunk, () => {
            if (!state.closed && ws.bufferedAmount < MAX_TCP_QUEUE_BYTES / 2) sock.resume();
          });
        });
        sock.on('error', err => {
          if (!state.closed) console.warn('Stream connection failed:', err.code || err.message);
          shutdown();
        });
        sock.on('close', shutdown);
      } catch (err) { if (!state.closed) reject(err); }
    }

    function createChannelTcpSession(id, target, firstData) {
      const session = { kind: 'tcp', id, closed: false, ready: false, socket: null,
        queue: [], queueBytes: 0, lastSeen: Date.now() };
      state.sessions.set(id, session);
      function upstream(data) {
        if (!data.length || session.closed) return;
        if (!session.ready) {
          session.queueBytes += data.length;
          if (session.queueBytes > MAX_TCP_QUEUE_BYTES) throw new Error('Channel stream buffer exceeded');
          session.queue.push(data);
        } else if (session.socket && !session.socket.destroyed) session.socket.write(data);
      }
      session.upstream = upstream;
      upstream(firstData);
      (async () => {
        try {
          const dest = await resolvePublic(target.host);
          if (session.closed || state.closed) return;
          const sock = net.createConnection({ host: dest.address, family: dest.family, port: target.port });
          session.socket = sock;
          sock.setTimeout(IDLE_MS, () => sock.destroy());
          sock.on('connect', () => {
            if (session.closed || state.closed) return;
            session.ready = true;
            for (const chunk of session.queue) sock.write(chunk);
            session.queue.length = 0;
            session.queueBytes = 0;
          });
          sock.on('data', chunk => {
            state.lastSeen = session.lastSeen = Date.now();
            for (let off = 0; off < chunk.length; off += 65535) {
              send(channelFrame(id, 2, chunk.subarray(off, off + 65535)));
            }
          });
          sock.on('error', () => { /* close handled below */ });
          sock.on('close', () => {
            if (!state.closed && state.sessions.get(id) === session) {
              send(channelFrame(id, 3));
              state.sessions.delete(id);
            }
            closeSession(session);
          });
        } catch (err) {
          if (!state.closed && state.sessions.get(id) === session) {
            console.warn('Channel connection rejected:', err.message);
            send(channelFrame(id, 3));
            state.sessions.delete(id);
          }
          closeSession(session);
        }
      })();
      return session;
    }

    function processNativeUdp(data) {
      if (data.length) state.pending = Buffer.concat([state.pending, data]);
      if (state.pending.length > MAX_PENDING_BYTES) throw new Error('Datagram buffer exceeded');
      while (state.pending.length >= 2) {
        const length = state.pending.readUInt16BE(0);
        if (!length || length > MAX_UDP_BYTES) throw new Error('Invalid datagram length');
        if (state.pending.length < 2 + length) break;
        const payload = state.pending.subarray(2, 2 + length);
        state.pending = state.pending.subarray(2 + length);
        sendUdp(state.directUdp, payload, state.directUdp.target);
      }
    }

    function processChannels(data) {
      if (data.length) state.pending = Buffer.concat([state.pending, data]);
      if (state.pending.length > MAX_PENDING_BYTES) throw new Error('Channel buffer exceeded');
      while (state.pending.length >= 2) {
        const metaSize = state.pending.readUInt16BE(0);
        if (metaSize < 4 || metaSize > 512) throw new Error('Invalid channel metadata length');
        if (state.pending.length < metaSize + 2) break;
        const meta = state.pending.subarray(2, metaSize + 2);
        const id = meta.readUInt16BE(0);
        const status = meta[2];
        const option = meta[3];
        let total = metaSize + 2;
        let payload = Buffer.alloc(0);
        if (option & 1) {
          if (state.pending.length < total + 2) break;
          const size = state.pending.readUInt16BE(total);
          if (size > MAX_CHANNEL_FRAME_BYTES) throw new Error('Channel frame too large');
          if (state.pending.length < total + 2 + size) break;
          payload = state.pending.subarray(total + 2, total + 2 + size);
          total += 2 + size;
        }
        state.pending = state.pending.subarray(total);
        if (status === 4) continue;
        if (status === 3) {
          closeSession(state.sessions.get(id));
          state.sessions.delete(id);
          continue;
        }
        if (status !== 1 && status !== 2) throw new Error('Unsupported channel status');
        let session = state.sessions.get(id);
        if (status === 1) {
          if (session) { closeSession(session); state.sessions.delete(id); }
          if (state.sessions.size >= MAX_CHANNEL_SESSIONS) throw new Error('Too many channel sessions');
          if (meta.length < 8) throw new Error('Invalid new channel frame');
          const network = meta[4];
          const target = parseAddress(meta, 5);
          if (!target) throw new Error('Truncated channel destination');
          if (network === 2) {
            session = newUdpSession(id, target, false);
            state.sessions.set(id, session);
            if (payload.length) sendUdp(session, payload, target);
          } else if (network === 1) {
            createChannelTcpSession(id, target, payload);
          } else throw new Error('Unsupported channel network');
          continue;
        }
        if (!session || session.closed) continue;
        session.lastSeen = Date.now();
        if (session.kind === 'tcp') {
          if (payload.length) session.upstream(payload);
        } else if (payload.length) {
          let target = session.target;
          if (meta.length > 4 && meta[4] === 2) {
            const changed = parseAddress(meta, 5);
            if (!changed) throw new Error('Truncated channel address');
            target = changed;
          }
          sendUdp(session, payload, target);
        }
      }
    }

    function begin(request) {
      if (request.command === 1) {
        state.mode = 'tcp';
        openDirectTcp(request, request.payload);
      } else if (request.command === 2) {
        state.mode = 'udp';
        state.directUdp = newUdpSession(-1, request, true);
        send(Buffer.from([0, 0]));
        processNativeUdp(request.payload);
      } else {
        state.mode = 'channels';
        send(Buffer.from([0, 0]));
        processChannels(request.payload);
      }
    }

    ws.on('message', (chunk, isBinary) => {
      if (state.closed) return;
      if (!isBinary) { reject(new Error('Binary frames required')); return; }
      state.lastSeen = Date.now();
      try {
        if (state.mode === 'header') {
          state.pending = Buffer.concat([state.pending, chunk]);
          if (state.pending.length > MAX_PENDING_BYTES) throw new Error('Initial request buffer exceeded');
          const request = parseSessionHeader(state.pending, uuidBytes);
          if (!request) {
            if (state.pending.length > 4096) throw new Error('Request header too large');
            return;
          }
          state.pending = Buffer.alloc(0);
          begin(request);
        } else if (state.mode === 'tcp') {
          directTcpData(chunk);
        } else if (state.mode === 'udp') {
          processNativeUdp(chunk);
        } else if (state.mode === 'channels') {
          processChannels(chunk);
        }
      } catch (err) { reject(err); }
    });
    ws.on('error', shutdown);
    ws.on('close', shutdown);
    const handshakeTimer = setTimeout(() => {
      if (state.mode === 'header') shutdown();
    }, 15000);
    handshakeTimer.unref();
    ws.on('close', () => clearTimeout(handshakeTimer));
  });

  httpServer.on('error', err => console.error('HTTP server error:', err.message));
  httpServer.listen(port, host, () => {
    console.log(`Service v2.0.1 ready on ${host}:${port}; WebSocket path ${path}; Node.js ${process.version}`);
    console.log('Handlers initialized. TLS is supplied by the platform.');
  });
  process.on('SIGTERM', () => {
    for (const client of wss.clients) client.terminate();
    httpServer.close();
  });
  return { httpServer, wss };
}

if (require.main === module) start();
module.exports = { start, parseSessionHeader, parseAddress, encodeAddress, channelFrame, isPublicIp };
