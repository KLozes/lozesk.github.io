/*
 * The browser's online-play transport (ROADMAP N2; docs/netplay_transport.md): one WebRTC peer connection between two players,
 * set up by copy-paste codes (no signalling server) and carrying
 *
 *   - the "game" data channel: unordered and unreliable (ordered: false, maxPacketLifeTime). Every rollback datagram
 *     (include/gba2/net/rollback_wire.h) is self-contained and repeats everything the peer has not acknowledged, so a lost or
 *     late datagram costs nothing and a retransmission would only add head-of-line blocking. A datagram that has waited in the
 *     browser's send queue for more than GAME_LIFETIME_MS is discarded there, and none is sent while more than MAX_BUFFERED bytes
 *     wait: the browser's SCTP keeps a congestion window that shrinks after losses, and a standing queue would deliver old
 *     datagrams late instead of the newest one (docs/netplay_transport.md, section 1);
 *   - the "control" data channel: ordered and reliable, for the handshake of the session (web/netplay-ui.js) and a goodbye.
 *
 * Both channels are negotiated (the same ids on both sides), so no ondatachannel race exists and the first byte can be sent
 * the moment a channel is open.
 *
 * A CODE is the session description, with every ICE candidate in it (gathering is awaited, so there is no trickle and no
 * second exchange): "GBA2-2o.<payload>.<check>" for the offer of the host, "GBA2-2a. ..." for the answer of the guest. The payload of
 * a version 2 code is what the other browser needs from the description and nothing else (the certificate fingerprint, the ICE login, the
 * addresses), packed into bytes and written in base64url: 80 to 170 characters. A description with anything else in it travels whole as a
 * version 1 code: the SDP, deflated (CompressionStream, where the browser has it), 600 to 700 characters. The check is four characters that
 * catch a cut or mistyped code before the browser rejects the description with an unreadable message. Nothing about the game is in a
 * code, and a code is useless once the connection it describes is closed.
 *
 * A ROOM CODE ("K7QF", four characters) replaces the two long codes: the pages swap them through a public relay (ntfy.sh unless another is
 * configured), see "room codes" below. The long codes stay as the fallback when the relay cannot be reached.
 *
 * The public STUN server is the default ICE server (the user's decision: STUN, no relay); the connection needs a direct path
 * (home routers are fine, strict symmetric NATs on both ends are not: the player is told).
 *
 * window.gba2Net = { Link, encodeCode, decodeCode, CodeError, ... } is used by the page and by the tests (tests/web/run_netplay_tests.mjs,
 * tests/web/test_codes.mjs).
 */
(() => {
  'use strict';

  const DEFAULT_ICE_SERVERS = [{ urls: 'stun:stun.l.google.com:19302' }];
  const VERSION = 1;                       // the whole description, deflated
  const COMPACT_VERSION = 2;               // the fields the other browser needs, packed
  const PREFIX = 'GBA2-';
  const CHANNEL_CONTROL = 0;
  const CHANNEL_GAME = 1;
  const MAX_BUFFERED = 1200;               // bytes queued on the game channel beyond which a datagram is not sent (the next one repeats it): about four of them
  const GAME_LIFETIME_MS = 40;             // a queued datagram older than this is discarded by the browser: the next one is on its way and carries the same inputs

  class CodeError extends Error {
    constructor(reason, message) { super(message); this.name = 'CodeError'; this.reason = reason; }
  }

  // ---- codes ---------------------------------------------------------------------------------------------------

  const B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_';
  const B64_INDEX = new Map([...B64].map((c, i) => [c, i]));

  function base64urlEncode(bytes) {
    let out = '';
    let i = 0;
    for (; i + 2 < bytes.length; i += 3) {
      const n = (bytes[i] << 16) | (bytes[i + 1] << 8) | bytes[i + 2];
      out += B64[n >> 18] + B64[(n >> 12) & 63] + B64[(n >> 6) & 63] + B64[n & 63];
    }
    if (i + 1 === bytes.length) {
      const n = bytes[i] << 16;
      out += B64[n >> 18] + B64[(n >> 12) & 63];
    } else if (i + 2 === bytes.length) {
      const n = (bytes[i] << 16) | (bytes[i + 1] << 8);
      out += B64[n >> 18] + B64[(n >> 12) & 63] + B64[(n >> 6) & 63];
    }
    return out;
  }

  function base64urlDecode(text) {
    if (text.length % 4 === 1) return null;
    const bytes = new Uint8Array(Math.floor(text.length * 3 / 4));
    let n = 0, bits = 0, at = 0;
    for (const c of text) {
      const v = B64_INDEX.get(c);
      if (v === undefined) return null;
      n = (n << 6) | v;
      bits += 6;
      if (bits >= 8) { bits -= 8; bytes[at++] = (n >> bits) & 255; }
    }
    return bytes.subarray(0, at);
  }

  async function pipe(bytes, stream) {
    const writer = stream.writable.getWriter();
    writer.write(bytes).catch(() => {});
    writer.close().catch(() => {});
    const reader = stream.readable.getReader();
    const chunks = [];
    let total = 0;
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      chunks.push(value);
      total += value.length;
    }
    const out = new Uint8Array(total);
    let at = 0;
    for (const chunk of chunks) { out.set(chunk, at); at += chunk.length; }
    return out;
  }

  const canCompress = () => typeof CompressionStream === 'function' && typeof DecompressionStream === 'function';

  /** Four base64url characters (24 bits of FNV-1a) over the text before them: a typo, a cut or a swapped character shows. */
  function checkOf(text) {
    let h = 0x811c9dc5;
    for (let i = 0; i < text.length; i++) { h ^= text.charCodeAt(i); h = Math.imul(h, 0x01000193) >>> 0; }
    h = ((h >>> 24) ^ h) & 0xffffff;
    return B64[h >> 18] + B64[(h >> 12) & 63] + B64[(h >> 6) & 63] + B64[h & 63];
  }

  // ---- the compact form (version 2) --------------------------------------------------------------------------

  /* The description of our two negotiated data channels is 700 to 1,000 characters, and a code of version 1 (that text, deflated) is 600 to 700.
   * What the other browser needs from it is little: the fingerprint of the DTLS certificate (32 bytes), the ICE credentials (a user fragment and a
   * password, 28 random characters in Chrome) and the addresses the machine can be reached at (6 bytes for an IPv4 address and its port, 18 for an
   * IPv6 address or for the mDNS name Chrome puts in place of a local address). The rest is the same in every session, and the receiver writes it
   * again. A code of version 2 is those fields, packed. A description with anything else in it (a second media section, an attribute this code does
   * not know, a fingerprint that is not SHA-256, a candidate it cannot write) is not packed and goes whole as a version 1 code, and a packed code is
   * read back and compared with what it was made from before it is given out. TCP candidates are left out (a rollback game cannot use a TCP path),
   * and so are the foundation, the priority and the related address of a candidate: the receiver makes them up the way Chrome does. */

  const ICE_CHARS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';   // the characters RFC 8839 allows in the login
  const ICE_INDEX = new Map([...ICE_CHARS].map((c, i) => [c, i]));
  const SETUPS = ['actpass', 'active', 'passive'];
  const CANDIDATE_TYPES = ['host', 'srflx', 'prflx', 'relay'];
  const TYPE_PREFERENCE = [126, 100, 110, 0];                // RFC 8445 5.1.2.2: what the priority of a candidate is made of
  const IGNORED_ATTRIBUTES = new Set(['extmap-allow-mixed', 'msid-semantic', 'ice-options', 'max-message-size', 'end-of-candidates', 'sendrecv']);
  const UUID_NAME = /^([0-9a-f]{8})-([0-9a-f]{4})-([0-9a-f]{4})-([0-9a-f]{4})-([0-9a-f]{12})\.local$/i;   // the mDNS name of a local address

  const hexOf = (bytes) => [...bytes].map((b) => b.toString(16).padStart(2, '0')).join('');
  const bytesOfHex = (hex) => Uint8Array.from(hex.match(/../g).map((h) => parseInt(h, 16)));

  function concat(parts) {
    const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
    let at = 0;
    for (const part of parts) { out.set(part, at); at += part.length; }
    return out;
  }

  function parseIPv6(text) {
    if (!/^[0-9a-fA-F:]+$/.test(text)) return null;          // no zone, no embedded IPv4 part
    const halves = text.split('::');
    if (halves.length > 2) return null;
    const head = halves[0] === '' ? [] : halves[0].split(':');
    const tail = halves.length === 2 && halves[1] !== '' ? halves[1].split(':') : [];
    if (halves.length === 1 ? head.length !== 8 : head.length + tail.length > 7) return null;
    const groups = [...head, ...Array(halves.length === 2 ? 8 - head.length - tail.length : 0).fill('0'), ...tail];
    const bytes = new Uint8Array(16);
    for (let i = 0; i < 8; i++) {
      if (!/^[0-9a-fA-F]{1,4}$/.test(groups[i])) return null;
      const v = parseInt(groups[i], 16);
      bytes[2 * i] = v >> 8;
      bytes[2 * i + 1] = v & 255;
    }
    return bytes;
  }

  function formatIPv6(bytes) {
    const groups = [];
    for (let i = 0; i < 16; i += 2) groups.push(((bytes[i] << 8) | bytes[i + 1]).toString(16));
    return groups.join(':');
  }

  /** An address as a candidate line has it: { kind: 0 IPv4 | 1 IPv6 | 2 mDNS name, bytes }, or null for anything else. */
  function parseAddress(text) {
    const v4 = /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/.exec(text);
    if (v4) {
      const numbers = v4.slice(1).map(Number);
      return numbers.some((n) => n > 255) ? null : { kind: 0, bytes: Uint8Array.from(numbers) };
    }
    const name = UUID_NAME.exec(text);
    if (name) return { kind: 2, bytes: bytesOfHex(name.slice(1).join('')) };
    if (text.includes(':')) { const bytes = parseIPv6(text); return bytes ? { kind: 1, bytes } : null; }
    return null;
  }

  function formatAddress(c) {
    if (c.kind === 0) return [...c.bytes].join('.');
    if (c.kind === 1) return formatIPv6(c.bytes);
    const h = hexOf(c.bytes);
    return h.slice(0, 8) + '-' + h.slice(8, 12) + '-' + h.slice(12, 16) + '-' + h.slice(16, 20) + '-' + h.slice(20) + '.local';
  }

  /** One a=candidate value: a candidate { type, kind, bytes, port }, { skip: true } for one that is not carried (TCP, RTCP), or null (not understood). */
  function parseCandidate(value) {
    const f = value.split(' ');
    if (f.length < 8 || f[6] !== 'typ') return null;
    const type = CANDIDATE_TYPES.indexOf(f[7]);
    if (type < 0 || !/^\d+$/.test(f[5]) || Number(f[5]) > 65535) return null;
    if (f[1] !== '1' || f[2].toLowerCase() !== 'udp') return { skip: true };
    const address = parseAddress(f[4]);
    return address ? { type, kind: address.kind, bytes: address.bytes, port: Number(f[5]) } : null;
  }

  /** The fields of a description, or null when it is not the plain description of one data channel connection that a packed code can carry. */
  function parseSdp(sdp) {
    if (typeof sdp !== 'string') return null;
    const lines = sdp.split(/\r\n|\n/).filter((line) => line !== '');
    if (lines[0] !== 'v=0') return null;
    const found = { ufrag: null, pwd: null, fingerprint: null, setup: -1, candidates: [] };
    let media = 0, mid = false;
    for (const line of lines) {
      if (line[1] !== '=') return null;
      if (line[0] === 'm') {
        if (++media > 1 || !/^m=application \d+ UDP\/DTLS\/SCTP webrtc-datachannel$/.test(line)) return null;
      } else if (line[0] === 'a') {
        const colon = line.indexOf(':');
        const name = colon < 0 ? line.slice(2) : line.slice(2, colon);
        const value = colon < 0 ? '' : line.slice(colon + 1);
        if (name === 'ice-ufrag') { if (found.ufrag !== null && found.ufrag !== value) return null; found.ufrag = value; }
        else if (name === 'ice-pwd') { if (found.pwd !== null && found.pwd !== value) return null; found.pwd = value; }
        else if (name === 'fingerprint') {
          const m = /^sha-256 ([0-9A-Fa-f]{2}(?::[0-9A-Fa-f]{2}){31})$/.exec(value);
          if (!m) return null;
          const bytes = bytesOfHex(m[1].replace(/:/g, ''));
          if (found.fingerprint !== null && hexOf(found.fingerprint) !== hexOf(bytes)) return null;
          found.fingerprint = bytes;
        } else if (name === 'setup') {
          const at = SETUPS.indexOf(value);
          if (at < 0 || (found.setup >= 0 && found.setup !== at)) return null;
          found.setup = at;
        } else if (name === 'mid') { if (value !== '0') return null; mid = true; }
        else if (name === 'group') { if (value !== 'BUNDLE 0') return null; }
        else if (name === 'sctp-port') { if (value !== '5000') return null; }
        else if (name === 'candidate') {
          const c = parseCandidate(value);
          if (c === null) return null;
          if (!c.skip) found.candidates.push(c);
        } else if (!IGNORED_ATTRIBUTES.has(name)) return null;
      } else if (!'vostc'.includes(line[0])) return null;
    }
    const login = (text, least) => text !== null && text.length >= least && text.length <= 255 && [...text].every((c) => ICE_INDEX.has(c));
    if (media !== 1 || !mid || !login(found.ufrag, 4) || !login(found.pwd, 22) || found.fingerprint === null || found.setup < 0) return null;
    if (found.candidates.length === 0 || found.candidates.length > 255) return null;
    return found;
  }

  function sameFields(a, b) {
    return !!a && !!b && a.ufrag === b.ufrag && a.pwd === b.pwd && a.setup === b.setup && hexOf(a.fingerprint) === hexOf(b.fingerprint) &&
      a.candidates.length === b.candidates.length &&
      a.candidates.every((c, i) => c.type === b.candidates[i].type && c.kind === b.candidates[i].kind && c.port === b.candidates[i].port && hexOf(c.bytes) === hexOf(b.candidates[i].bytes));
  }

  /** The characters of the ICE login, 6 bits each, most significant first. */
  function packLogin(text) {
    const out = new Uint8Array(Math.ceil(text.length * 6 / 8));
    let acc = 0, bits = 0, at = 0;
    for (const c of text) {
      acc = (acc << 6) | ICE_INDEX.get(c);
      bits += 6;
      while (bits >= 8) { bits -= 8; out[at++] = (acc >> bits) & 255; }
      acc &= (1 << bits) - 1;
    }
    if (bits > 0) out[at++] = (acc << (8 - bits)) & 255;
    return out;
  }

  function unpackLogin(bytes, count) {
    let acc = 0, bits = 0, at = 0, out = '';
    for (let i = 0; i < count; i++) {
      while (bits < 6) { acc = (acc << 8) | bytes[at++]; bits += 8; }
      bits -= 6;
      out += ICE_CHARS[(acc >> bits) & 63];
      acc &= (1 << bits) - 1;
    }
    return acc === 0 ? out : null;          // the padding bits are zero
  }

  /* The packed fields:   flags            bits 0-1 the DTLS role (a=setup), bit 2 the login has Chrome's sizes (4 and 24 characters), else two length bytes follow
   *                      login            the user fragment and the password, 6 bits a character
   *                      fingerprint      32 bytes (SHA-256)
   *                      candidates       a count, then for each: type (bits 0-1) and address kind (bits 2-3: IPv4, IPv6, mDNS name), the address (4 or 16 bytes), the port (2) */
  function packFields(found) {
    const sized = found.ufrag.length === 4 && found.pwd.length === 24;
    const parts = [Uint8Array.of(found.setup | (sized ? 4 : 0))];
    if (!sized) parts.push(Uint8Array.of(found.ufrag.length, found.pwd.length));
    parts.push(packLogin(found.ufrag + found.pwd), found.fingerprint, Uint8Array.of(found.candidates.length));
    for (const c of found.candidates) parts.push(Uint8Array.of(c.type | (c.kind << 2)), c.bytes, Uint8Array.of(c.port >> 8, c.port & 255));
    return concat(parts);
  }

  /** The fields of packed bytes, or null when they are not exactly what packFields makes. */
  function unpackFields(bytes) {
    let at = 0;
    const take = (n) => { if (at + n > bytes.length) return null; const out = bytes.subarray(at, at + n); at += n; return out; };
    const flags = take(1);
    if (!flags || (flags[0] & ~7) !== 0 || (flags[0] & 3) > 2) return null;
    let userLength = 4, passwordLength = 24;
    if ((flags[0] & 4) === 0) {
      const lengths = take(2);
      if (!lengths || lengths[0] < 4 || lengths[1] < 22) return null;
      [userLength, passwordLength] = lengths;
    }
    const packed = take(Math.ceil((userLength + passwordLength) * 6 / 8));
    const login = packed && unpackLogin(packed, userLength + passwordLength);
    const fingerprint = take(32);
    const count = take(1);
    if (login === null || login === undefined || !fingerprint || !count || count[0] === 0) return null;
    const candidates = [];
    for (let i = 0; i < count[0]; i++) {
      const head = take(1);
      if (!head || (head[0] & 0xf0) !== 0 || ((head[0] >> 2) & 3) > 2) return null;
      const kind = (head[0] >> 2) & 3;
      const address = take(kind === 0 ? 4 : 16);
      const port = take(2);
      if (!address || !port) return null;
      candidates.push({ type: head[0] & 3, kind, bytes: Uint8Array.from(address), port: (port[0] << 8) | port[1] });
    }
    if (at !== bytes.length) return null;
    return { ufrag: login.slice(0, userLength), pwd: login.slice(userLength), fingerprint: Uint8Array.from(fingerprint), setup: flags[0] & 3, candidates };
  }

  /** The description for the fields, written the way Chrome writes one for two negotiated data channels (and without end-of-candidates, as Chrome does). */
  function buildSdp(found) {
    const lines = ['v=0', 'o=- 1 2 IN IP4 127.0.0.1', 's=-', 't=0 0', 'a=group:BUNDLE 0', 'a=extmap-allow-mixed', 'a=msid-semantic: WMS',
      'm=application 9 UDP/DTLS/SCTP webrtc-datachannel', 'c=IN IP4 0.0.0.0'];
    found.candidates.forEach((c, i) => {
      const priority = ((TYPE_PREFERENCE[c.type] << 24) | ((65535 - Math.min(i, 65535)) << 8) | 255) >>> 0;   // the order of the list stays the order of preference
      let line = 'a=candidate:' + (i + 1) + ' 1 udp ' + priority + ' ' + formatAddress(c) + ' ' + c.port + ' typ ' + CANDIDATE_TYPES[c.type];
      if (c.type !== 0) line += ' raddr ' + (c.kind === 1 ? '::' : '0.0.0.0') + ' rport 0';
      lines.push(line + ' generation 0');
    });
    lines.push('a=ice-ufrag:' + found.ufrag, 'a=ice-pwd:' + found.pwd, 'a=ice-options:trickle',
      'a=fingerprint:sha-256 ' + hexOf(found.fingerprint).toUpperCase().match(/../g).join(':'), 'a=setup:' + SETUPS[found.setup],
      'a=mid:0', 'a=sctp-port:5000', 'a=max-message-size:262144');
    return lines.join('\r\n') + '\r\n';
  }

  /** kind: 'offer' or 'answer'. Returns the code text. */
  async function encodeCode(kind, sdp) {
    if (kind !== 'offer' && kind !== 'answer') throw new CodeError('kind', 'a code is an offer or an answer');
    const found = parseSdp(sdp);
    if (found) {
      const packed = packFields(found);
      const back = unpackFields(packed);
      if (sameFields(found, back) && sameFields(found, parseSdp(buildSdp(back)))) {      // nothing is lost on the way: otherwise the whole description goes
        const head = PREFIX + COMPACT_VERSION + (kind === 'offer' ? 'o' : 'a') + '.' + base64urlEncode(packed);
        return head + '.' + checkOf(head);
      }
    }
    const raw = new TextEncoder().encode(sdp);
    let flag = 0, data = raw;
    if (canCompress()) {
      try { data = await pipe(raw, new CompressionStream('deflate-raw')); flag = 1; } catch (e) { data = raw; flag = 0; }
    }
    const body = new Uint8Array(data.length + 1);
    body[0] = flag;
    body.set(data, 1);
    const head = PREFIX + VERSION + (kind === 'offer' ? 'o' : 'a') + '.' + base64urlEncode(body);
    return head + '.' + checkOf(head);
  }

  /** Reads what a player pasted (whitespace, quotes and line breaks added by chat programs are ignored). Throws CodeError. */
  async function decodeCode(text, expectedKind) {
    const clean = String(text || '').replace(/[\s"'`<>]/g, '');
    if (clean === '') throw new CodeError('empty', 'Paste the code first.');
    const start = clean.indexOf(PREFIX);
    if (start < 0) throw new CodeError('prefix', 'This is not a connection code of this game (it must start with GBA2-).');
    // head.payload.check; words or a full stop pasted after the code are ignored (the check is exactly four characters)
    const parts = clean.slice(start).split('.');
    if (parts.length < 3 || parts[2].length < 4) throw new CodeError('shape', 'The code is cut off: copy it again as one piece.');
    const head = parts[0], payload = parts[1], check = parts[2].slice(0, 4);
    const match = /^GBA2-(\d+)([oa])$/.exec(head);
    if (!match) throw new CodeError('prefix', 'This is not a connection code of this game.');
    const version = Number(match[1]);
    if (version !== VERSION && version !== COMPACT_VERSION) throw new CodeError('version', 'This code comes from another version of the game (' + match[1] + '); both players need the same page.');
    const kind = match[2] === 'o' ? 'offer' : 'answer';
    if (expectedKind && kind !== expectedKind) {
      throw new CodeError('kind', kind === 'offer'
        ? 'This is a host code (an offer). To join the match paste it under "Join"; the host needs your answer code instead.'
        : 'This is an answer code. The host pastes it under "Host"; to join a match paste the host\'s code.');
    }
    if (checkOf(head + '.' + payload) !== check) throw new CodeError('check', 'The code has a mistake in it (it is cut off or a character is wrong): copy it again.');
    const body = base64urlDecode(payload);
    if (version === COMPACT_VERSION) {
      const found = body === null ? null : unpackFields(body);
      if (!found) throw new CodeError('shape', 'The code cannot be read: copy it again.');
      return { kind, sdp: buildSdp(found) };
    }
    if (body === null || body.length < 2) throw new CodeError('shape', 'The code cannot be read: copy it again.');
    let data = body.subarray(1);
    if (body[0] === 1) {
      if (!canCompress()) throw new CodeError('browser', 'This browser cannot read compressed codes (it needs a current Chrome, Edge, Firefox or Safari).');
      try { data = await pipe(data, new DecompressionStream('deflate-raw')); } catch (e) { throw new CodeError('shape', 'The code cannot be read: copy it again.'); }
    } else if (body[0] !== 0) throw new CodeError('version', 'This code comes from another version of the game.');
    const sdp = new TextDecoder().decode(data);
    if (!sdp.startsWith('v=0')) throw new CodeError('shape', 'The code cannot be read: copy it again.');
    return { kind, sdp };
  }

  // ---- room codes: four characters instead of two long codes ----------------------------------------------------------------------

  /* The host's page listens on a topic of a public relay that is named after the room code; the guest's page posts a join there, with a random inbox topic of its own;
   * the host puts its long code into that inbox, and the guest puts its long answer into the room: the two pages swap what the players would otherwise paste, and
   * nothing else goes through the relay. The relay is anything that speaks the small part of the ntfy API used here (POST a message to a topic, listen to a topic with
   * server-sent events); the default is https://ntfy.sh, which needs no account. Nothing is cached (?cache=no): a message reaches whoever listens at that moment and is
   * not kept. A room code has about a million values, so a stranger can guess one while the room is open: the first guest to answer gets the room, a later one is told
   * it is taken, and the host's page says that someone joined (docs/netplay_transport.md, section 2b). */

  const DEFAULT_RELAY = 'https://ntfy.sh';
  const ROOM_ALPHABET = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';      // 32 characters: no I, O, 0 or 1, which are read wrongly
  const ROOM_TOPIC = 'gba2-r-';                                  // + the code: where the host listens
  const INBOX_TOPIC = 'gba2-g-';                                 // + 32 random hex digits: where a guest listens

  class RoomError extends Error {
    constructor(reason, message) { super(message); this.name = 'RoomError'; this.reason = reason; }
  }

  const randomBytes = (n) => { const out = new Uint8Array(n); globalThis.crypto.getRandomValues(out); return out; };

  function newRoomCode() { return [...randomBytes(4)].map((x) => ROOM_ALPHABET[x & 31]).join(''); }

  /** What a player typed ("k7q f", "K7Q-F") as a room code, 'K7QF', or null when it is not four characters of the alphabet (the page then tries it as a long code). */
  function parseRoomCode(text) {
    const t = String(text || '').trim().toUpperCase().replace(/[\s-]/g, '');
    return t.length === 4 && [...t].every((c) => ROOM_ALPHABET.includes(c)) ? t : null;
  }

  async function relayPost(relay, topic, message) {
    const response = await fetch(relay + '/' + topic + '?cache=no', { method: 'POST', body: JSON.stringify(message) });   // a plain text body: no CORS preflight
    if (!response.ok) throw new Error('the relay answered ' + response.status);
  }

  /** Listens to a topic. `opened` resolves when the stream is up (rejects after openTimeoutMs); onmessage gets each message of ours (JSON with v: 1 and a string t). */
  function relayListen(relay, topic, onmessage, { openTimeoutMs = 8000 } = {}) {
    let closed = false, timer = 0, source = null;
    const opened = new Promise((resolve, reject) => {
      try { source = new EventSource(relay + '/' + topic + '/sse'); } catch (e) { reject(e); return; }
      timer = setTimeout(() => reject(new Error('the relay did not answer')), openTimeoutMs);
      source.onopen = () => { clearTimeout(timer); resolve(); };
      source.onmessage = (event) => {
        let inner;
        try { const outer = JSON.parse(event.data); if (outer.event !== 'message') return; inner = JSON.parse(outer.message); } catch (e) { return; }
        if (!closed && inner && inner.v === 1 && typeof inner.t === 'string') { try { onmessage(inner); } catch (e) { /* the handler's problem */ } }
      };
    });
    return { opened, close() { closed = true; clearTimeout(timer); try { if (source) source.close(); } catch (e) { /* closed */ } } };
  }

  /**
   * The host's side: listens in room `code`. Resolves when the room is live; rejects when the relay cannot be reached. onjoin(inbox) is called for each guest that joins
   * (at most 8) until the first answer has arrived, and room.offer(inbox, longCode) then sends the host's long code to that guest; onanswer(longCode) gets the first answer,
   * which locks the room: a guest that joins after that is told it is taken. (So a friend who joins just before a stranger is not locked out, and one who reloads the page
   * and joins again can.)
   */
  async function openRoom(relay, code, { onjoin, onanswer, openTimeoutMs = 8000 }) {
    const offered = new Set();
    let locked = false;
    const listener = relayListen(relay, ROOM_TOPIC + code, (m) => {
      if (typeof m.re !== 'string' || !/^[0-9a-f]{32}$/.test(m.re)) return;
      if (m.t === 'join') {
        if (locked) relayPost(relay, INBOX_TOPIC + m.re, { v: 1, t: 'busy' }).catch(() => {});
        else if (!offered.has(m.re) && offered.size < 8) { offered.add(m.re); onjoin(m.re); }
      } else if (m.t === 'answer' && !locked && offered.has(m.re) && typeof m.code === 'string') { locked = true; onanswer(m.code); }
    }, { openTimeoutMs });
    try { await listener.opened; } catch (e) { listener.close(); throw new RoomError('relay', 'The short-code service could not be reached.'); }
    return {
      code,
      offer: (inbox, longCode) => relayPost(relay, INBOX_TOPIC + inbox, { v: 1, t: 'offer', code: longCode }),
      close: () => listener.close(),
    };
  }

  /**
   * The guest's side: joins room `code`; resolves with { offer, answer(longCode), close() } when the host's long code has arrived. Rejects with a RoomError whose reason is
   * 'relay' (not reachable), 'none' (nobody answered in waitMs: no such room) or 'busy' (somebody else got there first).
   */
  async function joinRoom(relay, code, { waitMs = 15000, openTimeoutMs = 8000 } = {}) {
    const inbox = [...randomBytes(16)].map((b) => b.toString(16).padStart(2, '0')).join('');
    let resolveOffer, rejectOffer;
    const offer = new Promise((resolve, reject) => { resolveOffer = resolve; rejectOffer = reject; });
    offer.catch(() => {});      // a rejection that arrives before anyone awaits it is not an error of its own
    const listener = relayListen(relay, INBOX_TOPIC + inbox, (m) => {
      if (m.t === 'offer' && typeof m.code === 'string') resolveOffer(m.code);
      else if (m.t === 'busy') rejectOffer(new RoomError('busy', 'Someone has already joined that match.'));
    }, { openTimeoutMs });
    const unreachable = new RoomError('relay', 'The short-code service could not be reached.');
    try { await listener.opened; } catch (e) { listener.close(); throw unreachable; }
    try { await relayPost(relay, ROOM_TOPIC + code, { v: 1, t: 'join', re: inbox }); } catch (e) { listener.close(); throw unreachable; }
    const timer = setTimeout(() => rejectOffer(new RoomError('none', 'No match is waiting with that code. Check it, or ask your friend to press Host a match again.')), waitMs);
    let longCode;
    try { longCode = await offer; } catch (e) { listener.close(); throw e; } finally { clearTimeout(timer); }
    return { offer: longCode, answer: (answerCode) => relayPost(relay, ROOM_TOPIC + code, { v: 1, t: 'answer', re: inbox, code: answerCode }), close: () => listener.close() };
  }

  // ---- the connection ------------------------------------------------------------------------------------------

  /**
   * States: new -> gathering -> (host: offered | guest: answered) -> connecting -> open, and failed or closed at any point.
   * Callbacks (all optional): onstate(state, detail), ondatagram(Uint8Array), oncontrol(object), onlog(text).
   */
  class Link {
    constructor({ iceServers = DEFAULT_ICE_SERVERS, gatherTimeoutMs = 6000, connectTimeoutMs = 25000, guestWaitMs = 180000, onstate, ondatagram, oncontrol, onlog } = {}) {
      this.iceServers = iceServers;
      this.gatherTimeoutMs = gatherTimeoutMs;
      this.connectTimeoutMs = connectTimeoutMs;     // the host, from the moment it has the answer: the browsers need a few seconds at most
      this.guestWaitMs = guestWaitMs;               // the guest, from the moment it made its answer: the answer travels by hand to the host first
      this.onstate = onstate || null;
      this.ondatagram = ondatagram || null;
      this.oncontrol = oncontrol || null;
      this.onlog = onlog || null;
      this.state = 'new';
      this.detail = '';
      this.role = null;                     // 'host' (made the offer) or 'guest'
      this.pc = null;
      this.control = null;
      this.game = null;
      this.candidates = [];
      this.queue = [];                      // datagrams received and not yet taken by poll()
      this.stats = { sent: 0, received: 0, bytes_sent: 0, bytes_received: 0, dropped_busy: 0, dropped_closed: 0, dropped_sim: 0, queue_overflow: 0, buffered_max: 0, buffered_sum: 0 };
      this.openedAt = 0;
      this.connectTimer = 0;
      this.sim = null;                      // see setSim
    }

    /** A bad network on purpose, for trying the settings on one machine: what this side SENDS on the game channel is delayed by
     *  delay_ms (+ up to jitter_ms) and each datagram is lost with probability loss (0..1). null or all zero: off. */
    setSim(sim) {
      this.sim = sim && (sim.delay_ms > 0 || sim.jitter_ms > 0 || sim.loss > 0) ? { delay_ms: +sim.delay_ms || 0, jitter_ms: +sim.jitter_ms || 0, loss: +sim.loss || 0 } : null;
    }

    #log(text) { if (this.onlog) this.onlog(text); }

    #set(state, detail = '') {
      if (this.state === 'closed' || (this.state === 'failed' && state !== 'closed')) return;
      this.state = state;
      this.detail = detail;
      this.#log('link ' + state + (detail ? ': ' + detail : ''));
      if (this.onstate) { try { this.onstate(state, detail); } catch (e) { /* the listener's problem */ } }
    }

    #create() {
      if (typeof RTCPeerConnection !== 'function') throw new Error('This browser has no WebRTC, so online play is not available in it.');
      const pc = new RTCPeerConnection({ iceServers: this.iceServers });
      this.pc = pc;
      pc.onicecandidate = (event) => { if (event.candidate) this.candidates.push(event.candidate.candidate); };
      pc.onconnectionstatechange = () => {
        this.#log('connection state ' + pc.connectionState);
        if (pc.connectionState === 'failed') {
          // A guest has been checking paths since it made its answer, long before the host has it (the answer is carried by hand): the
          // host's own checks, once it has the answer, revive the pairs, so the guest goes on waiting; its timer ends the wait.
          if (this.role === 'guest' && this.state === 'connecting') this.#log('connection failed while waiting for the host (the host\'s checks may still revive it)');
          else this.#set('failed', 'No direct path between the two computers could be found (a firewall or a strict router blocks it).');
        }
        else if (pc.connectionState === 'closed') this.#set('closed', 'The connection was closed.');
        else if (pc.connectionState === 'disconnected' && this.state === 'open') this.#log('connection disconnected (may recover)');
      };
      this.control = pc.createDataChannel('control', { ordered: true, negotiated: true, id: CHANNEL_CONTROL });
      this.game = pc.createDataChannel('game', { ordered: false, maxPacketLifeTime: GAME_LIFETIME_MS, negotiated: true, id: CHANNEL_GAME });
      this.game.binaryType = 'arraybuffer';
      this.control.onmessage = (event) => {
        if (typeof event.data !== 'string' || !this.oncontrol) return;
        let message;
        try { message = JSON.parse(event.data); } catch (e) { return; }
        try { this.oncontrol(message); } catch (e) { this.#log('control handler: ' + e); }
      };
      this.game.onmessage = (event) => {
        const bytes = new Uint8Array(event.data);
        ++this.stats.received;
        this.stats.bytes_received += bytes.length;
        if (this.ondatagram) { this.ondatagram(bytes); return; }
        if (this.queue.length >= 512) { ++this.stats.queue_overflow; this.queue.shift(); }
        this.queue.push(bytes);
      };
      let opened = 0;
      const channelOpen = () => {
        if (++opened === 2) {
          clearTimeout(this.connectTimer);
          this.openedAt = performance.now();
          this.#set('open');
        }
      };
      this.control.onopen = channelOpen;
      this.game.onopen = channelOpen;
      const closed = () => { if (this.state === 'open' || this.state === 'connecting') this.#set('closed', 'The other player left or the connection was lost.'); };
      this.control.onclose = closed;
      this.game.onclose = closed;
      return pc;
    }

    #gathered() {
      const pc = this.pc;
      return new Promise((resolve, reject) => {
        const done = () => {
          clearTimeout(timer);
          pc.removeEventListener('icegatheringstatechange', check);
          if (this.candidates.length === 0 && !/a=candidate:/.test(pc.localDescription.sdp)) {
            reject(new Error('No network address could be found for this computer, so nobody can connect to it.'));
          } else resolve();
        };
        const check = () => { if (pc.iceGatheringState === 'complete') done(); };
        const timer = setTimeout(done, this.gatherTimeoutMs);
        pc.addEventListener('icegatheringstatechange', check);
        check();
      });
    }

    #armConnectTimer() {
      clearTimeout(this.connectTimer);
      const guest = this.role === 'guest';
      this.connectTimer = setTimeout(() => {
        if (this.state === 'connecting') {
          this.#set('failed', guest
            ? 'The host did not connect in time. The host must paste your answer code and press Connect; start again if it took too long.'
            : 'The connection did not come up: no direct path between the two computers could be found, or the answer code is not the one for this host code.');
        }
      }, guest ? this.guestWaitMs : this.connectTimeoutMs);
    }

    /** The host: returns the offer code to give to the other player. */
    async createOffer() {
      if (this.state !== 'new') throw new Error('this link was used already');
      this.role = 'host';
      const pc = this.#create();
      this.#set('gathering');
      try {
        await pc.setLocalDescription(await pc.createOffer());
        await this.#gathered();
      } catch (e) { this.#set('failed', String(e && e.message || e)); throw e; }
      const code = await encodeCode('offer', pc.localDescription.sdp);
      this.#set('offered');
      return code;
    }

    /** The host, with the guest's answer code. */
    async acceptAnswer(text) {
      if (this.state !== 'offered') throw new Error('there is no offer waiting for an answer');
      const { sdp } = await decodeCode(text, 'answer');
      try { await this.pc.setRemoteDescription({ type: 'answer', sdp }); } catch (e) {
        throw new CodeError('sdp', 'The browser did not accept that code (is it the answer to this host code, and not an older one?).');
      }
      this.#set('connecting');
      this.#armConnectTimer();
    }

    /** The guest, with the host's offer code: returns the answer code to give back. */
    async acceptOffer(text) {
      if (this.state !== 'new') throw new Error('this link was used already');
      const { sdp } = await decodeCode(text, 'offer');
      this.role = 'guest';
      const pc = this.#create();
      this.#set('gathering');
      try {
        await pc.setRemoteDescription({ type: 'offer', sdp });
        await pc.setLocalDescription(await pc.createAnswer());
        await this.#gathered();
      } catch (e) {
        const wasCode = e && e.name === 'InvalidAccessError' || /remote|sdp|description/i.test(String(e && e.message));
        this.#set('failed', String(e && e.message || e));
        throw wasCode ? new CodeError('sdp', 'The browser did not accept that code (is it a host code of this game?).') : e;
      }
      const code = await encodeCode('answer', pc.localDescription.sdp);
      this.#set('connecting');
      this.#armConnectTimer();
      return code;
    }

    /** One datagram on the unreliable channel. Returns false when it was not sent (channel not open, or its queue is full: the
     *  next datagram repeats what this one carried). */
    send(bytes) {
      const channel = this.game;
      if (!channel || channel.readyState !== 'open') { ++this.stats.dropped_closed; return false; }
      const sim = this.sim;
      if (sim) {
        if (Math.random() < sim.loss) { ++this.stats.dropped_sim; return true; }
        const wait = sim.delay_ms + Math.random() * sim.jitter_ms;
        if (wait >= 1) { setTimeout(() => this.#write(bytes), wait); return true; }
      }
      return this.#write(bytes);
    }

    #write(bytes) {
      const channel = this.game;
      if (!channel || channel.readyState !== 'open') { ++this.stats.dropped_closed; return false; }
      const queued = channel.bufferedAmount;
      if (queued > this.stats.buffered_max) this.stats.buffered_max = queued;
      this.stats.buffered_sum += queued;        // with `sent`: the mean queue a datagram found (0 on a healthy link)
      if (queued > MAX_BUFFERED) { ++this.stats.dropped_busy; return false; }
      try { channel.send(bytes); } catch (e) { ++this.stats.dropped_closed; return false; }
      ++this.stats.sent;
      this.stats.bytes_sent += bytes.length;
      return true;
    }

    /** The oldest datagram that arrived and was not handed to ondatagram, or null (the page's frame loop polls). */
    poll() { return this.queue.length ? this.queue.shift() : null; }

    /** A message on the reliable channel (a JSON-serializable object). */
    sendControl(message) {
      const channel = this.control;
      if (!channel || channel.readyState !== 'open') return false;
      try { channel.send(JSON.stringify(message)); } catch (e) { return false; }
      return true;
    }

    /** Round-trip time and path of the selected candidate pair, from the browser's statistics (null when unknown). */
    async path() {
      if (!this.pc) return null;
      try {
        const report = await this.pc.getStats();
        let pair = null;
        const locals = new Map(), remotes = new Map();
        report.forEach((r) => {
          if (r.type === 'local-candidate') locals.set(r.id, r);
          else if (r.type === 'remote-candidate') remotes.set(r.id, r);
        });
        report.forEach((r) => { if (r.type === 'candidate-pair' && r.nominated && r.state === 'succeeded') pair = r; });
        if (!pair) return null;
        const local = locals.get(pair.localCandidateId), remote = remotes.get(pair.remoteCandidateId);
        return {
          rtt_ms: pair.currentRoundTripTime !== undefined ? Math.round(pair.currentRoundTripTime * 1000) : null,
          local_type: local ? local.candidateType : null, remote_type: remote ? remote.candidateType : null,
        };
      } catch (e) { return null; }
    }

    close(reason) {
      if (this.state === 'closed') return;
      clearTimeout(this.connectTimer);
      try { if (this.control && this.control.readyState === 'open') this.control.send(JSON.stringify({ t: 'bye', reason: reason || '' })); } catch (e) { /* closing anyway */ }
      this.#set('closed', reason || 'closed');
      try { this.pc?.close(); } catch (e) { /* closed */ }
    }
  }

  window.gba2Net = {
    Link, encodeCode, decodeCode, CodeError, DEFAULT_ICE_SERVERS, VERSION, COMPACT_VERSION, MAX_BUFFERED, GAME_LIFETIME_MS,
    sdp: { parse: parseSdp, pack: packFields, unpack: unpackFields, build: buildSdp, same: sameFields, checkOf, base64urlEncode, base64urlDecode },   // for the tests
    Room: { open: openRoom, join: joinRoom, newCode: newRoomCode, parse: parseRoomCode, Error: RoomError, DEFAULT_RELAY, ALPHABET: ROOM_ALPHABET },
  };
})();

/*
 * Online play in the page (ROADMAP N3; docs/netplay_session.md): the panel where two players exchange their codes, the handshake that
 * proves both pages run the same build and the same package, and the control of the game's online mode (the gba2_net_* functions of
 * the module, tools/battle_preview.c). The WebRTC link and the codes are web/netplay.js.
 *
 * The flow, host first:
 *   1. the host creates a code (the offer) and sends it to the guest by any chat program;
 *   2. the guest pastes it, gets an answer code and sends it back;
 *   3. the host pastes the answer and presses Connect: the link opens;
 *   4. over the control channel both pages say "hello" with their build and package identities; a difference ends the session with a
 *      plain message (two versions of the game do not play the same game);
 *   5. the host measures the round trip, picks the input delay and the rollback window and a session id, and tells the guest;
 *   6. both pages open the game's online mode (a fresh Versus selection with default save and options: gba2_net_prepare), exchange the
 *      hash of that starting state and compare (a difference means the games would diverge from the first frame);
 *   7. both start the rollback layer (gba2_net_go) and play; the page watches the layer (gba2_net_status) and ends the session when
 *      the link closes, the other player leaves, the games disagree or the connection is lost.
 *
 * window.gba2Online exposes the same steps to the browser tests (tests/web/run_netplay_tests.mjs).
 */
(() => {
  'use strict';

  const PROTO = 1;
  const $ = (id) => document.getElementById(id);

  const online = {
    state: 'idle',      // idle, hosting, joining, linked, preparing, playing, over
    view: 'choose',     // which step the panel shows while idle, hosting or joining: choose, host, join
    message: '',
    role: null,         // 'host' or 'guest'
    link: null,
    peer: null,         // what the other page said in its hello
    peerAway: false,    // the other player's tab is hidden: their game cannot run, ours waits
    room: null,         // a room code in use: { code, closed, handle }
    roomCode: '',       // the host's room code once it is live (the panel shows it)
    roomError: '',      // why the host has no room code (the relay could not be reached)
    session: null,      // { id, delay, prediction, local }
    info: {},           // the latest parsed gba2_net_status
    history: [],
    init,
    copyStats,          // the statistics of the match as an object (and on the clipboard): the chip's Copy stats button
  };
  window.gba2Online = online;

  let api = null, ui = null, dev = {}, log = () => {};
  let pollTimer = 0, rttSamples = [];
  let samples = [], lastSampleAt = 0;   // one line a second of how the match is going (copyStats): the newest 900
  let waiting = null;                 // { want: 't' value, resolve, reject, timer } for the handshake steps

  // ---- helpers -------------------------------------------------------------------------------------------------

  const module = () => api && api.module;
  const callText = (fn, ...args) => { const m = module(); return m && m[fn] ? m.UTF8ToString(m[fn](...args)) : ''; };

  function parseStatus(text) {
    const out = {};
    for (const line of String(text || '').split('\n')) {
      const i = line.indexOf('=');
      if (i > 0) out[line.slice(0, i)] = line.slice(i + 1);
    }
    return out;
  }

  function setState(state, message) {
    online.state = state;
    if (message !== undefined) online.message = message;
    online.history.push(state + (message ? ': ' + message : ''));
    document.documentElement.dataset.online = state;
    render();
  }

  // ---- the panel -----------------------------------------------------------------------------------------------

  function render() {
    if (!ui) return;
    const state = online.state;
    const early = state === 'idle' || state === 'hosting' || state === 'joining';
    ui.choose.hidden = !(state === 'idle' && online.view === 'choose');
    ui.hostBox.hidden = !(early && online.view === 'host');
    ui.joinBox.hidden = !(early && online.view === 'join');
    if (ui.room) { ui.room.hidden = !(state === 'hosting' && online.roomCode); ui.roomCode.textContent = online.roomCode || ''; }
    ui.leave.hidden = state === 'idle' && online.view === 'choose';
    ui.leave.textContent = state === 'over' ? 'Back to the game' : 'Cancel';
    ui.status.textContent = online.message || '';
    ui.status.classList.toggle('bad', state === 'over' && /disagree|lost|stopped|different|left|could not|cannot/i.test(online.message));
    ui.btn.setAttribute('aria-pressed', String(state !== 'idle'));
    const playing = state === 'playing' || state === 'over';
    ui.chip.hidden = !(playing || state === 'preparing' || state === 'linked');
    if (!playing) ui.chipReplay.hidden = true;
    if (state === 'playing' || state === 'over') {
      const s = online.info;
      const bits = [];
      bits.push(state === 'over' ? 'Online match ended' : 'Online · you are Player ' + (Number(s.local_player || 0) + 1));
      if (state === 'playing' && online.peerAway) bits.push('the other player is in another tab, waiting for them');
      else {
        if (state === 'playing' && s.rtt_ms !== undefined && Number(s.rtt_ms) >= 0) bits.push(s.rtt_ms + ' ms');
        if (state === 'playing' && s.rollbacks !== undefined) bits.push(s.rollbacks + ' rollbacks');
      }
      ui.chipText.textContent = bits.join(' · ');
      ui.chipReplay.hidden = !(Number(s.confirmed_frames || 0) > 0);   // the frames recorded: they stay after the session ended
    } else if (state === 'preparing') ui.chipText.textContent = 'Online · starting the match…';
    else if (state === 'linked') ui.chipText.textContent = 'Online · connected, checking the game versions…';
    if (state === 'playing' && !ui.panel.hidden) { releaseKeyboard(); ui.panel.hidden = true; }
  }

  /** Downloads the match so far as a replay: the pads of every confirmed frame of both players, which the headless runner replays to
   *  the very hashes the two games agreed on (docs/replay_format.md). Returns the number of frames saved, or 0. */
  function saveReplay() {
    const m = module();
    if (!m || !m._gba2_net_replay || !m.FS) return 0;
    const frames = m._gba2_net_replay();
    if (frames <= 0) { online.message = 'There is nothing to save yet.'; render(); return 0; }
    const bytes = m.FS.readFile('/netplay-match.replay');
    const when = new Date();
    const pad = (n) => String(n).padStart(2, '0');
    const name = 'gba2-online-' + when.getFullYear() + pad(when.getMonth() + 1) + pad(when.getDate()) + '-' + pad(when.getHours()) + pad(when.getMinutes()) + pad(when.getSeconds()) + '.replay';
    const url = URL.createObjectURL(new Blob([bytes], { type: 'text/plain' }));
    const link = document.createElement('a');
    link.href = url;
    link.download = name;
    link.hidden = true;
    document.body.appendChild(link);
    link.click();
    link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 30000);
    online.lastReplay = { name, frames, bytes: bytes.length };
    return frames;
  }

  // The host's choices of input delay and rollback window are remembered by this browser (a convenience; nothing depends on it).
  const SETTINGS_KEY = 'gba2.online.settings';
  const hasOption = (select, value) => Array.prototype.some.call(select.options, (o) => o.value === value);
  function loadSettings() {
    try {
      const saved = JSON.parse(localStorage.getItem(SETTINGS_KEY) || '{}');
      if (typeof saved.delay === 'string' && hasOption(ui.delay, saved.delay)) ui.delay.value = saved.delay;
      if (typeof saved.window === 'string' && hasOption(ui.window, saved.window)) ui.window.value = saved.window;
    } catch (e) { /* storage may be unavailable or hold something else */ }
  }
  function saveSettings() {
    try { localStorage.setItem(SETTINGS_KEY, JSON.stringify({ delay: ui.delay.value, window: ui.window.value })); } catch (e) { /* ignore */ }
  }

  /** The game gets the keyboard and the pads back: a code field that still has the focus (or still holds the game's input off) when the panel
   *  goes away would leave the player with controls that do nothing, and a browser does not always say "blur" for a field that was hidden. */
  function releaseKeyboard() {
    const active = document.activeElement;
    if (ui && active && active !== document.body && ui.panel.contains(active) && typeof active.blur === 'function') active.blur();
    const m = module();
    if (m && m._gba2_web_input) m._gba2_web_input(1);
  }

  function showPanel(show) {
    if (!show && ui.panel.contains(document.activeElement)) releaseKeyboard();
    ui.panel.hidden = !show;
    ui.btn.setAttribute('aria-expanded', String(show));
  }

  function copyFrom(textarea, button) {
    textarea.focus();
    textarea.select();
    const done = () => { const old = button.textContent; button.textContent = 'Copied'; setTimeout(() => { button.textContent = old; }, 1200); };
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(textarea.value).then(done, () => { try { document.execCommand('copy'); done(); } catch (e) { /* the player selects by hand */ } });
    else { try { document.execCommand('copy'); done(); } catch (e) { /* the player selects by hand */ } }
  }

  // ---- link, handshake -----------------------------------------------------------------------------------------

  /** The bad connection of the panel (or of GBA2_DEV.netplay.sim in the tests): what this page sends is delayed and thinned. */
  function currentSim() {
    if (dev.netplay && dev.netplay.sim) return dev.netplay.sim;
    if (!ui || !ui.simDelay || !ui.simLoss) return null;
    return { delay_ms: Number(ui.simDelay.value) || 0, jitter_ms: (Number(ui.simDelay.value) || 0) * 0.2, loss: Number(ui.simLoss.value) || 0 };
  }

  function newLink() {
    const settings = (dev.netplay && dev.netplay.link) || {};
    const iceServers = dev.netplay && dev.netplay.iceServers !== undefined ? dev.netplay.iceServers : window.gba2Net.DEFAULT_ICE_SERVERS;
    const link = new window.gba2Net.Link(Object.assign({
      iceServers,
      onstate: (state, detail) => linkState(link, state, detail),
      oncontrol: (message) => control(link, message),
      onlog: (text) => log('online: ' + text),
    }, settings));
    online.link = link;
    link.setSim(currentSim());
    const m = module();
    m.gba2NetSend = (bytes) => link.send(bytes);
    m.gba2NetReceive = () => link.poll();
    return link;
  }

  function linkState(link, state, detail) {
    if (link !== online.link) return;
    if (state === 'open' && online.state !== 'playing') {
      closeRoom();
      setState('linked', 'Connected. Checking that you both run the same game…');
      link.sendControl({ t: 'hello', proto: PROTO, build: api.build.id, game: api.build.assets.game.index.sha256, engine: api.build.engine.wasm });
      handshake(link);     // the clocks of the start-up messages run from the moment the link is open (the codes took as long as the players needed)
    } else if (state === 'failed') {
      end('The connection could not be made. ' + detail + (/direct path/.test(detail || '')
        ? ' Try again; if it keeps failing the two networks need a relay, which this version does not have.' : ' Try again.'));
    } else if (state === 'closed' && online.state !== 'idle' && online.state !== 'over') {
      end(online.peerBye ? 'The other player ' + describeBye(online.peerBye) : (detail || 'The connection was closed.'));
    }
  }

  /** What the other page said when it closed the link (link.close(reason)): 'left', 'closed', or a sentence of its own. */
  function describeBye(reason) {
    if (reason === 'left') return 'left the match.';
    if (reason === 'closed') return 'closed the page.';
    return 'stopped the match: ' + reason + '.';
  }

  function expect(type, ms) {
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => { waiting = null; reject(new Error('timeout waiting for ' + type)); }, ms);
      waiting = { want: type, resolve: (m) => { clearTimeout(timer); waiting = null; resolve(m); }, reject };
    });
  }

  function control(link, message) {
    if (link !== online.link || !message || typeof message !== 'object') return;
    if (message.t === 'bye') { online.peerBye = String(message.reason || 'they left'); return; }
    if (message.t === 'ping') { link.sendControl({ t: 'pong', n: message.n }); return; }
    if (message.t === 'away') { online.peerAway = !!message.away; render(); return; }
    if (message.t === 'hello') { online.peer = message; if (waiting && waiting.want === 'hello') waiting.resolve(message); else online.pendingHello = message; return; }
    if (waiting && waiting.want === message.t) waiting.resolve(message);
    else (online.pending = online.pending || {})[message.t] = message;
  }

  async function takeMessage(type, ms) {
    if (type === 'hello' && online.pendingHello) { const m = online.pendingHello; online.pendingHello = null; return m; }
    if (online.pending && online.pending[type]) { const m = online.pending[type]; delete online.pending[type]; return m; }
    return expect(type, ms);
  }

  const median = (list) => { const s = [...list].sort((a, b) => a - b); return s[Math.floor(s.length / 2)]; };

  async function measureRtt(link) {
    const samples = [];
    for (let n = 0; n < 6; n++) {
      const t0 = performance.now();
      link.sendControl({ t: 'ping', n });
      try { await takeMessage('pong', 3000); } catch (e) { break; }
      samples.push(performance.now() - t0);
    }
    return samples.length ? median(samples.slice(1).length ? samples.slice(1) : samples) : 100;
  }

  /** Delay and window for a round trip (ms): the delay is counted in network frames of a battle, two VBlanks each (33.3 ms, the
   *  original's VSync(2); the menus' one-VBlank frames are lockstep, where the layer sets its own delay), and leaves about one frame
   *  of the one-way trip to guess. The host's settings (and, for the tests, GBA2_DEV.netplay.delay / .prediction) override it. */
  function chooseSettings(rttMs) {
    const oneWayFrames = rttMs / 2 / (2000 / 60);
    let delay = Math.max(1, Math.min(5, Math.round(oneWayFrames) - 1));
    let prediction = 8;
    const chosenDelay = dev.netplay && dev.netplay.delay !== undefined ? String(dev.netplay.delay) : ui.delay ? ui.delay.value : 'auto';
    if (chosenDelay !== 'auto') delay = Math.max(0, Math.min(5, Number(chosenDelay) | 0));
    const chosenWindow = dev.netplay && dev.netplay.prediction !== undefined ? dev.netplay.prediction : ui.window ? Number(ui.window.value) : 8;
    if (chosenWindow >= 2 && chosenWindow <= 12) prediction = chosenWindow | 0;
    return { delay, prediction };
  }

  /** The fighters under the two cursors when the online Versus selection opens (0A:0A unless the host's page says otherwise: the tests). */
  function startBanks(value) {
    const ok = Array.isArray(value) && value.length === 2 && value.every((b) => Number.isInteger(b) && b >= 0 && b < 34);
    return ok ? [value[0], value[1]] : [10, 10];
  }

  async function handshake(link) {
    try {
      const theirs = await takeMessage('hello', 8000);
      const mine = { build: api.build.id, game: api.build.assets.game.index.sha256, engine: api.build.engine.wasm };
      if (theirs.proto !== PROTO || theirs.build !== mine.build || theirs.game !== mine.game || theirs.engine !== mine.engine) {
        const what = theirs.proto !== PROTO ? 'a different online protocol' : theirs.game !== mine.game ? 'different game data' : 'a different version of the page';
        link.sendControl({ t: 'bye', reason: 'we run different versions of the game' });
        return end('You and the other player run different versions of the game (' + what + '; yours ' + mine.build + ', theirs ' + String(theirs.build) + '). ' +
          'Reload the page (Ctrl+F5) and check that you both use the same address.');
      }
      let session;
      if (online.role === 'host') {
        const rtt = await measureRtt(link);
        const chosen = chooseSettings(rtt);
        const id = (crypto.getRandomValues(new Uint32Array(1))[0] | 1) >>> 0;
        const banks = startBanks(dev.netplay && dev.netplay.banks);
        session = { id, delay: chosen.delay, prediction: chosen.prediction, local: 0, rtt, banks };
        link.sendControl({ t: 'config', id, delay: chosen.delay, prediction: chosen.prediction, banks });
      } else {
        const config = await takeMessage('config', 20000);
        session = { id: config.id >>> 0, delay: config.delay, prediction: config.prediction, local: 1, banks: startBanks(config.banks) };
      }
      online.session = session;
      setState('preparing', 'Starting the match…');
      // Open the game's online mode: a second game at the Versus selection with default save and options. (Heavy: a second or two.)
      await new Promise((resolve) => setTimeout(resolve, 30));
      const failure = module()._gba2_net_prepare(session.local, session.delay, session.prediction, session.banks[0], session.banks[1]);
      if (failure !== 0) return end('The game could not start the online mode (' + callText('_gba2_net_error') + ').');
      const fixture = callText('_gba2_net_fixture');
      link.sendControl({ t: 'fixture', hash: fixture });
      const theirFixture = await takeMessage('fixture', 30000);
      if (theirFixture.hash !== fixture) {
        module()._gba2_net_stop();
        link.sendControl({ t: 'bye', reason: 'the two games start from different states' });
        return end('The two games do not start from the same state (' + fixture + ' against ' + String(theirFixture.hash) + '): playing would desynchronise at once. Check that you both run the same version of the page.');
      }
      const code = module()._gba2_net_go(session.id);
      if (code !== 0) return end('The game could not start the match (' + callText('_gba2_net_error') + ').');
      setState('playing', '');
      startPolling();
      if (document.hidden) setHidden(true);
    } catch (e) {
      if (online.state !== 'over' && online.state !== 'idle') end('The other player did not answer the start-up messages (' + (e && e.message || e) + ').');
    }
  }

  // ---- a hidden tab --------------------------------------------------------------------------------------------
  // A hidden tab gets no animation frames, so this player's game would stop sending and the other player's game would give the
  // connection up after five seconds. While the tab is hidden a timer (a browser lets it fire about once a second) keeps the layer and
  // the link alive instead: the other player's game waits for it and says why, and nothing is drawn or heard in the hidden tab.

  let backgroundTimer = 0;

  function stopBackground() { if (backgroundTimer) { clearInterval(backgroundTimer); backgroundTimer = 0; } }

  function setHidden(hidden) {
    if (online.state !== 'playing') return;
    stopBackground();
    if (online.link && online.link.state === 'open') online.link.sendControl({ t: 'away', away: hidden });
    if (hidden) {
      backgroundTimer = setInterval(() => {
        const m = module();
        if (m && m._gba2_net_background) m._gba2_net_background(performance.now());
      }, (dev.netplay && dev.netplay.backgroundMs) || 500);
    }
  }

  // ---- watching the game ---------------------------------------------------------------------------------------

  function startPolling() {
    stopPolling();
    pollTimer = setInterval(() => {
      const m = module();
      if (!m || !m._gba2_net_status) return;
      online.info = parseStatus(callText('_gba2_net_status'));
      if (online.state === 'playing') recordSample();
      if (online.state === 'playing' && online.info.phase === 'over') end(online.info.message || 'The online match ended.', true);
      else render();
    }, 250);
  }

  const SAMPLE_FIELDS = ['rtt_ms', 'advantage', 'head', 'confirmed', 'verified', 'rollbacks', 'max_depth', 'wrong', 'frames_run', 'speculative', 'lockstep', 'hitches', 'hitch_max',
    'forgiven', 'sent', 'received', 'updates', 'updates_slow', 'update_ms_max', 'drawn'];

  /** About once a second while playing: the numbers that say whether lag comes from the link (round trip, datagrams that did not arrive, the browser's send queue),
   *  from the game waiting for the other player (head against confirmed), or from this computer (slow updates). */
  function recordSample() {
    const now = performance.now();
    if (now - lastSampleAt < 1000) return;
    lastSampleAt = now;
    const s = online.info, link = online.link && online.link.stats ? online.link.stats : {};
    const row = [Math.round(now / 100) / 10];
    for (const key of SAMPLE_FIELDS) row.push(Number(s[key] !== undefined ? s[key] : -1));
    row.push(link.buffered_max || 0, link.dropped_busy || 0, link.dropped_sim || 0, link.sent || 0, link.received || 0, online.peerAway ? 1 : 0);
    samples.push(row);
    if (samples.length > 900) samples.shift();
  }

  /** The statistics of this match as text, for the clipboard: the settings, the path the browsers chose, the totals, and a line a second. */
  async function copyStats() {
    const link = online.link;
    let path = null;
    try { path = link && link.path ? await link.path() : null; } catch (e) { /* none */ }
    const report = {
      gba2_online_stats: 1, when: new Date().toISOString(), build: api && api.build && api.build.id, user_agent: navigator.userAgent, role: online.role,
      state: online.state, session: online.session && { delay: online.session.delay, prediction: online.session.prediction, rtt_at_start_ms: online.session.rtt },
      screen: { refresh_hint: window.screen && window.screen.width + 'x' + window.screen.height, ratio: window.devicePixelRatio }, path, link_state: link && link.state,
      link: link && link.stats, status: online.info,
      sample_columns: ['seconds'].concat(SAMPLE_FIELDS, ['buffered_max', 'dropped_busy', 'dropped_sim', 'link_sent', 'link_received', 'peer_away']), samples,
    };
    const text = JSON.stringify(report);
    let copied = false;
    try { await navigator.clipboard.writeText(text); copied = true; } catch (e) { /* not allowed: the fallback below */ }
    if (!copied) {
      const box = document.createElement('textarea');
      box.value = text; box.style.position = 'fixed'; box.style.opacity = '0';
      document.body.appendChild(box); box.select();
      try { copied = document.execCommand('copy'); } catch (e) { copied = false; }
      box.remove();
    }
    online.lastStats = { copied, bytes: text.length, samples: samples.length };
    const label = ui && ui.chipStats ? ui.chipStats : null;
    if (label) { const was = label.textContent; label.textContent = copied ? 'Copied' : 'Could not copy'; setTimeout(() => { label.textContent = was; }, 2500); }
    return report;
  }

  function stopPolling() { if (pollTimer) { clearInterval(pollTimer); pollTimer = 0; } }

  function end(message, fromGame) {
    if (online.state === 'over' || online.state === 'idle') return;
    online.info = parseStatus(callText('_gba2_net_status'));
    stopPolling();
    stopBackground();
    closeRoom();
    if (waiting) { waiting.reject(new Error('ended')); waiting = null; }
    if (online.link && online.link.state !== 'closed') online.link.close(message);
    // The game stays on its last picture until the player leaves (or the page is asked to).
    if (!fromGame && online.info.phase !== 'playing' && online.info.phase !== 'over') { try { module()._gba2_net_stop(); } catch (e) { /* not prepared */ } }
    setState('over', message);
    showPanel(true);
  }

  function reset() {
    stopPolling();
    stopBackground();
    closeRoom();
    if (waiting) { waiting.reject(new Error('left')); waiting = null; }
    if (online.link) { if (online.link.state !== 'closed') online.link.close('left'); online.link = null; }
    const m = module();
    if (m) { try { m._gba2_net_stop(); } catch (e) { /* none */ } m.gba2NetSend = null; m.gba2NetReceive = null; }
    if (ui) releaseKeyboard();
    online.role = null; online.peer = null; online.peerAway = false; online.session = null; online.info = {}; online.pending = {}; online.pendingHello = null; online.peerBye = null;
    samples = []; lastSampleAt = 0;
    online.view = 'choose';
    if (ui) { ui.offer.value = ''; ui.answerIn.value = ''; ui.offerIn.value = ''; ui.answerOut.value = ''; if (ui.answerBox) ui.answerBox.hidden = true; if (ui.long) ui.long.open = true; }
    setState('idle', '');
  }

  // ---- the steps (the buttons call these; so do the tests) -----------------------------------------------------

  /** Host, step 1: returns the code to send to the guest. */
  // ---- room codes -----------------------------------------------------------------------------------------------

  /** The relay of the room codes: GBA2_DEV.netplay.relay (a URL, or false for none: the tests that paste codes by hand), else ntfy.sh. */
  function relayUrl() {
    const configured = dev.netplay && dev.netplay.relay;
    if (configured === false) return null;
    return typeof configured === 'string' ? configured : window.gba2Net.Room.DEFAULT_RELAY;
  }

  function closeRoom() {
    const room = online.room;
    online.room = null;
    online.roomCode = '';
    online.roomError = '';
    if (room) { room.closed = true; clearTimeout(room.timer); if (room.handle) room.handle.close(); }
  }

  /**
   * Host: opens a room for the long code, in the background (the long code is on screen already, and works whatever happens here). When the room is live its code
   * appears in the panel and the long code folds away; when the relay cannot be reached the long code stays open and says so.
   */
  function startRoom(link, longCode) {
    const relay = relayUrl();
    if (!relay) return;
    const Room = window.gba2Net.Room;
    const room = { code: Room.newCode(), closed: false, handle: null };
    online.room = room;
    const opening = Room.open(relay, room.code, {
      openTimeoutMs: (dev.netplay && dev.netplay.relayOpenMs) || 8000,
      onjoin: async (inbox) => {
        if (online.link !== link || room.closed) return;
        online.message = 'Someone joined. Connecting…';
        render();
        try { const handle = await opening; await handle.offer(inbox, longCode); }
        catch (e) { online.message = 'The short-code service stopped answering. Send the long code instead.'; if (ui.long) ui.long.open = true; render(); }
      },
      onanswer: async (answer) => {
        if (online.link !== link || room.closed) return;
        try { await link.acceptAnswer(answer); online.message = 'Connecting…'; }
        catch (e) { online.message = 'That answer could not be used (' + String(e && e.message || e) + ') Ask your friend to join again.'; }
        render();
      },
    });
    opening.then((handle) => {
      if (room.closed) { handle.close(); return; }
      room.handle = handle;
      online.roomCode = room.code;
      online.message = 'Tell your friend the code above. The match starts when they join.';
      if (ui.long) ui.long.open = false;
      // A room code is a few characters that a stranger could guess, so it does not stay open for ever: the long code goes on working.
      room.timer = setTimeout(() => {
        if (online.room !== room || online.state !== 'hosting') return;
        closeRoom();
        online.message = 'That code has expired (a code lasts ten minutes). Press Cancel and Host a match again for a new one, or send the long code.';
        if (ui.long) ui.long.open = true;
        render();
      }, (dev.netplay && dev.netplay.roomTtlMs) || 10 * 60 * 1000);
      render();
    }).catch((e) => {
      if (room.closed) return;
      online.roomError = String(e && e.message || e);
      online.message = 'The short-code service could not be reached. Send the long code to your friend instead.';
      if (ui.long) ui.long.open = true;
      render();
    });
  }

  /** Guest: a room code the host told them. Finds the host through the relay, makes the answer and sends it back there; the link then opens as always. */
  async function guestJoinRoom(typed) {
    const Room = window.gba2Net.Room;
    const code = Room.parse(typed);
    if (!code) throw new Error('that is not a room code');
    if (online.state !== 'idle') throw new Error('an online session is already in progress');
    if (!module() || !module()._gba2_net_prepare) throw new Error('the game has not started yet');
    const relay = relayUrl();
    if (!relay) throw new Error('room codes are not available here');
    online.role = 'guest';
    online.view = 'join';
    setState('joining', 'Looking for the match…');
    const room = { code, closed: false, handle: null };
    online.room = room;
    let link = null;
    try {
      const joined = await Room.join(relay, code, { waitMs: (dev.netplay && dev.netplay.roomWaitMs) || 15000, openTimeoutMs: (dev.netplay && dev.netplay.relayOpenMs) || 8000 });
      room.handle = joined;
      if (room.closed) { joined.close(); return code; }          // the player left while it was looking
      online.message = 'Found the match. Connecting…';
      render();
      link = newLink();
      const answer = await link.acceptOffer(joined.offer);
      await joined.answer(answer);
      joined.close();
      room.handle = null;
      online.message = 'Connecting…';
      render();
      return code;
    } catch (e) {
      if (room.closed) return code;
      const reason = e && (e.name === 'RoomError' || e.name === 'CodeError');
      if (reason) {
        // nothing was started that matters: the guest can type the code again, or paste the long code
        closeRoom();
        if (link) { link.close('could not join'); online.link = null; }
        online.role = null;
        setState('idle', String(e.message) + (e.reason === 'relay' ? ' Ask your friend for the long code (under "The long code" on their screen) and paste it here instead.' : ''));
      } else end(String(e && e.message || e));
      throw e;
    }
  }

  async function hostCreate() {
    if (online.state !== 'idle') throw new Error('an online session is already in progress');
    if (!module() || !module()._gba2_net_prepare) throw new Error('the game has not started yet');
    online.role = 'host';
    online.view = 'host';
    setState('hosting', 'Making the code…');
    const link = newLink();
    try {
      const code = await link.createOffer();
      online.message = 'Send the code to your friend. When they send an answer back, paste it below and press Connect.';
      render();
      startRoom(link, code);        // in the background: when it is live the short code appears, and the long one folds away
      return code;
    } catch (e) { end(String(e && e.message || e)); throw e; }
  }

  /** Host, step 2: the guest's answer. */
  async function hostConnect(answer) {
    if (online.state !== 'hosting' || !online.link) throw new Error('make a host code first');
    try {
      await online.link.acceptAnswer(answer);
      closeRoom();
      online.message = 'Connecting…';
      render();
    } catch (e) {
      online.message = String(e && e.message || e);
      render();
      throw e;
    }
  }

  /** Guest: the host's code; returns the answer code to send back. */
  async function guestJoin(offer) {
    if (online.state !== 'idle') throw new Error('an online session is already in progress');
    if (!module() || !module()._gba2_net_prepare) throw new Error('the game has not started yet');
    online.role = 'guest';
    online.view = 'join';
    const link = newLink();
    setState('joining', 'Reading the code…');
    try {
      const answer = await link.acceptOffer(offer);
      online.message = 'Send this answer to the host. The match starts when the host presses Connect.';
      render();
      return answer;
    } catch (e) {
      if (e && e.name === 'CodeError') {
        // a code that cannot be read: nothing was started, the guest pastes another
        link.close('bad code');
        online.link = null;
        online.role = null;
        setState('idle', String(e.message));
      } else end(String(e && e.message || e));
      throw e;
    }
  }

  function leave() {
    reset();
    showPanel(false);
  }

  // ---- wiring --------------------------------------------------------------------------------------------------

  function init(context) {
    api = context.api;
    dev = context.dev || {};
    log = context.log || (() => {});
    ui = {
      btn: $('btn-online'), panel: $('online'), choose: $('online-choose'), hostBox: $('online-host-box'), joinBox: $('online-join-box'),
      offer: $('online-offer'), answerIn: $('online-answer-in'), offerIn: $('online-offer-in'), answerOut: $('online-answer-out'),
      room: $('online-room'), roomCode: $('online-room-code'), long: $('online-long'), answerBox: $('online-answer-box'),
      delay: $('online-delay'), window: $('online-window'), simDelay: $('online-sim-delay'), simLoss: $('online-sim-loss'), status: $('online-status'), leave: $('online-leave'), chip: $('online-chip'), chipText: $('online-chip-text'), chipReplay: $('online-chip-replay'), chipStats: $('online-chip-stats'), chipLeave: $('online-chip-leave'),
    };
    if (!ui.btn || !ui.panel) return;
    for (const select of [ui.simDelay, ui.simLoss]) if (select) select.addEventListener('change', () => { if (online.link) online.link.setSim(currentSim()); });
    if (ui.delay && ui.window) { loadSettings(); ui.delay.addEventListener('change', saveSettings); ui.window.addEventListener('change', saveSettings); }
    ui.btn.addEventListener('mousedown', (e) => e.preventDefault());
    ui.btn.addEventListener('click', () => {
      if (ui.btn.disabled) return;
      showPanel(ui.panel.hidden);
    });
    $('online-host').addEventListener('click', async () => {
      try { ui.offer.value = await hostCreate(); ui.offer.focus(); ui.offer.select(); } catch (e) { /* the status line has the message */ }
    });
    $('online-join').addEventListener('click', () => { online.view = 'join'; setState('idle', 'Type the code your friend sees, then press Join.'); ui.offerIn.focus(); });
    $('online-copy-offer').addEventListener('click', () => copyFrom(ui.offer, $('online-copy-offer')));
    $('online-copy-answer').addEventListener('click', () => copyFrom(ui.answerOut, $('online-copy-answer')));
    $('online-copy-room').addEventListener('click', () => {
      const button = $('online-copy-room'), text = ui.roomCode.textContent;
      const done = () => { button.textContent = 'Copied'; setTimeout(() => { button.textContent = 'Copy'; }, 1200); };
      if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).then(done, () => { /* the player reads it out */ }); else done();
    });
    $('online-connect').addEventListener('click', async () => { try { await hostConnect(ui.answerIn.value); } catch (e) { /* shown */ } });
    $('online-answer').addEventListener('click', async () => {
      if (online.link || online.state === 'joining') return;
      try {
        if (relayUrl() && window.gba2Net.Room.parse(ui.offerIn.value)) await guestJoinRoom(ui.offerIn.value);      // four characters: a room code
        else { ui.answerOut.value = await guestJoin(ui.offerIn.value); ui.answerBox.hidden = false; ui.answerOut.focus(); ui.answerOut.select(); }     // else the host's long code
      } catch (e) { /* the status line has the message */ }
    });
    ui.leave.addEventListener('click', leave);
    ui.chipLeave.addEventListener('click', leave);
    ui.chipReplay.addEventListener('click', saveReplay);
    if (ui.chipStats) ui.chipStats.addEventListener('click', copyStats);
    // Typing a code must not press game buttons or be eaten by the game's key handling.
    for (const field of [ui.offer, ui.answerIn, ui.offerIn, ui.answerOut, ui.delay, ui.window, ui.simDelay, ui.simLoss]) {
      if (!field) continue;
      field.addEventListener('focus', () => { const m = module(); if (m && m._gba2_web_input) m._gba2_web_input(0); });
      field.addEventListener('blur', () => { const m = module(); if (m && m._gba2_web_input) m._gba2_web_input(1); });
    }
    // The game's keyboard layer (SDL) listens on the window and consumes the keys it turns into its own events: it cancels every key press, so the browser
    // inserts nothing and a code cannot be typed (a paste with the mouse worked, which hid it). A key typed into a field of the panel must not travel that far.
    for (const type of ['keydown', 'keyup', 'keypress']) {
      ui.panel.addEventListener(type, (event) => {
        const target = event.target;
        if (target && (target.tagName === 'TEXTAREA' || target.tagName === 'INPUT' || target.tagName === 'SELECT')) event.stopPropagation();
      });
    }
    document.addEventListener('visibilitychange', () => setHidden(document.hidden));
    window.addEventListener('pagehide', () => { if (online.link && online.link.state === 'open') online.link.close('closed'); });
    online.hostCreate = hostCreate;
    online.hostConnect = hostConnect;
    online.guestJoin = guestJoin;
    online.guestJoinRoom = guestJoinRoom;
    online.leave = leave;
    online.saveReplay = saveReplay;
    online.enable = (on) => { ui.btn.disabled = !on; ui.btn.title = on ? 'Play against a friend over the internet' : 'Start the game first'; };
    online.enable(false);
    render();
  }
})();

/*
 * Page shell of the browser build: the asset loader, the module driver and the controls (docs/web_host.md).
 *
 *   1. instantiate the WebAssembly module (gba2.js / gba2.wasm) without running main();
 *   2. mount /save (IndexedDB-backed): the memory-card save and settings.cfg;
 *   3. download the game assets listed by assets/game/manifest.json, verify every file's SHA-256 against it, keep the
 *      verified bytes in IndexedDB (the second visit reads them from there) and write them into the module's
 *      in-memory file system under /assets;
 *   4. show "Click to start"; the click (a user gesture, which also unlocks Web Audio) calls main('--assets', '/assets');
 *   5. meanwhile fetch the optional 2x sprite art (assets/sprites2x, listed by a build-time index) the same way.
 *
 * Everything is relative to the page's own address, so it works under a sub-path (https://user.github.io/repo/).
 * window.gba2 exposes the state for the browser tests (tests/web). window.GBA2_DEV, when defined before this script
 * runs, carries test settings (extra arguments, environment, files to fetch into the file system, autostart).
 */
(() => {
  'use strict';

  const $ = (id) => document.getElementById(id);
  const build = JSON.parse($('gba2-build').textContent);
  const dev = window.GBA2_DEV || {};
  const ui = {
    canvas: $('canvas'), stage: $('stage'), overlay: $('overlay'), box: $('overlay-box'), title: $('overlay-title'),
    detail: $('overlay-detail'), bar: $('bar'), fill: $('bar-fill'), barText: $('bar-text'), start: $('start'),
    note: $('overlay-note'), logBox: $('log-box'), log: $('log'), status: $('status'),
    fullscreen: $('btn-fullscreen'), sound: $('btn-sound'), volume: $('volume'), volumeText: $('volume-text'), integer: $('btn-integer'), help: $('btn-help'), helpBox: $('help'),
  };

  const api = {
    build,
    phase: 'boot',          // boot, loading, ready, running, exited, error
    module: null,
    error: null,
    exitCode: null,
    log: [],
    timings: {},
    stats: { game: null, sprites2x: null },
    persist: { writes: 0, active: false, errors: 0, available: false },
    gl: null,
    status: {},
  };
  window.gba2 = api;
  const t0 = performance.now();
  const mark = (name) => { api.timings[name] = Math.round(performance.now() - t0); };
  mark('script');

  // ---- small helpers ---------------------------------------------------------------------------------------

  const MIB = 1024 * 1024;
  const formatBytes = (n) => (n >= 1e6 ? (n / 1e6).toFixed(1) + ' MB' : Math.max(1, Math.round(n / 1e3)) + ' kB');
  const HEX = Array.from({ length: 256 }, (_, i) => i.toString(16).padStart(2, '0'));

  async function sha256Hex(bytes) {
    const digest = new Uint8Array(await crypto.subtle.digest('SHA-256', bytes));
    let text = '';
    for (let i = 0; i < digest.length; i++) text += HEX[digest[i]];
    return text;
  }

  function logLine(text, isError) {
    api.log.push((isError ? '! ' : '') + text);
    if (api.log.length > 400) api.log.splice(0, api.log.length - 400);
    ui.log.textContent = api.log.slice(-60).join('\n');
    if (isError) console.warn(text); else console.log(text);
  }

  function setPhase(phase) {
    api.phase = phase;
    document.documentElement.dataset.phase = phase;
  }

  function showOverlay({ title, detail, note = '', error = false, progress = null, start = false }) {
    ui.overlay.hidden = false;
    ui.overlay.classList.toggle('error', error);
    ui.title.textContent = title;
    ui.detail.textContent = detail;
    ui.note.textContent = note;
    ui.bar.hidden = progress === null;
    if (progress !== null) setProgress(progress.fraction, progress.text);
    else ui.barText.textContent = '';
    ui.start.hidden = !start;
    ui.logBox.hidden = api.log.length === 0 && !error;
  }

  function setProgress(fraction, text) {
    const percent = Math.max(0, Math.min(100, Math.round(fraction * 100)));
    ui.fill.style.width = percent + '%';
    ui.bar.setAttribute('aria-valuenow', String(percent));
    ui.barText.textContent = text || '';
  }

  function fail(message, detail) {
    if (api.phase === 'error') return;
    api.error = message;
    setPhase('error');
    logLine(message + (detail ? ' ' + detail : ''), true);
    showOverlay({ title: 'The game could not run', detail: message, note: detail || '', error: true });
    ui.logBox.hidden = false;
    ui.logBox.open = true;
    addReload();
  }

  function addReload() {
    if ($('reload')) return;
    const button = document.createElement('button');
    button.id = 'reload';
    button.type = 'button';
    button.textContent = 'Reload the page';
    button.style.marginTop = '14px';
    button.addEventListener('click', () => location.reload());
    ui.box.insertBefore(button, ui.logBox);
  }

  // A WebAssembly trap (out-of-bounds access, unreachable) thrown out of the frame callback ends the game: say so. Any other script
  // error (an extension, a device event) is only logged; the game keeps running.
  window.addEventListener('error', (event) => {
    const trap = typeof WebAssembly === 'object' && event.error instanceof WebAssembly.RuntimeError;
    if (api.phase === 'running' && trap) fail('The game stopped with a WebAssembly error.', String(event.message || ''));
    else if (event.message) logLine('script error: ' + event.message, true);
  });
  window.addEventListener('unhandledrejection', (event) => {
    if (api.phase !== 'error' && api.phase !== 'running') fail('Something went wrong while loading.', String(event.reason?.message || event.reason));
  });

  // ---- canvas size: integer multiples of 320x240 in device pixels -------------------------------------------

  let integerScaling = true;
  try { integerScaling = localStorage.getItem('gba2.integer') !== '0'; } catch (e) { /* storage may be unavailable */ }

  function layout() {
    const ratio = window.devicePixelRatio || 1;
    const box = ui.stage.getBoundingClientRect();
    const availW = Math.max(1, Math.floor(box.width * ratio));
    const availH = Math.max(1, Math.floor(box.height * ratio));
    const fit = Math.min(availW / 320, availH / 240);
    let width, height;
    if (integerScaling && fit >= 1) {
      const k = Math.floor(fit);
      width = 320 * k;
      height = 240 * k;
    } else {
      width = Math.max(2, Math.floor(320 * fit));
      height = Math.max(2, Math.floor(240 * fit));
    }
    if (ui.canvas.width !== width) ui.canvas.width = width;
    if (ui.canvas.height !== height) ui.canvas.height = height;
    ui.canvas.style.setProperty('width', width / ratio + 'px', 'important');
    ui.canvas.style.setProperty('height', height / ratio + 'px', 'important');
    api.canvas = { width, height, ratio, integer: integerScaling && fit >= 1 };
  }

  new ResizeObserver(layout).observe(ui.stage);
  window.addEventListener('resize', layout);
  document.addEventListener('fullscreenchange', layout);
  layout();

  // ---- asset loader ----------------------------------------------------------------------------------------

  // The verified files are kept in IndexedDB (one record per file: its SHA-256 and its bytes). A second visit reads them from
  // there in batches, checks every file against the manifest again and writes it into the module's file system; nothing is
  // requested from the network. (The Cache API holds the same data, but its per-entry cost made a return visit several
  // times slower in measurements: docs/web_host.md.)
  const STORE_DB = 'gba2-assets';
  const STORE = 'files';
  let store = null;

  async function openStore() {
    if (dev.noCache || !('indexedDB' in window)) return null;
    try {
      return await new Promise((resolve, reject) => {
        const request = indexedDB.open(STORE_DB, 1);
        request.onupgradeneeded = () => request.result.createObjectStore(STORE);
        request.onsuccess = () => resolve(request.result);
        request.onerror = () => reject(request.error);
        request.onblocked = () => reject(new Error('the database is blocked by another tab'));
      });
    } catch (e) { logLine('The browser cache (IndexedDB) is unavailable: ' + e, true); return null; }
  }

  function storeGetMany(keys) {
    return new Promise((resolve, reject) => {
      const tx = store.transaction(STORE, 'readonly');
      const objects = tx.objectStore(STORE);
      const out = new Array(keys.length);
      keys.forEach((key, i) => { objects.get(key).onsuccess = (event) => { out[i] = event.target.result; }; });
      tx.oncomplete = () => resolve(out);
      tx.onerror = tx.onabort = () => reject(tx.error || new Error('read aborted'));
    });
  }

  /** Writes records in batches (one transaction per about 32 files or 6 MB) in the background, so a download never waits for the disk. */
  class StoreWriter {
    constructor() { this.pending = []; this.bytes = 0; this.active = Promise.resolve(); this.errors = 0; this.ms = 0; }
    add(key, record, size) {
      this.pending.push([key, record]);
      this.bytes += size;
      if (this.pending.length >= 32 || this.bytes >= 6 * MIB) this.flush();
    }
    flush() {
      const batch = this.pending;
      this.pending = [];
      this.bytes = 0;
      if (!batch.length) return;
      this.active = this.active.then(() => new Promise((resolve) => {
        const t = performance.now();
        let tx;
        try { tx = store.transaction(STORE, 'readwrite', { durability: 'relaxed' }); } catch (e) { tx = store.transaction(STORE, 'readwrite'); }
        for (const [key, record] of batch) tx.objectStore(STORE).put(record, key);
        const done = () => { this.ms += performance.now() - t; resolve(); };
        tx.oncomplete = done;
        tx.onerror = tx.onabort = () => { this.errors++; done(); };
      }));
    }
    async drain() { this.flush(); await this.active; }
  }

  async function storePrune(prefix, wantedKeys) {
    const keys = await new Promise((resolve, reject) => {
      const request = store.transaction(STORE, 'readonly').objectStore(STORE).getAllKeys();
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
    const stale = keys.filter((k) => typeof k === 'string' && k.startsWith(prefix) && !wantedKeys.has(k));
    if (!stale.length) return;
    await new Promise((resolve, reject) => {
      const tx = store.transaction(STORE, 'readwrite');
      for (const key of stale) tx.objectStore(STORE).delete(key);
      tx.oncomplete = resolve;
      tx.onerror = tx.onabort = () => reject(tx.error);
    });
  }

  function absolute(base, relative) { return new URL(relative, new URL(base, document.baseURI)).href; }

  /** Downloads url into a Uint8Array of exactly entry.bytes, reporting progress. */
  async function download(url, entry, mode, onBytes) {
    const response = await fetch(url, { cache: mode, credentials: 'same-origin' });
    if (!response.ok) throw new Error('HTTP ' + response.status);
    const out = new Uint8Array(entry.bytes);
    let at = 0;
    const reader = response.body.getReader();
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      if (at + value.length > out.length) { reader.cancel(); throw new Error('longer than the manifest says (' + entry.bytes + ' bytes)'); }
      out.set(value, at);
      at += value.length;
      onBytes(value.length);
    }
    if (at !== out.length) throw new Error('is ' + at + ' bytes, the manifest says ' + entry.bytes);
    return out;
  }

  /** The verified bytes of one file from the network: two tries with the HTTP cache, a last one bypassing it. */
  async function fetchVerified(baseUrl, entry, counters) {
    const url = baseUrl + entry.path;
    let lastError = null;
    for (let attempt = 0; attempt < 3; attempt++) {
      let counted = 0;
      try {
        let t = performance.now();
        const bytes = await download(url, entry, attempt === 2 ? 'reload' : 'default', (n) => { counted += n; counters.bytesDone += n; });
        counters.ms.download += performance.now() - t;
        t = performance.now();
        const hash = await sha256Hex(bytes);
        counters.ms.hash += performance.now() - t;
        if (hash !== entry.sha256) throw new Error('SHA-256 is ' + hash.slice(0, 12) + '..., the manifest says ' + entry.sha256.slice(0, 12) + '...');
        counters.fromNetwork++;
        counters.networkBytes += entry.bytes;
        return bytes;
      } catch (e) {
        counters.bytesDone -= counted;
        lastError = e;
        counters.retries++;
      }
    }
    throw new Error(entry.path + ': ' + (lastError && lastError.message));
  }

  async function pool(items, concurrency, worker) {
    let next = 0;
    let failure = null;
    const lane = async () => {
      while (!failure) {
        const i = next++;
        if (i >= items.length) return;
        try { await worker(items[i]); } catch (e) { failure = failure || e; }
      }
    };
    await Promise.all(Array.from({ length: Math.min(concurrency, items.length) }, lane));
    if (failure) throw failure;
  }

  const madeDirectories = new Set(['/']);
  function makeDirectories(FS, directory) {
    if (madeDirectories.has(directory)) return;
    const parent = directory.slice(0, directory.lastIndexOf('/')) || '/';
    makeDirectories(FS, parent);
    try { FS.mkdir(directory); } catch (e) { /* exists */ }
    madeDirectories.add(directory);
  }

  function writeFile(FS, path, bytes) {
    makeDirectories(FS, path.slice(0, path.lastIndexOf('/')) || '/');
    FS.writeFile(path, bytes, { canOwn: true });
  }

  /** Fetches a small index file verified against the hash this page was built with. */
  async function fetchPinned(url, pin) {
    const bytes = await download(url, pin, 'no-cache', () => {});
    const hash = await sha256Hex(bytes);
    if (hash !== pin.sha256) {
      throw new Error(pin.path + ' does not match this page (' + hash.slice(0, 12) + ' instead of ' + pin.sha256.slice(0, 12) +
        '): the site is being updated, reload in a minute');
    }
    return bytes;
  }

  /** The files of the game package: every file the manifest lists, once. */
  function manifestFiles(manifest) {
    const seen = new Map();
    const add = (f) => {
      if (typeof f.path !== 'string' || !/^[A-Za-z0-9_./-]+$/.test(f.path) || f.path.includes('..') || f.path.startsWith('/')) {
        throw new Error('bad path in the manifest: ' + f.path);
      }
      const old = seen.get(f.path);
      if (old && (old.sha256 !== f.sha256 || old.bytes !== f.bytes)) throw new Error('the manifest lists ' + f.path + ' twice, differently');
      seen.set(f.path, { path: f.path, bytes: f.bytes, sha256: f.sha256 });
    };
    for (const f of manifest.resources || []) add(f);
    for (const e of manifest.entries || []) for (const f of e.files || []) add(f);
    return [...seen.values()];
  }

  /**
   * Loads one tree of assets (name = 'game' or 'sprites2x') into /assets/<name> of the module's file system.
   * Resolves with the statistics. onProgress(done, total, counters) is called as bytes arrive.
   */
  async function loadTree(name, onProgress) {
    const FS = api.module.FS;
    const spec = build.assets[name];
    const baseUrl = absolute(spec.base, '');
    const counters = { name, files: 0, bytes: 0, bytesDone: 0, fromCache: 0, fromNetwork: 0, networkBytes: 0, retries: 0,
      cacheMisses: 0, cacheErrors: 0, seconds: 0,
      ms: { match: 0, read: 0, hash: 0, download: 0, put: 0, write: 0 } };   // summed over the parallel lanes
    const started = performance.now();
    const pin = spec.index;
    const indexBytes = await fetchPinned(baseUrl + pin.path, pin);
    const index = JSON.parse(new TextDecoder().decode(indexBytes));
    const files = name === 'game' ? manifestFiles(index) : index.files;
    if (name === 'game') writeFile(FS, '/assets/game/' + pin.path, indexBytes);
    counters.files = files.length;
    counters.bytes = files.reduce((n, f) => n + f.bytes, 0);
    onProgress(0, counters.bytes, counters);
    let last = 0;
    const tick = () => {
      const now = performance.now();
      if (now - last > 80) { last = now; onProgress(counters.bytesDone, counters.bytes, counters); }
    };
    const timer = setInterval(tick, 80);
    const keyOf = (entry) => name + '/' + entry.path;
    const place = (entry, bytes) => {
      const t = performance.now();
      writeFile(FS, '/assets/' + name + '/' + entry.path, bytes);
      counters.ms.write += performance.now() - t;
    };
    try {
      // 1. What this browser already holds: read in batches (at most 64 files or about 8 MB each), verify, write.
      const misses = [];
      if (store) {
        const batches = [];
        for (let i = 0, batch = [], size = 0; i <= files.length; i++) {
          if (i === files.length || batch.length >= 64 || size >= 8 * MIB) { if (batch.length) batches.push(batch); batch = []; size = 0; }
          if (i < files.length) { batch.push(files[i]); size += files[i].bytes; }
        }
        await pool(batches, 6, async (batch) => {
          let t = performance.now();
          let records;
          try { records = await storeGetMany(batch.map(keyOf)); } catch (e) { counters.cacheErrors++; records = []; }
          counters.ms.read += performance.now() - t;
          for (let i = 0; i < batch.length; i++) {
            const entry = batch[i], record = records[i];
            let good = false;
            if (record && record.sha256 === entry.sha256 && record.data && record.data.byteLength === entry.bytes) {
              const bytes = new Uint8Array(record.data);
              t = performance.now();
              good = (await sha256Hex(bytes)) === entry.sha256;
              counters.ms.hash += performance.now() - t;
              if (good) {
                place(entry, bytes);
                counters.fromCache++;
                counters.bytesDone += entry.bytes;
              }
            }
            if (!good) { if (record) counters.cacheMisses++; misses.push(entry); }
            tick();
          }
        });
      } else {
        misses.push(...files);
      }
      // 2. The rest from the network, eight at a time; each file is verified, written, and queued to be kept for the next visit.
      const writer = new StoreWriter();
      await pool(misses, name === 'game' ? 8 : 4, async (entry) => {
        const bytes = await fetchVerified(baseUrl, entry, counters);
        place(entry, bytes);
        if (store) writer.add(keyOf(entry), { sha256: entry.sha256, data: bytes.buffer }, entry.bytes);
        tick();
      });
      if (store) {
        await writer.drain();
        counters.ms.put += writer.ms;
        counters.cacheErrors += writer.errors;
      }
    } finally {
      clearInterval(timer);
    }
    onProgress(counters.bytesDone, counters.bytes, counters);
    counters.seconds = (performance.now() - started) / 1000;
    if (store) {
      // Drop what an older build of the site left behind (files the current manifest no longer lists).
      try { await storePrune(name + '/', new Set(files.map(keyOf))); } catch (e) { /* pruning is best effort */ }
    }
    return counters;
  }

  // ---- the module, the save folder ----------------------------------------------------------------------------

  function loadScript(src) {
    return new Promise((resolve, reject) => {
      const script = document.createElement('script');
      script.src = src;
      script.onload = resolve;
      script.onerror = () => reject(new Error('could not load ' + src));
      document.head.appendChild(script);
    });
  }

  async function createModule() {
    await loadScript(build.engine.js);
    mark('engine_script');
    const config = {
      canvas: ui.canvas,
      noInitialRun: true,
      print: (text) => logLine(text, false),
      printErr: (text) => logLine(text, true),
      locateFile: (path, directory) => directory + (path.endsWith('.wasm') ? build.engine.wasm : path),
      gba2Env: Object.assign({ GBA2_SAVE_DIR: '/save' }, dev.env || {}),   // read by web/pre.js before the C runtime starts
      onAbort: (what) => fail('The game crashed.', String(what)),
      gba2Exited: (code) => {
        api.exitCode = code;
        setPhase('exited');
        flushSaves();
        showOverlay({ title: code === 0 ? 'The game has ended' : 'The game stopped', detail: code === 0 ? 'Nothing more to run.' : 'Exit code ' + code + '. The log below says why.', error: code !== 0 });
        ui.logBox.hidden = false;
        if (code !== 0) ui.logBox.open = true;
        addReload();
      },
    };
    const module = await window.createGba2(config);
    api.module = module;
    mark('module_ready');
    return module;
  }

  function mountSaves(module) {
    const FS = module.FS;
    FS.mkdir('/save');
    FS.mount(module.IDBFS, { autoPersist: true }, '/save');
    module.IDBFS.onAutoPersistStateChanged = (active) => {
      api.persist.active = active;
      if (!active) api.persist.writes++;
    };
    return new Promise((resolve) => {
      FS.syncfs(true, (error) => {
        if (error) {
          logLine('Saves cannot be kept in this browser (' + error + '); they last until the page is closed.', true);
          api.persist.available = false;
        } else api.persist.available = true;
        resolve();
      });
    });
  }

  function flushSaves() {
    if (!api.module || !api.persist.available) return;
    try {
      api.module.FS.syncfs(false, (error) => { if (error) { api.persist.errors++; logLine('Saving to IndexedDB failed: ' + error, true); } });
    } catch (e) { /* module gone */ }
  }

  function savedSetting(key) {
    try {
      const text = new TextDecoder().decode(api.module.FS.readFile('/save/settings.cfg'));
      for (const line of text.split('\n')) if (line.startsWith(key + '=')) return line.slice(key.length + 1).trim();
    } catch (e) { /* none yet */ }
    return null;
  }

  async function fetchDevFiles(module) {
    for (const [path, url] of Object.entries(dev.files || {})) {
      const response = await fetch(url);
      if (!response.ok) throw new Error('dev file ' + url + ': HTTP ' + response.status);
      writeFile(module.FS, path, new Uint8Array(await response.arrayBuffer()));
    }
  }

  // ---- progress display ---------------------------------------------------------------------------------------

  function treeProgress(label) {
    return (done, total, c) => {
      const fraction = total ? done / total : 0;
      const where = c.fromCache && !c.fromNetwork ? ' (from this browser’s cache)' : '';
      setProgress(fraction, formatBytes(done) + ' of ' + formatBytes(total) + where);
      if (api.phase === 'loading') ui.detail.textContent = label;
    };
  }

  async function loadAll() {
    setPhase('loading');
    // What the page cannot run without: say so instead of failing somewhere inside.
    if (typeof WebAssembly !== 'object') return fail('This browser cannot run WebAssembly.', 'Use a current Chrome, Edge, Firefox or Safari.');
    if (!window.crypto || !window.crypto.subtle) {
      return fail('This page needs a secure connection.', 'The browser only offers its hashing functions on https (or localhost): open the https address of the site.');
    }
    showOverlay({ title: 'Gundam Battle Assault 2', detail: 'Starting the game engine', progress: { fraction: 0, text: '' } });
    store = await openStore();
    try { await createModule(); } catch (e) { return fail('The game engine could not be loaded.', String(e && e.message || e)); }
    await mountSaves(api.module);
    mark('saves_ready');
    try { await fetchDevFiles(api.module); } catch (e) { return fail('A test file could not be loaded.', String(e && e.message || e)); }

    const wantsHd = savedSetting('sprites') === 'hd';
    try {
      showOverlay({ title: 'Gundam Battle Assault 2', detail: 'Downloading the game data', progress: { fraction: 0, text: '' } });
      api.stats.game = await loadTree('game', treeProgress('Downloading the game data (once; this browser keeps it afterwards)'));
      mark('game_assets');
      if (!dev.noSprites && (wantsHd || dev.waitSprites)) {
        showOverlay({ title: 'Gundam Battle Assault 2', detail: 'Downloading the 2x sprite art you chose', progress: { fraction: 0, text: '' } });
        api.stats.sprites2x = await loadTree('sprites2x', treeProgress('Downloading the 2x sprite art you chose'));
        mark('sprites_assets');
      }
    } catch (e) {
      return fail('The game data could not be loaded.', String(e && e.message || e));
    }
    if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});
    setPhase('ready');
    mark('ready');
    showOverlay({
      title: 'Gundam Battle Assault 2',
      detail: 'Ready.',
      note: 'Keyboard: arrows and A S D F G (player 1), I J K L and Z X C V B (player 2). Enter starts. Gamepads work too.' +
        (window.matchMedia && window.matchMedia('(pointer: coarse)').matches ? ' This game needs a keyboard or a gamepad; touch controls are not available.' : ''),
      start: true,
    });
    ui.start.focus();
    if (dev.autostart) start();
    if (!api.stats.sprites2x && !dev.noSprites) backgroundSprites();
  }

  let spritesLoading = false;
  async function backgroundSprites() {
    spritesLoading = true;
    try {
      const sprite = (done, total) => { ui.status.textContent = '2x sprite art: ' + Math.round(100 * done / Math.max(1, total)) + '%'; };
      api.stats.sprites2x = await loadTree('sprites2x', sprite);
      mark('sprites_assets');
      ui.status.textContent = '';
      spritesLoading = false;
      if (api.module._gba2_web_assets_changed) api.module._gba2_web_assets_changed();
      showStatus();
    } catch (e) {
      spritesLoading = false;
      logLine('2x sprite art could not be loaded: ' + (e && e.message || e), true);
      ui.status.textContent = '2x sprite art unavailable';
    }
  }

  // ---- start, status ------------------------------------------------------------------------------------------

  /**
   * Is the browser's WebGL2 a software renderer (SwiftShader, llvmpipe, WARP: a machine without GPU acceleration)? The GPU renderer's
   * shader is heavy for a CPU: a frame takes 0.2 s there, where the game's own software rasterizer takes 12 ms. A throw-away canvas
   * asks (the game's canvas must keep its context type for the game).
   */
  function probeWebGl() {
    try {
      const gl = document.createElement('canvas').getContext('webgl2');
      if (!gl) return { webgl2: false, software: false, renderer: '' };
      const info = gl.getExtension('WEBGL_debug_renderer_info');
      const renderer = String(info ? gl.getParameter(info.UNMASKED_RENDERER_WEBGL) : gl.getParameter(gl.RENDERER));
      const lose = gl.getExtension('WEBGL_lose_context');
      if (lose) lose.loseContext();
      return { webgl2: true, renderer, software: /swiftshader|llvmpipe|softpipe|software|basic render|microsoft basic|warp/i.test(renderer) };
    } catch (e) {
      return { webgl2: false, software: false, renderer: '' };
    }
  }

  function start() {
    if (api.phase !== 'ready') return;
    ui.overlay.hidden = true;
    setPhase('running');
    mark('start');
    ui.canvas.focus();
    const args = ['--assets', '/assets', ...(dev.args || [])];
    // With no GPU acceleration the game starts on its software rasterizer, unless the player chose a renderer (F2 saves the choice).
    api.gl = probeWebGl();
    if (api.gl.software && savedSetting('renderer') === null && !args.includes('--renderer')) {
      args.push('--renderer', 'software');
      logLine('WebGL2 is a software renderer here (' + api.gl.renderer + '): starting with the game\'s own software rasterizer (F2 switches).', false);
    }
    try {
      api.module.callMain(args);
    } catch (e) {
      fail('The game could not start.', String(e && e.message || e));
      return;
    }
    mark('main_returned');
    layout();
    pollStatus();
    if (window.gba2Online && window.gba2Online.enable) window.gba2Online.enable(true);
  }

  function parseStatus(text) {
    const result = {};
    for (const line of text.split('\n')) {
      const i = line.indexOf('=');
      if (i > 0) result[line.slice(0, i)] = line.slice(i + 1);
    }
    return result;
  }

  let statusTimer = 0;
  function showStatus() {
    if (api.phase !== 'running' || !api.module) return;
    layout();   // SDL sets an inline CSS size on the canvas when it creates the window: put the page's back
    const text = api.module.UTF8ToString(api.module._gba2_web_status());
    if (!text) return;
    const s = parseStatus(text);
    api.status = s;
    if (!api.timings.first_frame) mark('first_frame');
    if (!spritesLoading) ui.status.textContent = 'Renderer: ' + s.renderer + ' (F2)  Sprites: ' + s.sprites + ' (H)';
    api.glDescription = s.description || null;
  }
  function pollStatus() {
    if (statusTimer) return;
    statusTimer = setInterval(showStatus, 500);
  }

  // ---- buttons, keys ------------------------------------------------------------------------------------------

  ui.start.addEventListener('click', start);

  // Volume. SDL2 plays through a ScriptProcessorNode that it connects to the context's destination as soon as the game opens its audio device
  // (inside the engine, at the first click). The page wraps createScriptProcessor so that this one connection goes through a GainNode instead
  // (the master volume), which is there from the first sample: the slider sets its gain, as percent squared (the ear hears level, not amplitude),
  // and the choice is kept in localStorage. Nothing of the game's own sound changes (the netplay tests compare it before this node).
  const VOLUME_KEY = 'gba2.volume';
  let volume = 100;
  try {
    const saved = localStorage.getItem(VOLUME_KEY);
    if (saved !== null && saved !== '' && Number.isFinite(Number(saved))) volume = Math.min(100, Math.max(0, Math.round(Number(saved))));
  } catch (e) { /* storage may be blocked */ }
  const volumeGain = () => (volume / 100) * (volume / 100);
  const audio = { master: null, routed: 0, get volume() { return volume; } };   // for the tests
  api.audio = audio;
  const BaseContext = window.BaseAudioContext || window.AudioContext || window.webkitAudioContext;
  if (BaseContext && BaseContext.prototype && typeof BaseContext.prototype.createScriptProcessor === 'function') {
    const create = BaseContext.prototype.createScriptProcessor;
    BaseContext.prototype.createScriptProcessor = function createScriptProcessor(...args) {
      const node = create.apply(this, args);
      const connect = node.connect;
      node.connect = function connectThroughMaster(destination, ...rest) {
        if (destination !== this.context.destination) return connect.call(this, destination, ...rest);
        if (!audio.master || audio.master.context !== this.context) {
          const gain = this.context.createGain();
          gain.gain.value = volumeGain();
          connect.call(gain, this.context.destination);
          audio.master = gain;
        }
        connect.call(this, audio.master);
        audio.routed += 1;
        return destination;
      };
      return node;
    };
  }

  let muted = false;
  const setMuted = (on) => {
    muted = on;
    const context = api.module && api.module.SDL2 && api.module.SDL2.audioContext;
    if (context) { if (muted) context.suspend(); else context.resume(); }
    ui.sound.textContent = muted ? 'Sound off' : 'Sound on';
    ui.sound.setAttribute('aria-pressed', String(muted));
  };

  /** The game's own keyboard and pad input, off while the slider has the focus (as for the code fields of the online panel). */
  const gameInput = (on) => { const m = api.module; if (m && m._gba2_web_input) m._gba2_web_input(on ? 1 : 0); };

  const showVolume = () => {
    ui.volume.value = String(volume);
    ui.volumeText.textContent = volume + '%';
    ui.volume.setAttribute('aria-valuetext', volume + ' percent');
    ui.volume.title = 'Volume: ' + volume + '%';
  };
  const setVolume = (percent, fromUser) => {
    volume = Math.min(100, Math.max(0, Math.round(percent)));
    showVolume();
    try { localStorage.setItem(VOLUME_KEY, String(volume)); } catch (e) { /* ignore */ }
    if (audio.master) audio.master.gain.setTargetAtTime(volumeGain(), audio.master.context.currentTime, 0.015);
    if (fromUser && muted) setMuted(false);   // moving the slider asks for sound
  };
  showVolume();
  ui.volume.addEventListener('input', () => setVolume(Number(ui.volume.value), true));
  ui.volume.addEventListener('focus', () => gameInput(false));
  ui.volume.addEventListener('blur', () => gameInput(true));
  // A mouse or finger that has set the volume gives the keyboard back to the game at once; a keyboard user keeps the slider until Escape, Enter or Tab.
  for (const type of ['pointerup', 'pointercancel']) ui.volume.addEventListener(type, () => ui.volume.blur());
  for (const type of ['keydown', 'keyup', 'keypress']) {   // SDL listens on the window and would cancel the arrow keys and eat the others
    ui.volume.addEventListener(type, (event) => {
      event.stopPropagation();
      if (type === 'keydown' && (event.key === 'Escape' || event.key === 'Enter')) ui.volume.blur();
    });
  }

  // Sound: the browser may leave an audio context suspended until the page has been used; any click or key resumes it (unless the
  // player muted it with the button).
  const resumeAudio = () => {
    const context = api.module && api.module.SDL2 && api.module.SDL2.audioContext;
    if (context && context.state === 'suspended' && !muted && api.phase === 'running') context.resume().catch(() => {});
  };
  window.addEventListener('pointerdown', resumeAudio, true);
  window.addEventListener('keydown', resumeAudio, true);

  // Any key also starts (a key press is a user gesture too; a gamepad button is not, so it does not).
  window.addEventListener('keydown', (event) => {
    if (api.phase === 'ready' && !ui.overlay.hidden && event.target !== ui.start && !(event.target && event.target.tagName === 'INPUT') && !event.ctrlKey && !event.metaKey && !event.altKey &&
        event.code !== 'Tab' && event.code !== 'Escape' && !/^(F\d+|Shift|Control|Alt|Meta|OS|CapsLock|NumLock|ContextMenu)/.test(event.code)) {
      event.preventDefault();
      start();
    }
  }, true);

  const GAME_CODES = new Set(['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Space', 'Tab', 'Backspace', 'Backslash', 'Enter',
    'F2', 'F3', 'KeyA', 'KeyS', 'KeyD', 'KeyF', 'KeyG', 'KeyH', 'KeyI', 'KeyJ', 'KeyK', 'KeyL', 'KeyN', 'KeyR', 'KeyZ', 'KeyX', 'KeyC',
    'KeyV', 'KeyB']);
  // A field of the page (the online codes, the online settings) gets its keys.
  const isTextField = (target) => target && (target.tagName === 'TEXTAREA' || target.tagName === 'INPUT' || target.tagName === 'SELECT' || target.isContentEditable);
  // The page must not scroll, tab away or activate a focused button while the game has the keyboard.
  window.addEventListener('keydown', (event) => {
    if (api.phase === 'running' && GAME_CODES.has(event.code) && !event.ctrlKey && !event.metaKey && !event.altKey && !isTextField(event.target)) {
      event.preventDefault();
      if (document.activeElement && document.activeElement !== document.body && document.activeElement !== ui.canvas) document.activeElement.blur();
    }
  }, true);
  window.addEventListener('keyup', (event) => {
    if (api.phase === 'running' && GAME_CODES.has(event.code) && !isTextField(event.target)) event.preventDefault();
  }, true);

  const noFocus = (button) => button.addEventListener('mousedown', (e) => e.preventDefault());
  [ui.fullscreen, ui.sound, ui.integer, ui.help].forEach(noFocus);

  ui.fullscreen.addEventListener('click', () => {
    if (document.fullscreenElement) document.exitFullscreen();
    else if (document.documentElement.requestFullscreen) document.documentElement.requestFullscreen().catch(() => {});
  });

  ui.sound.addEventListener('click', () => setMuted(!muted));

  ui.integer.addEventListener('click', () => {
    integerScaling = !integerScaling;
    try { localStorage.setItem('gba2.integer', integerScaling ? '1' : '0'); } catch (e) { /* ignore */ }
    ui.integer.textContent = 'Integer scaling: ' + (integerScaling ? 'on' : 'off');
    ui.integer.setAttribute('aria-pressed', String(integerScaling));
    layout();
  });
  ui.integer.textContent = 'Integer scaling: ' + (integerScaling ? 'on' : 'off');
  ui.integer.setAttribute('aria-pressed', String(integerScaling));

  ui.help.addEventListener('click', () => {
    ui.helpBox.hidden = !ui.helpBox.hidden;
    ui.help.setAttribute('aria-expanded', String(!ui.helpBox.hidden));
  });

  ui.canvas.addEventListener('webglcontextlost', (event) => {
    event.preventDefault();
    fail('The browser lost the WebGL context (the graphics driver was reset).', 'Reload the page; your save is kept.');
  });

  // The save folder is flushed when a write happens (IDBFS autoPersist) and again whenever the page goes away.
  document.addEventListener('visibilitychange', () => { if (document.hidden) flushSaves(); });
  window.addEventListener('pagehide', flushSaves);

  // Pads are only visible to a page after a button press on them.
  window.addEventListener('gamepadconnected', (event) => { logLine('Gamepad: ' + event.gamepad.id, false); });

  api.start = start;
  api.flushSaves = flushSaves;
  api.layout = layout;
  if (window.gba2Online && window.gba2Online.init) window.gba2Online.init({ api, dev, log: (text) => logLine(text, false) });

  loadAll().catch((e) => fail('Loading failed.', String(e && e.message || e)));
})();
