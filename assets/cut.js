/* Dimas HUB · recorte de MP4 sem recompressão.
   Lê só o índice (moov) e os trechos pedidos de um MP4 remoto via leitura por faixas (Range),
   e monta novos MP4 (um por corte ou um único com vários cortes). Também gera ZIP sem compressão. */
(function (root) {
  'use strict';
  const td = new TextDecoder();
  const u32 = (d, o) => d.getUint32(o);
  const u64 = (d, o) => d.getUint32(o) * 4294967296 + d.getUint32(o + 4);
  const type4 = (b, o) => String.fromCharCode(b[o], b[o + 1], b[o + 2], b[o + 3]);

  // ---------- leitura ----------
  async function topBoxes(read, size) {
    const out = {}; let o = 0;
    while (o + 8 <= size) {
      const h = await read(o, Math.min(o + 15, size - 1));
      const d = new DataView(h.buffer, h.byteOffset, h.byteLength);
      let s = u32(d, 0); const t = type4(h, 4); let hl = 8;
      if (s === 1) { s = u64(d, 8); hl = 16; } else if (s === 0) s = size - o;
      if (s < 8) break;
      if (t === 'moov' || t === 'ftyp') out[t] = { off: o, size: s, hl };
      o += s;
      if (out.moov && out.ftyp) break;
    }
    if (!out.moov) throw new Error('Arquivo sem índice (moov). Ele precisa ser um MP4 completo.');
    return out;
  }
  function children(b, start, end) {
    const d = new DataView(b.buffer, b.byteOffset, b.byteLength); const list = []; let o = start;
    while (o + 8 <= end) {
      let s = u32(d, o); const t = type4(b, o + 4); let hl = 8;
      if (s === 1) { s = u64(d, o + 8); hl = 16; } else if (s === 0) s = end - o;
      if (s < 8 || o + s > end) break;
      list.push({ t, o, s, b: o + hl, e: o + s }); o += s;
    }
    return list;
  }
  const find = (b, box, t) => children(b, box.b, box.e).find(x => x.t === t);
  function parseMoov(b) {
    const d = new DataView(b.buffer, b.byteOffset, b.byteLength);
    const top = { b: 0, e: b.byteLength };
    const moov = children(b, 0, b.byteLength).find(x => x.t === 'moov');
    const mvhd = find(b, moov, 'mvhd');
    const mvTs = d.getUint8(mvhd.b) === 1 ? u32(d, mvhd.b + 20) : u32(d, mvhd.b + 12);
    const tracks = [];
    for (const trak of children(b, moov.b, moov.e).filter(x => x.t === 'trak')) {
      const tkhd = find(b, trak, 'tkhd'); const mdia = find(b, trak, 'mdia');
      const mdhd = find(b, mdia, 'mdhd'); const hdlr = find(b, mdia, 'hdlr');
      const minf = find(b, mdia, 'minf'); const stbl = find(b, minf, 'stbl');
      const handler = type4(b, hdlr.b + 8);
      if (handler !== 'vide' && handler !== 'soun') continue;
      const mv = d.getUint8(mdhd.b);
      const ts = mv === 1 ? u32(d, mdhd.b + 20) : u32(d, mdhd.b + 12);
      const lang = mv === 1 ? d.getUint16(mdhd.b + 32) : d.getUint16(mdhd.b + 20);
      const tv = d.getUint8(tkhd.b);
      const wOff = tkhd.b + (tv === 1 ? 88 : 76);
      const width = u32(d, wOff), height = u32(d, wOff + 4);
      // edit list: deslocamento inicial (atraso de B-frames, priming do áudio)
      let shift = 0; const edts = find(b, trak, 'edts');
      if (edts) { const el = find(b, edts, 'elst'); if (el) { const v = d.getUint8(el.b); const n = u32(d, el.b + 4); let p = el.b + 8;
        for (let i = 0; i < n; i++) { const mt = v === 1 ? u64(d, p + 8) : d.getInt32(p + 4); const dur = v === 1 ? u64(d, p) : u32(d, p);
          if (mt === -1 || mt === 4294967295 || mt === 18446744073709552000) { p += v === 1 ? 20 : 12; continue; } shift = mt; break; } } }
      const sub = {}; for (const c of children(b, stbl.b, stbl.e)) sub[c.t] = c;
      const stsdRaw = b.slice(sub.stsd.o, sub.stsd.e);
      // stsz
      let p = sub.stsz.b; const fixed = u32(d, p + 4); const n = u32(d, p + 8);
      const size = new Uint32Array(n); if (fixed) size.fill(fixed); else for (let i = 0; i < n; i++) size[i] = u32(d, p + 12 + i * 4);
      // stts -> dts
      const dts = new Float64Array(n); const dur = new Uint32Array(n);
      p = sub.stts.b; let ne = u32(d, p + 4), k = 0, t = 0;
      for (let i = 0; i < ne; i++) { const c = u32(d, p + 8 + i * 8), dl = u32(d, p + 12 + i * 8); for (let j = 0; j < c && k < n; j++) { dts[k] = t; dur[k] = dl; t += dl; k++; } }
      // ctts
      const cto = new Int32Array(n);
      if (sub.ctts) { p = sub.ctts.b; ne = u32(d, p + 4); k = 0; for (let i = 0; i < ne; i++) { const c = u32(d, p + 8 + i * 8), v = d.getInt32(p + 12 + i * 8); for (let j = 0; j < c && k < n; j++) cto[k++] = v; } }
      // stss
      let sync; if (sub.stss) { sync = new Uint8Array(n); p = sub.stss.b; ne = u32(d, p + 4); for (let i = 0; i < ne; i++) { const s = u32(d, p + 8 + i * 4) - 1; if (s < n) sync[s] = 1; } } else { sync = new Uint8Array(n).fill(1); }
      // chunks
      const co = sub.stco || sub.co64; const is64 = !!sub.co64; p = co.b; const nc = u32(d, p + 4);
      const chunkOff = new Float64Array(nc); for (let i = 0; i < nc; i++) chunkOff[i] = is64 ? u64(d, p + 8 + i * 8) : u32(d, p + 8 + i * 4);
      const offset = new Float64Array(n);
      p = sub.stsc.b; ne = u32(d, p + 4); const stsc = []; for (let i = 0; i < ne; i++) stsc.push([u32(d, p + 8 + i * 12), u32(d, p + 12 + i * 12)]);
      k = 0;
      for (let i = 0; i < stsc.length; i++) {
        const first = stsc[i][0] - 1, last = i + 1 < stsc.length ? stsc[i + 1][0] - 1 : nc, per = stsc[i][1];
        for (let c = first; c < last && k < n; c++) { let o = chunkOff[c]; for (let j = 0; j < per && k < n; j++) { offset[k] = o; o += size[k]; k++; } }
      }
      const hdrRaw = b.slice(hdlr.o, hdlr.e);
      const xmhd = find(b, minf, handler === 'vide' ? 'vmhd' : 'smhd');
      tracks.push({ kind: handler === 'vide' ? 'video' : 'audio', ts, lang, width, height, shift, n, size, dts, dur, cto, sync, offset,
        stsdRaw, hdlrRaw: hdrRaw, xmhdRaw: xmhd ? b.slice(xmhd.o, xmhd.e) : null, hasCtts: !!sub.ctts });
    }
    const video = tracks.find(t => t.kind === 'video'); const audio = tracks.find(t => t.kind === 'audio');
    if (!video) throw new Error('O arquivo não tem faixa de vídeo.');
    if (!video.n) throw new Error('Este MP4 é do tipo fragmentado (gravado em partes), que o recorte ainda não lê. Exporte o jogo como MP4 comum.');
    return { mvTs, video, audio };
  }
  async function open(read, size) {
    const tb = await topBoxes(read, size);
    const m = await read(tb.moov.off, tb.moov.off + tb.moov.size - 1);
    const info = parseMoov(m);
    info.ftyp = tb.ftyp ? await read(tb.ftyp.off, tb.ftyp.off + tb.ftyp.size - 1) : null;
    info.read = read; info.fileSize = size;
    return info;
  }
  // tempo de apresentação (s) da amostra i
  const pts = (tr, i) => (tr.dts[i] + tr.cto[i] - tr.shift) / tr.ts;
  function lowerBound(arr, v) { let lo = 0, hi = arr.length; while (lo < hi) { const m = (lo + hi) >> 1; if (arr[m] < v) lo = m + 1; else hi = m; } return lo; }
  // escolhe as amostras de um corte [s,e] (segundos)
  function plan(info, s, e) {
    const v = info.video; const n = v.n;
    // primeiro quadro-chave com pts <= s (busca pelo dts, que é ordenado)
    let i = Math.min(n - 1, Math.max(0, lowerBound(v.dts, (s + 1) * v.ts + v.shift)));
    while (i > 0 && (!v.sync[i] || pts(v, i) > s + 1e-6)) i--;
    while (i > 0 && !v.sync[i]) i--;
    // próximo quadro-chave com pts >= e (corte termina antes dele)
    let j = Math.min(n, lowerBound(v.dts, Math.max(0, (e - 1) * v.ts)));
    while (j < n && !(v.sync[j] && pts(v, j) >= e - 1e-6)) j++;
    if (j <= i) j = Math.min(n, i + 1);
    const v0 = pts(v, i), v1 = j < n ? pts(v, j) : pts(v, n - 1) + v.dur[n - 1] / v.ts;
    const seg = { v: [i, j], vStart: v0, vEnd: v1, s: Math.max(s, v0), e: Math.min(e, v1) };
    const a = info.audio;
    if (a) {
      let ai = lowerBound(a.dts, v0 * a.ts + a.shift); let aj = lowerBound(a.dts, v1 * a.ts + a.shift);
      seg.a = [Math.min(ai, a.n), Math.min(Math.max(aj, ai), a.n)];
    }
    // faixa de bytes que cobre as duas faixas
    let lo = Infinity, hi = 0;
    for (let k = i; k < j; k++) { lo = Math.min(lo, v.offset[k]); hi = Math.max(hi, v.offset[k] + v.size[k]); }
    if (a && seg.a[1] > seg.a[0]) for (let k = seg.a[0]; k < seg.a[1]; k++) { lo = Math.min(lo, a.offset[k]); hi = Math.max(hi, a.offset[k] + a.size[k]); }
    seg.lo = lo; seg.hi = hi; seg.bytes = hi - lo;
    return seg;
  }
  async function fetchSeg(info, seg, onBytes) {
    const CH = 8 * 1024 * 1024; const parts = []; let got = 0;
    for (let o = seg.lo; o < seg.hi; o += CH) { const end = Math.min(seg.hi, o + CH) - 1; const p = await info.read(o, end); parts.push(p); got += p.byteLength; if (onBytes) onBytes(p.byteLength); }
    const buf = new Uint8Array(got); let q = 0; for (const p of parts) { buf.set(p, q); q += p.byteLength; }
    seg.buf = buf;
  }
  const slice = (info, seg, tr, k) => seg.buf.subarray(tr.offset[k] - seg.lo, tr.offset[k] - seg.lo + tr.size[k]);

  // ---------- escrita ----------
  function cat(list) { let n = 0; for (const x of list) n += x.byteLength; const o = new Uint8Array(n); let p = 0; for (const x of list) { o.set(x, p); p += x.byteLength; } return o; }
  function be32(v) { const b = new Uint8Array(4); new DataView(b.buffer).setUint32(0, v >>> 0); return b; }
  function be16(v) { const b = new Uint8Array(2); new DataView(b.buffer).setUint16(0, v); return b; }
  function be64(v) { const b = new Uint8Array(8); const d = new DataView(b.buffer); d.setUint32(0, Math.floor(v / 4294967296)); d.setUint32(4, v >>> 0); return b; }
  const str = s => new Uint8Array([...s].map(c => c.charCodeAt(0)));
  function box(t, ...parts) { const body = cat(parts.flat()); return cat([be32(body.byteLength + 8), str(t), body]); }
  function full(t, v, f, ...parts) { return box(t, new Uint8Array([v, (f >> 16) & 255, (f >> 8) & 255, f & 255]), ...parts); }
  const MATRIX = cat([be32(0x10000), be32(0), be32(0), be32(0), be32(0x10000), be32(0), be32(0), be32(0), be32(0x40000000)]);
  function u32arr(a) { const b = new Uint8Array(a.length * 4); const d = new DataView(b.buffer); for (let i = 0; i < a.length; i++) d.setUint32(i * 4, a[i] >>> 0); return b; }
  function i32pairs(p) { const b = new Uint8Array(p.length * 8); const d = new DataView(b.buffer); for (let i = 0; i < p.length; i++) { d.setUint32(i * 8, p[i][0]); d.setInt32(i * 8 + 4, p[i][1]); } return b; }
  function rle(vals) { const out = []; for (const v of vals) { const l = out[out.length - 1]; if (l && l[1] === v) l[0]++; else out.push([1, v]); } return out; }

  // monta um MP4 a partir de segmentos já baixados.
  // exact=true: usa lista de edição para começar/terminar exatamente no lance (só com 1 segmento).
  function build(info, segs, exact) {
    const tracksOut = [];
    const kinds = info.audio ? ['video', 'audio'] : ['video'];
    for (const kind of kinds) {
      const tr = info[kind]; const samples = []; // {seg,k,dur,cto,sync}
      const chunks = []; // por segmento: [inicioAmostra, qtd]
      let accV = 0; // tempo acumulado do vídeo (s), para alinhar o áudio
      let acc = 0; // ticks acumulados nesta faixa
      for (const seg of segs) {
        const st = (seg.info || info)[kind]; if (!st) { chunks.push([samples.length, 0]); accV += seg.vEnd - seg.vStart; continue; }
        const [a, b] = kind === 'video' ? seg.v : seg.a;
        const segLenS = seg.vEnd - seg.vStart;
        if (kind === 'audio') {
          // alinha o início do áudio do segmento ao início do vídeo do segmento
          const want = Math.round(accV * tr.ts + (b > a ? ((st.dts[a] - st.shift) / st.ts - seg.vStart) * tr.ts : 0));
          if (samples.length) { const last = samples[samples.length - 1]; const gap = want - acc; if (gap > 0) { last.dur += gap; acc += gap; } }
        }
        const first = samples.length;
        for (let k = a; k < b; k++) {
          const d = k + 1 < st.n ? st.dts[k + 1] - st.dts[k] : st.dur[k];
          samples.push({ seg, st, k, dur: Math.max(1, d), cto: st.cto[k], sync: st.sync[k] });
          acc += Math.max(1, d);
        }
        if (kind === 'audio' && samples.length > first) {
          // não deixa o áudio do segmento passar do fim do vídeo do segmento
          const limit = Math.round((accV + segLenS) * tr.ts);
          while (acc > limit + tr.dur[0] && samples.length > first + 1) { const r = samples.pop(); acc -= r.dur; }
        }
        chunks.push([first, samples.length - first]);
        accV += segLenS;
      }
      tracksOut.push({ kind, tr, samples, chunks, total: acc });
    }
    // dados (mdat): segmento a segmento, vídeo e depois áudio
    const order = []; // {t, ci}
    for (let ci = 0; ci < segs.length; ci++) for (let ti = 0; ti < tracksOut.length; ti++) if (tracksOut[ti].chunks[ci][1] > 0) order.push({ ti, ci });
    const dataParts = []; const chunkPos = tracksOut.map(() => []);
    let pos = 0;
    for (const { ti, ci } of order) {
      const T = tracksOut[ti]; const [f, c] = T.chunks[ci]; chunkPos[ti].push({ ci, pos });
      for (let x = f; x < f + c; x++) { const s = T.samples[x]; const data = slice(info, s.seg, s.st, s.k); dataParts.push(data); pos += data.byteLength; }
    }
    const mdatSize = pos;
    // edição
    const seg0 = segs[0];
    const movieDur = exact ? (seg0.e - seg0.s) : tracksOut[0].total / tracksOut[0].tr.ts - (tracksOut[0].samples.length ? 0 : 0);
    function trak(T, id, base) {
      const tr = T.tr; const S = T.samples; const isV = T.kind === 'video';
      const mediaDur = T.total;
      const firstCto = S.length ? S[0].cto : 0;
      let mediaTime, editDur;
      if (exact) {
        if (isV) mediaTime = firstCto + Math.round((seg0.s - seg0.vStart) * tr.ts);
        else { const a0 = S.length ? (S[0].st.dts[S[0].k] - S[0].st.shift) / S[0].st.ts : seg0.vStart; mediaTime = Math.max(0, Math.round((seg0.s - a0) * tr.ts)); }
        editDur = Math.round((seg0.e - seg0.s) * 1000);
      } else {
        if (isV) mediaTime = firstCto; else { const a0 = S.length ? (S[0].st.dts[S[0].k] - S[0].st.shift) / S[0].st.ts : seg0.vStart; mediaTime = Math.max(0, Math.round((seg0.vStart - a0) * tr.ts)); }
        editDur = Math.round((mediaDur - mediaTime) / tr.ts * 1000);
      }
      editDur = Math.max(1, editDur);
      const tkhd = full('tkhd', 0, 3, be32(0), be32(0), be32(id), be32(0), be32(editDur), be32(0), be32(0), be16(0), be16(isV ? 0 : 1), be16(isV ? 0 : 0x0100), be16(0), MATRIX, be32(isV ? tr.width : 0), be32(isV ? tr.height : 0));
      const elst = box('edts', full('elst', 0, 0, be32(1), be32(editDur), be32(mediaTime), be16(1), be16(0)));
      const mdhd = full('mdhd', 0, 0, be32(0), be32(0), be32(tr.ts), be32(mediaDur), be16(tr.lang), be16(0));
      const stts = full('stts', 0, 0, (() => { const r = rle(S.map(s => s.dur)); return [be32(r.length), u32arr(r.flatMap(x => [x[0], x[1]]))]; })());
      const parts = [tr.stsdRaw, stts];
      if (tr.hasCtts) { const r = rle(S.map(s => s.cto)); parts.push(full('ctts', 0, 0, be32(r.length), i32pairs(r))); }
      if (isV) { const ss = []; S.forEach((s, i) => { if (s.sync) ss.push(i + 1); }); if (ss.length < S.length) parts.push(full('stss', 0, 0, be32(ss.length), u32arr(ss))); }
      const cp = chunkPos[tracksOut.indexOf(T)];
      const counts = cp.map(c => T.chunks[c.ci][1]);
      const stscE = []; counts.forEach((c, i) => { const l = stscE[stscE.length - 1]; if (!l || l[1] !== c) stscE.push([i + 1, c]); });
      parts.push(full('stsc', 0, 0, be32(stscE.length), u32arr(stscE.flatMap(e => [e[0], e[1], 1]))));
      parts.push(full('stsz', 0, 0, be32(0), be32(S.length), u32arr(S.map(s => s.st.size[s.k]))));
      parts.push(full('co64', 0, 0, be32(cp.length), cat(cp.map(c => be64(base + c.pos)))));
      const stbl = box('stbl', ...parts);
      const dinf = box('dinf', full('dref', 0, 0, be32(1), full('url ', 0, 1)));
      const xm = tr.xmhdRaw || (isV ? full('vmhd', 0, 1, new Uint8Array(8)) : full('smhd', 0, 0, new Uint8Array(4)));
      const minf = box('minf', xm, dinf, stbl);
      const mdia = box('mdia', mdhd, tr.hdlrRaw, minf);
      return box('trak', tkhd, elst, mdia);
    }
    const ftyp = box('ftyp', str('isom'), be32(512), str('isom'), str('iso2'), str('avc1'), str('mp41'));
    function moov(base) {
      const mvdur = Math.max(1, Math.round(movieDur * 1000));
      const mvhd = full('mvhd', 0, 0, be32(0), be32(0), be32(1000), be32(mvdur), be32(0x10000), be16(0x0100), be16(0), be32(0), be32(0), MATRIX, new Uint8Array(24), be32(tracksOut.length + 1));
      return box('moov', mvhd, ...tracksOut.map((T, i) => trak(T, i + 1, base)));
    }
    const m0 = moov(0); const base = ftyp.byteLength + m0.byteLength + 16;
    const m1 = moov(base);
    const mdatHdr = cat([be32(1), str('mdat'), be64(mdatSize + 16)]);
    return { parts: [ftyp, m1, mdatHdr, ...dataParts], size: base + mdatSize, duration: movieDur };
  }

  // ---------- ZIP (sem compressão) ----------
  const CRC = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
  function crc32(parts) { let c = 0xFFFFFFFF; for (const p of parts) for (let i = 0; i < p.length; i++) c = CRC[(c ^ p[i]) & 255] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
  function le(v, n) { const b = new Uint8Array(n); for (let i = 0; i < n; i++) b[i] = (v / Math.pow(256, i)) & 255; return b; }
  function zip(files) { // files: [{name, parts, size}]
    const enc = new TextEncoder(); const out = []; const cen = []; let off = 0;
    for (const f of files) {
      const nm = enc.encode(f.name); const crc = crc32(f.parts);
      const lh = cat([le(0x04034b50, 4), le(20, 2), le(0x0800, 2), le(0, 2), le(0, 2), le(0, 2), le(crc, 4), le(f.size, 4), le(f.size, 4), le(nm.length, 2), le(0, 2), nm]);
      out.push(lh, ...f.parts);
      cen.push(cat([le(0x02014b50, 4), le(20, 2), le(20, 2), le(0x0800, 2), le(0, 2), le(0, 2), le(0, 2), le(crc, 4), le(f.size, 4), le(f.size, 4), le(nm.length, 2), le(0, 2), le(0, 2), le(0, 2), le(0, 2), le(0, 4), le(off, 4), nm]));
      off += lh.byteLength + f.size;
    }
    const cd = cat(cen);
    out.push(cd, cat([le(0x06054b50, 4), le(0, 2), le(0, 2), le(files.length, 2), le(files.length, 2), le(cd.byteLength, 4), le(off, 4), le(0, 2)]));
    return out;
  }
  // assinatura dos codecs (para saber se dá para juntar arquivos diferentes num vídeo só)
  function codecKey(info) { const h = a => { let x = 0; for (let i = 0; i < a.length; i++) x = (x * 31 + a[i]) >>> 0; return x + ':' + a.length; }; return h(info.video.stsdRaw) + '|' + (info.audio ? h(info.audio.stsdRaw) + ':' + info.audio.ts : '') + '|' + info.video.ts; }

  const api = { open, plan, fetchSeg, build, zip, codecKey };
  if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.DimasCut = api;
})(typeof window !== 'undefined' ? window : globalThis);
