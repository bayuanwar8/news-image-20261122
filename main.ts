// news-image-20261122, account 1 (@bayuanwar8).
// One-page world-news picture for Sunday 22 November 2026, drawn from scratch
// with Node 22 stdlib only. Renders at 2x (2048x2048), downscales to 1024x1024
// with a separable Lanczos-3 filter, and writes a deterministic PNG.
// No network, no clock, no randomness: the same input always yields the same bytes.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { deflateSync } from 'node:zlib';

const S = 2; // render scale
const W = 1024 * S;
const H = 1024 * S;
const OUT_W = 1024;
const OUT_H = 1024;

// ---------------------------------------------------------------------------
// Small utilities
// ---------------------------------------------------------------------------
function clamp255(v: number): number {
  return Math.max(0, Math.min(255, Math.round(v)));
}
function rgb(r: number, g: number, b: number): [number, number, number] {
  return [r, g, b];
}
const PAPER = rgb(247, 242, 232);
const INK = rgb(18, 18, 18);
const RED = rgb(176, 30, 36);
const MUTED = rgb(96, 92, 84);
const RULE = rgb(190, 182, 168);
const WHITE = rgb(255, 255, 255);

// Region palette, single source of truth.
const REG_PAL: Record<string, [number, number, number]> = {
  Europe: [42, 93, 176],
  Asia: [176, 30, 36],
  ME: [200, 138, 0],
  Africa: [122, 74, 158],
  Americas: [26, 122, 110],
  Oceania: [58, 122, 58],
  Global: [102, 102, 102],
};

// ---------------------------------------------------------------------------
// TTF parsing (DejaVu only; BMP cmap format 4/12, simple + composite glyphs)
// ---------------------------------------------------------------------------
type TableMap = Map<string, { off: number; len: number }>;

class Font {
  name: string;
  data: Buffer;
  tables: TableMap;
  upem: number;
  numGlyphs: number;
  numHMetrics: number;
  locaFmt: number;
  cmap4: Buffer | null = null;
  cmap12: Buffer | null = null;

  constructor(path: string) {
    this.name = path;
    this.data = readFileSync(path);
    const d = this.data;
    const numTables = d.readUInt16BE(4);
    this.tables = new Map();
    for (let i = 0; i < numTables; i++) {
      const o = 12 + i * 16;
      const tag = d.toString('ascii', o, o + 4);
      this.tables.set(tag, { off: d.readUInt32BE(o + 8), len: d.readUInt32BE(o + 12) });
    }
    const head = this.must('head');
    this.upem = d.readUInt16BE(head.off + 18);
    this.locaFmt = d.readInt16BE(head.off + 50);
    this.numGlyphs = d.readUInt16BE(this.must('maxp').off + 4);
    this.numHMetrics = d.readUInt16BE(this.must('hhea').off + 34);
    const cmap = this.must('cmap');
    const nSub = d.readUInt16BE(cmap.off + 2);
    for (let i = 0; i < nSub; i++) {
      const so = cmap.off + 4 + i * 8;
      const subOff = cmap.off + d.readUInt32BE(so + 4);
      const fmt = d.readUInt16BE(subOff);
      if (fmt === 12 && !this.cmap12) this.cmap12 = d.subarray(subOff, subOff + d.readUInt32BE(subOff + 4));
      if (fmt === 4 && !this.cmap4) this.cmap4 = d.subarray(subOff, subOff + d.readUInt16BE(subOff + 2));
    }
  }

  must(tag: string): { off: number; len: number } {
    const t = this.tables.get(tag);
    if (!t) throw new Error('missing table ' + tag + ' in ' + this.name);
    return t;
  }

  glyphIndex(code: number): number {
    if (this.cmap12) {
      const c = this.cmap12;
      const n = c.readUInt32BE(12);
      let lo = 0;
      let hi = n - 1;
      while (lo <= hi) {
        const mid = (lo + hi) >> 1;
        const go = 16 + mid * 12;
        const s = c.readUInt32BE(go);
        const e = c.readUInt32BE(go + 4);
        if (code < s) hi = mid - 1;
        else if (code > e) lo = mid + 1;
        else return c.readUInt32BE(go + 8) + (code - s);
      }
      return 0;
    }
    if (this.cmap4) {
      const c = this.cmap4;
      const segCount = c.readUInt16BE(6) >> 1;
      const endBase = 14;
      const startBase = endBase + segCount * 2 + 2;
      const deltaBase = startBase + segCount * 2;
      const rangeBase = deltaBase + segCount * 2;
      for (let i = 0; i < segCount; i++) {
        const end = c.readUInt16BE(endBase + i * 2);
        if (code > end) continue;
        const start = c.readUInt16BE(startBase + i * 2);
        if (code < start) return 0;
        const delta = c.readInt16BE(deltaBase + i * 2);
        const ro = c.readUInt16BE(rangeBase + i * 2);
        if (ro === 0) return (code + delta) & 0xffff;
        const addr = rangeBase + i * 2 + ro + (code - start) * 2;
        const g = c.readUInt16BE(addr);
        if (g === 0) return 0;
        return (g + delta) & 0xffff;
      }
      return 0;
    }
    return 0;
  }

  advance(gid: number): number {
    const h = this.must('hmtx');
    const i = Math.min(gid, this.numHMetrics - 1);
    return this.data.readUInt16BE(h.off + i * 4);
  }

  // Returns outline contours: each contour is a list of segments.
  // Segment: {x0,y0,cx,cy,x1,y1} quadratic, or line when cx/cy are null.
  glyphOutline(gid: number): Seg[][] {
    const loca = this.must('loca');
    const glyf = this.must('glyf');
    const d = this.data;
    let off0: number;
    let off1: number;
    if (this.locaFmt === 0) {
      off0 = d.readUInt16BE(loca.off + gid * 2) * 2;
      off1 = d.readUInt16BE(loca.off + (gid + 1) * 2) * 2;
    } else {
      off0 = d.readUInt32BE(loca.off + gid * 4);
      off1 = d.readUInt32BE(loca.off + (gid + 1) * 4);
    }
    if (off1 <= off0) return [];
    const g0 = glyf.off + off0;
    const nCont = d.readInt16BE(g0);
    if (nCont >= 0) return this.simpleOutline(g0, nCont);
    return this.compositeOutline(g0);
  }

  simpleOutline(g0: number, nCont: number): Seg[][] {
    const d = this.data;
    const endPts: number[] = [];
    for (let i = 0; i < nCont; i++) endPts.push(d.readUInt16BE(g0 + 10 + i * 2));
    const nPts = endPts.length ? endPts[nCont - 1] + 1 : 0;
    let p = g0 + 10 + nCont * 2;
    const instrLen = d.readUInt16BE(p);
    p += 2 + instrLen;
    const flags: number[] = [];
    while (flags.length < nPts) {
      const f = d[p++];
      flags.push(f);
      if (f & 0x08) {
        const rep = d[p++];
        for (let i = 0; i < rep; i++) flags.push(f);
      }
    }
    const xs: number[] = new Array(nPts).fill(0);
    const ys: number[] = new Array(nPts).fill(0);
    let x = 0;
    for (let i = 0; i < nPts; i++) {
      const f = flags[i];
      if (f & 0x02) {
        const v = d[p++];
        x += f & 0x10 ? v : -v;
      } else if (!(f & 0x10)) {
        x += d.readInt16BE(p);
        p += 2;
      }
      xs[i] = x;
    }
    let y = 0;
    for (let i = 0; i < nPts; i++) {
      const f = flags[i];
      if (f & 0x04) {
        const v = d[p++];
        y += f & 0x20 ? v : -v;
      } else if (!(f & 0x20)) {
        y += d.readInt16BE(p);
        p += 2;
      }
      ys[i] = y;
    }
    const contours: Seg[][] = [];
    let start = 0;
    for (let c = 0; c < nCont; c++) {
      const end = endPts[c];
      const pts: Pt[] = [];
      for (let i = start; i <= end; i++) pts.push({ x: xs[i], y: ys[i], on: (flags[i] & 0x01) !== 0 });
      contours.push(contourToSegs(pts));
      start = end + 1;
    }
    return contours;
  }

  compositeOutline(g0: number): Seg[][] {
    const d = this.data;
    let p = g0 + 10;
    const out: Seg[][] = [];
    for (;;) {
      const flags = d.readUInt16BE(p);
      const compGid = d.readUInt16BE(p + 2);
      p += 4;
      let dx = 0;
      let dy = 0;
      if (flags & 0x0001) {
        dx = d.readInt16BE(p);
        dy = d.readInt16BE(p + 2);
        p += 4;
      } else {
        dx = d.readInt8(p);
        dy = d.readInt8(p + 1);
        p += 2;
      }
      let a = 1;
      let b = 0;
      let cc = 0;
      let dd = 1;
      if (flags & 0x0008) {
        a = d.readInt16BE(p) / 16384;
        dd = a;
        p += 2;
      } else if (flags & 0x0040) {
        a = d.readInt16BE(p) / 16384;
        dd = d.readInt16BE(p + 2) / 16384;
        p += 4;
      } else if (flags & 0x0080) {
        a = d.readInt16BE(p) / 16384;
        b = d.readInt16BE(p + 2) / 16384;
        cc = d.readInt16BE(p + 4) / 16384;
        dd = d.readInt16BE(p + 6) / 16384;
        p += 8;
      }
      const sub = this.glyphOutline(compGid);
      for (const contour of sub) {
        out.push(
          contour.map((s) => ({
            x0: s.x0 * a + s.y0 * cc + dx,
            y0: s.x0 * b + s.y0 * dd + dy,
            cx: s.cx === null ? null : s.cx * a + s.cy * cc + dx,
            cy: s.cy === null ? null : s.cx * b + s.cy * dd + dy,
            x1: s.x1 * a + s.y1 * cc + dx,
            y1: s.x1 * b + s.y1 * dd + dy,
          })),
        );
      }
      if (!(flags & 0x0020)) break;
    }
    return out;
  }
}

type Pt = { x: number; y: number; on: boolean };
type Seg = { x0: number; y0: number; cx: number | null; cy: number | null; x1: number; y1: number };

function contourToSegs(pts: Pt[]): Seg[] {
  const segs: Seg[] = [];
  if (pts.length === 0) return segs;
  // Build the point ring starting at an on-curve point (or the midpoint of
  // first/last when both are off-curve).
  const ring: Pt[] = [];
  let startIdx = 0;
  for (let i = 0; i < pts.length; i++) if (pts[i].on) { startIdx = i; break; }
  if (pts.every((q) => !q.on)) {
    // All off-curve: implied on-curve points are midpoints.
    const n = pts.length;
    for (let i = 0; i < n; i++) {
      const a = pts[i];
      const b = pts[(i + 1) % n];
      ring.push({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2, on: true });
      ring.push(a);
    }
  } else {
    for (let i = 0; i < pts.length; i++) ring.push(pts[(startIdx + i) % pts.length]);
  }
  // Walk the ring: on-curve points anchor segments; an off-curve point between
  // two on-curve points is a quadratic control; consecutive off-curve points
  // get an implied on-curve midpoint between them.
  const n = ring.length;
  let cur = ring[0];
  let i = 1;
  while (i < n) {
    const p = ring[i];
    if (p.on) {
      segs.push({ x0: cur.x, y0: cur.y, cx: null, cy: null, x1: p.x, y1: p.y });
      cur = p;
      i++;
    } else {
      const nxt = ring[(i + 1) % n];
      if (nxt.on) {
        segs.push({ x0: cur.x, y0: cur.y, cx: p.x, cy: p.y, x1: nxt.x, y1: nxt.y });
        cur = nxt;
        i += 2;
      } else {
        const mid = { x: (p.x + nxt.x) / 2, y: (p.y + nxt.y) / 2, on: true };
        segs.push({ x0: cur.x, y0: cur.y, cx: p.x, cy: p.y, x1: mid.x, y1: mid.y });
        cur = mid;
        i++;
      }
    }
  }
  // Close the contour back to the start point.
  if (cur.x !== ring[0].x || cur.y !== ring[0].y) {
    const p = ring[n - 1];
    if (!p.on && p !== cur) {
      segs.push({ x0: cur.x, y0: cur.y, cx: p.x, cy: p.y, x1: ring[0].x, y1: ring[0].y });
    } else {
      segs.push({ x0: cur.x, y0: cur.y, cx: null, cy: null, x1: ring[0].x, y1: ring[0].y });
    }
  }
  return segs;
}

// ---------------------------------------------------------------------------
// Glyph flattening (adaptive) and rasterisation with fractional coverage
// ---------------------------------------------------------------------------
type Line = { x0: number; y0: number; x1: number; y1: number };

function flattenQuad(s: Seg, tol: number, out: Line[]): void {
  if (s.cx === null || s.cy === null) {
    out.push({ x0: s.x0, y0: s.y0, x1: s.x1, y1: s.y1 });
    return;
  }
  // Adaptive subdivision: split until the control point sits within tol of
  // the chord (flatness test), with a depth cap. Fixed segment counts make
  // big serif letters wavy; this keeps curves smooth at every size.
  const stack: Seg[] = [s];
  let guard = 0;
  while (stack.length && guard < 4096) {
    guard++;
    const q = stack.pop()!;
    const dx = q.x1 - q.x0;
    const dy = q.y1 - q.y0;
    const len = Math.hypot(dx, dy);
    const dev = len > 0 ? Math.abs((q.cx! - q.x0) * dy - (q.cy! - q.y0) * dx) / len : Math.hypot(q.cx! - q.x0, q.cy! - q.y0);
    if (dev <= tol || len < 0.5) {
      out.push({ x0: q.x0, y0: q.y0, x1: q.x1, y1: q.y1 });
    } else {
      const mx01 = (q.x0 + q.cx!) / 2;
      const my01 = (q.y0 + q.cy!) / 2;
      const mx12 = (q.cx! + q.x1) / 2;
      const my12 = (q.cy! + q.y1) / 2;
      const mx = (mx01 + mx12) / 2;
      const my = (my01 + my12) / 2;
      stack.push({ x0: mx, y0: my, cx: mx12, cy: my12, x1: q.x1, y1: q.y1 });
      stack.push({ x0: q.x0, y0: q.y0, cx: mx01, cy: my01, x1: mx, y1: my });
    }
  }
}

type GlyphTile = {
  w: number;
  h: number;
  ox: number; // pixel offset of tile origin relative to pen position (x)
  oy: number; // pixel offset of tile origin relative to baseline (y, down positive)
  adv: number; // advance in pixels
  cov: Float32Array; // coverage 0..1 per pixel
};

const glyphCache = new Map<string, GlyphTile>();

function rasterGlyph(font: Font, code: number, px: number): GlyphTile {
  // Cache key MUST include the font identity: all four DejaVu faces share
  // upem 2048, so a key without it swaps bold and regular glyphs.
  const key = font.name + '|' + code + '|' + px;
  const hit = glyphCache.get(key);
  if (hit) return hit;
  const gid = font.glyphIndex(code);
  const scale = px / font.upem;
  const adv = font.advance(gid) * scale;
  const contours = font.glyphOutline(gid);
  const lines: Line[] = [];
  const tol = 0.22; // pixels at render size
  for (const contour of contours) {
    for (const s of contour) {
      flattenQuad(
        { x0: s.x0 * scale, y0: -s.y0 * scale, cx: s.cx === null ? null : s.cx * scale, cy: s.cy === null ? null : -s.cy * scale, x1: s.x1 * scale, y1: -s.y1 * scale },
        tol,
        lines,
      );
    }
  }
  // Bounding box of the flattened outline.
  let minX = Infinity;
  let maxX = -Infinity;
  let minY = Infinity;
  let maxY = -Infinity;
  for (const l of lines) {
    minX = Math.min(minX, l.x0, l.x1);
    maxX = Math.max(maxX, l.x0, l.x1);
    minY = Math.min(minY, l.y0, l.y1);
    maxY = Math.max(maxY, l.y0, l.y1);
  }
  if (!isFinite(minX) || lines.length === 0) {
    const tile: GlyphTile = { w: 0, h: 0, ox: 0, oy: 0, adv, cov: new Float32Array(0) };
    glyphCache.set(key, tile);
    return tile;
  }
  // Sub-pixel phase anchoring: the tile grid is anchored to integer pixels
  // relative to the pen, so identical glyphs at different positions rasterise
  // identically and stems never drift by a fraction of a pixel.
  const ox = Math.floor(minX);
  const oy = Math.floor(minY);
  const w = Math.ceil(maxX) - ox + 1;
  const h = Math.ceil(maxY) - oy + 1;
  const cov = new Float32Array(w * h);
  const SUB = 4; // vertical supersample rows per pixel
  for (let row = 0; row < h; row++) {
    for (let sub = 0; sub < SUB; sub++) {
      const y = oy + row + (sub + 0.5) / SUB;
      const xs: number[] = [];
      for (const l of lines) {
        const y0 = l.y0;
        const y1 = l.y1;
        if ((y0 <= y && y1 > y) || (y1 <= y && y0 > y)) {
          const t = (y - y0) / (y1 - y0);
          xs.push(l.x0 + t * (l.x1 - l.x0));
        }
      }
      xs.sort((a, b) => a - b);
      for (let k = 0; k + 1 < xs.length; k += 2) {
        const a = xs[k];
        const b = xs[k + 1];
        const c0 = Math.max(a, ox);
        const c1 = Math.min(b, ox + w);
        if (c1 <= c0) continue;
        const px0 = Math.floor(c0);
        const px1 = Math.floor(c1 - 1e-9);
        for (let pxI = px0; pxI <= px1; pxI++) {
          const lo = Math.max(c0, pxI);
          const hi = Math.min(c1, pxI + 1);
          if (hi > lo) cov[row * w + (pxI - ox)] += (hi - lo) / SUB;
        }
      }
    }
  }
  const tile: GlyphTile = { w, h, ox, oy, adv, cov };
  glyphCache.set(key, tile);
  return tile;
}

// ---------------------------------------------------------------------------
// Canvas (2x buffer) and text engine
// ---------------------------------------------------------------------------
const buf = new Uint8Array(W * H * 3);
for (let i = 0; i < W * H; i++) {
  buf[i * 3] = PAPER[0];
  buf[i * 3 + 1] = PAPER[1];
  buf[i * 3 + 2] = PAPER[2];
}

function setPx2(x: number, y: number, c: [number, number, number]): void {
  if (x < 0 || y < 0 || x >= W || y >= H) return;
  const i = (y * W + x) * 3;
  buf[i] = c[0];
  buf[i + 1] = c[1];
  buf[i + 2] = c[2];
}

function blendPx2(x: number, y: number, c: [number, number, number], a: number): void {
  if (a <= 0 || x < 0 || y < 0 || x >= W || y >= H) return;
  if (a >= 1) {
    setPx2(x, y, c);
    return;
  }
  const i = (y * W + x) * 3;
  buf[i] = clamp255(buf[i] * (1 - a) + c[0] * a);
  buf[i + 1] = clamp255(buf[i + 1] * (1 - a) + c[1] * a);
  buf[i + 2] = clamp255(buf[i + 2] * (1 - a) + c[2] * a);
}

// Final-coordinate helpers (all layout numbers are in final 1024px space).
const fx = (v: number): number => Math.round(v * S);
function fillRect(x: number, y: number, w: number, h: number, c: [number, number, number]): void {
  const x0 = Math.max(0, fx(x));
  const y0 = Math.max(0, fx(y));
  const x1 = Math.min(W, fx(x + w));
  const y1 = Math.min(H, fx(y + h));
  for (let yy = y0; yy < y1; yy++) {
    let i = (yy * W + x0) * 3;
    for (let xx = x0; xx < x1; xx++) {
      buf[i] = c[0];
      buf[i + 1] = c[1];
      buf[i + 2] = c[2];
      i += 3;
    }
  }
}

function fillCircle(cx: number, cy: number, r: number, c: [number, number, number]): void {
  const x0 = Math.max(0, fx(cx - r));
  const x1 = Math.min(W - 1, fx(cx + r));
  const y0 = Math.max(0, fx(cy - r));
  const y1 = Math.min(H - 1, fx(cy + r));
  const ccx = cx * S;
  const ccy = cy * S;
  const rr = r * S;
  for (let yy = y0; yy <= y1; yy++) {
    const dy = yy + 0.5 - ccy;
    for (let xx = x0; xx <= x1; xx++) {
      const dx = xx + 0.5 - ccx;
      if (dx * dx + dy * dy <= rr * rr) setPx2(xx, yy, c);
    }
  }
}

// Even-odd polygon fill, final coords.
function fillPoly(pts: [number, number][], c: [number, number, number]): void {
  const p = pts.map(([a, b]) => [a * S, b * S] as [number, number]);
  let minY = Infinity;
  let maxY = -Infinity;
  for (const [, y] of p) {
    minY = Math.min(minY, y);
    maxY = Math.max(maxY, y);
  }
  const y0 = Math.max(0, Math.floor(minY));
  const y1 = Math.min(H - 1, Math.ceil(maxY));
  for (let yy = y0; yy <= y1; yy++) {
    const y = yy + 0.5;
    const xs: number[] = [];
    for (let i = 0; i < p.length; i++) {
      const [ax, ay] = p[i];
      const [bx, by] = p[(i + 1) % p.length];
      if ((ay <= y && by > y) || (by <= y && ay > y)) {
        xs.push(ax + ((y - ay) / (by - ay)) * (bx - ax));
      }
    }
    xs.sort((a, b) => a - b);
    for (let k = 0; k + 1 < xs.length; k += 2) {
      const x0 = Math.max(0, Math.ceil(xs[k] - 0.5));
      const x1 = Math.min(W - 1, Math.floor(xs[k + 1] - 0.5));
      for (let xx = x0; xx <= x1; xx++) setPx2(xx, yy, c);
    }
  }
}

// Thick line drawn as a quad, final coords.
function strokeLine(x0: number, y0: number, x1: number, y1: number, w: number, c: [number, number, number]): void {
  const dx = x1 - x0;
  const dy = y1 - y0;
  const len = Math.hypot(dx, dy) || 1;
  const nx = (-dy / len) * (w / 2);
  const ny = (dx / len) * (w / 2);
  fillPoly(
    [
      [x0 + nx, y0 + ny],
      [x1 + nx, y1 + ny],
      [x1 - nx, y1 - ny],
      [x0 - nx, y0 - ny],
    ],
    c,
  );
}

// ---- Text ----
let F_SERIF: Font;
let F_SERIF_B: Font;
let F_SANS: Font;
let F_SANS_B: Font;

function loadFonts(): void {
  const dir = dirname(fileURLToPath(import.meta.url));
  F_SERIF = new Font(join(dir, 'fonts', 'DejaVuSerif.ttf'));
  F_SERIF_B = new Font(join(dir, 'fonts', 'DejaVuSerif-Bold.ttf'));
  F_SANS = new Font(join(dir, 'fonts', 'DejaVuSans.ttf'));
  F_SANS_B = new Font(join(dir, 'fonts', 'DejaVuSans-Bold.ttf'));
}

function textWidth(s: string, size: number, font: Font): number {
  const px = size * S;
  let w = 0;
  for (const ch of s) w += rasterGlyph(font, ch.codePointAt(0)!, px).adv;
  return w / S;
}

// Draw text; x,y are final coords, y = baseline. align: 'l' | 'c' | 'r'.
// Positions snap to integer final pixels (so integer 2x pixels) at every size.
function drawText(s: string, x: number, y: number, size: number, font: Font, c: [number, number, number], align: 'l' | 'c' | 'r' = 'l'): void {
  const px = size * S;
  const total = textWidth(s, size, font);
  let penX = x;
  if (align === 'c') penX = x - total / 2;
  if (align === 'r') penX = x - total;
  penX = Math.round(penX * S) / S; // snap glyph x to integer 2x pixels
  const baseY = Math.round(y * S);
  const gamma = size <= 16;
  let cursor = penX * S;
  for (const ch of s) {
    const tile = rasterGlyph(font, ch.codePointAt(0)!, px);
    if (tile.w > 0) {
      const gx = Math.round(cursor) + tile.ox;
      const gy = baseY + tile.oy;
      for (let row = 0; row < tile.h; row++) {
        const yy = gy + row;
        if (yy < 0 || yy >= H) continue;
        for (let col = 0; col < tile.w; col++) {
          let a = tile.cov[row * tile.w + col];
          if (a <= 0) continue;
          if (a > 1) a = 1;
          if (gamma) a = Math.pow(a, 0.6);
          blendPx2(gx + col, yy, c, a);
        }
      }
    }
    cursor += tile.adv;
  }
}

// Greedy word wrap to a max width (final px). Returns lines.
function wrap(s: string, size: number, font: Font, maxW: number): string[] {
  const words = s.split(' ');
  const lines: string[] = [];
  let cur = '';
  for (const w of words) {
    const test = cur ? cur + ' ' + w : w;
    if (textWidth(test, size, font) <= maxW || !cur) cur = test;
    else {
      lines.push(cur);
      cur = w;
    }
  }
  if (cur) lines.push(cur);
  return lines;
}

// ---------------------------------------------------------------------------
// PNG encoding (deterministic: no ancillary chunks, fixed deflate level)
// ---------------------------------------------------------------------------
const CRC_TABLE = new Uint32Array(256);
for (let n = 0; n < 256; n++) {
  let c = n;
  for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  CRC_TABLE[n] = c >>> 0;
}
function crc32(b: Buffer): number {
  let c = 0xffffffff;
  for (let i = 0; i < b.length; i++) c = CRC_TABLE[(c ^ b[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type: string, data: Buffer): Buffer {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, 'ascii');
  data.copy(out, 8);
  out.writeUInt32BE(crc32(Buffer.concat([Buffer.from(type, 'ascii'), data])), 8 + data.length);
  return out;
}
function encodePNG(rgbBuf: Uint8Array, w: number, h: number): Buffer {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(w, 0);
  ihdr.writeUInt32BE(h, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = 2; // colour type RGB
  ihdr[10] = 0;
  ihdr[11] = 0;
  ihdr[12] = 0;
  const raw = Buffer.alloc(h * (1 + w * 3));
  for (let y = 0; y < h; y++) {
    raw[y * (1 + w * 3)] = 0;
    Buffer.from(rgbBuf.buffer, rgbBuf.byteOffset + y * w * 3, w * 3).copy(raw, y * (1 + w * 3) + 1);
  }
  const idat = deflateSync(raw, { level: 9 });
  const sig = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]);
  return Buffer.concat([sig, chunk('IHDR', ihdr), chunk('IDAT', idat), chunk('IEND', Buffer.alloc(0))]);
}

// ---------------------------------------------------------------------------
// Lanczos-3 downscale 2048 -> 1024 (separable, float accumulator, clamp+round)
// ---------------------------------------------------------------------------
function lanczos(x: number): number {
  if (x === 0) return 1;
  if (Math.abs(x) >= 3) return 0;
  const pix = Math.PI * x;
  return (Math.sin(pix) / pix) * (Math.sin(pix / 3) / (pix / 3));
}
function downscale(src: Uint8Array, sw: number, sh: number, dw: number, dh: number): Uint8Array {
  // Horizontal pass into a float buffer dw x sh.
  const tmp = new Float32Array(dw * sh * 3);
  const scaleX = sw / dw;
  for (let y = 0; y < sh; y++) {
    for (let x = 0; x < dw; x++) {
      const cx = (x + 0.5) * scaleX - 0.5;
      const x0 = Math.ceil(cx - 3 * scaleX);
      const x1 = Math.floor(cx + 3 * scaleX);
      let ws = 0;
      let r = 0;
      let g = 0;
      let b = 0;
      for (let sx = x0; sx <= x1; sx++) {
        const wgt = lanczos((sx - cx) / scaleX);
        if (wgt === 0) continue;
        const sxx = Math.max(0, Math.min(sw - 1, sx));
        const i = (y * sw + sxx) * 3;
        r += src[i] * wgt;
        g += src[i + 1] * wgt;
        b += src[i + 2] * wgt;
        ws += wgt;
      }
      const o = (y * dw + x) * 3;
      tmp[o] = r / ws;
      tmp[o + 1] = g / ws;
      tmp[o + 2] = b / ws;
    }
  }
  const out = new Uint8Array(dw * dh * 3);
  const scaleY = sh / dh;
  for (let y = 0; y < dh; y++) {
    const cy = (y + 0.5) * scaleY - 0.5;
    const y0 = Math.ceil(cy - 3 * scaleY);
    const y1 = Math.floor(cy + 3 * scaleY);
    for (let x = 0; x < dw; x++) {
      let ws = 0;
      let r = 0;
      let g = 0;
      let b = 0;
      for (let sy = y0; sy <= y1; sy++) {
        const wgt = lanczos((sy - cy) / scaleY);
        if (wgt === 0) continue;
        const syy = Math.max(0, Math.min(sh - 1, sy));
        const i = (syy * dw + x) * 3;
        r += tmp[i] * wgt;
        g += tmp[i + 1] * wgt;
        b += tmp[i + 2] * wgt;
        ws += wgt;
      }
      const o = (y * dw + x) * 3;
      out[o] = clamp255(r / ws);
      out[o + 1] = clamp255(g / ws);
      out[o + 2] = clamp255(b / ws);
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Scene helpers: every scene is drawn with code into its own rect.
// ---------------------------------------------------------------------------
function sky(x: number, y: number, w: number, h: number, top: [number, number, number], bot: [number, number, number]): void {
  const steps = 24;
  for (let i = 0; i < steps; i++) {
    const t = i / (steps - 1);
    fillRect(x, y + (h * i) / steps, w, h / steps + 0.6, [
      Math.round(top[0] + (bot[0] - top[0]) * t),
      Math.round(top[1] + (bot[1] - top[1]) * t),
      Math.round(top[2] + (bot[2] - top[2]) * t),
    ]);
  }
}
function flame(x: number, y: number, r: number): void {
  fillCircle(x, y, r, rgb(255, 122, 26));
  fillCircle(x, y - r * 0.25, r * 0.62, rgb(255, 196, 66));
  fillCircle(x, y - r * 0.45, r * 0.3, rgb(255, 240, 180));
}
// Layered flame tongues (outer orange, mid yellow, pale core) for a burning scene.
function flameTongues(x: number, y: number, s: number): void {
  fillPoly(
    [
      [x - s * 0.55, y],
      [x - s * 0.3, y - s * 0.7],
      [x, y - s * 1.15],
      [x + s * 0.28, y - s * 0.62],
      [x + s * 0.55, y],
    ],
    rgb(255, 110, 20),
  );
  fillPoly(
    [
      [x - s * 0.34, y],
      [x - s * 0.16, y - s * 0.5],
      [x + s * 0.05, y - s * 0.85],
      [x + s * 0.3, y - s * 0.45],
      [x + s * 0.34, y],
    ],
    rgb(255, 190, 60),
  );
  fillPoly(
    [
      [x - s * 0.16, y],
      [x - s * 0.06, y - s * 0.32],
      [x + s * 0.08, y - s * 0.5],
      [x + s * 0.16, y],
    ],
    rgb(255, 235, 170),
  );
}
// Quadcopter drone: X arms, rotor-blur discs, body, red light.
function quadcopter(cx: number, cy: number, s: number): void {
  strokeLine(cx - s, cy - s * 0.5, cx + s, cy + s * 0.5, 1.4, rgb(30, 30, 34));
  strokeLine(cx + s, cy - s * 0.5, cx - s, cy + s * 0.5, 1.4, rgb(30, 30, 34));
  fillCircle(cx - s, cy - s * 0.5, s * 0.45, rgb(180, 185, 195));
  fillCircle(cx + s, cy - s * 0.5, s * 0.45, rgb(180, 185, 195));
  fillCircle(cx - s, cy + s * 0.5, s * 0.45, rgb(180, 185, 195));
  fillCircle(cx + s, cy + s * 0.5, s * 0.45, rgb(180, 185, 195));
  fillRect(cx - s * 0.4, cy - s * 0.28, s * 0.8, s * 0.56, rgb(30, 30, 34));
  fillCircle(cx, cy + s * 0.3, 1.2, rgb(255, 60, 50));
}
function smoke(x: number, y: number, r: number, c: [number, number, number]): void {
  fillCircle(x, y, r, c);
  fillCircle(x + r * 0.7, y - r * 0.5, r * 0.8, c);
  fillCircle(x - r * 0.7, y - r * 0.45, r * 0.75, c);
}
function person(x: number, y: number, s: number, shirt: [number, number, number], skin: [number, number, number] = rgb(214, 164, 120)): void {
  fillCircle(x, y - s * 0.78, s * 0.22, skin); // head
  fillRect(x - s * 0.24, y - s * 0.55, s * 0.48, s * 0.62, shirt); // torso
  fillRect(x - s * 0.24, y + s * 0.05, s * 0.2, s * 0.5, rgb(40, 40, 48)); // legs
  fillRect(x + s * 0.04, y + s * 0.05, s * 0.2, s * 0.5, rgb(40, 40, 48));
}
function flagPole(x: number, y: number, h: number, c: [number, number, number]): void {
  strokeLine(x, y, x, y - h, 1.6, rgb(60, 56, 50));
  fillPoly(
    [
      [x, y - h],
      [x + 13, y - h + 4],
      [x, y - h + 8],
    ],
    c,
  );
}

// Scene 1: COP31 collapse — dramatic night plenary hall in Antalya.
// Deep hall, arched windows with moon, a row of country flags, a long table
// in perspective with delegates leaning in, a cracked globe centrepiece and
// a tilted NO DEAL stamp cutting across the table.
function sceneCOP31(x: number, y: number, w: number, h: number): void {
  // Wall + ceiling.
  sky(x, y, w, h, rgb(16, 26, 42), rgb(40, 62, 84));
  fillRect(x, y, w, h * 0.08, rgb(11, 19, 30));
  // Wall clock (overtime, ~2am) top right, clear of the number badge.
  fillCircle(x + w * 0.945, y + h * 0.13, h * 0.055, rgb(238, 232, 220));
  fillCircle(x + w * 0.945, y + h * 0.13, h * 0.045, WHITE);
  strokeLine(x + w * 0.945, y + h * 0.13, x + w * 0.945, y + h * 0.095, 1.4, rgb(30, 30, 34));
  strokeLine(x + w * 0.945, y + h * 0.13, x + w * 0.965, y + h * 0.115, 1.4, rgb(30, 30, 34));
  // Arched windows with night sky.
  for (let i = 0; i < 3; i++) {
    const wx = x + w * (0.14 + i * 0.29);
    fillPoly(
      [
        [wx, y + h * 0.44],
        [wx + w * 0.02, y + h * 0.18],
        [wx + w * 0.1, y + h * 0.1],
        [wx + w * 0.18, y + h * 0.18],
        [wx + w * 0.2, y + h * 0.44],
      ],
      rgb(122, 100, 58),
    );
    fillPoly(
      [
        [wx + w * 0.018, y + h * 0.44],
        [wx + w * 0.036, y + h * 0.2],
        [wx + w * 0.1, y + h * 0.13],
        [wx + w * 0.164, y + h * 0.2],
        [wx + w * 0.182, y + h * 0.44],
      ],
      rgb(9, 17, 30),
    );
  }
  // Stars + crescent moon in the middle window.
  for (let i = 0; i < 9; i++) {
    fillCircle(x + w * (0.18 + ((i * 53) % 60) / 100), y + h * (0.15 + ((i * 29) % 22) / 100), 0.9, WHITE);
  }
  fillCircle(x + w * 0.5, y + h * 0.2, h * 0.04, rgb(240, 230, 190));
  fillCircle(x + w * 0.512, y + h * 0.195, h * 0.035, rgb(9, 17, 30));
  // Pendant lights with warm glow.
  for (let i = 0; i < 4; i++) {
    const lx = x + w * (0.17 + i * 0.22);
    strokeLine(lx, y + h * 0.08, lx, y + h * 0.15, 1.2, rgb(90, 80, 60));
    fillCircle(lx, y + h * 0.18, h * 0.062, rgb(255, 190, 90));
    fillCircle(lx, y + h * 0.18, h * 0.032, rgb(255, 232, 170));
  }
  // Row of small country flags along the wall.
  const flagCols: [number, number, number][][] = [
    [rgb(30, 60, 150), rgb(255, 210, 60)],
    [rgb(180, 30, 40), rgb(240, 240, 240)],
    [rgb(240, 240, 240), rgb(200, 40, 50)],
    [rgb(40, 90, 180), rgb(255, 140, 40)],
    [rgb(200, 30, 40), rgb(240, 240, 240)],
    [rgb(200, 40, 40), rgb(240, 240, 240)],
    [rgb(255, 200, 60), rgb(30, 60, 150)],
    [rgb(255, 150, 40), rgb(240, 240, 240)],
    [rgb(30, 140, 60), rgb(255, 220, 60)],
    [rgb(210, 30, 40), rgb(240, 240, 240)],
  ];
  for (let i = 0; i < 10; i++) {
    const fx0 = x + w * (0.055 + i * 0.09);
    const fy = y + h * 0.5;
    strokeLine(fx0, fy, fx0, fy - h * 0.085, 1.2, rgb(70, 64, 54));
    fillRect(fx0, fy - h * 0.085, w * 0.055, h * 0.04, flagCols[i][0]);
    fillRect(fx0, fy - h * 0.045, w * 0.055, h * 0.04, flagCols[i][1]);
  }
  // Floor.
  fillRect(x, y + h * 0.84, w, h * 0.16, rgb(22, 30, 42));
  // Warm light pool on the floor.
  fillPoly(
    [
      [x + w * 0.3, y + h],
      [x + w * 0.38, y + h * 0.86],
      [x + w * 0.62, y + h * 0.86],
      [x + w * 0.7, y + h],
    ],
    rgb(88, 66, 38),
  );
  // Long table in perspective (top + front face).
  fillPoly(
    [
      [x + w * 0.1, y + h * 0.6],
      [x + w * 0.9, y + h * 0.6],
      [x + w * 0.98, y + h * 0.84],
      [x + w * 0.02, y + h * 0.84],
    ],
    rgb(122, 84, 48),
  );
  fillPoly(
    [
      [x + w * 0.1, y + h * 0.6],
      [x + w * 0.9, y + h * 0.6],
      [x + w * 0.88, y + h * 0.64],
      [x + w * 0.12, y + h * 0.64],
    ],
    rgb(198, 166, 116),
  );
  fillPoly(
    [
      [x + w * 0.02, y + h * 0.84],
      [x + w * 0.98, y + h * 0.84],
      [x + w * 0.98, y + h * 0.9],
      [x + w * 0.02, y + h * 0.9],
    ],
    rgb(88, 58, 30),
  );
  // Papers, microphones, glasses on the table.
  for (let i = 0; i < 6; i++) {
    fillRect(x + w * (0.16 + i * 0.13), y + h * (0.68 + ((i * 7) % 5) / 100), w * 0.05, h * 0.045, rgb(238, 234, 224));
  }
  for (let i = 0; i < 4; i++) {
    const mx0 = x + w * (0.24 + i * 0.17);
    strokeLine(mx0, y + h * 0.72, mx0, y + h * 0.64, 1.2, rgb(40, 40, 44));
    fillCircle(mx0, y + h * 0.63, 1.6, rgb(40, 40, 44));
  }
  // Delegates leaning in behind the table.
  const shirts: [number, number, number][] = [rgb(42, 93, 176), rgb(176, 30, 36), rgb(26, 122, 110), rgb(200, 138, 0), rgb(122, 74, 158), rgb(58, 122, 58), rgb(180, 90, 40), rgb(60, 60, 66)];
  const skins: [number, number, number][] = [rgb(214, 164, 120), rgb(180, 130, 95), rgb(235, 195, 155), rgb(160, 110, 80), rgb(214, 164, 120), rgb(235, 195, 155), rgb(180, 130, 95), rgb(160, 110, 80)];
  for (let i = 0; i < 8; i++) {
    const cx = x + w * (0.1 + i * 0.114);
    person(cx, y + h * 0.62, h * 0.24, shirts[i], skins[i]);
    // Hair.
    fillCircle(cx, y + h * 0.62 - h * 0.24 * 0.82, h * 0.24 * 0.2, i % 2 ? rgb(40, 32, 26) : rgb(90, 78, 66));
  }
  // One delegate standing at the right end, gesturing.
  person(x + w * 0.94, y + h * 0.62, h * 0.3, rgb(176, 30, 36));
  strokeLine(x + w * 0.94, y + h * 0.5, x + w * 0.99, y + h * 0.38, 2, rgb(214, 164, 120));
  // Cracked globe centrepiece on a stand.
  fillRect(x + w * 0.47, y + h * 0.56, w * 0.06, h * 0.05, rgb(70, 58, 40));
  fillCircle(x + w * 0.5, y + h * 0.47, h * 0.115, rgb(90, 150, 190));
  fillPoly(
    [
      [x + w * 0.45, y + h * 0.42],
      [x + w * 0.5, y + h * 0.47],
      [x + w * 0.47, y + h * 0.53],
      [x + w * 0.44, y + h * 0.48],
    ],
    rgb(90, 170, 110),
  );
  fillPoly(
    [
      [x + w * 0.53, y + h * 0.4],
      [x + w * 0.56, y + h * 0.46],
      [x + w * 0.52, y + h * 0.5],
      [x + w * 0.51, y + h * 0.44],
    ],
    rgb(90, 170, 110),
  );
  strokeLine(x + w * 0.46, y + h * 0.38, x + w * 0.55, y + h * 0.55, 2.4, rgb(176, 30, 36));
  strokeLine(x + w * 0.55, y + h * 0.38, x + w * 0.46, y + h * 0.55, 2.4, rgb(176, 30, 36));
  // Tilted NO DEAL stamp across the table front.
  fillPoly(
    [
      [x + w * 0.34, y + h * 0.7],
      [x + w * 0.68, y + h * 0.66],
      [x + w * 0.7, y + h * 0.8],
      [x + w * 0.36, y + h * 0.84],
    ],
    rgb(176, 30, 36),
  );
  fillPoly(
    [
      [x + w * 0.355, y + h * 0.712],
      [x + w * 0.665, y + h * 0.676],
      [x + w * 0.68, y + h * 0.786],
      [x + w * 0.375, y + h * 0.822],
    ],
    rgb(200, 45, 50),
  );
  drawText('NO DEAL', x + w * 0.515, y + h * 0.775, 15, F_SANS_B, WHITE, 'c');
  // Two fallen papers on the floor.
  fillRect(x + w * 0.72, y + h * 0.92, w * 0.05, h * 0.05, rgb(238, 234, 224));
  fillRect(x + w * 0.78, y + h * 0.94, w * 0.04, h * 0.04, rgb(220, 216, 206));
}

// Scene 2: Hormuz tankers — cinematic strait at dusk: misty cliffs, low sun,
// two burning supertankers in the middle distance, fire-lit water in front.
function sceneHormuz(x: number, y: number, w: number, h: number): void {
  // ---- Background: dusk sky, low sun with halo, thin clouds.
  sky(x, y, w, h, rgb(198, 96, 40), rgb(250, 208, 145));
  fillCircle(x + w * 0.8, y + h * 0.17, h * 0.16, rgb(248, 190, 110));
  fillCircle(x + w * 0.8, y + h * 0.17, h * 0.12, rgb(250, 218, 145));
  fillCircle(x + w * 0.8, y + h * 0.17, h * 0.09, rgb(255, 240, 198));
  const cloud = (cx: number, cy: number, cw: number) => {
    fillPoly(
      [
        [cx, cy],
        [cx + cw * 0.3, cy - h * 0.02],
        [cx + cw * 0.7, cy - h * 0.015],
        [cx + cw, cy],
        [cx + cw * 0.7, cy + h * 0.012],
        [cx + cw * 0.3, cy + h * 0.015],
      ],
      rgb(246, 196, 138),
    );
    fillPoly(
      [
        [cx + cw * 0.1, cy + h * 0.008],
        [cx + cw * 0.9, cy + h * 0.008],
        [cx + cw * 0.8, cy + h * 0.02],
        [cx + cw * 0.2, cy + h * 0.02],
      ],
      rgb(224, 148, 92),
    );
  };
  cloud(x + w * 0.05, y + h * 0.1, w * 0.3);
  cloud(x + w * 0.52, y + h * 0.3, w * 0.26);
  cloud(x + w * 0.28, y + h * 0.42, w * 0.2);
  // ---- Far cliffs in haze, then near cliffs with sunlit ridge + texture.
  fillPoly(
    [
      [x, y + h * 0.55],
      [x + w * 0.13, y + h * 0.24],
      [x + w * 0.24, y + h * 0.55],
    ],
    rgb(158, 128, 104),
  );
  fillPoly(
    [
      [x + w, y + h * 0.55],
      [x + w * 0.88, y + h * 0.3],
      [x + w * 0.8, y + h * 0.55],
    ],
    rgb(158, 128, 104),
  );
  fillRect(x, y + h * 0.5, w, h * 0.05, rgb(244, 202, 148)); // mist at the cliff bases
  fillPoly(
    [
      [x, y + h * 0.55],
      [x + w * 0.1, y + h * 0.18],
      [x + w * 0.17, y + h * 0.55],
    ],
    rgb(104, 74, 56),
  );
  strokeLine(x + w * 0.1, y + h * 0.18, x + w * 0.17, y + h * 0.55, 1.4, rgb(232, 170, 110));
  strokeLine(x + w * 0.04, y + h * 0.34, x + w * 0.09, y + h * 0.3, 1.2, rgb(82, 58, 44));
  strokeLine(x + w * 0.06, y + h * 0.44, x + w * 0.11, y + h * 0.4, 1.2, rgb(82, 58, 44));
  strokeLine(x + w * 0.03, y + h * 0.48, x + w * 0.07, y + h * 0.46, 1.2, rgb(140, 105, 80));
  fillPoly(
    [
      [x + w, y + h * 0.55],
      [x + w * 0.9, y + h * 0.24],
      [x + w * 0.84, y + h * 0.55],
    ],
    rgb(104, 74, 56),
  );
  strokeLine(x + w * 0.9, y + h * 0.24, x + w * 0.84, y + h * 0.55, 1.4, rgb(232, 170, 110));
  strokeLine(x + w * 0.93, y + h * 0.36, x + w * 0.89, y + h * 0.32, 1.2, rgb(82, 58, 44));
  strokeLine(x + w * 0.95, y + h * 0.46, x + w * 0.91, y + h * 0.42, 1.2, rgb(82, 58, 44));
  // ---- Sea: dark teal gradient, deep at the bottom, horizon sheen.
  for (let i = 0; i < 8; i++) {
    const t = i / 7;
    fillRect(x, y + h * (0.55 + (0.45 * i) / 8), w, (h * 0.45) / 8 + 0.6, [
      Math.round(36 - 22 * t),
      Math.round(88 - 52 * t),
      Math.round(108 - 62 * t),
    ]);
  }
  fillRect(x, y + h * 0.55, w, h * 0.02, rgb(150, 190, 205));
  // Sun reflection column (before the ships, so hulls occlude it).
  for (let i = 0; i < 6; i++)
    fillRect(x + w * (0.765 + ((i * 7) % 3) * 0.008), y + h * (0.57 + i * 0.065), w * (0.06 - i * 0.004), h * 0.022, rgb(250, 198, 115));
  // Distant escort ship in the haze + wake.
  fillPoly(
    [
      [x + w * 0.44, y + h * 0.52],
      [x + w * 0.56, y + h * 0.52],
      [x + w * 0.54, y + h * 0.545],
      [x + w * 0.44, y + h * 0.545],
    ],
    rgb(40, 62, 78),
  );
  fillRect(x + w * 0.485, y + h * 0.49, w * 0.03, h * 0.03, rgb(40, 62, 78));
  strokeLine(x + w * 0.5, y + h * 0.49, x + w * 0.5, y + h * 0.44, 1.2, rgb(40, 62, 78));
  fillCircle(x + w * 0.5, y + h * 0.435, 1.2, rgb(255, 200, 120));
  strokeLine(x + w * 0.42, y + h * 0.55, x + w * 0.58, y + h * 0.55, 1.2, rgb(140, 175, 195));
  // ---- Flame tongues + layered smoke helpers.
  const tongues = (cx: number, cy: number, s: number) => {
    fillPoly(
      [
        [cx - s * 0.55, cy],
        [cx - s * 0.3, cy - s * 0.7],
        [cx, cy - s * 1.15],
        [cx + s * 0.28, cy - s * 0.62],
        [cx + s * 0.55, cy],
      ],
      rgb(255, 110, 20),
    );
    fillPoly(
      [
        [cx - s * 0.34, cy],
        [cx - s * 0.16, cy - s * 0.5],
        [cx + s * 0.05, cy - s * 0.85],
        [cx + s * 0.3, cy - s * 0.45],
        [cx + s * 0.34, cy],
      ],
      rgb(255, 190, 60),
    );
    fillPoly(
      [
        [cx - s * 0.16, cy],
        [cx - s * 0.06, cy - s * 0.32],
        [cx + s * 0.08, cy - s * 0.5],
        [cx + s * 0.16, cy],
      ],
      rgb(255, 235, 170),
    );
    // Embers rising.
    fillCircle(cx - s * 0.4, cy - s * 1.25, 1.8, rgb(255, 160, 60));
    fillCircle(cx + s * 0.35, cy - s * 1.05, 1.5, rgb(255, 190, 80));
    fillCircle(cx + s * 0.1, cy - s * 1.4, 1.4, rgb(255, 140, 40));
    fillCircle(cx - s * 0.15, cy - s * 1.55, 1.2, rgb(255, 200, 100));
  };
  const smokeStack = (cx: number, cy: number, s: number) => {
    fillCircle(cx, cy, s, rgb(58, 58, 62));
    fillCircle(cx + s * 0.65, cy - s * 0.45, s * 0.78, rgb(58, 58, 62));
    fillCircle(cx - s * 0.65, cy - s * 0.4, s * 0.72, rgb(58, 58, 62));
    fillCircle(cx + s * 0.2, cy - s * 0.7, s * 0.6, rgb(82, 82, 86));
    fillCircle(cx - s * 0.3, cy - s * 0.85, s * 0.5, rgb(104, 104, 108));
    fillCircle(cx, cy - s * 0.15, s * 0.5, rgb(52, 52, 56)); // dark core
  };
  // ---- One supertanker, drawn twice (mirrored, second one lower).
  const tanker = (mirror: boolean, dy: number) => {
    const X = (f: number) => x + w * (mirror ? 1 - f : f);
    const XR = (f: number, fw: number) => x + w * (mirror ? 1 - f - fw : f);
    const Y = (f: number) => y + h * (f + dy);
    // Hull with raked bow + flat stern; red boot-top; deck edge.
    fillPoly(
      [
        [X(0.07), Y(0.6)],
        [X(0.385), Y(0.6)],
        [X(0.44), Y(0.72)],
        [X(0.07), Y(0.72)],
      ],
      rgb(52, 52, 58),
    );
    fillPoly(
      [
        [X(0.07), Y(0.68)],
        [X(0.415), Y(0.68)],
        [X(0.44), Y(0.72)],
        [X(0.07), Y(0.72)],
      ],
      rgb(140, 40, 34),
    );
    // Hull plating: weld lines + plate seams.
    strokeLine(X(0.07), Y(0.64), X(0.405), Y(0.64), 1, rgb(30, 30, 34));
    strokeLine(X(0.14), Y(0.6), X(0.14), Y(0.68), 1, rgb(30, 30, 34));
    strokeLine(X(0.26), Y(0.6), X(0.26), Y(0.68), 1, rgb(30, 30, 34));
    // Draft marks + anchor + name plate near the bow.
    strokeLine(X(0.405), Y(0.63), X(0.425), Y(0.63), 1.2, rgb(220, 220, 225));
    strokeLine(X(0.4), Y(0.66), X(0.42), Y(0.66), 1.2, rgb(220, 220, 225));
    strokeLine(X(0.4), Y(0.69), X(0.418), Y(0.69), 1.2, rgb(220, 220, 225));
    fillCircle(X(0.395), Y(0.615), 1.6, rgb(30, 30, 34));
    fillRect(XR(0.37, 0.03), Y(0.605), w * 0.03, h * 0.012, rgb(220, 220, 225));
    strokeLine(X(0.378), Y(0.608), X(0.386), Y(0.608), 1, rgb(40, 40, 44));
    strokeLine(X(0.39), Y(0.608), X(0.396), Y(0.608), 1, rgb(40, 40, 44));
    // Shadow under the hull at the waterline.
    fillRect(XR(0.07, 0.37), Y(0.72), w * 0.37, h * 0.018, rgb(16, 40, 52));
    // Deck edge + railing posts.
    fillRect(XR(0.07, 0.315), Y(0.585), w * 0.315, h * 0.015, rgb(180, 180, 186));
    for (let i = 0; i < 6; i++) strokeLine(X(0.1 + i * 0.045), Y(0.585), X(0.1 + i * 0.045), Y(0.565), 1, rgb(120, 120, 126));
    // Superstructure with bridge wings, 2 window rows, radar on the roof.
    fillRect(XR(0.085, 0.075), Y(0.5), w * 0.075, h * 0.1, rgb(235, 232, 224));
    fillRect(XR(0.075, 0.012), Y(0.52), w * 0.012, h * 0.03, rgb(235, 232, 224)); // bridge wing
    fillRect(XR(0.148, 0.012), Y(0.52), w * 0.012, h * 0.03, rgb(235, 232, 224));
    for (let r = 0; r < 2; r++)
      for (let c = 0; c < 3; c++) fillRect(XR(0.095 + c * 0.02, 0.012), Y(0.525 + r * 0.03), w * 0.012, h * 0.02, rgb(40, 44, 52));
    strokeLine(X(0.122), Y(0.5), X(0.122), Y(0.465), 1.2, rgb(60, 60, 66)); // radar mast
    strokeLine(X(0.11), Y(0.47), X(0.134), Y(0.47), 1.2, rgb(60, 60, 66));
    fillCircle(X(0.122), Y(0.462), 1.2, rgb(255, 220, 120));
    fillCircle(X(0.075), Y(0.52), 1.2, rgb(255, 60, 50)); // wing nav light
    fillRect(XR(0.085, 0.075), Y(0.6), w * 0.075, h * 0.008, rgb(90, 90, 96)); // shadow at its base
    // Funnel with orange band + white mark.
    fillRect(XR(0.165, 0.035), Y(0.455), w * 0.035, h * 0.145, rgb(70, 70, 76));
    fillRect(XR(0.165, 0.035), Y(0.455), w * 0.035, h * 0.03, rgb(30, 30, 34));
    fillRect(XR(0.165, 0.035), Y(0.5), w * 0.035, h * 0.02, rgb(230, 120, 40));
    fillCircle(X(0.1825), Y(0.53), 1.4, rgb(235, 232, 224));
    // Mast with rigging + nav light.
    strokeLine(X(0.36), Y(0.6), X(0.36), Y(0.47), 1.6, rgb(40, 40, 44));
    strokeLine(X(0.345), Y(0.48), X(0.375), Y(0.48), 1.6, rgb(40, 40, 44));
    strokeLine(X(0.36), Y(0.47), X(0.435), Y(0.6), 1, rgb(90, 90, 96)); // rigging to bow
    strokeLine(X(0.36), Y(0.47), X(0.2), Y(0.585), 1, rgb(90, 90, 96)); // rigging to stern
    fillCircle(X(0.36), Y(0.465), 1.3, rgb(255, 60, 50));
    // Deck tanks with shading + connecting pipe; cargo hatches; vents.
    const tank = (tx: number) => {
      fillCircle(X(tx), Y(0.585), h * 0.02, rgb(140, 140, 146));
      fillCircle(X(tx) - 1, Y(0.585) - 1, h * 0.011, rgb(185, 185, 190));
      fillRect(X(tx) - w * 0.008, Y(0.585), w * 0.016, h * 0.012, rgb(110, 110, 116));
    };
    tank(0.205);
    tank(0.3);
    tank(0.335);
    strokeLine(X(0.205), Y(0.585), X(0.335), Y(0.585), 1.2, rgb(120, 120, 126));
    fillRect(XR(0.225, 0.035), Y(0.575), w * 0.035, h * 0.012, rgb(96, 96, 102)); // hatch
    fillRect(XR(0.315, 0.03), Y(0.575), w * 0.03, h * 0.012, rgb(96, 96, 102));
    strokeLine(X(0.24), Y(0.585), X(0.24), Y(0.56), 1.2, rgb(110, 110, 116)); // vent
    strokeLine(X(0.24), Y(0.56), X(0.252), Y(0.56), 1.2, rgb(110, 110, 116));
    // Lifeboat on davits beside the superstructure.
    strokeLine(X(0.075), Y(0.52), X(0.07), Y(0.5), 1.2, rgb(90, 90, 96));
    strokeLine(X(0.095), Y(0.52), X(0.09), Y(0.5), 1.2, rgb(90, 90, 96));
    fillRect(XR(0.062, 0.035), Y(0.5), w * 0.035, h * 0.02, rgb(230, 120, 40));
    fillCircle(X(0.062), Y(0.51), h * 0.01, rgb(230, 120, 40));
    fillCircle(X(0.097), Y(0.51), h * 0.01, rgb(230, 120, 40));
    // Fire + smoke rooted on the deck breach; warm glow on the hull.
    tongues(X(0.245), Y(0.585), h * 0.105);
    tongues(X(0.295), Y(0.585), h * 0.06);
    smokeStack(X(0.26), Y(0.38), h * 0.085);
    fillRect(XR(0.2, 0.09), Y(0.6), w * 0.09, h * 0.02, rgb(200, 90, 30)); // glow on hull
    fillRect(XR(0.148, 0.012), Y(0.5), w * 0.012, h * 0.1, rgb(230, 130, 50)); // glow on superstructure edge, fire side
    // Bow wave + foam at the waterline.
    fillPoly(
      [
        [X(0.43), Y(0.7)],
        [X(0.47), Y(0.72)],
        [X(0.43), Y(0.735)],
      ],
      rgb(220, 230, 235),
    );
    fillCircle(X(0.455), Y(0.745), 1.4, rgb(230, 238, 242));
    fillCircle(X(0.44), Y(0.755), 1.1, rgb(230, 238, 242));
    for (let i = 0; i < 4; i++) fillCircle(X(0.1 + i * 0.08), Y(0.735), 1.1, rgb(200, 220, 230));
  };
  tanker(false, 0);
  tanker(true, 0.04);
  // ---- Foreground: fire reflections, foam lines, wave texture.
  const fireRefl = (fx: number, fy: number) => {
    fillRect(x + w * (fx - 0.05), y + h * (fy + 0.02), w * 0.1, h * 0.02, rgb(255, 150, 50));
    fillRect(x + w * (fx - 0.035), y + h * (fy + 0.055), w * 0.07, h * 0.018, rgb(230, 110, 35));
    fillRect(x + w * (fx - 0.02), y + h * (fy + 0.09), w * 0.04, h * 0.016, rgb(200, 90, 30));
    fillRect(x + w * (fx - 0.012), y + h * (fy + 0.125), w * 0.024, h * 0.014, rgb(170, 70, 28));
  };
  fireRefl(0.245, 0.74);
  fireRefl(0.755, 0.78);
  strokeLine(x + w * 0.3, y + h * 0.8, x + w * 0.42, y + h * 0.8, 1.2, rgb(150, 190, 210));
  strokeLine(x + w * 0.48, y + h * 0.86, x + w * 0.58, y + h * 0.86, 1.2, rgb(150, 190, 210));
  strokeLine(x + w * 0.12, y + h * 0.9, x + w * 0.24, y + h * 0.9, 1.2, rgb(150, 190, 210));
  strokeLine(x + w * 0.62, y + h * 0.93, x + w * 0.74, y + h * 0.93, 1.2, rgb(120, 160, 190));
  strokeLine(x + w * 0.05, y + h * 0.97, x + w * 0.2, y + h * 0.97, 1.2, rgb(100, 140, 170));
  fillCircle(x + w * 0.5, y + h * 0.9, 1.2, rgb(200, 220, 230));
  fillCircle(x + w * 0.85, y + h * 0.88, 1.2, rgb(200, 220, 230));
  fillCircle(x + w * 0.33, y + h * 0.95, 1.1, rgb(190, 210, 222));
  // Birds.
  strokeLine(x + w * 0.3, y + h * 0.14, x + w * 0.33, y + h * 0.12, 1.2, rgb(60, 50, 44));
  strokeLine(x + w * 0.33, y + h * 0.12, x + w * 0.36, y + h * 0.14, 1.2, rgb(60, 50, 44));
  strokeLine(x + w * 0.62, y + h * 0.1, x + w * 0.65, y + h * 0.08, 1.2, rgb(60, 50, 44));
  strokeLine(x + w * 0.65, y + h * 0.08, x + w * 0.68, y + h * 0.1, 1.2, rgb(60, 50, 44));
  strokeLine(x + w * 0.42, y + h * 0.06, x + w * 0.44, y + h * 0.045, 1.1, rgb(60, 50, 44));
  strokeLine(x + w * 0.44, y + h * 0.045, x + w * 0.46, y + h * 0.06, 1.1, rgb(60, 50, 44));
}

// Scene 3: Vegas GP — night race, neon skyline, two F1 cars.
function sceneVegas(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(16, 14, 40), rgb(58, 30, 90));
  // Neon skyline.
  const cols: [number, number, number][] = [rgb(255, 60, 140), rgb(60, 200, 255), rgb(255, 200, 60), rgb(120, 255, 150)];
  for (let i = 0; i < 7; i++) {
    const bx = x + w * (0.03 + i * 0.135);
    const bh = h * (0.2 + ((i * 37) % 20) / 100);
    fillRect(bx, y + h * 0.42 - bh, w * 0.09, bh, rgb(30, 26, 60));
    fillRect(bx, y + h * 0.42 - bh, w * 0.09, h * 0.03, cols[i % 4]);
    for (let k = 0; k < 4; k++) fillRect(bx + w * 0.015 + k * w * 0.02, y + h * 0.42 - bh + h * 0.07, w * 0.008, h * 0.05, rgb(255, 230, 120));
  }
  // Track.
  fillRect(x, y + h * 0.62, w, h * 0.38, rgb(38, 38, 44));
  strokeLine(x, y + h * 0.7, x + w, y + h * 0.66, 2, rgb(230, 230, 230));
  strokeLine(x, y + h * 0.9, x + w, y + h * 0.94, 2, rgb(230, 230, 230));
  // F1 car helper.
  const car = (cx: number, cy: number, body: [number, number, number], s: number) => {
    fillRect(cx - s * 0.5, cy - s * 0.14, s, s * 0.28, body);
    fillPoly(
      [
        [cx + s * 0.1, cy - s * 0.3],
        [cx + s * 0.42, cy - s * 0.12],
        [cx + s * 0.42, cy + s * 0.12],
        [cx + s * 0.1, cy + s * 0.28],
      ],
      rgb(20, 20, 26),
    );
    fillRect(cx - s * 0.62, cy - s * 0.3, s * 0.14, s * 0.6, rgb(20, 20, 26));
    fillCircle(cx - s * 0.28, cy - s * 0.22, s * 0.16, rgb(12, 12, 14));
    fillCircle(cx + s * 0.3, cy + s * 0.22, s * 0.16, rgb(12, 12, 14));
    fillCircle(cx - s * 0.28, cy + s * 0.22, s * 0.16, rgb(12, 12, 14));
    fillCircle(cx + s * 0.3, cy - s * 0.22, s * 0.16, rgb(12, 12, 14));
  };
  car(x + w * 0.3, y + h * 0.76, rgb(20, 90, 200), h * 0.3);
  car(x + w * 0.68, y + h * 0.86, rgb(220, 50, 40), h * 0.26);
  // Light trails behind the cars.
  strokeLine(x + w * 0.02, y + h * 0.74, x + w * 0.2, y + h * 0.75, 2, rgb(120, 160, 255));
  strokeLine(x + w * 0.4, y + h * 0.84, x + w * 0.58, y + h * 0.85, 2, rgb(255, 120, 100));
  // Checkered start line on the track.
  for (let i = 0; i < 6; i++) fillRect(x + w * (0.46 + i * 0.012), y + h * 0.62, w * 0.012, h * 0.03, i % 2 ? rgb(20, 20, 20) : WHITE);
  // Crowd dots along the far side of the track.
  for (let i = 0; i < 16; i++) fillCircle(x + w * (0.04 + i * 0.06), y + h * 0.6, 1.8, i % 3 ? rgb(230, 220, 200) : rgb(255, 200, 90));
  // Neon signs on two buildings.
  fillRect(x + w * 0.05, y + h * 0.3, w * 0.06, h * 0.05, rgb(255, 60, 140));
  fillRect(x + w * 0.72, y + h * 0.26, w * 0.07, h * 0.05, rgb(60, 220, 255));
  // Checkered flag.
  fillRect(x + w * 0.88, y + h * 0.5, w * 0.09, h * 0.07, WHITE);
  fillRect(x + w * 0.88, y + h * 0.5, w * 0.045, h * 0.035, rgb(20, 20, 20));
  fillRect(x + w * 0.925, y + h * 0.535, w * 0.045, h * 0.035, rgb(20, 20, 20));
  strokeLine(x + w * 0.88, y + h * 0.5, x + w * 0.88, y + h * 0.62, 1.6, rgb(60, 56, 50));
}

// Scene 4: Democrats — Capitol dome, blue wave, big 258.
function sceneDemocrats(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(190, 215, 235), rgb(235, 240, 245));
  // Capitol building.
  fillRect(x + w * 0.08, y + h * 0.55, w * 0.84, h * 0.2, rgb(235, 232, 225));
  fillRect(x + w * 0.3, y + h * 0.42, w * 0.4, h * 0.14, rgb(235, 232, 225));
  fillCircle(x + w * 0.5, y + h * 0.42, h * 0.13, rgb(240, 238, 232));
  fillRect(x + w * 0.485, y + h * 0.2, w * 0.03, h * 0.1, rgb(240, 238, 232));
  fillCircle(x + w * 0.5, y + h * 0.2, h * 0.02, rgb(42, 93, 176));
  for (let i = 0; i < 6; i++) fillRect(x + w * (0.16 + i * 0.12), y + h * 0.58, w * 0.05, h * 0.14, rgb(200, 196, 188));
  // Flags on the Capitol wings + stars in the sky.
  flagPole(x + w * 0.2, y + h * 0.44, h * 0.14, rgb(42, 93, 176));
  flagPole(x + w * 0.8, y + h * 0.44, h * 0.14, rgb(176, 30, 36));
  for (let i = 0; i < 8; i++) fillCircle(x + w * ((i * 61) % 100) / 100, y + h * ((i * 17) % 20) / 100, 0.9, rgb(255, 240, 180));
  // Blue wave of seats.
  fillPoly(
    [
      [x, y + h],
      [x, y + h * 0.82],
      [x + w * 0.3, y + h * 0.72],
      [x + w * 0.62, y + h * 0.78],
      [x + w, y + h * 0.66],
      [x + w, y + h],
    ],
    rgb(42, 93, 176),
  );
  drawText('258', x + w * 0.5, y + h * 0.9, Math.round(h * 0.32), F_SANS_B, WHITE, 'c');
}

// Scene 5: Bahrain strike — night sky, missile trails, base, fire.
function sceneBahrain(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(12, 16, 34), rgb(48, 52, 84));
  for (let i = 0; i < 14; i++) fillCircle(x + w * ((i * 67) % 100) / 100, y + h * ((i * 31) % 40) / 100, 1.1, WHITE);
  // Missile trails arcing down.
  strokeLine(x + w * 0.2, y + h * 0.06, x + w * 0.38, y + h * 0.55, 2, rgb(255, 190, 90));
  strokeLine(x + w * 0.55, y + h * 0.04, x + w * 0.62, y + h * 0.5, 2, rgb(255, 190, 90));
  strokeLine(x + w * 0.85, y + h * 0.1, x + w * 0.78, y + h * 0.55, 2, rgb(255, 190, 90));
  fillCircle(x + w * 0.2, y + h * 0.06, 2.5, rgb(255, 220, 150));
  fillCircle(x + w * 0.55, y + h * 0.04, 2.5, rgb(255, 220, 150));
  // Base buildings.
  fillRect(x + w * 0.05, y + h * 0.62, w * 0.24, h * 0.2, rgb(70, 72, 84));
  fillRect(x + w * 0.36, y + h * 0.66, w * 0.28, h * 0.16, rgb(70, 72, 84));
  fillRect(x + w * 0.7, y + h * 0.6, w * 0.25, h * 0.22, rgb(70, 72, 84));
  // Lit windows on the base.
  for (let i = 0; i < 5; i++) fillRect(x + w * (0.09 + i * 0.17), y + h * 0.68, w * 0.03, h * 0.05, rgb(255, 210, 110));
  // Fourth missile trail, thinner + explosion glow.
  strokeLine(x + w * 0.38, y + h * 0.1, x + w * 0.46, y + h * 0.52, 1.4, rgb(255, 190, 90));
  fillCircle(x + w * 0.5, y + h * 0.62, h * 0.2, rgb(255, 140, 40));
  fillCircle(x + w * 0.82, y + h * 0.58, h * 0.16, rgb(255, 140, 40));
  // Fire and smoke at the plant.
  flame(x + w * 0.5, y + h * 0.62, h * 0.12);
  flame(x + w * 0.82, y + h * 0.58, h * 0.09);
  smoke(x + w * 0.5, y + h * 0.42, h * 0.09, rgb(60, 60, 66));
  smoke(x + w * 0.82, y + h * 0.42, h * 0.08, rgb(60, 60, 66));
  fillRect(x, y + h * 0.82, w, h * 0.18, rgb(24, 26, 36));
}

// Scene 6: Riyadh intercepts — dusk sky, layered skyline, interceptor arcs meeting a burst.
function sceneRiyadh(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(30, 44, 80), rgb(226, 156, 92));
  // Far skyline in haze.
  fillRect(x + w * 0.1, y + h * 0.62, w * 0.1, h * 0.22, rgb(112, 102, 126));
  fillRect(x + w * 0.44, y + h * 0.58, w * 0.12, h * 0.26, rgb(112, 102, 126));
  fillRect(x + w * 0.68, y + h * 0.64, w * 0.1, h * 0.2, rgb(112, 102, 126));
  // Near skyline.
  fillRect(x + w * 0.04, y + h * 0.6, w * 0.12, h * 0.24, rgb(58, 60, 76));
  fillRect(x + w * 0.2, y + h * 0.5, w * 0.1, h * 0.34, rgb(58, 60, 76));
  fillRect(x + w * 0.34, y + h * 0.66, w * 0.16, h * 0.18, rgb(58, 60, 76));
  fillRect(x + w * 0.56, y + h * 0.55, w * 0.12, h * 0.29, rgb(58, 60, 76));
  fillRect(x + w * 0.74, y + h * 0.62, w * 0.2, h * 0.22, rgb(58, 60, 76));
  // Kingdom Centre tower with its lit arch opening (tall, centre-right).
  fillRect(x + w * 0.6, y + h * 0.28, w * 0.07, h * 0.56, rgb(58, 60, 76));
  fillPoly(
    [
      [x + w * 0.605, y + h * 0.3],
      [x + w * 0.635, y + h * 0.52],
      [x + w * 0.665, y + h * 0.3],
    ],
    rgb(255, 190, 100),
  );
  fillPoly(
    [
      [x + w * 0.62, y + h * 0.34],
      [x + w * 0.635, y + h * 0.48],
      [x + w * 0.65, y + h * 0.34],
    ],
    rgb(52, 58, 84),
  );
  // Lit windows in the near skyline.
  for (let i = 0; i < 10; i++) fillRect(x + w * (0.06 + ((i * 37) % 80) / 100), y + h * (0.56 + ((i * 23) % 20) / 100), w * 0.02, h * 0.03, rgb(255, 220, 130));
  // Crescent moon with halo.
  fillCircle(x + w * 0.86, y + h * 0.12, h * 0.09, rgb(240, 220, 170));
  fillCircle(x + w * 0.86, y + h * 0.12, h * 0.05, rgb(240, 230, 190));
  fillCircle(x + w * 0.875, y + h * 0.115, h * 0.045, rgb(53, 57, 81));
  // Searchlight beams with bright cores.
  strokeLine(x + w * 0.24, y + h * 0.84, x + w * 0.4, y + h * 0.4, 2.6, rgb(200, 210, 225));
  strokeLine(x + w * 0.24, y + h * 0.84, x + w * 0.4, y + h * 0.4, 1.2, rgb(240, 244, 250));
  strokeLine(x + w * 0.72, y + h * 0.84, x + w * 0.58, y + h * 0.42, 2.6, rgb(200, 210, 225));
  strokeLine(x + w * 0.72, y + h * 0.84, x + w * 0.58, y + h * 0.42, 1.2, rgb(240, 244, 250));
  // Interceptor arcs: smooth curves drawn as short segments.
  const arc = (x0: number, y0: number, x1: number, y1: number, cx: number, cy: number, wd: number, c: [number, number, number]) => {
    let px = x0;
    let py = y0;
    for (let t = 0.1; t <= 1.001; t += 0.1) {
      const qx = (1 - t) * (1 - t) * x0 + 2 * (1 - t) * t * cx + t * t * x1;
      const qy = (1 - t) * (1 - t) * y0 + 2 * (1 - t) * t * cy + t * t * y1;
      strokeLine(px, py, qx, qy, wd, c);
      px = qx;
      py = qy;
    }
  };
  // Faint echo arcs for motion, just behind the bright ones.
  arc(x + w * 0.1, y + h * 0.82, x + w * 0.52, y + h * 0.34, x + w * 0.22, y + h * 0.34, 1, rgb(255, 220, 130));
  arc(x + w * 0.92, y + h * 0.84, x + w * 0.52, y + h * 0.34, x + w * 0.82, y + h * 0.38, 1, rgb(255, 220, 130));
  arc(x + w * 0.1, y + h * 0.78, x + w * 0.52, y + h * 0.3, x + w * 0.22, y + h * 0.3, 1.8, rgb(255, 230, 140));
  arc(x + w * 0.92, y + h * 0.8, x + w * 0.52, y + h * 0.3, x + w * 0.82, y + h * 0.34, 1.8, rgb(255, 230, 140));
  arc(x + w * 0.5, y + h * 0.84, x + w * 0.52, y + h * 0.3, x + w * 0.5, y + h * 0.5, 1.8, rgb(255, 230, 140));
  // Intercept burst: irregular asymmetric explosion — flame tongues + smoke, NO radial rays (rays read as a second sun).
  flameTongues(x + w * 0.52, y + h * 0.34, h * 0.2);
  flameTongues(x + w * 0.46, y + h * 0.36, h * 0.13);
  flameTongues(x + w * 0.58, y + h * 0.36, h * 0.11);
  fillCircle(x + w * 0.5, y + h * 0.14, h * 0.07, rgb(70, 62, 74)); // asymmetric smoke mass above
  fillCircle(x + w * 0.56, y + h * 0.1, h * 0.055, rgb(90, 80, 90));
  fillCircle(x + w * 0.45, y + h * 0.12, h * 0.05, rgb(80, 72, 82));
  fillCircle(x + w * 0.52, y + h * 0.16, h * 0.045, rgb(50, 44, 54));
  fillCircle(x + w * 0.48, y + h * 0.44, 1.4, rgb(255, 200, 90)); // falling debris
  fillCircle(x + w * 0.56, y + h * 0.48, 1.2, rgb(255, 180, 70));
  fillCircle(x + w * 0.53, y + h * 0.54, 1, rgb(230, 150, 60));
  fillCircle(x + w * 0.44, y + h * 0.5, 1.1, rgb(255, 170, 60));
  fillCircle(x + w * 0.6, y + h * 0.52, 1, rgb(255, 190, 90));
  // Ground band with city lights.
  fillRect(x, y + h * 0.84, w, h * 0.16, rgb(40, 44, 56));
  for (let i = 0; i < 8; i++) fillCircle(x + w * (0.05 + i * 0.12), y + h * 0.88, 1.2, rgb(255, 210, 110));
  strokeLine(x + w * 0.05, y + h * 0.94, x + w * 0.95, y + h * 0.94, 1, rgb(255, 200, 120));
}

// Scene 7: Sinaloa capture — mountains, helicopter, house, soldiers.
function sceneSinaloa(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(210, 180, 130), rgb(240, 220, 170));
  fillPoly(
    [
      [x, y + h * 0.6],
      [x + w * 0.25, y + h * 0.25],
      [x + w * 0.45, y + h * 0.6],
    ],
    rgb(110, 130, 80),
  );
  fillPoly(
    [
      [x + w * 0.35, y + h * 0.6],
      [x + w * 0.65, y + h * 0.15],
      [x + w * 0.95, y + h * 0.6],
    ],
    rgb(90, 110, 66),
  );
  fillPoly(
    [
      [x + w * 0.2, y + h * 0.32],
      [x + w * 0.25, y + h * 0.25],
      [x + w * 0.3, y + h * 0.32],
    ],
    WHITE,
  );
  // Helicopter.
  fillCircle(x + w * 0.68, y + h * 0.22, h * 0.07, rgb(50, 56, 62));
  fillRect(x + w * 0.68, y + h * 0.2, w * 0.16, h * 0.05, rgb(50, 56, 62));
  strokeLine(x + w * 0.52, y + h * 0.16, x + w * 0.86, y + h * 0.16, 2, rgb(50, 56, 62));
  // Searchlight beam from the helicopter + dust at the raid.
  fillPoly(
    [
      [x + w * 0.66, y + h * 0.26],
      [x + w * 0.7, y + h * 0.26],
      [x + w * 0.78, y + h * 0.6],
      [x + w * 0.62, y + h * 0.6],
    ],
    rgb(240, 230, 180),
  );
  fillCircle(x + w * 0.56, y + h * 0.74, h * 0.08, rgb(200, 180, 130));
  fillCircle(x + w * 0.66, y + h * 0.78, h * 0.07, rgb(200, 180, 130));
  // Second mountain ridge behind + cactus.
  fillPoly(
    [
      [x, y + h * 0.5],
      [x + w * 0.2, y + h * 0.3],
      [x + w * 0.42, y + h * 0.5],
    ],
    rgb(140, 155, 105),
  );
  fillRect(x + w * 0.9, y + h * 0.62, w * 0.02, h * 0.12, rgb(60, 110, 60));
  fillRect(x + w * 0.88, y + h * 0.66, w * 0.02, h * 0.05, rgb(60, 110, 60));
  // House and soldiers.
  fillRect(x + w * 0.08, y + h * 0.62, w * 0.26, h * 0.2, rgb(180, 140, 100));
  fillPoly(
    [
      [x + w * 0.06, y + h * 0.62],
      [x + w * 0.21, y + h * 0.5],
      [x + w * 0.36, y + h * 0.62],
    ],
    rgb(150, 60, 50),
  );
  fillRect(x + w * 0.44, y + h * 0.68, w * 0.5, h * 0.14, rgb(140, 120, 80));
  person(x + w * 0.5, y + h * 0.82, h * 0.22, rgb(70, 90, 60));
  person(x + w * 0.64, y + h * 0.82, h * 0.22, rgb(70, 90, 60));
  person(x + w * 0.78, y + h * 0.82, h * 0.22, rgb(70, 90, 60));
  fillRect(x, y + h * 0.82, w, h * 0.18, rgb(120, 105, 70));
}

// Scene 8: Kyiv apartment strike — night block, smoke, fire glow.
function sceneKyiv(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(20, 26, 44), rgb(60, 70, 100));
  for (let i = 0; i < 10; i++) fillCircle(x + w * ((i * 53) % 100) / 100, y + h * ((i * 29) % 35) / 100, 1, WHITE);
  // Apartment blocks.
  fillRect(x + w * 0.06, y + h * 0.3, w * 0.24, h * 0.52, rgb(70, 74, 88));
  fillRect(x + w * 0.36, y + h * 0.22, w * 0.28, h * 0.6, rgb(84, 88, 102));
  fillRect(x + w * 0.7, y + h * 0.34, w * 0.24, h * 0.48, rgb(70, 74, 88));
  for (let r = 0; r < 4; r++) {
    for (let c = 0; c < 3; c++) {
      const lit = (r * 3 + c) % 3 === 0;
      fillRect(x + w * (0.4 + c * 0.08), y + h * (0.28 + r * 0.12), w * 0.04, h * 0.06, lit ? rgb(255, 210, 110) : rgb(40, 44, 58));
    }
  }
  // Damage and fire on the middle block.
  fillPoly(
    [
      [x + w * 0.36, y + h * 0.4],
      [x + w * 0.5, y + h * 0.3],
      [x + w * 0.64, y + h * 0.42],
      [x + w * 0.55, y + h * 0.5],
      [x + w * 0.42, y + h * 0.48],
    ],
    rgb(30, 30, 36),
  );
  flame(x + w * 0.5, y + h * 0.44, h * 0.09);
  smoke(x + w * 0.5, y + h * 0.24, h * 0.1, rgb(80, 80, 88));
  // Second smoke layer + moon + ground debris.
  smoke(x + w * 0.62, y + h * 0.18, h * 0.08, rgb(90, 90, 98));
  fillCircle(x + w * 0.86, y + h * 0.12, h * 0.045, rgb(235, 230, 210));
  fillRect(x + w * 0.12, y + h * 0.8, w * 0.06, h * 0.02, rgb(20, 22, 30));
  fillRect(x + w * 0.68, y + h * 0.79, w * 0.05, h * 0.02, rgb(20, 22, 30));
  fillRect(x, y + h * 0.82, w, h * 0.18, rgb(28, 30, 40));
}

// Scene 9: Benghazi ship — dawn harbour, warship, drone, explosion.
function sceneBenghazi(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(44, 54, 96), rgb(205, 125, 105));
  for (let i = 0; i < 10; i++) fillCircle(x + w * ((i * 41) % 100) / 100, y + h * ((i * 23) % 30) / 100, 1, WHITE);
  // Dawn band + moon with halo.
  fillRect(x, y + h * 0.52, w, h * 0.08, rgb(205, 130, 105));
  fillCircle(x + w * 0.88, y + h * 0.12, h * 0.09, rgb(230, 225, 200));
  fillCircle(x + w * 0.88, y + h * 0.12, h * 0.05, rgb(235, 230, 210));
  // Harbour water: dark gradient + moon path.
  for (let i = 0; i < 5; i++) {
    const t = i / 4;
    fillRect(x, y + h * (0.6 + (0.4 * i) / 5), w, (h * 0.4) / 5 + 0.6, [Math.round(40 - 14 * t), Math.round(74 - 30 * t), Math.round(106 - 44 * t)]);
  }
  for (let i = 0; i < 4; i++) fillRect(x + w * (0.865 + ((i * 5) % 2) * 0.008), y + h * (0.64 + i * 0.08), w * 0.03, h * 0.02, rgb(220, 215, 190));
  // Pier with bollards, crates, crane.
  fillRect(x, y + h * 0.58, w * 0.3, h * 0.06, rgb(90, 88, 84));
  for (let i = 0; i < 3; i++) fillRect(x + w * (0.04 + i * 0.09), y + h * 0.555, w * 0.02, h * 0.025, rgb(60, 58, 54));
  fillRect(x + w * 0.1, y + h * 0.52, w * 0.04, h * 0.06, rgb(120, 110, 95)); // crate
  fillRect(x + w * 0.15, y + h * 0.54, w * 0.03, h * 0.04, rgb(100, 92, 80));
  strokeLine(x + w * 0.24, y + h * 0.58, x + w * 0.24, y + h * 0.38, 1.6, rgb(70, 68, 64)); // crane mast
  strokeLine(x + w * 0.24, y + h * 0.38, x + w * 0.3, y + h * 0.44, 1.4, rgb(70, 68, 64)); // crane jib
  strokeLine(x + w * 0.3, y + h * 0.44, x + w * 0.3, y + h * 0.5, 1, rgb(70, 68, 64)); // hook line
  // Warship with turret, bridge windows, radar, pennant.
  fillRect(x + w * 0.3, y + h * 0.62, w * 0.5, h * 0.1, rgb(104, 112, 124));
  strokeLine(x + w * 0.32, y + h * 0.67, x + w * 0.78, y + h * 0.67, 1, rgb(48, 52, 60)); // hull plating line
  fillPoly(
    [
      [x + w * 0.8, y + h * 0.62],
      [x + w * 0.92, y + h * 0.66],
      [x + w * 0.8, y + h * 0.72],
    ],
    rgb(104, 112, 124),
  );
  fillRect(x + w * 0.36, y + h * 0.58, w * 0.09, h * 0.04, rgb(122, 130, 142)); // gun turret
  strokeLine(x + w * 0.45, y + h * 0.6, x + w * 0.52, y + h * 0.6, 1.6, rgb(122, 130, 142)); // barrel
  fillRect(x + w * 0.42, y + h * 0.52, w * 0.14, h * 0.1, rgb(122, 130, 142)); // bridge
  fillRect(x + w * 0.44, y + h * 0.54, w * 0.02, h * 0.03, rgb(255, 220, 130)); // lit bridge windows
  fillRect(x + w * 0.48, y + h * 0.54, w * 0.02, h * 0.03, rgb(255, 220, 130));
  strokeLine(x + w * 0.48, y + h * 0.52, x + w * 0.48, y + h * 0.4, 2, rgb(122, 130, 142));
  strokeLine(x + w * 0.44, y + h * 0.42, x + w * 0.52, y + h * 0.42, 1.4, rgb(122, 130, 142)); // radar bar
  fillCircle(x + w * 0.48, y + h * 0.39, 1.2, rgb(255, 80, 60)); // radar light
  fillPoly(
    [
      [x + w * 0.48, y + h * 0.4],
      [x + w * 0.505, y + h * 0.415],
      [x + w * 0.48, y + h * 0.43],
    ],
    rgb(176, 30, 36),
  ); // pennant
  fillRect(x + w * 0.82, y + h * 0.64, w * 0.025, h * 0.012, rgb(220, 220, 225)); // hull number plate
  fillCircle(x + w * 0.9, y + h * 0.68, 1.2, rgb(40, 44, 52)); // anchor
  // Quadcopter drone above — bigger, with a thin motion trail.
  strokeLine(x + w * 0.36, y + h * 0.26, x + w * 0.46, y + h * 0.235, 1, rgb(165, 175, 190));
  quadcopter(x + w * 0.55, y + h * 0.22, h * 0.11);
  // Explosion on deck: bigger flame tongues + debris + layered smoke.
  flameTongues(x + w * 0.55, y + h * 0.62, h * 0.17);
  fillCircle(x + w * 0.55, y + h * 0.4, 1.4, rgb(255, 160, 60)); // debris
  fillCircle(x + w * 0.6, y + h * 0.46, 1.2, rgb(255, 190, 80));
  fillCircle(x + w * 0.5, y + h * 0.5, 1, rgb(255, 140, 40));
  fillCircle(x + w * 0.55, y + h * 0.3, h * 0.1, rgb(60, 60, 66)); // smoke column
  fillCircle(x + w * 0.6, y + h * 0.26, h * 0.08, rgb(60, 60, 66));
  fillCircle(x + w * 0.51, y + h * 0.24, h * 0.07, rgb(80, 80, 86));
  fillCircle(x + w * 0.55, y + h * 0.28, h * 0.05, rgb(52, 52, 56));
  // Fire glow on the hull + water.
  fillRect(x + w * 0.4, y + h * 0.62, w * 0.3, h * 0.02, rgb(235, 125, 45));
  fillRect(x + w * 0.48, y + h * 0.74, w * 0.14, h * 0.02, rgb(255, 150, 50));
  fillRect(x + w * 0.51, y + h * 0.78, w * 0.08, h * 0.018, rgb(230, 110, 35));
  fillRect(x + w * 0.53, y + h * 0.82, w * 0.04, h * 0.016, rgb(200, 90, 30));
  // Harbour lights, wave lines, second smoke puff.
  for (let i = 0; i < 6; i++) fillCircle(x + w * (0.04 + i * 0.05), y + h * 0.56, 1.2, rgb(255, 210, 110));
  strokeLine(x + w * 0.12, y + h * 0.8, x + w * 0.24, y + h * 0.8, 1.2, rgb(120, 160, 190));
  strokeLine(x + w * 0.7, y + h * 0.86, x + w * 0.84, y + h * 0.86, 1.2, rgb(120, 160, 190));
  fillCircle(x + w * 0.68, y + h * 0.34, h * 0.07, rgb(70, 70, 76));
  fillCircle(x + w * 0.72, y + h * 0.3, h * 0.05, rgb(90, 90, 96));
}

// Scene 10: Cikande factory fire — factory, big flames, smoke columns.
function sceneCikande(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(60, 30, 24), rgb(140, 70, 40));
  // Factory building.
  fillRect(x + w * 0.06, y + h * 0.55, w * 0.6, h * 0.27, rgb(150, 140, 125));
  fillPoly(
    [
      [x + w * 0.06, y + h * 0.55],
      [x + w * 0.16, y + h * 0.42],
      [x + w * 0.26, y + h * 0.55],
    ],
    rgb(120, 110, 100),
  );
  fillPoly(
    [
      [x + w * 0.26, y + h * 0.55],
      [x + w * 0.36, y + h * 0.42],
      [x + w * 0.46, y + h * 0.55],
    ],
    rgb(120, 110, 100),
  );
  for (let i = 0; i < 4; i++) fillRect(x + w * (0.12 + i * 0.13), y + h * 0.62, w * 0.06, h * 0.1, rgb(60, 56, 52));
  // Chimney.
  fillRect(x + w * 0.72, y + h * 0.3, w * 0.08, h * 0.52, rgb(130, 120, 110));
  fillRect(x + w * 0.7, y + h * 0.27, w * 0.12, h * 0.04, rgb(110, 100, 92));
  // Flames through the roof and smoke.
  flame(x + w * 0.2, y + h * 0.5, h * 0.13);
  flame(x + w * 0.45, y + h * 0.52, h * 0.11);
  smoke(x + w * 0.2, y + h * 0.28, h * 0.11, rgb(50, 46, 44));
  smoke(x + w * 0.48, y + h * 0.3, h * 0.1, rgb(50, 46, 44));
  smoke(x + w * 0.76, y + h * 0.14, h * 0.09, rgb(60, 56, 52));
  fillRect(x, y + h * 0.82, w, h * 0.18, rgb(40, 32, 28));
  // Rising embers + lit windows + small fire truck.
  for (let i = 0; i < 7; i++) fillCircle(x + w * (0.18 + ((i * 41) % 40) / 100), y + h * (0.2 + ((i * 19) % 18) / 100), 1.4, rgb(255, 160, 60));
  for (let i = 0; i < 3; i++) fillRect(x + w * (0.5 + i * 0.04), y + h * 0.64, w * 0.02, h * 0.05, rgb(255, 210, 110));
  fillRect(x + w * 0.84, y + h * 0.74, w * 0.12, h * 0.08, rgb(200, 40, 35));
  fillCircle(x + w * 0.87, y + h * 0.82, h * 0.03, rgb(20, 20, 22));
  fillCircle(x + w * 0.93, y + h * 0.82, h * 0.03, rgb(20, 20, 22));
}

// Scene 11: Bitcoin — chart plunging then recovering, big coin.
function sceneBitcoin(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(24, 28, 40), rgb(48, 58, 80));
  // Grid.
  for (let i = 1; i < 4; i++) strokeLine(x + w * 0.06, y + (h * i) / 4, x + w * 0.94, y + (h * i) / 4, 0.8, rgb(70, 80, 100));
  // Chart: fall then recovery.
  const pts: [number, number][] = [
    [0.06, 0.3],
    [0.18, 0.34],
    [0.3, 0.42],
    [0.42, 0.62],
    [0.52, 0.72],
    [0.62, 0.66],
    [0.74, 0.5],
    [0.86, 0.42],
    [0.94, 0.4],
  ];
  for (let i = 0; i + 1 < pts.length; i++) {
    const [ax, ay] = pts[i];
    const [bx, by] = pts[i + 1];
    strokeLine(x + w * ax, y + h * ay, x + w * bx, y + h * by, 2.4, i < 4 ? rgb(230, 80, 70) : rgb(90, 200, 120));
  }
  // Down arrow at the dip, up arrow at the close.
  fillPoly(
    [
      [x + w * 0.52, y + h * 0.78],
      [x + w * 0.47, y + h * 0.7],
      [x + w * 0.57, y + h * 0.7],
    ],
    rgb(230, 80, 70),
  );
  // Candlesticks along the bottom, behind the chart line.
  for (let i = 0; i < 9; i++) {
    const cx0 = x + w * (0.08 + i * 0.1);
    const up = (i * 7) % 3 !== 0;
    fillRect(cx0, y + h * (up ? 0.8 : 0.76), w * 0.035, h * (up ? 0.1 : 0.14), up ? rgb(90, 200, 120) : rgb(230, 80, 70));
    strokeLine(cx0 + w * 0.017, y + h * (up ? 0.76 : 0.72), cx0 + w * 0.017, y + h * (up ? 0.94 : 0.94), 1, up ? rgb(90, 200, 120) : rgb(230, 80, 70));
  }
  // Big coin.
  fillCircle(x + w * 0.76, y + h * 0.3, h * 0.2, rgb(247, 147, 26));
  fillCircle(x + w * 0.76, y + h * 0.3, h * 0.16, rgb(255, 170, 60));
  drawText('B', x + w * 0.76, y + h * 0.42, Math.round(h * 0.24), F_SANS_B, rgb(120, 60, 0), 'c');
  // Price labels on dark chips so the candlesticks never camouflage them.
  const pSize = Math.max(8, Math.round(h * 0.13));
  const w58 = textWidth('$58,900', pSize, F_SANS_B);
  fillRect(x + w * 0.2 - 2, y + h * 0.92 - pSize - 1, w58 + 4, pSize + 3, rgb(24, 28, 40));
  drawText('$58,900', x + w * 0.2, y + h * 0.92, pSize, F_SANS_B, rgb(230, 120, 110), 'l');
  const w61 = textWidth('$61,271', pSize, F_SANS_B);
  fillRect(x + w * 0.8 - w61 - 2, y + h * 0.92 - pSize - 1, w61 + 4, pSize + 3, rgb(24, 28, 40));
  drawText('$61,271', x + w * 0.8, y + h * 0.92, pSize, F_SANS_B, rgb(140, 220, 160), 'r');
}

// Scene 12: Sudan drones — dusty city, UN building, drone, explosion.
function sceneSudan(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(235, 200, 140), rgb(208, 148, 92));
  // Dust haze bands.
  fillRect(x, y + h * 0.22, w, h * 0.05, rgb(240, 212, 160));
  fillRect(x, y + h * 0.38, w, h * 0.04, rgb(232, 198, 145));
  // Far skyline in haze.
  fillRect(x + w * 0.08, y + h * 0.46, w * 0.12, h * 0.36, rgb(182, 156, 116));
  fillRect(x + w * 0.5, y + h * 0.42, w * 0.14, h * 0.4, rgb(182, 156, 116));
  fillRect(x + w * 0.74, y + h * 0.48, w * 0.12, h * 0.34, rgb(182, 156, 116));
  // Near skyline with dark windows.
  fillRect(x + w * 0.04, y + h * 0.5, w * 0.14, h * 0.32, rgb(140, 112, 78));
  fillRect(x + w * 0.22, y + h * 0.4, w * 0.16, h * 0.42, rgb(140, 112, 78));
  fillRect(x + w * 0.42, y + h * 0.55, w * 0.18, h * 0.27, rgb(140, 112, 78));
  fillRect(x + w * 0.64, y + h * 0.44, w * 0.14, h * 0.38, rgb(140, 112, 78));
  fillRect(x + w * 0.82, y + h * 0.58, w * 0.14, h * 0.24, rgb(140, 112, 78));
  for (let i = 0; i < 6; i++) fillRect(x + w * (0.07 + ((i * 29) % 80) / 100), y + h * (0.5 + ((i * 17) % 18) / 100), w * 0.018, h * 0.035, rgb(90, 70, 48));
  // Minaret silhouette.
  fillRect(x + w * 0.92, y + h * 0.3, w * 0.03, h * 0.52, rgb(140, 112, 78));
  fillPoly(
    [
      [x + w * 0.915, y + h * 0.3],
      [x + w * 0.935, y + h * 0.18],
      [x + w * 0.955, y + h * 0.3],
    ],
    rgb(140, 112, 78),
  );
  // UN building (white, centre) with blue flag + shaded side.
  fillRect(x + w * 0.3, y + h * 0.58, w * 0.4, h * 0.24, rgb(240, 238, 230));
  fillRect(x + w * 0.64, y + h * 0.58, w * 0.06, h * 0.24, rgb(210, 206, 196));
  for (let r = 0; r < 2; r++)
    for (let i = 0; i < 5; i++) fillRect(x + w * (0.33 + i * 0.07), y + h * (0.62 + r * 0.07), w * 0.04, h * 0.05, rgb(90, 110, 150));
  fillCircle(x + w * 0.5, y + h * 0.66, 1.4, rgb(40, 90, 180)); // emblem dot
  // Drone with motion trail.
  strokeLine(x + w * 0.62, y + h * 0.18, x + w * 0.72, y + h * 0.19, 1, rgb(120, 100, 70));
  strokeLine(x + w * 0.64, y + h * 0.22, x + w * 0.72, y + h * 0.225, 1, rgb(120, 100, 70));
  quadcopter(x + w * 0.78, y + h * 0.2, h * 0.09);
  // Explosion: bigger flame tongues + smoke + dust cloud + debris.
  flameTongues(x + w * 0.62, y + h * 0.58, h * 0.15);
  fillCircle(x + w * 0.62, y + h * 0.36, h * 0.08, rgb(90, 80, 70));
  fillCircle(x + w * 0.67, y + h * 0.31, h * 0.06, rgb(90, 80, 70));
  fillCircle(x + w * 0.58, y + h * 0.3, h * 0.05, rgb(110, 98, 84));
  fillCircle(x + w * 0.62, y + h * 0.6, h * 0.07, rgb(215, 190, 150)); // dust at the base
  fillCircle(x + w * 0.68, y + h * 0.62, h * 0.05, rgb(215, 190, 150));
  fillCircle(x + w * 0.56, y + h * 0.62, h * 0.045, rgb(205, 180, 140));
  fillCircle(x + w * 0.66, y + h * 0.42, 1.2, rgb(255, 160, 60)); // debris
  fillCircle(x + w * 0.58, y + h * 0.46, 1, rgb(255, 190, 80));
  // Ground: dusty street, rubble, palm silhouette.
  fillRect(x, y + h * 0.82, w, h * 0.18, rgb(120, 100, 70));
  fillRect(x + w * 0.1, y + h * 0.86, w * 0.08, h * 0.04, rgb(90, 74, 52));
  fillRect(x + w * 0.24, y + h * 0.9, w * 0.06, h * 0.03, rgb(90, 74, 52));
  fillRect(x + w * 0.78, y + h * 0.88, w * 0.07, h * 0.035, rgb(90, 74, 52));
  strokeLine(x + w * 0.08, y + h * 0.82, x + w * 0.08, y + h * 0.6, 1.6, rgb(90, 70, 48)); // palm trunk
  strokeLine(x + w * 0.08, y + h * 0.6, x + w * 0.045, y + h * 0.54, 1.4, rgb(90, 70, 48));
  strokeLine(x + w * 0.08, y + h * 0.6, x + w * 0.115, y + h * 0.54, 1.4, rgb(90, 70, 48));
  strokeLine(x + w * 0.08, y + h * 0.6, x + w * 0.08, y + h * 0.52, 1.4, rgb(90, 70, 48));
  strokeLine(x + w * 0.08, y + h * 0.6, x + w * 0.055, y + h * 0.56, 1.4, rgb(90, 70, 48));
  strokeLine(x + w * 0.08, y + h * 0.6, x + w * 0.105, y + h * 0.56, 1.4, rgb(90, 70, 48));
  // Harsh sun with halo + dust haze.
  fillCircle(x + w * 0.88, y + h * 0.12, h * 0.09, rgb(250, 215, 140));
  fillCircle(x + w * 0.88, y + h * 0.12, h * 0.07, rgb(255, 225, 150));
  fillCircle(x + w * 0.3, y + h * 0.7, h * 0.09, rgb(225, 200, 155));
  fillCircle(x + w * 0.82, y + h * 0.74, h * 0.07, rgb(225, 200, 155));
}

// Scene 13: Europe protests — crowd with placards, city behind.
function sceneProtests(x: number, y: number, w: number, h: number): void {
  sky(x, y, w, h, rgb(180, 200, 220), rgb(235, 235, 230));
  // City behind.
  fillRect(x + w * 0.05, y + h * 0.34, w * 0.16, h * 0.3, rgb(140, 140, 150));
  fillRect(x + w * 0.26, y + h * 0.24, w * 0.18, h * 0.4, rgb(130, 130, 142));
  fillRect(x + w * 0.5, y + h * 0.3, w * 0.16, h * 0.34, rgb(140, 140, 150));
  fillRect(x + w * 0.72, y + h * 0.2, w * 0.2, h * 0.44, rgb(130, 130, 142));
  // Placards.
  const plac = (px: number, py: number, c: [number, number, number]) => {
    fillRect(px - w * 0.07, py - h * 0.12, w * 0.14, h * 0.1, WHITE);
    strokeLine(px, py - h * 0.02, px, py + h * 0.1, 1.6, rgb(60, 56, 50));
    strokeLine(px - w * 0.05, py - h * 0.07, px + w * 0.05, py - h * 0.07, 2, c);
  };
  plac(x + w * 0.18, y + h * 0.62, rgb(176, 30, 36));
  plac(x + w * 0.5, y + h * 0.58, rgb(42, 93, 176));
  plac(x + w * 0.82, y + h * 0.62, rgb(200, 138, 0));
  // Crowd.
  const shirts: [number, number, number][] = [rgb(176, 30, 36), rgb(42, 93, 176), rgb(26, 122, 110), rgb(200, 138, 0), rgb(122, 74, 158), rgb(60, 60, 66), rgb(58, 122, 58), rgb(180, 90, 40)];
  for (let i = 0; i < 8; i++) person(x + w * (0.07 + i * 0.12), y + h * 0.86, h * 0.3, shirts[i]);
  fillRect(x, y + h * 0.86, w, h * 0.14, rgb(90, 88, 84));
  // Second row of heads behind + long banner + lit city windows.
  for (let i = 0; i < 7; i++) fillCircle(x + w * (0.12 + i * 0.13), y + h * 0.74, h * 0.05, rgb(150, 120, 95));
  fillRect(x + w * 0.3, y + h * 0.68, w * 0.4, h * 0.05, rgb(176, 30, 36));
  strokeLine(x + w * 0.3, y + h * 0.68, x + w * 0.3, y + h * 0.78, 1.4, rgb(60, 56, 50));
  strokeLine(x + w * 0.7, y + h * 0.68, x + w * 0.7, y + h * 0.78, 1.4, rgb(60, 56, 50));
  for (let i = 0; i < 6; i++) fillRect(x + w * (0.08 + ((i * 43) % 80) / 100), y + h * (0.28 + ((i * 19) % 12) / 100), w * 0.02, h * 0.04, rgb(255, 220, 130));
}

// ---------------------------------------------------------------------------
// Content (all wording drafted here, in this session, from the verified facts)
// ---------------------------------------------------------------------------
type Tag = 'CONFIRMED' | 'REPORTED' | 'OFFICIAL';
const TAG_COL: Record<Tag, [number, number, number]> = {
  CONFIRMED: [26, 122, 110],
  REPORTED: [176, 110, 20],
  OFFICIAL: [42, 93, 176],
};

type Hero = {
  n: number;
  region: string;
  scene: (x: number, y: number, w: number, h: number) => void;
  head: string;
  deck: string;
  tag: Tag;
  source: string;
};

const HEROES: Hero[] = [
  {
    n: 1,
    region: 'ME',
    scene: sceneCOP31,
    head: 'COP31 COLLAPSES WITH NO DEAL',
    deck: 'After a record 44 hours of overtime, talks end in Antalya with no agreement - the first summit since 2000 without a cover decision.',
    tag: 'CONFIRMED',
    source: 'CNN',
  },
  {
    n: 2,
    region: 'ME',
    scene: sceneHormuz,
    head: 'TWO TANKERS HIT AND BURNING IN HORMUZ',
    deck: 'Mines hit two supertankers; Iran readies a 14+ tanker convoy.',
    tag: 'REPORTED',
    source: 'Reuters',
  },
  {
    n: 3,
    region: 'Americas',
    scene: sceneVegas,
    head: 'VERSTAPPEN WINS A WILD VEGAS GP',
    deck: '35 lead changes, 352 overtakes; Norris beaten by 0.639s.',
    tag: 'CONFIRMED',
    source: 'Formula 1',
  },
];

type Mid = {
  n: number;
  region: string;
  scene: (x: number, y: number, w: number, h: number) => void;
  head: string;
  deck: string;
  tag: Tag;
  source: string;
};

const MIDS: Mid[] = [
  {
    n: 4,
    region: 'Americas',
    scene: sceneDemocrats,
    head: 'DEMOCRATS TAKE BIGGEST HOUSE MAJORITY SINCE 1992',
    deck: '330-vote recount win seals 258 seats; Foxx concedes.',
    tag: 'CONFIRMED',
    source: 'CNN / AP / BBC',
  },
  {
    n: 5,
    region: 'ME',
    scene: sceneBahrain,
    head: 'IRAN HITS US BASE IN BAHRAIN',
    deck: 'Missiles and drones hit a civilian plant on Sitra Island Saturday night; two hurt.',
    tag: 'REPORTED',
    source: 'Reuters / AFP',
  },
  {
    n: 6,
    region: 'ME',
    scene: sceneRiyadh,
    head: 'RIYADH SHOOTS DOWN DRONE AND MISSILE',
    deck: 'Saudi defences destroy a Houthi drone bound for Riyadh; a missile heads west.',
    tag: 'OFFICIAL',
    source: 'Saudi coalition / Reuters',
  },
  {
    n: 7,
    region: 'Americas',
    scene: sceneSinaloa,
    head: "CARTEL BOSS 'EL CHAPO ISIDRO' CAPTURED",
    deck: 'Special forces seize the Sinaloa boss; 11 dead in the raid, including four soldiers.',
    tag: 'CONFIRMED',
    source: 'AP',
  },
  {
    n: 8,
    region: 'Europe',
    scene: sceneKyiv,
    head: 'RUSSIAN STRIKE HITS KYIV APARTMENT BLOCK',
    deck: 'Three killed as a strike near the capital hits a residential building.',
    tag: 'REPORTED',
    source: 'AP',
  },
  {
    n: 9,
    region: 'Africa',
    scene: sceneBenghazi,
    head: 'DRONE BLAST HITS RUSSIAN WARSHIP IN BENGHAZI',
    deck: 'A suspected Ukrainian drone strike sparks fire aboard the corvette Merkury at dawn.',
    tag: 'REPORTED',
    source: 'Reuters',
  },
  {
    n: 10,
    region: 'Asia',
    scene: sceneCikande,
    head: 'CANDY FACTORY FIRE IN CIKANDE',
    deck: 'Three dead and 36 missing after a blaze at the Fonusa Agung Mulia plant in Banten.',
    tag: 'CONFIRMED',
    source: 'AP / Reuters',
  },
  {
    n: 11,
    region: 'Global',
    scene: sceneBitcoin,
    head: 'BITCOIN SLIDES BELOW $59,000',
    deck: 'The coin dips to about $58,900 overnight, then recovers to close near $61,271.',
    tag: 'REPORTED',
    source: 'Finnhub',
  },
  {
    n: 12,
    region: 'Africa',
    scene: sceneSudan,
    head: 'DRONES KILL FOUR IN KHARTOUM',
    deck: 'A strike blamed on the RSF hits a UN building with staff inside.',
    tag: 'REPORTED',
    source: 'Reuters',
  },
  {
    n: 13,
    region: 'Europe',
    scene: sceneProtests,
    head: 'EUROPE PROTESTS ENTER DAY THREE',
    deck: 'Cost-of-living and housing marches run from Portugal to France, day three.',
    tag: 'REPORTED',
    source: 'AP',
  },
];

type AlsoOn = { n: number; region: string; place: string; text: string };
const ALSO_ON: AlsoOn[] = [
  { n: 14, region: 'ME', place: 'Tehran', text: 'Iran shows off a dual-missile launcher and an underground missile city.' },
  { n: 15, region: 'ME', place: 'Ramallah', text: 'West Bank settlers torch vehicles and homes.' },
  { n: 16, region: 'ME', place: 'Gaza', text: 'Israeli forces kill two people.' },
  { n: 17, region: 'Africa', place: 'Nigeria', text: 'Boat capsizes on the way to a funeral; at least 24 dead.' },
  { n: 18, region: 'Asia', place: 'Bangkok', text: 'Thai court upholds a royal defamation conviction, cuts the term to 3 years.' },
  { n: 19, region: 'Asia', place: 'Okinawa', text: 'Restored Shuri Castle hall reopens seven years after the fire.' },
  { n: 20, region: 'Europe', place: 'Rome', text: 'Paolo Bulgari dies at 89.' },
  { n: 21, region: 'Africa', place: 'South Africa', text: 'Phumzile Mlambo-Ngcuka dies at 71.' },
  { n: 22, region: 'Europe', place: 'Warsaw', text: 'Poland says Russia twice tried to kill a Ukrainian American rapper.' },
  { n: 23, region: 'Asia', place: 'Beijing', text: 'China eases margin trading rules; ratio cut from 100% to 80% from 30 Nov.' },
  { n: 24, region: 'Americas', place: 'Washington', text: 'Nvidia faces US demands over AI chips sold to China.' },
  { n: 25, region: 'Asia', place: 'China', text: 'Memory chipmakers CXMT and YMTC gain ground amid US curbs.' },
  { n: 26, region: 'Asia', place: 'Taipei', text: 'Taiwan cautions Canada over closer ties with China.' },
  { n: 27, region: 'Oceania', place: 'Sydney', text: 'Lowy index: the US-China power gap in Asia is narrowing.' },
  { n: 28, region: 'Asia', place: 'New Delhi', text: 'Indian Youth Congress protests at Meta offices.' },
  { n: 29, region: 'Europe', place: 'Sicily', text: 'Former Italian police chief found dead amid a bombing inquiry.' },
  { n: 30, region: 'Europe', place: 'Moscow', text: 'Russia weighs a US offer on European security.' },
  { n: 31, region: 'ME', place: 'Hormuz', text: 'Lewis Pugh swims through the war-hit strait.' },
  { n: 32, region: 'Asia', place: 'Washington', text: "China's spy agency reportedly ran a campaign to obtain AI chips." },
  { n: 33, region: 'Americas', place: 'Washington', text: 'Trump says Iran wants a deal.' },
  { n: 34, region: 'Asia', place: "Cox's Bazar", text: 'Rohingya welcome the ICJ verdict and ask to go home.' },
  { n: 35, region: 'Asia', place: 'Brussels', text: 'EU-Indonesia trade deal signed Saturday: 98.5% of tariffs scrapped.' },
];

const STATS: [string, string][] = [
  ['44 HOURS', 'COP31 overtime'],
  ['258 SEATS', 'Democrats in the House'],
  ['0.639s', "Verstappen's winning margin"],
  ['2 TANKERS', 'hit in Hormuz'],
  ['11 KILLED', 'Sinaloa raid'],
  ['36 MISSING', 'Cikande fire'],
];

// Map pins: lon/lat plus hand-placed display position (final px) so crowded
// zones never touch. Badge radius 6.5, centre distance kept at 13 or more.
type Pin = { n: number; region: string; lon: number; lat: number; dx: number; dy: number };
const PINS: Pin[] = [
  { n: 1, region: 'ME', lon: 30.7, lat: 36.9, dx: 359, dy: 881 },
  { n: 2, region: 'ME', lon: 56.5, lat: 26.6, dx: 413, dy: 879 },
  { n: 3, region: 'Americas', lon: -115.1, lat: 36.1, dx: 106, dy: 881 },
  { n: 4, region: 'Americas', lon: -77.0, lat: 38.9, dx: 166, dy: 886 },
  { n: 5, region: 'ME', lon: 50.6, lat: 26.2, dx: 404, dy: 890 },
  { n: 6, region: 'ME', lon: 46.7, lat: 24.7, dx: 390, dy: 892 },
  { n: 7, region: 'Americas', lon: -107.4, lat: 24.8, dx: 119, dy: 887 },
  { n: 8, region: 'Europe', lon: 30.5, lat: 50.4, dx: 363, dy: 867 },
  { n: 9, region: 'Africa', lon: 20.1, lat: 32.1, dx: 343, dy: 892 },
  { n: 10, region: 'Asia', lon: 106.3, lat: -6.2, dx: 499, dy: 906 },
  { n: 11, region: 'Global', lon: 0, lat: 0, dx: 310, dy: 902 },
  { n: 12, region: 'Africa', lon: 32.5, lat: 15.6, dx: 362, dy: 896 },
  { n: 13, region: 'Europe', lon: 2.35, lat: 48.85, dx: 309, dy: 877 },
  { n: 14, region: 'ME', lon: 51.4, lat: 35.7, dx: 399, dy: 877 },
  { n: 15, region: 'ME', lon: 35.2, lat: 31.9, dx: 373, dy: 878 },
  { n: 16, region: 'ME', lon: 34.45, lat: 31.5, dx: 376, dy: 892 },
  { n: 17, region: 'Africa', lon: 7.0, lat: 7.0, dx: 324, dy: 899 },
  { n: 18, region: 'Asia', lon: 100.5, lat: 13.75, dx: 489, dy: 894 },
  { n: 19, region: 'Asia', lon: 127.7, lat: 26.2, dx: 541, dy: 884 },
  { n: 20, region: 'Europe', lon: 12.5, lat: 41.9, dx: 328, dy: 879 },
  { n: 21, region: 'Africa', lon: 28.0, lat: -26.2, dx: 360, dy: 917 },
  { n: 22, region: 'Europe', lon: 21.0, lat: 52.2, dx: 349, dy: 866 },
  { n: 23, region: 'Asia', lon: 116.4, lat: 39.9, dx: 513, dy: 875 },
  { n: 24, region: 'Americas', lon: -77.0, lat: 38.9, dx: 180, dy: 886 },
  { n: 25, region: 'Asia', lon: 121.5, lat: 31.2, dx: 526, dy: 881 },
  { n: 26, region: 'Asia', lon: 121.6, lat: 25.0, dx: 529, dy: 895 },
  { n: 27, region: 'Oceania', lon: 151.2, lat: -33.9, dx: 579, dy: 922 },
  { n: 28, region: 'Asia', lon: 77.2, lat: 28.6, dx: 447, dy: 885 },
  { n: 29, region: 'Europe', lon: 14.0, lat: 37.5, dx: 342, dy: 878 },
  { n: 30, region: 'Europe', lon: 37.6, lat: 55.75, dx: 381, dy: 865 },
  { n: 31, region: 'ME', lon: 57.0, lat: 26.8, dx: 418, dy: 892 },
  { n: 32, region: 'Asia', lon: -77.0, lat: 38.9, dx: 166, dy: 872 },
  { n: 33, region: 'Americas', lon: -77.0, lat: 38.9, dx: 180, dy: 872 },
  { n: 34, region: 'Asia', lon: 92.0, lat: 21.4, dx: 474, dy: 889 },
  { n: 35, region: 'Asia', lon: 4.35, lat: 50.85, dx: 321, dy: 867 },
];

// Simplified continent outlines in lon/lat (stylised, recognisable shapes).
const CONTINENTS: [number, number][][] = [
  // North America
  [[-168, 66], [-140, 70], [-125, 71], [-110, 68], [-95, 69], [-85, 66], [-80, 73], [-65, 62], [-55, 52], [-60, 47], [-70, 42], [-75, 35], [-80, 32], [-81, 26], [-90, 21], [-97, 16], [-94, 17], [-87, 13], [-83, 9], [-79, 9], [-92, 15], [-105, 20], [-110, 24], [-114, 29], [-120, 34], [-124, 42], [-124, 48], [-130, 55], [-140, 60], [-155, 58], [-162, 55]],
  // Greenland
  [[-58, 64], [-45, 60], [-40, 65], [-30, 68], [-22, 70], [-30, 74], [-50, 76], [-60, 74]],
  // South America
  [[-79, 9], [-77, 4], [-80, -3], [-81, -6], [-77, -12], [-72, -18], [-70, -23], [-70, -30], [-72, -37], [-73, -44], [-70, -50], [-66, -55], [-68, -52], [-62, -45], [-58, -38], [-52, -33], [-48, -28], [-41, -23], [-35, -8], [-35, -6], [-44, -3], [-50, 0], [-52, 4], [-60, 8], [-62, 9], [-70, 11], [-75, 10]],
  // Africa
  [[-17, 15], [-17, 21], [-15, 27], [-10, 31], [-5, 35], [0, 36], [10, 37], [11, 34], [20, 32], [30, 31], [32, 31], [34, 28], [37, 22], [39, 18], [43, 12], [48, 11], [51, 12], [46, 5], [41, -2], [40, -10], [36, -18], [32, -26], [28, -33], [20, -35], [17, -32], [14, -22], [12, -17], [13, -12], [9, -1], [9, 4], [-8, 5], [-13, 8], [-17, 12]],
  // Eurasia
  [[-10, 36], [-9, 38], [-9, 43], [-2, 44], [-1, 46], [-4, 48], [-1, 49], [2, 51], [5, 53], [8, 55], [8, 57], [10, 59], [5, 60], [5, 62], [12, 64], [18, 66], [25, 70], [30, 70], [35, 68], [40, 68], [45, 68], [55, 69], [65, 69], [70, 72], [75, 72], [80, 73], [90, 75], [100, 76], [110, 74], [120, 73], [130, 72], [140, 72], [150, 70], [158, 69], [162, 66], [170, 66], [178, 65], [178, 62], [170, 60], [162, 60], [158, 56], [155, 53], [150, 59], [142, 55], [140, 50], [135, 44], [130, 42], [127, 40], [122, 38], [120, 34], [115, 30], [110, 25], [108, 20], [105, 15], [104, 10], [100, 8], [98, 12], [95, 16], [92, 21], [90, 22], [86, 20], [82, 17], [80, 13], [77, 8], [75, 12], [72, 20], [68, 23], [66, 25], [62, 25], [58, 25], [56, 27], [52, 28], [50, 29], [48, 30], [44, 29], [40, 28], [38, 24], [36, 21], [35, 28], [34, 31], [30, 36], [27, 37], [23, 36], [20, 40], [19, 42], [15, 44], [12, 44], [8, 44], [3, 43], [0, 40], [-2, 37], [-6, 36], [-9, 37]],
  // United Kingdom
  [[-5, 50], [-3, 53], [-5, 56], [-3, 58], [-1, 57], [0, 53]],
  // Japan
  [[130, 31], [132, 33], [135, 34], [138, 35], [140, 37], [141, 39], [142, 42], [144, 44], [142, 45], [140, 42], [138, 38], [135, 35], [132, 33]],
  // Indonesia
  [[95, 5], [98, 3], [102, 0], [106, -6], [110, -7], [114, -8], [118, -9], [122, -9], [126, -8], [130, -4], [131, -1], [128, 1], [124, 1], [120, 0], [116, 1], [112, -2], [108, -3], [104, -2], [100, 0]],
  // Australia
  [[114, -22], [114, -30], [115, -35], [120, -34], [125, -32], [130, -32], [135, -35], [140, -38], [145, -38], [150, -37], [153, -32], [153, -27], [150, -23], [146, -19], [142, -15], [142, -11], [137, -12], [135, -15], [132, -12], [130, -13], [126, -14], [122, -17], [118, -20]],
  // New Zealand
  [[167, -45], [170, -42], [174, -40], [176, -38], [178, -38], [175, -41], [172, -43], [168, -46]],
  // Madagascar
  [[44, -16], [47, -15], [50, -16], [49, -20], [46, -24], [44, -25], [43, -21]],
  // Iceland
  [[-22, 64], [-18, 63], [-14, 64], [-16, 66], [-21, 66]],
];

// ---------------------------------------------------------------------------
// Layout
// ---------------------------------------------------------------------------
function tagPill(tag: Tag, x: number, y: number): number {
  // Draws a small tag pill with its top at y; returns its width.
  const w = textWidth(tag, 9, F_SANS_B) + 10;
  fillRect(x, y, w, 13, TAG_COL[tag]);
  drawText(tag, x + 5, y + 10, 9, F_SANS_B, WHITE, 'l');
  return w;
}

function renderHeader(): void {
  drawText('THE WORLD IN ONE DAY', 8, 30, 13, F_SANS_B, RED, 'l');
  // Count strip, top right.
  const label = '35 STORIES  |  7 REGIONS';
  const pw = textWidth(label, 12, F_SANS_B) + 20;
  fillRect(1016 - pw, 14, pw, 22, RED);
  drawText(label, 1016 - pw / 2, 30, 12, F_SANS_B, WHITE, 'c');
  drawText('Sunday 22 November 2026', 8, 82, 52, F_SERIF_B, INK, 'l');
  drawText('COP31 collapses with no deal after a record 44-hour overtime - as tankers burn in Hormuz,', 8, 106, 15, F_SANS, INK, 'l');
  drawText('Verstappen takes Las Vegas and Democrats win their biggest House majority since 1992.', 8, 124, 15, F_SANS, INK, 'l');
  fillRect(8, 132, 1000, 3, RED);
  fillRect(8, 137, 1000, 1, INK);
}

function renderHeroes(): void {
  const y0 = 142;
  // Three heroes side by side, equal width.
  const numBadge = (n: number, region: string, cx: number, cy: number, r: number) => {
    fillCircle(cx, cy, r, REG_PAL[region]);
    fillCircle(cx, cy, r - 1.2, REG_PAL[region]);
    drawText(String(n), cx, cy + r * 0.38, r * 0.95, F_SANS_B, WHITE, 'c');
  };
  const cols = [8, 344, 680];
  for (let k = 0; k < 3; k++) {
    const h = HEROES[k];
    const x = cols[k];
    h.scene(x, y0, 328, 145);
    numBadge(h.n, h.region, x + 16, y0 + 16, 11);
    const lines = wrap(h.head, 14, F_SANS_B, 328);
    lines.slice(0, 3).forEach((ln, i) => drawText(ln, x, 301 + i * 15, 14, F_SANS_B, INK, 'l'));
    const deck = wrap(h.deck, 11, F_SANS, 328);
    deck.slice(0, 3).forEach((ln, i) => drawText(ln, x, 349 + i * 14, 11, F_SANS, MUTED, 'l'));
    const tw = tagPill(h.tag, x, 386);
    drawText(h.source, x + tw + 6, 396, 9, F_SANS, MUTED, 'l');
  }
  // Divider under the hero band.
  fillRect(8, 406, 1000, 1, RULE);
}

function renderMids(): void {
  // Ten mids (4-13) in two rows of five: scene on top, text below.
  const colX = [8, 210, 412, 614, 816];
  const rowY = [412, 548];
  MIDS.forEach((m, idx) => {
    const x = colX[idx % 5];
    const y = rowY[Math.floor(idx / 5)];
    m.scene(x, y, 196, 58);
    fillCircle(x + 11, y + 11, 10, REG_PAL[m.region]);
    drawText(String(m.n), x + 11, y + 14.5, 10, F_SANS_B, WHITE, 'c');
    const head = wrap(m.head, 11.5, F_SANS_B, 196);
    head.slice(0, 2).forEach((ln, i) => drawText(ln, x, y + 70 + i * 14, 11.5, F_SANS_B, INK, 'l'));
    const deck = wrap(m.deck, 10, F_SANS, 196);
    deck.slice(0, 3).forEach((ln, i) => drawText(ln, x, y + 96 + i * 11, 10, F_SANS, MUTED, 'l'));
    const tp = tagPill(m.tag, x, y + 124);
    drawText(m.source, x + tp + 6, y + 134, 9, F_SANS, MUTED, 'l');
  });
  fillRect(8, 690, 1000, 1, RULE);
}

function renderAlsoOn(): void {
  drawText('ALSO ON', 8, 702, 13, F_SANS_B, RED, 'l');
  drawText('22 MORE STORIES', 120, 702, 11, F_SANS_B, MUTED, 'l');
  const colX = [8, 516];
  const y0 = 718;
  const lead = 11;
  ALSO_ON.forEach((a, idx) => {
    const col = idx < 11 ? 0 : 1;
    const row = idx % 11;
    const x = colX[col];
    const y = y0 + row * lead;
    const colW = col === 0 ? 486 : 500; // keep a clear gutter between columns
    drawText(String(a.n), x, y, 9.5, F_SANS_B, REG_PAL[a.region], 'l');
    const nx = x + 22;
    const placeW = textWidth(a.place + ' - ', 9.5, F_SANS_B);
    drawText(a.place + ' - ', nx, y, 9.5, F_SANS_B, INK, 'l');
    // Trim the story text so the line never overflows its column.
    let t = a.text;
    const maxW = colW - 22 - placeW;
    while (t.length > 0 && textWidth(t, 9.5, F_SANS) > maxW) t = t.slice(0, -1);
    if (t.length < a.text.length) t = t.replace(/[,;:. ]+$/, '') + '...';
    drawText(t, nx + placeW, y, 9.5, F_SANS, INK, 'l');
  });
  fillRect(8, 836, 1000, 1, RULE);
}

function renderMapAndDateCheck(): void {
  const mx = 8;
  const my = 856;
  const mw = 640;
  const mh = 80;
  drawText('WHERE IT HAPPENED', mx, 850, 11, F_SANS_B, INK, 'l');
  // Ocean and land.
  fillRect(mx, my, mw, mh, rgb(216, 228, 238));
  const proj = (lon: number, lat: number): [number, number] => [
    mx + ((lon + 170) / 360) * mw,
    my + ((78 - lat) / 136) * mh,
  ];
  for (const cont of CONTINENTS) {
    fillPoly(cont.map(([lo, la]) => proj(lo, la)), rgb(208, 198, 170));
  }
  // Graticule, faint.
  for (let lo = -150; lo <= 150; lo += 30) strokeLine(proj(lo, 78)[0], my, proj(lo, 78)[0], my + mh, 0.6, rgb(190, 205, 218));
  // Leader lines, then badges.
  for (const p of PINS) {
    const [bx, by] = proj(p.lon, p.lat);
    if (Math.hypot(p.dx - bx, p.dy - by) > 3) strokeLine(bx, by, p.dx, p.dy, 0.8, rgb(120, 120, 120));
    fillCircle(bx, by, 1.6, rgb(60, 60, 60));
  }
  for (const p of PINS) {
    fillCircle(p.dx, p.dy, 6.5, REG_PAL[p.region]);
    fillCircle(p.dx, p.dy, 5.6, REG_PAL[p.region]);
    drawText(String(p.n), p.dx, p.dy + 3.2, 8.5, F_SANS_B, WHITE, 'c');
  }
  // Legend.
  const legend: [string, string][] = [
    ['Europe', 'Europe'],
    ['Asia', 'Asia'],
    ['Middle East', 'ME'],
    ['Africa', 'Africa'],
    ['Americas', 'Americas'],
    ['Oceania', 'Oceania'],
    ['Global', 'Global'],
  ];
  let lx = mx;
  for (const [label, key] of legend) {
    fillCircle(lx + 4, 942, 4, REG_PAL[key]);
    drawText(label, lx + 11, 945, 9, F_SANS, INK, 'l');
    lx += 11 + textWidth(label, 9, F_SANS) + 16;
  }
  // DATE CHECK panel.
  const dx = 664;
  fillRect(dx, 842, 352, 108, rgb(238, 232, 220));
  fillRect(dx, 842, 352, 2, RED);
  drawText('DATE CHECK - NOT TODAY', dx + 10, 858, 11, F_SANS_B, RED, 'l');
  const dc: [string, string][] = [
    ['SAT 21 NOV: ', 'Davao jet, all 146 safe; three missiles downed over Riyadh; Kryvyi Rih; Crimea bridge; MQ-9 Hormuz.'],
    ['ALSO SAT: ', 'Trump data-centre tax; Rahul 124*; Russell takes Vegas pole.'],
    ['EARLIER: ', 'Shenzhen (19 Nov); Anthropic debut; GTA VI; Voyager 1 (18 Nov); ICJ + Wall Street (20 Nov).'],
    ['UNCONFIRMED: ', 'BepiColombo in orbit around Mercury.'],
  ];
  let cy = 872;
  for (const [lead, body] of dc) {
    const lines = wrap(lead + body, 9, F_SANS, 332);
    lines.forEach((ln) => {
      drawText(ln, dx + 10, cy, 9, F_SANS, INK, 'l');
      cy += 10;
    });
    cy += 2;
  }
}

function renderStatsAndFooter(): void {
  fillRect(8, 954, 1000, 1, RULE);
  const cellW = 1000 / 6;
  STATS.forEach(([num, label], i) => {
    const x = 8 + i * cellW;
    drawText(num, x, 968, 14, F_SANS_B, RED, 'l');
    drawText(label, x, 981, 9, F_SANS, MUTED, 'l');
    if (i > 0) fillRect(x - 6, 960, 1, 22, RULE);
  });
  fillRect(8, 988, 1000, 1, INK);
  drawText('Every story here happened or was first reported on Sunday 22 November 2026. Figures and officials\u2019 claims are attributed to their sources.', 512, 998, 10, F_SANS, MUTED, 'c');
  drawText('Sources named beside each story  |  Original drawings', 512, 1010, 10, F_SANS, MUTED, 'c');
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------
function main(): void {
  loadFonts();
  renderHeader();
  renderHeroes();
  renderMids();
  renderAlsoOn();
  renderMapAndDateCheck();
  renderStatsAndFooter();
  const small = downscale(buf, W, H, OUT_W, OUT_H);
  const png = encodePNG(small, OUT_W, OUT_H);
  const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, 'entry.png'), png);
}

main();
