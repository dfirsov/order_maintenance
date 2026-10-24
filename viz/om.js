/* Insert-only order-maintenance core (docs/SPEC.md §4-5), ported from the Python
 * prototype for the visualizer: prototype/core.py, pq.py, top_wbbt.py, guards.py.
 *
 * The port follows the prototype statement for statement, so that it can be checked
 * against it (viz/test: same keys, fallbacks, step counts and state digests after
 * every operation). Differences:
 *   - labels and tags are BigInt (tags are H·β bits wide);
 *   - only the WBBT top structure (no SimpleTop), always built eagerly;
 *   - the lemma-checker instrumentation is dropped;
 *   - every primitive appends an event to `core.log`, which the page displays.
 *
 * Records refer to each other by integer index (NIL = -1), as in the prototype.
 */
(function (root) {
"use strict";

const NIL = -1;
const QUIET = 0, OVERFLOW = 1, SPLITTING = 2, DEAD = 3;
const LEFT = 0, RIGHT = 1;
const B = BigInt;

class GuardFailure extends Error {}

function ceilLog2(x) { let k = 0; while ((1 << k) < x) k++; return k; }   // = ceil(log2 x), x >= 1

/* Params.for_capacity of prototype/core.py, with the WBBT top. */
function paramsFor(N, o = {}) {
  const c_G = o.c_G ?? 2, c_T = o.c_T ?? 1;
  const L = Math.max(o.L_min ?? 4, ceilLog2(Math.max(N, 2)));
  const G = c_G * L;
  const T = c_T * L * L;
  const theta = Math.floor(2 * T / 3);
  const B_e = 2 * G + ceilLog2(8 * G + 8) + 8;
  const gpc = Math.max(1, Math.floor(3 * T / G));
  const B_g = 2 * gpc + ceilLog2(8 * gpc + 8) + 8;
  const a = o.a ?? 8;
  return {
    N, L, G, T, theta, B_e, B_g,
    D_e: (1n << B(B_e - 1)) / B(8 * G + 8),
    D_g: (1n << B(B_g - 1)) / B(8 * gpc + 8),
    K_G: o.K_G ?? 4, K_C: o.K_C ?? 4, K_R: o.K_R ?? 2,
    top_a: a, top_s: o.s ?? 8, top_beta: o.beta ?? (4 * a + 8),
  };
}

const newElem = (g, lab, h) => ({ next: NIL, prev: NIL, grp: g, lab, live: true, h });
const newGroup = c => ({ next: NIL, prev: NIL, first: NIL, last: NIL, chk: c, lab: 0n, size: 0,
                         st: QUIET, src: NIL, l: NIL, r: NIL, alive: true });
const newChunk = () => ({ next: NIL, prev: NIL, first: NIL, last: NIL, size: 0, st: QUIET,
                          src: NIL, l: NIL, r: NIL, tag: 0n, alive: true });

/* ------------------------------------------------------------------ pq.py */
class BucketPQ {
  constructor(core) {
    this.core = core;
    this.theta = core.P.theta;
    this.bucket = new Map();     // size -> Set of chunks, in insertion order
    this.nb_next = new Map();
    this.nb_prev = new Map();
    this.hi = null;
    this.lo = null;
    this.where = new Map();      // chunk -> its bucket
  }
  empty() { return this.hi === null; }
  _link_after(s, p) {
    let n;
    if (p === null) { n = this.lo; this.lo = s; }
    else { n = this.nb_next.get(p); this.nb_next.set(p, s); }
    this.nb_prev.set(s, p);
    this.nb_next.set(s, n);
    if (n !== null) this.nb_prev.set(n, s); else this.hi = s;
  }
  _add(c, s, p) {
    const b = this.bucket.get(s);
    if (b) b.add(c);
    else { this.bucket.set(s, new Set([c])); this._link_after(s, p); }
    this.where.set(c, s);
  }
  _del(c) {
    const s = this.where.get(c);
    this.where.delete(c);
    const b = this.bucket.get(s);
    b.delete(c);
    if (b.size === 0) {
      this.bucket.delete(s);
      const p = this.nb_prev.get(s), n = this.nb_next.get(s);
      this.nb_prev.delete(s); this.nb_next.delete(s);
      if (p !== null) this.nb_next.set(p, n); else this.lo = n;
      if (n !== null) this.nb_prev.set(n, p); else this.hi = p;
    }
  }
  _insert_scan(c, s) {
    let p = s - 1;
    while (p > this.theta && !this.bucket.has(p)) { p--; this.core.stats.pq_scan++; }
    this._add(c, s, p > this.theta ? p : null);
  }
  adjust(c, old, nw) {
    this.core.stats.steps++;
    const th = this.theta;
    if (old <= th && th < nw) this._insert_scan(c, nw);
    else if (nw <= th && th < old) this._del(c);
    else if (old > th && nw > th) {
      if (nw === old + 1) {
        const b = this.bucket.get(old);
        const p = b.size > 1 ? old : this.nb_prev.get(old);
        this._del(c); this._add(c, nw, p);
      } else if (nw === old - 1) {
        const p = this.nb_prev.get(old);
        this._del(c); this._add(c, nw, p);
      } else { this._del(c); this._insert_scan(c, nw); }
    }
  }
  enter_if_above(c) {
    const s = this.core.C[c].size;
    if (s > this.theta) this._insert_scan(c, s);
  }
  pop_max() {
    const b = this.bucket.get(this.hi);
    let c; for (c of b);          // last inserted (LIFO within a bucket)
    this._del(c);
    return c;
  }
  /* buckets from the largest down: [[size, [chunks...]], ...] */
  buckets() {
    const out = [];
    for (let s = this.hi; s !== null; s = this.nb_prev.get(s)) out.push([s, [...this.bucket.get(s)]]);
    return out;
  }
}

/* ------------------------------------------------------------ top_wbbt.py */
function newNode(h) {
  return { height: h, live_parent: NIL, children: [], weight: 0, lab: new Map(), order: [],
           in_tables: [], first: NIL, last: NIL, draining: false, t1: NIL, t2: NIL,
           side: new Map(), overflow_of: NIL, alive: true };
}

class WBBTTop {
  constructor(core, a, s, beta) {
    this.core = core;
    this.a = a; this.s = s; this.beta = beta;
    this.bb = B(beta);
    this.top_steps = 0;
    this.relabels = 0;
    this.renumbered = false;
    this.drains = 0;
    this.ghosts = 0;
    const P = core.P;
    const m_max = P.m_max || Math.floor(6 * P.N / Math.max(P.theta, 1)) + 16;
    this.H = 2;
    while (a ** (this.H - 1) < m_max) this.H++;
    this._reset();
  }
  _reset() {
    this.nodes = [];
    this.path = [];      // chunk -> [NIL, p1, ..., pH]
    this.cin = [];       // chunk -> nodes whose table holds it
    this.lpar = [];      // chunk -> live height-1 parent
  }
  _new_node(h) { this.nodes.push(newNode(h)); return this.nodes.length - 1; }
  _in_tables(e, h) { return h === 0 ? this.cin[e] : this.nodes[e].in_tables; }
  _tag_of(c) {
    const p = this.path[c];
    let t = 0n, below = c;
    for (let j = 1; j <= this.H; j++) {
      t |= this.nodes[p[j]].lab.get(below) << (B(j - 1) * this.bb);
      below = p[j];
    }
    return t;
  }
  _guard_tag(c, t) {
    const C = this.core.C, pr = C[c].prev, nx = C[c].next;
    if (pr !== NIL && !(C[pr].tag < t)) throw new GuardFailure("top: tag not above predecessor");
    if (nx !== NIL && !(t < C[nx].tag)) throw new GuardFailure("top: tag not below successor");
  }
  _room_next_to(T, e, before) {
    const i = T.order.indexOf(e);
    let lo, hi;
    if (before) { lo = i > 0 ? T.lab.get(T.order[i - 1]) : -1n; hi = T.lab.get(e); }
    else { lo = T.lab.get(e); hi = i + 1 < T.order.length ? T.lab.get(T.order[i + 1]) : 1n << this.bb; }
    if (lo + 1n >= hi) throw new GuardFailure("top: table full");
    return (lo + hi) / 2n;
  }
  _table_insert(T, e, nw, before, lab) {
    const i = T.order.indexOf(e);
    T.order.splice(before ? i : i + 1, 0, nw);
    T.lab.set(nw, lab);
    if (T.draining) T.side.set(nw, T.side.get(e));
  }

  init_first(c) {
    this._reset();
    const center = 1n << (this.bb - 1n);
    this.cin[c] = [];
    const p = new Array(this.H + 1).fill(NIL);
    let below = c, tag = 0n;
    for (let h = 1; h <= this.H; h++) {
      const v = this._new_node(h), V = this.nodes[v];
      V.children = [below]; V.order = [below]; V.lab.set(below, center);
      V.weight = 1; V.first = V.last = c;
      if (h === 1) { this.cin[c] = [v]; this.lpar[c] = v; }
      else { this.nodes[below].in_tables = [v]; this.nodes[below].live_parent = v; }
      p[h] = v;
      tag |= center << (B(h - 1) * this.bb);
      below = v;
    }
    this.path[c] = p;
    this.core.C[c].tag = tag;
  }

  relabel_all() {
    this.relabels++;
    const core = this.core, chunks = [];
    for (let c = core.first_chunk; c !== NIL; c = core.C[c].next) chunks.push(c);
    this._build(chunks);
    this.top_steps += chunks.length;
    const tags = chunks.map(c => core.C[c].tag);
    this.renumbered = tags.some((t, i) => i > 0 && tags[i - 1] >= t);
    if (this.renumbered) chunks.forEach((c, i) => { core.C[c].tag = B(i + 1); });
  }

  _build(chunks) {
    this._reset();
    const a = this.a, H = this.H;
    let level = chunks.slice();
    for (let h = 1; h <= H; h++) {
      const groups = [];
      if (h < H) for (let i = 0; i < level.length; i += a) groups.push(level.slice(i, i + a));
      else groups.push(level);
      const nxt = [];
      for (const grp of groups) {
        const v = this._new_node(h), V = this.nodes[v];
        V.children = grp.slice(); V.order = grp.slice();
        const gap = (1n << this.bb) / B(grp.length + 1);
        grp.forEach((e, i) => {
          V.lab.set(e, B(i + 1) * gap);
          if (h === 1) { this.cin[e] = [v]; this.lpar[e] = v; V.weight += 1; }
          else { const E = this.nodes[e]; E.in_tables = [v]; E.live_parent = v; V.weight += E.weight; }
        });
        nxt.push(v);
      }
      level = nxt;
    }
    for (const c of chunks) {
      const p = new Array(H + 1).fill(NIL);
      let v = this.lpar[c];
      for (let j = 1; j <= H; j++) {
        p[j] = v;
        const V = this.nodes[v];
        if (V.first === NIL) V.first = c;
        V.last = c;
        v = V.live_parent;
      }
      this.path[c] = p;
    }
    for (const c of chunks) this.core.C[c].tag = this._tag_of(c);
  }

  insert_around(x, y, z) {
    const H = this.H, px = this.path[x], tabs = this.cin[x];
    const ly = new Map(), lz = new Map();
    for (const T of tabs) ly.set(T, this._room_next_to(this.nodes[T], x, true));
    for (const T of tabs) lz.set(T, this._room_next_to(this.nodes[T], x, false));
    const f1x = this.nodes[px[1]].lab.get(x);
    const ty = this.core.C[x].tag - f1x + ly.get(px[1]);
    const tz = this.core.C[x].tag - f1x + lz.get(px[1]);
    this._guard_tag(y, ty);
    this._guard_tag(z, tz);
    for (const T of tabs) {
      this._table_insert(this.nodes[T], x, y, true, ly.get(T));
      this._table_insert(this.nodes[T], x, z, false, lz.get(T));
    }
    for (const c of [y, z]) {
      this.path[c] = new Array(H + 1).fill(NIL);
      this.cin[c] = tabs.slice();
      this.lpar[c] = this.lpar[x];
    }
    const lp = this.nodes[this.lpar[x]];
    const i = lp.children.indexOf(x);
    lp.children.splice(i, 1, y, x, z);
    this.core.C[y].tag = ty;
    this.core.C[z].tag = tz;
    this.top_steps++;
    const info = { x, y, z, phase: "copy path", at: NIL, steps: 0 };
    const job = this._job(x, y, z, info);
    job.info = info;
    return job;
  }

  step(job) {
    this.top_steps++;
    return !job.next().done;
  }

  *_job(x, y, z, info) {
    const H = this.H;
    for (let j = 1; j <= H; j++) {
      info.phase = "copy path"; info.at = j;
      const v = this.path[x][j];
      this.path[y][j] = this.path[z][j] = v;
      const V = this.nodes[v];
      if (V.first === x) V.first = y;
      if (V.last === x) V.last = z;
      yield;
    }
    let v = this.lpar[y];
    while (v !== NIL) {
      info.phase = "walk up"; info.at = v;
      const V = this.nodes[v], up = V.live_parent;
      V.weight += 2;
      if (up !== NIL && !V.draining && V.overflow_of === NIL && V.weight > 2 * this.a ** V.height) {
        this._start_drain(v);
        yield;
      }
      const src = V.overflow_of;
      if (src !== NIL) {
        for (let k = 0; k < this.s; k++) {
          if (!this._drain_step(src)) break;
          yield;
        }
      }
      yield;
      v = up;
    }
  }

  _start_drain(v) {
    let V = this.nodes[v];
    const h = V.height, kids = V.children;
    if (kids.length < 2) return;
    const wt = h === 1 ? (() => 1) : (e => this.nodes[e].weight);
    let total = 0; for (const e of kids) total += wt(e);
    let acc = 0, k = 0;
    while (k < kids.length - 1 && acc + wt(kids[k]) <= Math.floor(total / 2)) { acc += wt(kids[k]); k++; }
    k = Math.max(k, 1);
    if (h > 1) {
      while (0 < k && k < kids.length && this._same_drain(kids[k - 1], kids[k])) k++;
      if (k >= kids.length) {
        k = kids.length - 1;
        while (k > 0 && this._same_drain(kids[k - 1], kids[k])) k--;
      }
      if (k === 0) return;
    }
    const boundary = kids[k];
    const entries = V.order.filter(e => h === 1 || kids.includes(e) || this.nodes[e].first !== NIL);
    const side = new Map();
    let s_ = LEFT;
    for (const e of V.order) { if (e === boundary) s_ = RIGHT; side.set(e, s_); }
    if (h > 1) for (const e of entries) { const E = this.nodes[e]; if (E.draining) side.set(e, side.get(E.t1)); }
    const left = entries.filter(e => side.get(e) === LEFT);
    const right = entries.filter(e => side.get(e) === RIGHT);
    const l1 = new Map(), l2 = new Map();
    for (const T of V.in_tables) l1.set(T, this._room_next_to(this.nodes[T], v, true));
    for (const T of V.in_tables) l2.set(T, this._room_next_to(this.nodes[T], v, false));
    // -- mutate
    this.drains++;
    const v1 = this._new_node(h), v2 = this._new_node(h);
    V = this.nodes[v];
    const V1 = this.nodes[v1], V2 = this.nodes[v2];
    for (const T of V.in_tables) {
      this._table_insert(this.nodes[T], v, v1, true, l1.get(T));
      this._table_insert(this.nodes[T], v, v2, false, l2.get(T));
    }
    V1.in_tables = V.in_tables.slice();
    V2.in_tables = V.in_tables.slice();
    for (const [W, part] of [[V1, left], [V2, right]]) {
      const gap = (1n << this.bb) / B(part.length + 1);
      W.order = part.slice();
      part.forEach((e, i) => W.lab.set(e, B(i + 1) * gap));
    }
    for (const e of left) this._in_tables(e, h - 1).push(v1);
    for (const e of right) this._in_tables(e, h - 1).push(v2);
    V1.children = kids.filter(e => side.get(e) === LEFT);
    V2.children = kids.filter(e => side.get(e) === RIGHT);
    for (const [W, w] of [[V1, v1], [V2, v2]]) {
      for (const e of W.children) { if (h === 1) this.lpar[e] = w; else this.nodes[e].live_parent = w; }
      W.weight = 0; for (const e of W.children) W.weight += wt(e);
      W.live_parent = V.live_parent;
      W.overflow_of = v;
    }
    const par = this.nodes[V.live_parent];
    par.children.splice(par.children.indexOf(v), 1, v1, v2);
    V.draining = true; V.t1 = v1; V.t2 = v2; V.side = side;
    this.ghosts++;
    V.live_parent = NIL;
    V.children = [];
    this.top_steps += V.order.length + V.in_tables.length;
    this.core.emit({ k: "drain", v, v1, v2, h });
  }

  _same_drain(a_, b_) {
    const A = this.nodes[a_], Bn = this.nodes[b_];
    return A.overflow_of !== NIL && A.overflow_of === Bn.overflow_of;
  }

  _drain_step(v) {
    const V = this.nodes[v];
    if (!V.alive) return false;
    const h = V.height;
    if (V.first === NIL) { this._finish_drain(v); return false; }
    let y = V.first;
    let below = h === 1 ? y : this.path[y][h - 1];
    let t, left;
    if (V.side.get(below) === LEFT) { t = V.t1; left = true; }
    else {
      y = V.last;
      below = h === 1 ? y : this.path[y][h - 1];
      if (V.side.get(below) !== RIGHT) throw new GuardFailure("top: drain sides out of order");
      t = V.t2; left = false;
    }
    const T = this.nodes[t], p = this.path[y], par = this.nodes[p[h + 1]], b = this.bb;
    if (!par.lab.has(t) || !T.lab.has(below)) throw new GuardFailure("top: missing table entry");
    const hb = B(h) * b, h1b = B(h - 1) * b;
    const old = (par.lab.get(v) << hb) | (V.lab.get(below) << h1b);
    const nw = (par.lab.get(t) << hb) | (T.lab.get(below) << h1b);
    const tag = this.core.C[y].tag - old + nw;
    this._guard_tag(y, tag);
    // -- mutate
    this.core.C[y].tag = tag;
    p[h] = t;
    const C = this.core.C;
    if (V.first === V.last) V.first = V.last = NIL;
    else if (left) V.first = C[y].next;
    else V.last = C[y].prev;
    if (left) { if (T.first === NIL) T.first = y; T.last = y; }
    else { if (T.last === NIL) T.last = y; T.first = y; }
    this.core.emit({ k: "sweep", v, c: y, t, h });
    return true;
  }

  _finish_drain(v) {
    const V = this.nodes[v], h = V.height;
    for (const e of V.order) {
      const tabs = this._in_tables(e, h - 1), i = tabs.indexOf(v);
      if (i >= 0) tabs.splice(i, 1);
    }
    for (const T of V.in_tables) {
      const Tn = this.nodes[T];
      Tn.order.splice(Tn.order.indexOf(v), 1);
      Tn.lab.delete(v);
      Tn.side.delete(v);
    }
    for (const t of [V.t1, V.t2]) if (this.nodes[t].overflow_of === v) this.nodes[t].overflow_of = NIL;
    V.alive = false;
    V.in_tables = [];
    this.ghosts--;
    this.top_steps += V.order.length;
    this.core.emit({ k: "drained", v, h });
  }

  root() {
    for (let i = 0; i < this.nodes.length; i++)
      if (this.nodes[i].alive && this.nodes[i].height === this.H) return i;
    return NIL;
  }
}

/* ---------------------------------------------------------------- core.py */
class Core {
  constructor(P) {
    this.P = P;
    this.E = []; this.Gs = []; this.C = []; this.free_g = [];
    this.stats = { steps: 0, fallbacks: 0, pq_scan: 0, reservations: 0 };
    this.fallback_reasons = [];
    this.log = [];
    this.count = 0;
    this.pq = new BucketPQ(this);
    this.top = new WBBTTop(this, P.top_a, P.top_s, P.top_beta);
    this.res_job = null;
    const c = this._new_chunk();
    const g = this._new_group(c);
    this.top.init_first(c);
    this.Gs[g].lab = 1n << B(P.B_g - 1);
    this.C[c].first = this.C[c].last = g;
    this.HEAD = this._new_elem(g, 1n << B(P.B_e - 1), -1);
    this.E[this.HEAD].live = false;
    this.Gs[g].first = this.Gs[g].last = this.HEAD;
    this.Gs[g].size = 1;
    this.C[c].size = 1;
    this.first_group = g;
    this.first_chunk = c;
    this.tail = this.HEAD;
    this.count = 1;
  }

  emit(ev) { this.log.push(ev); }
  totalSteps() { return this.stats.steps + this.top.top_steps; }

  _new_elem(g, lab, h) { this.E.push(newElem(g, lab, h)); return this.E.length - 1; }
  _new_group(c) {
    if (this.free_g.length) { const i = this.free_g.pop(); this.Gs[i] = newGroup(c); return i; }
    this.Gs.push(newGroup(c)); return this.Gs.length - 1;
  }
  _new_chunk() { this.C.push(newChunk()); return this.C.length - 1; }

  _between(a, b, why) {
    if (a + 1n >= b) throw new GuardFailure(why);
    return (a + b) / 2n;
  }
  _after(a, D, Bits, why) {
    const v = a + D;
    if (v >= (1n << B(Bits)) || v <= a) throw new GuardFailure(why);
    return v;
  }
  _before(b, D, why) {
    if (b < D || D <= 0n) throw new GuardFailure(why);
    return b - D;
  }

  key(e) {
    const x = this.E[e], g = this.Gs[x.grp];
    return [this.C[g.chk].tag, g.lab, x.lab];
  }
  order(x, y) {
    const a = this.key(x), b = this.key(y);
    for (let i = 0; i < 3; i++) if (a[i] !== b[i]) return a[i] < b[i];
    return false;
  }

  insert_after(x, h) {
    let y;
    try { y = this._insert_elem(x, h); }
    catch (ex) { if (!(ex instanceof GuardFailure)) throw ex; this._fallback(ex.message); y = this._insert_elem(x, h); }
    try { this._background(y); }
    catch (ex) { if (!(ex instanceof GuardFailure)) throw ex; this._fallback(ex.message); }
    return y;
  }
  insert_first(h) { return this.insert_after(this.HEAD, h); }
  mark_dead(x) { this.E[x].live = false; }

  _insert_elem(x, h) {
    const P = this.P, ex = this.E[x], g = ex.grp, G = this.Gs[g];
    const lab = x === G.last ? this._after(ex.lab, P.D_e, P.B_e, "elem: no room after last")
                             : this._between(ex.lab, this.E[ex.next].lab, "elem: no room between");
    this.stats.steps++;
    const y = this._new_elem(g, lab, h), ey = this.E[y];
    ey.prev = x; ey.next = ex.next;
    if (ex.next !== NIL) this.E[ex.next].prev = y;
    ex.next = y;
    if (this.tail === x) this.tail = y;
    if (G.last === x) G.last = y;
    G.size++;
    this.count++;
    this._chunk_size(G.chk, +1);
    this.emit({ k: "insert", y, x, g, lab });
    return y;
  }

  _background(y) {
    const P = this.P, g = this.E[y].grp;
    if (this.Gs[g].st === QUIET && this.Gs[g].size >= P.G) this._start_group_split(g);
    this._drive_group(this.E[y].grp);
    this._drive_chunk(this.Gs[this.E[y].grp].chk);
    this._reservation(P.K_R);
  }

  _chunk_size(c, d) {
    const C = this.C[c], old = C.size;
    C.size += d;
    if (C.st === QUIET) this.pq.adjust(c, old, C.size);
  }

  _start_group_split(g) {
    const P = this.P;
    let G = this.Gs[g];
    if (g === NIL || !G.alive) throw new GuardFailure("group: split of a dead group");
    const c = G.chk, C = this.C[c];
    const lab_l = g === C.first ? this._before(G.lab, P.D_g, "group: no room before first")
                                : this._between(this.Gs[G.prev].lab, G.lab, "group: no room left");
    const lab_r = g === C.last ? this._after(G.lab, P.D_g, P.B_g, "group: no room after last")
                               : this._between(G.lab, this.Gs[G.next].lab, "group: no room right");
    this.stats.steps++;
    const gl = this._new_group(c), gr = this._new_group(c);
    G = this.Gs[g];
    const L_ = this.Gs[gl], R_ = this.Gs[gr];
    L_.lab = lab_l; L_.st = OVERFLOW; L_.src = g;
    R_.lab = lab_r; R_.st = OVERFLOW; R_.src = g;
    L_.prev = G.prev; L_.next = g;
    if (G.prev !== NIL) this.Gs[G.prev].next = gl; else this.first_group = gl;
    G.prev = gl;
    R_.prev = g; R_.next = G.next;
    if (G.next !== NIL) this.Gs[G.next].prev = gr;
    G.next = gr;
    if (C.first === g) C.first = gl;
    if (C.last === g) C.last = gr;
    G.st = SPLITTING; G.l = gl; G.r = gr;
    this.emit({ k: "gsplit", g, gl, gr });
  }

  _drive_group(g) {
    const G = this.Gs[g];
    let s;
    if (G.st === SPLITTING) s = g; else if (G.st === OVERFLOW) s = G.src; else return;
    for (let i = 0; i < this.P.K_G; i++) if (!this._group_split_step(s)) return;
  }

  _group_split_step(g) {
    const P = this.P, G = this.Gs[g];
    if (g === NIL || !G.alive) throw new GuardFailure("group split: dead group");
    if (G.first === NIL) { this._remove_group(g); return false; }
    const gl = G.l, gr = G.r, L_ = this.Gs[gl], R_ = this.Gs[gr];
    const center = 1n << B(P.B_e - 1);
    let e, lab, dst;
    if (L_.size <= R_.size) {
      if (L_.next !== g) throw new GuardFailure("group split: left sibling not adjacent");
      e = G.first;
      lab = L_.first === NIL ? center : this._after(this.E[L_.last].lab, P.D_e, P.B_e, "elem: push-back room");
      this.stats.steps++;
      if (G.first === G.last) G.first = G.last = NIL; else G.first = this.E[e].next;
      if (L_.first === NIL) L_.first = e;
      L_.last = e;
      dst = gl;
    } else {
      if (R_.prev !== g) throw new GuardFailure("group split: right sibling not adjacent");
      e = G.last;
      lab = R_.first === NIL ? center : this._before(this.E[R_.first].lab, P.D_e, "elem: push-front room");
      this.stats.steps++;
      if (G.first === G.last) G.first = G.last = NIL; else G.last = this.E[e].prev;
      if (R_.first === NIL) R_.last = e;
      R_.first = e;
      dst = gr;
    }
    const D = this.Gs[dst];
    this.E[e].grp = dst;
    this.E[e].lab = lab;
    G.size--;
    D.size++;
    if (D.chk !== G.chk) { this._chunk_size(D.chk, +1); this._chunk_size(G.chk, -1); }
    this.emit({ k: "gmove", e, from: g, to: dst, lab });
    return true;
  }

  _remove_group(g) {
    this.stats.steps++;
    const G = this.Gs[g], C = this.C[G.chk];
    if (G.prev !== NIL) this.Gs[G.prev].next = G.next; else this.first_group = G.next;
    if (G.next !== NIL) this.Gs[G.next].prev = G.prev;
    if (C.first === g && C.last === g) C.first = C.last = NIL;
    else if (C.first === g) C.first = G.next;
    else if (C.last === g) C.last = G.prev;
    const quiet = [];
    for (const s of [G.l, G.r]) {
      const S = this.Gs[s];
      if (S.st === OVERFLOW && S.src === g) { S.st = QUIET; S.src = NIL; quiet.push(s); }
    }
    G.alive = false;
    G.next = G.prev = NIL;
    this.free_g.push(g);
    this.emit({ k: "gdone", g, l: G.l, r: G.r });
    for (const s of quiet) if (this.Gs[s].size >= this.P.G) this._start_group_split(s);
  }

  _drive_chunk(c) {
    const C = this.C[c];
    let s;
    if (C.st === SPLITTING) s = c; else if (C.st === OVERFLOW) s = C.src; else return;
    for (let i = 0; i < this.P.K_C; i++) if (!this._chunk_split_step(s)) return;
  }

  _unit(x, left) {
    const X = this.C[x], g0 = left ? X.first : X.last, G0 = this.Gs[g0];
    if (G0.st === OVERFLOW) {
      const S = this.Gs[G0.src];
      let unit;
      if (left && S.l === g0) unit = [g0, G0.src, S.r];
      else if (!left && S.r === g0) unit = [S.l, G0.src, g0];
      else return [g0];
      if (unit.some(a => this.Gs[a].chk !== x)) throw new GuardFailure("chunk split: family not contiguous in chunk");
      for (let i = 0; i + 1 < unit.length; i++)
        if (this.Gs[unit[i]].next !== unit[i + 1]) throw new GuardFailure("chunk split: family not contiguous in chunk");
      return unit;
    }
    return [g0];
  }

  _chunk_split_step(x) {
    const P = this.P, X = this.C[x];
    if (X.first === NIL) { this._remove_chunk(x); return false; }
    const y = X.l, z = X.r, Y = this.C[y], Z = this.C[z];
    const center = 1n << B(P.B_g - 1);
    const left = Y.size <= Z.size;
    const unit = this._unit(x, left);
    const labs = [];
    if (left) {
      if (Y.next !== x) throw new GuardFailure("chunk split: left sibling not adjacent");
      let prev = Y.first === NIL ? null : this.Gs[Y.last].lab;
      for (let i = 0; i < unit.length; i++) {
        prev = prev === null ? center : this._after(prev, P.D_g, P.B_g, "group: push-back room");
        labs.push(prev);
      }
    } else {
      if (Z.prev !== x) throw new GuardFailure("chunk split: right sibling not adjacent");
      let nxt = Z.first === NIL ? null : this.Gs[Z.first].lab;
      for (let i = 0; i < unit.length; i++) {
        nxt = nxt === null ? center : this._before(nxt, P.D_g, "group: push-front room");
        labs.push(nxt);
      }
      labs.reverse();
    }
    this.stats.steps += unit.length;
    const first = unit[0], last = unit[unit.length - 1];
    let dst;
    if (left) {
      if (X.last === last) X.first = X.last = NIL; else X.first = this.Gs[last].next;
      if (Y.first === NIL) Y.first = first;
      Y.last = last;
      dst = y;
    } else {
      if (X.first === first) X.first = X.last = NIL; else X.last = this.Gs[first].prev;
      if (Z.first === NIL) Z.last = last;
      Z.first = first;
      dst = z;
    }
    let s = 0;
    unit.forEach((gg, i) => { const Gg = this.Gs[gg]; Gg.chk = dst; Gg.lab = labs[i]; s += Gg.size; });
    X.size -= s;
    this.C[dst].size += s;
    this.emit({ k: "cmove", groups: unit.slice(), from: x, to: dst, family: unit.length === 3 });
    return true;
  }

  _remove_chunk(x) {
    this.stats.steps++;
    const X = this.C[x];
    X.st = DEAD;
    for (const s of [X.l, X.r]) {
      const S = this.C[s];
      if (S.st === OVERFLOW && S.src === x) { S.st = QUIET; S.src = NIL; this.pq.enter_if_above(s); }
    }
    this.emit({ k: "cdone", c: x, l: X.l, r: X.r });
  }

  _reservation(k) {
    for (let i = 0; i < k; i++) {
      this.stats.steps++;
      if (this.res_job === null) {
        if (this.pq.empty()) return;
        this.stats.reservations++;
        const x = this.pq.pop_max();
        if (!(0 <= x && x < this.C.length)) throw new GuardFailure("reservation: invalid chunk");
        const y = this._new_chunk(), z = this._new_chunk();
        const X = this.C[x], Y = this.C[y], Z = this.C[z];
        Y.prev = X.prev; Y.next = x;
        if (X.prev !== NIL) this.C[X.prev].next = y; else this.first_chunk = y;
        X.prev = y;
        Z.prev = x; Z.next = X.next;
        if (X.next !== NIL) this.C[X.next].prev = z;
        X.next = z;
        const job = this.top.insert_around(x, y, z);
        X.st = SPLITTING; X.l = y; X.r = z;
        Y.st = OVERFLOW; Y.src = x;
        Z.st = OVERFLOW; Z.src = x;
        this.res_job = job;
        this.emit({ k: "reserve", x, y, z, size: X.size });
      } else {
        this.res_job.info.steps++;
        if (!this.top.step(this.res_job)) {
          this.emit({ k: "jobdone", x: this.res_job.info.x, steps: this.res_job.info.steps });
          this.res_job = null;
        }
      }
    }
  }

  _fallback(reason) {
    const P = this.P;
    this.stats.fallbacks++;
    this.fallback_reasons.push(reason);
    this.emit({ k: "fallback", reason });
    const seq = [];
    for (let e = this.HEAD; e !== NIL; e = this.E[e].next) seq.push(e);
    this.Gs = []; this.C = []; this.free_g = [];
    this.pq = new BucketPQ(this);
    this.res_job = null;
    const gs = Math.max(1, Math.floor(P.G / 2));
    const gpc = Math.max(1, Math.floor(Math.floor(P.T / 2) / gs));
    const groups = [], chunks = [];
    for (let i = 0; i < seq.length; i += gs) groups.push(seq.slice(i, i + gs));
    for (let i = 0; i < groups.length; i += gpc) chunks.push(groups.slice(i, i + gpc));
    let prev_c = NIL, prev_g = NIL;
    for (const cgroups of chunks) {
      const c = this._new_chunk(), C = this.C[c];
      C.prev = prev_c;
      if (prev_c !== NIL) this.C[prev_c].next = c;
      const step_g = (1n << B(P.B_g)) / B(cgroups.length + 1);
      cgroups.forEach((elems, j) => {
        const g = this._new_group(c), G = this.Gs[g];
        G.lab = B(j + 1) * step_g;
        G.prev = prev_g;
        if (prev_g !== NIL) this.Gs[prev_g].next = g;
        const step_e = (1n << B(P.B_e)) / B(elems.length + 1);
        elems.forEach((el, k) => { this.E[el].grp = g; this.E[el].lab = B(k + 1) * step_e; });
        G.first = elems[0]; G.last = elems[elems.length - 1]; G.size = elems.length;
        if (j === 0) C.first = g;
        C.last = g;
        C.size += elems.length;
        prev_g = g;
      });
      prev_c = c;
    }
    this.first_chunk = 0;
    this.first_group = 0;
    this.top.relabel_all();
  }

  /* -------------------------------------------------------------- inspection */
  elements() {
    const out = [];
    for (let e = this.HEAD; e !== NIL; e = this.E[e].next) out.push(e);
    return out;
  }
  chunks() {
    const out = [];
    for (let c = this.first_chunk; c !== NIL; c = this.C[c].next) out.push(c);
    return out;
  }
  groupsOf(c) {
    const out = [], C = this.C[c];
    if (C.first === NIL) return out;
    for (let g = C.first; ; g = this.Gs[g].next) { out.push(g); if (g === C.last) break; }
    return out;
  }
  elemsOf(g) {
    const out = [], G = this.Gs[g];
    if (G.first === NIL) return out;
    for (let e = G.first; ; e = this.E[e].next) { out.push(e); if (e === G.last) break; }
    return out;
  }
  /* INV-S, derived form: keys strictly increase along the element list. */
  keysSorted() {
    const es = this.elements();
    for (let i = 1; i < es.length; i++) if (!this.order(es[i - 1], es[i])) return false;
    return true;
  }
}

const OM = { NIL, QUIET, OVERFLOW, SPLITTING, DEAD, LEFT, RIGHT, GuardFailure, paramsFor, Core };
if (typeof module !== "undefined" && module.exports) module.exports = OM;
else root.OM = OM;
})(typeof self !== "undefined" ? self : this);
