// Static figures and tables of the tours. Each figure is an inline SVG that takes its colours
// from the theme through the classes of assets/guide.css. The table values come from the same
// module that the interactive examples use, so the build computes them.
import { ringGraph, forestDistribution } from '../site/assets/math-core.mjs';

const round = (value) => Math.round(value * 100) / 100;
const line = (a, b, cls) => `<line x1="${round(a[0])}" y1="${round(a[1])}" x2="${round(b[0])}" y2="${round(b[1])}" class="${cls}"/>`;
const node = (p, cls = 'fig-node', radius = 4.5) => `<circle cx="${round(p[0])}" cy="${round(p[1])}" r="${radius}" class="${cls}"/>`;
const label = (p, text, cls = 'fig-text', anchor = 'middle') => `<text x="${round(p[0])}" y="${round(p[1])}" text-anchor="${anchor}" class="${cls}">${text}</text>`;
const svg = (width, height, title, body) => `<svg viewBox="0 0 ${width} ${height}" role="img" aria-label="${title}">${body}</svg>`;

// A ring of four squares. The marked set P is the top square. One cycle goes around the ring.
function ringMarked() {
  const cx = 190, cy = 158, outer = 124, inner = 74, half = 0.34;
  const at = (angle, radius) => [cx + radius * Math.cos(angle), cy + radius * Math.sin(angle)];
  const tiles = [0, 1, 2, 3].map((i) => {
    const angle = -Math.PI / 2 + i * Math.PI / 2;
    return { a: at(angle - half, outer), b: at(angle - half, inner), c: at(angle + half, outer), d: at(angle + half, inner) };
  });
  const parts = [];
  parts.push(`<ellipse cx="${cx}" cy="${cy - (outer + inner) / 2}" rx="68" ry="44" class="fig-region"/>`);
  tiles.forEach((tile, i) => {
    const next = tiles[(i + 1) % 4];
    for (const [u, v] of [[tile.a, tile.c], [tile.a, tile.d], [tile.b, tile.c], [tile.b, tile.d], [tile.c, next.a], [tile.d, next.b]]) {
      parts.push(line(u, v, 'fig-edge'));
    }
  });
  const [t0, t1, t2, t3] = tiles;
  // The cycle: a0 d0 b0 c0 | a1 c1 | a2 d2 | b3 c3 | back to a0.
  for (const [u, v] of [[t0.a, t0.d], [t0.d, t0.b], [t0.b, t0.c], [t0.c, t1.a], [t3.c, t0.a]]) parts.push(line(u, v, 'fig-warm fig-dash'));
  for (const [u, v] of [[t1.a, t1.c], [t1.c, t2.a], [t2.a, t2.d], [t2.d, t3.b], [t3.b, t3.c]]) parts.push(line(u, v, 'fig-warm'));
  tiles.forEach((tile, i) => {
    for (const p of [tile.a, tile.b, tile.c, tile.d]) parts.push(node(p, i === 0 ? 'fig-node fig-node-marked' : 'fig-node'));
  });
  parts.push(label([cx - 92, cy - (outer + inner) / 2 - 26], 'P', 'fig-text fig-text-accent'));
  return svg(380, 316, 'A ring of four squares. The marked set P is the top square. A cycle goes once around the ring. Its edges that touch P are dashed. Its other edges form a path.', parts.join(''));
}

// A vertex of degree five becomes a path of three vertices.
function splitVertex() {
  const parts = [];
  const v = [96, 86];
  for (const end of [[30, 40], [30, 132]]) parts.push(line(v, end, 'fig-accent'));
  for (const end of [[112, 22], [172, 52], [172, 120]]) parts.push(line(v, end, 'fig-edge'));
  parts.push(node(v));
  parts.push(label([16, 91], 'W', 'fig-text fig-text-accent'));
  parts.push(label([98, 112], 'v', 'fig-text fig-text-math'));
  parts.push(line([200, 86], [240, 86], 'fig-arrow'));
  parts.push('<path d="M246 86 l-10 -5 v10 z" class="fig-arrow-head"/>');
  const v1 = [352, 86], v2 = [428, 86], v3 = [504, 86];
  for (const end of [[296, 40], [296, 132]]) parts.push(line(v1, end, 'fig-accent'));
  parts.push(line(v1, v2, 'fig-warm'), line(v2, v3, 'fig-warm'));
  parts.push(line(v2, [428, 22], 'fig-edge'), line(v3, [560, 48], 'fig-edge'), line(v3, [560, 124], 'fig-edge'));
  parts.push(node(v1, 'fig-node fig-node-marked'), node(v2), node(v3));
  parts.push(label([282, 91], 'W', 'fig-text fig-text-accent'));
  for (const [x, index] of [[352, 1], [428, 2], [504, 3]]) parts.push(label([x, 116], `v<tspan dy="-7" font-size="12">${index}</tspan>`, 'fig-text fig-text-math'));
  return svg(576, 160, 'Left: a vertex v of degree five on two edges of W. Right: a path of three vertices in the place of v. The two edges of W end at the first vertex of the path, and this vertex is put into P.', parts.join(''));
}

// A capped ladder: a chain of a square, a single rung and a square between the caps s and t.
function ladder() {
  const top = 44, bottom = 128, parts = [];
  const pair = (x) => [[x, top], [x, bottom]];
  const s = [36, 86], t = [444, 86];
  const [a, b, c, d, e] = [100, 170, 240, 310, 380].map(pair);
  const square = (left, right) => {
    for (const u of left) for (const w of right) parts.push(line(u, w, 'fig-accent'));
  };
  const interfaceEdges = (left, right) => { parts.push(line(left[0], right[0], 'fig-edge'), line(left[1], right[1], 'fig-edge')); };
  parts.push(line(s, a[0], 'fig-edge'), line(s, a[1], 'fig-edge'));
  square(a, b);
  interfaceEdges(b, c);
  parts.push(line(c[0], c[1], 'fig-warm'));
  interfaceEdges(c, d);
  square(d, e);
  parts.push(line(t, e[0], 'fig-edge'), line(t, e[1], 'fig-edge'));
  for (const p of [s, t, ...a, ...b, ...c, ...d, ...e]) parts.push(node(p));
  parts.push(label([36, 68], 's', 'fig-text fig-text-math'), label([444, 68], 't', 'fig-text fig-text-math'));
  parts.push(label([135, 156], 'square', 'fig-text fig-text-accent'), label([240, 156], 'single rung', 'fig-text fig-text-warm'), label([345, 156], 'square', 'fig-text fig-text-accent'));
  return svg(480, 168, 'A ladder between two ends s and t. It is a chain of a square, a single rung and a square. Two edges join each tile to the next tile.', parts.join(''));
}

// Two large pieces with small boundaries in a graph without short cycles.
function pieces() {
  const parts = [];
  parts.push('<rect x="6" y="14" width="508" height="172" class="fig-frame"/>');
  parts.push('<ellipse cx="62" cy="100" rx="30" ry="22" class="fig-region"/>');
  parts.push(label([62, 105], 'P', 'fig-text fig-text-accent'));
  const piece = (cx, title) => {
    parts.push(`<ellipse cx="${cx}" cy="100" rx="78" ry="52" class="fig-piece"/>`);
    parts.push(label([cx, 96], title, 'fig-text'));
    parts.push(label([cx, 116], 'at most 3/5', 'fig-text fig-text-warm'));
  };
  piece(206, 'piece 1');
  piece(404, 'piece 2');
  for (const [u, w] of [[[92, 100], [128, 100]], [[278, 82], [332, 82]], [[280, 118], [330, 118]], [[206, 48], [206, 26]], [[404, 152], [404, 174]], [[474, 82], [500, 70]]]) {
    parts.push(line(u, w, 'fig-edge'), node(u, 'fig-node', 3.5), node(w, 'fig-node', 3.5));
  }
  return svg(520, 200, 'A graph with a small marked set P and two large pieces. Few edges leave each piece. In each piece the forest proportion is at most three fifths.', parts.join(''));
}

export const figures = {
  'ring-marked': ringMarked,
  'split-vertex': splitVertex,
  ladder,
  pieces,
};

// The proportion q for a ring of k squares, where the marked set is one square.
function ringProportions() {
  const rows = [2, 3, 4, 5, 6].map((squares) => {
    const ring = ringGraph(squares);
    const marked = new Set([...ring.tiles[0].left, ...ring.tiles[0].right]);
    const atMarked = ring.edges.filter(([u, v]) => marked.has(u) || marked.has(v));
    const { favorable, total } = forestDistribution(ring.n, ring.edges, atMarked);
    return `<tr><td>${squares}</td><td>${total.toLocaleString('en-US')}</td><td>${favorable.toLocaleString('en-US')}</td><td>${(favorable / total).toFixed(3)}</td></tr>`;
  });
  return `<div class="table-scroll"><table class="values"><thead><tr><th scope="col">Squares</th><th scope="col">Even subgraphs</th><th scope="col">Outside part is a forest</th><th scope="col">Proportion</th></tr></thead><tbody>${rows.join('')}</tbody></table></div>`;
}

export const tables = {
  'ring-proportions': ringProportions,
};
