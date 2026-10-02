/** Small, exact finite-graph calculations for the illustrated proof guide.
 * No proof statements are inferred from these examples. Graphs are simple.
 */
export const edgeKey = ([u, v]) => u < v ? `${u}-${v}` : `${v}-${u}`;

export function normalizeEdges(n, edges) {
  if (!Number.isInteger(n) || n < 0 || n > 32) throw new RangeError('Use 0–32 vertices.');
  const unique = new Map();
  for (const pair of edges) {
    if (!Array.isArray(pair) || pair.length !== 2) throw new TypeError('An edge needs two endpoints.');
    const [u, v] = pair;
    if (!Number.isInteger(u) || !Number.isInteger(v) || u < 0 || v < 0 || u >= n || v >= n || u === v) {
      throw new RangeError('Edges must join two distinct vertices of the graph.');
    }
    unique.set(edgeKey(pair), u < v ? [u, v] : [v, u]);
  }
  return [...unique.values()].sort((a, b) => a[0] - b[0] || a[1] - b[1]);
}

function disjointSets(n) {
  const parents = Array.from({ length: n }, (_, i) => i);
  const find = (x) => {
    while (parents[x] !== x) { parents[x] = parents[parents[x]]; x = parents[x]; }
    return x;
  };
  const join = (u, v) => {
    const a = find(u), b = find(v);
    if (a === b) return false;
    parents[a] = b;
    return true;
  };
  return { find, join };
}

export function graphStats(n, inputEdges) {
  const edges = normalizeEdges(n, inputEdges);
  const sets = disjointSets(n);
  let components = n;
  for (const [u, v] of edges) if (sets.join(u, v)) components--;
  return { vertices: n, edges: edges.length, components, excess: edges.length - n,
    rank: edges.length - n + components };
}

export function edgeDegrees(n, edges) {
  const degrees = Array(n).fill(0);
  for (const [u, v] of normalizeEdges(n, edges)) { degrees[u]++; degrees[v]++; }
  return degrees;
}

export function isEvenEdgeSet(n, edges) {
  return edgeDegrees(n, edges).every((degree) => degree % 2 === 0);
}

export function isForest(n, edges) {
  const sets = disjointSets(n);
  for (const [u, v] of normalizeEdges(n, edges)) if (!sets.join(u, v)) return false;
  return true;
}

export function isSimpleCycle(n, inputEdges) {
  const edges = normalizeEdges(n, inputEdges);
  if (edges.length < 3) return false;
  const degrees = edgeDegrees(n, edges);
  if (!degrees.every((d) => d === 0 || d === 2)) return false;
  const sets = disjointSets(n);
  edges.forEach(([u, v]) => sets.join(u, v));
  return new Set(degrees.flatMap((d, v) => d ? [sets.find(v)] : [])).size === 1;
}

/** Each undirected cycle occurs once: minimum vertex first, orientation canonical. */
export function enumerateSimpleCycles(n, inputEdges) {
  if (n > 8) throw new RangeError('Cycle enumeration is bounded to eight vertices.');
  const edges = normalizeEdges(n, inputEdges);
  const adjacency = Array.from({ length: n }, () => []);
  edges.forEach(([u, v]) => { adjacency[u].push(v); adjacency[v].push(u); });
  const cycles = [];
  for (let start = 0; start < n; start++) {
    const used = new Set([start]);
    const path = [start];
    function walk(vertex) {
      for (const next of adjacency[vertex]) {
        if (next === start && path.length >= 3 && path[1] < path[path.length - 1]) {
          cycles.push([...path]);
        } else if (next > start && !used.has(next)) {
          used.add(next); path.push(next); walk(next); path.pop(); used.delete(next);
        }
      }
    }
    walk(start);
  }
  return cycles.sort((a, b) => a.length - b.length || a.join(',').localeCompare(b.join(',')));
}

export function cycleEdges(vertices) {
  if (vertices.length < 3) throw new RangeError('A simple cycle needs at least three vertices.');
  return vertices.map((v, i) => [v, vertices[(i + 1) % vertices.length]]);
}

export function xorEdgeSets(...edgeSets) {
  const result = new Map();
  for (const edges of edgeSets) for (const edge of edges) {
    const key = edgeKey(edge);
    if (result.has(key)) result.delete(key);
    else result.set(key, [...edge].sort((a, b) => a - b));
  }
  return [...result.values()].sort((a, b) => a[0] - b[0] || a[1] - b[1]);
}

/** Fundamental cycles relative to a spanning forest; valid also when disconnected. */
export function cycleBasis(n, inputEdges) {
  const edges = normalizeEdges(n, inputEdges);
  const sets = disjointSets(n);
  const tree = Array.from({ length: n }, () => []);
  const chords = [];
  for (const [u, v] of edges) {
    if (sets.join(u, v)) { tree[u].push(v); tree[v].push(u); }
    else chords.push([u, v]);
  }
  return chords.map(([u, v]) => {
    const previous = Array(n).fill(-1);
    previous[u] = u;
    const queue = [u];
    for (let head = 0; head < queue.length && previous[v] < 0; head++) {
      for (const next of tree[queue[head]]) if (previous[next] < 0) {
        previous[next] = queue[head]; queue.push(next);
      }
    }
    const cycle = [[u, v]];
    for (let at = v; at !== u; at = previous[at]) cycle.push([at, previous[at]]);
    return normalizeEdges(n, cycle);
  });
}

export function enumerateEvenSets(n, edges) {
  const basis = cycleBasis(n, edges);
  if (basis.length > 16) throw new RangeError('Even-set enumeration is bounded to rank 16.');
  return Array.from({ length: 2 ** basis.length }, (_, mask) =>
    xorEdgeSets(...basis.filter((_, i) => (mask & (2 ** i)) !== 0)));
}

export function forestDistribution(n, edges, witnessEdges) {
  const witness = new Set(normalizeEdges(n, witnessEdges).map(edgeKey));
  const ambient = new Set(normalizeEdges(n, edges).map(edgeKey));
  if ([...witness].some((key) => !ambient.has(key))) throw new RangeError('The witness must lie in the graph.');
  const words = enumerateEvenSets(n, edges).map((word) => {
    const outside = word.filter((edge) => !witness.has(edgeKey(edge)));
    return { word, outside, forest: isForest(n, outside) };
  });
  const favorable = words.filter((word) => word.forest).length;
  return { words, favorable, total: words.length, probability: favorable / words.length };
}

export function binaryConstruction(k, shortcutMask = 0) {
  if (!Number.isInteger(k) || k < 1 || k > 16) throw new RangeError('Use 1–16 binary segments.');
  if (!Number.isInteger(shortcutMask) || shortcutMask < 0 || shortcutMask >= 2 ** k) throw new RangeError('Invalid shortcut choices.');
  const segments = Array.from({ length: k }, (_, i) => ({ index: i,
    saving: 2 ** i, originalLength: 2 ** i + 1, shortcut: (shortcutMask & (2 ** i)) !== 0 }));
  const length = 1 + segments.reduce((sum, s) => sum + (s.shortcut ? 1 : s.originalLength), 0);
  return { k, segments, length, min: k + 1, max: 2 ** k + k, saving: 2 ** k + k - length };
}

/** Exact threshold definition for the finite, representable input (no log-rounding errors). */
export function logStar(n) {
  if (!Number.isFinite(n) || n <= 0) throw new RangeError('Enter a finite positive number.');
  const finiteTowers = [1, 2, 4, 16, 65536];
  for (let k = 0; k < finiteTowers.length; k++) if (n <= finiteTowers[k]) return k;
  // The next threshold is 2^65536, far above Number.MAX_VALUE.
  return 5;
}

export function logStarSteps(n) {
  const count = logStar(n);
  const values = [n];
  while (values[values.length - 1] > 1 && values.length <= 6) {
    values.push(Math.log2(values[values.length - 1]));
  }
  return { count, values, roundedBoundary: values.length - 1 !== count };
}

/** The Cauchy–Schwarz upper bound, conditional on E[Z²] ≤ 2μ² + Kμ. */
export function secondMomentBound(mu, K = 1) {
  if (!Number.isFinite(mu) || mu <= 0) throw new RangeError('The mean must be finite and positive.');
  if (!Number.isFinite(K) || K < 0) throw new RangeError('K must be finite and nonnegative.');
  return 0.5 + K / (4 * mu + 2 * K);
}

/** An illustration only: it deliberately omits the theorem's error terms. */
export function idealizedRecurrence(steps) {
  if (!Number.isInteger(steps) || steps < 0 || steps > 8) throw new RangeError('Use 0–8 idealized steps.');
  return { steps, phi: 2 ** -steps, denominator: 2 ** steps, towerLevelIncrement: steps };
}

/** ℓ internally disjoint length-two paths from A={0} to B={1}. */
export function thetaCutDistribution(links) {
  if (!Number.isInteger(links) || links < 1 || links > 4) throw new RangeError('Use 1–4 links.');
  const paths = Array.from({ length: links }, (_, i) => [[0, i + 2], [i + 2, 1]]);
  const edges = paths.flat();
  const n = links + 2;
  const words = enumerateEvenSets(n, edges).map((word) => {
    const keys = new Set(word.map(edgeKey));
    return {
      word,
      selectedPaths: paths.flatMap((path, i) => path.every((edge) => keys.has(edgeKey(edge))) ? [i] : []),
      zeroA: !word.some(([u, v]) => u === 0 || v === 0),
      zeroB: !word.some(([u, v]) => u === 1 || v === 1),
    };
  });
  const total = words.length;
  const countA = words.filter(({ zeroA }) => zeroA).length;
  const countB = words.filter(({ zeroB }) => zeroB).length;
  const countBoth = words.filter(({ zeroA, zeroB }) => zeroA && zeroB).length;
  const probabilityA = countA / total, probabilityB = countB / total, probabilityBoth = countBoth / total;
  return { links, n, paths, edges, words, total, countA, countB, countBoth,
    probabilityA, probabilityB, probabilityBoth,
    correlationRatio: probabilityBoth / (probabilityA * probabilityB) };
}

/** Ordinary and cyclic nonbacktracking are different tests at the closing seam. */
export function analyzeWalk(n, inputEdges, vertices) {
  const edges = normalizeEdges(n, inputEdges);
  const available = new Set(edges.map(edgeKey));
  if (!Array.isArray(vertices) || !vertices.length || vertices.some((v) => !Number.isInteger(v) || v < 0 || v >= n)) {
    throw new RangeError('A walk needs vertices of the graph.');
  }
  const walkedEdges = vertices.slice(1).map((v, i) => [vertices[i], v]);
  if (walkedEdges.some((edge) => !available.has(edgeKey(edge)))) throw new RangeError('Every step must follow an edge.');
  const reversals = [];
  for (let i = 1; i < vertices.length - 1; i++) if (vertices[i - 1] === vertices[i + 1]) reversals.push(i);
  const closed = vertices.length > 1 && vertices[0] === vertices[vertices.length - 1];
  const closureBacktracks = closed && vertices[1] === vertices[vertices.length - 2];
  const interior = closed ? vertices.slice(0, -1) : vertices;
  const counts = new Map();
  for (const v of interior) counts.set(v, (counts.get(v) || 0) + 1);
  const repeatedVertices = [...counts].filter(([, count]) => count > 1).map(([v]) => v);
  const nonbacktracking = reversals.length === 0;
  return { vertices: [...vertices], walkedEdges, length: walkedEdges.length, closed,
    reversals, closureBacktracks, nonbacktracking,
    cyclicallyNonbacktracking: closed && nonbacktracking && !closureBacktracks,
    repeatedVertices,
    simpleCycle: closed && walkedEdges.length >= 3 && repeatedVertices.length === 0 };
}
