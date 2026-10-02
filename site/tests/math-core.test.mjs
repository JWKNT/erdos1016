import test from 'node:test';
import assert from 'node:assert/strict';
import {
  edgeKey, normalizeEdges, graphStats, edgeDegrees, isEvenEdgeSet, isForest,
  isSimpleCycle, enumerateSimpleCycles, cycleEdges, xorEdgeSets, cycleBasis,
  enumerateEvenSets, forestDistribution, binaryConstruction, logStar,
  logStarSteps, secondMomentBound, idealizedRecurrence, thetaCutDistribution, analyzeWalk,
} from '../assets/math-core.mjs';

const allEdges = (n) => Array.from({ length: n }, (_, u) =>
  Array.from({ length: n - u - 1 }, (_, offset) => [u, u + offset + 1])).flat();
const fromMask = (edges, mask) => edges.filter((_, i) => Boolean(mask & 2 ** i));
const wordKey = (edges) => edges.map(edgeKey).sort().join(',');
const completeSix = allEdges(6);
const sixEdgeIndex = new Map(completeSix.map((edge, i) => [edgeKey(edge), i]));
const sixMask = (edges) => edges.reduce((mask, edge) => mask | 2 ** sixEdgeIndex.get(edgeKey(edge)), 0);
const bowTie = [[0, 1], [1, 2], [2, 0], [0, 3], [3, 4], [4, 0]];
const left = [[0, 1], [1, 2], [2, 0]];
const right = [[3, 4], [4, 5], [5, 3]];
const bridgeGraph = [...left, ...right, [2, 3]];

// Independent bit-mask oracle: degree-two vertices and one connected component.
function isCycleMask(mask, edges, n) {
  const degrees = Array(n).fill(0);
  const adjacency = Array.from({ length: n }, () => []);
  for (let i = 0; i < edges.length; i++) if (mask & 2 ** i) {
    const [u, v] = edges[i];
    degrees[u]++; degrees[v]++;
    adjacency[u].push(v); adjacency[v].push(u);
  }
  const vertices = degrees.flatMap((degree, i) => degree ? [i] : []);
  if (vertices.length < 3 || degrees.some((degree) => degree !== 0 && degree !== 2)) return false;
  const seen = new Set([vertices[0]]), queue = [vertices[0]];
  for (const u of queue) for (const v of adjacency[u]) if (!seen.has(v)) { seen.add(v); queue.push(v); }
  return seen.size === vertices.length;
}

function bruteEvenSets(n, edges) {
  const results = [];
  for (let mask = 0; mask < 2 ** edges.length; mask++) {
    const parity = Array(n).fill(0);
    for (let i = 0; i < edges.length; i++) if (mask & 2 ** i) {
      const [u, v] = edges[i]; parity[u] ^= 1; parity[v] ^= 1;
    }
    if (parity.every((p) => p === 0)) results.push(wordKey(fromMask(edges, mask)));
  }
  return results.sort();
}

test('normalization, graph statistics and validation', () => {
  assert.deepEqual(normalizeEdges(3, [[2, 0], [0, 2], [2, 1]]), [[0, 2], [1, 2]]);
  assert.deepEqual(graphStats(6, bridgeGraph), { vertices: 6, edges: 7, components: 1, excess: 1, rank: 2 });
  assert.deepEqual(graphStats(7, [...left, ...right]), { vertices: 7, edges: 6, components: 3, excess: -1, rank: 2 });
  assert.deepEqual(graphStats(0, []), { vertices: 0, edges: 0, components: 0, excess: 0, rank: 0 });
  assert.throws(() => normalizeEdges(3, [[1, 1]]), RangeError);
  assert.throws(() => normalizeEdges(3, [[0, 3]]), RangeError);
  assert.throws(() => normalizeEdges(3, [[0, 1.5]]), RangeError);
  assert.throws(() => normalizeEdges(3, [[1]]), TypeError);
  assert.throws(() => normalizeEdges(-1, []), RangeError);
  assert.throws(() => enumerateSimpleCycles(9, []), RangeError);
});

test('familiar graphs have the expected cycle counts and lengths', () => {
  const c6 = cycleEdges([0, 1, 2, 3, 4, 5]);
  assert.deepEqual(enumerateSimpleCycles(6, c6), [[0, 1, 2, 3, 4, 5]]);
  assert.equal(enumerateSimpleCycles(5, bowTie).length, 2);
  assert.equal(enumerateSimpleCycles(6, bridgeGraph).length, 2);
  const counts = enumerateSimpleCycles(6, completeSix).reduce((result, cycle) => {
    result[cycle.length] = (result[cycle.length] || 0) + 1;
    return result;
  }, {});
  assert.deepEqual(counts, { 3: 20, 4: 45, 5: 72, 6: 60 });
  assert.equal(enumerateSimpleCycles(6, completeSix).length, 197);
  assert.deepEqual(enumerateSimpleCycles(6, [[0, 1], [1, 2], [2, 3]]), []);
});

test('cycle enumeration matches an independent oracle for all 32,768 simple six-vertex graphs', () => {
  const cycleMasks = [];
  for (let mask = 0; mask < 2 ** completeSix.length; mask++) {
    if (isCycleMask(mask, completeSix, 6)) cycleMasks.push(mask);
  }
  assert.equal(cycleMasks.length, 197);
  for (let graph = 0; graph < 2 ** completeSix.length; graph++) {
    const expected = cycleMasks.filter((cycle) => (cycle & graph) === cycle);
    const actual = enumerateSimpleCycles(6, fromMask(completeSix, graph))
      .map((vertices) => sixMask(cycleEdges(vertices))).sort((a, b) => a - b);
    assert.deepEqual(actual, expected, `Cycle set mismatch for graph mask ${graph}`);
  }
});

test('cycle bases span exactly the even words for every simple graph on five vertices', () => {
  const edges = allEdges(5);
  for (let mask = 0; mask < 2 ** edges.length; mask++) {
    const graph = fromMask(edges, mask);
    const basis = cycleBasis(5, graph);
    assert.equal(basis.length, graphStats(5, graph).rank);
    basis.forEach((cycle) => assert.equal(isSimpleCycle(5, cycle), true));
    const words = enumerateEvenSets(5, graph);
    assert.equal(words.length, 2 ** basis.length);
    assert.equal(new Set(words.map(wordKey)).size, words.length);
    assert.deepEqual(words.map(wordKey).sort(), bruteEvenSets(5, graph), `Even-word mismatch for graph mask ${mask}`);
  }
});

test('the bow tie illustrates that even words need not be simple cycles', () => {
  const basis = cycleBasis(5, bowTie);
  assert.equal(basis.length, 2);
  const both = xorEdgeSets(...basis);
  assert.equal(both.length, 6);
  assert.equal(isEvenEdgeSet(5, both), true);
  assert.equal(isSimpleCycle(5, both), false);
  assert.deepEqual(edgeDegrees(5, both), [4, 2, 2, 2, 2]);
  assert.deepEqual(xorEdgeSets(basis[0], basis[0]), []);
  assert.equal(isEvenEdgeSet(5, []), true);
  assert.equal(isSimpleCycle(5, []), false);
  assert.equal(isForest(5, []), true);
  assert.equal(isForest(5, basis[0]), false);
});

test('forest restriction uses the uniform ambient even-set distribution', () => {
  const distribution = forestDistribution(6, bridgeGraph, left);
  assert.equal(distribution.total, 4);
  assert.equal(distribution.favorable, 2);
  assert.equal(distribution.probability, 0.5);
  assert.deepEqual(distribution.words.map(({ forest }) => forest), [true, true, false, false]);
  assert.deepEqual(distribution.words.map(({ outside }) => outside.length), [0, 0, 3, 3]);
  assert.equal(distribution.words.some(({ word }) => word.some((edge) => edgeKey(edge) === '2-3')), false);
  const counts = new Map();
  for (const { outside } of distribution.words) counts.set(wordKey(outside), (counts.get(wordKey(outside)) || 0) + 1);
  assert.deepEqual([...counts.values()], [2, 2]);
  assert.throws(() => forestDistribution(6, bridgeGraph, [[0, 5]]), RangeError);
});

test('binary shortcuts bijectively produce every integer in the promised interval', () => {
  for (let k = 1; k <= 10; k++) {
    const lengths = [];
    for (let mask = 0; mask < 2 ** k; mask++) {
      const construction = binaryConstruction(k, mask);
      assert.equal(construction.saving, mask);
      assert.equal(construction.length, 2 ** k + k - mask);
      assert.equal(construction.min, k + 1);
      assert.equal(construction.max, 2 ** k + k);
      lengths.push(construction.length);
    }
    assert.deepEqual(lengths.sort((a, b) => a - b), Array.from({ length: 2 ** k }, (_, i) => k + 1 + i));
  }
  assert.deepEqual(binaryConstruction(4, 0).segments.map(({ originalLength }) => originalLength), [2, 3, 5, 9]);
  assert.equal(binaryConstruction(4, 0).length, 20);
  assert.equal(binaryConstruction(4, 15).length, 5);
  assert.throws(() => binaryConstruction(0), RangeError);
  assert.throws(() => binaryConstruction(4, 16), RangeError);
  assert.throws(() => binaryConstruction(4, -1), RangeError);
});

test('base-two log-star classifies exact thresholds and their adjacent representable values', () => {
  const cases = [
    [Number.MIN_VALUE, 0], [0.5, 0], [1, 0], [1 + Number.EPSILON, 1],
    [2 - Number.EPSILON, 1], [2, 1], [2 + 2 * Number.EPSILON, 2],
    [4 - 2 * Number.EPSILON, 2], [4, 2], [4 + 4 * Number.EPSILON, 3],
    [16 - 8 * Number.EPSILON, 3], [16, 3], [16 + 16 * Number.EPSILON, 4],
    [65536 - 32768 * Number.EPSILON, 4], [65536, 4], [65536 + 65536 * Number.EPSILON, 5],
    [1e100, 5], [Number.MAX_VALUE, 5],
  ];
  for (const [n, expected] of cases) assert.equal(logStar(n), expected, `logStar(${n})`);
  assert.deepEqual(logStarSteps(65536), { count: 4, values: [65536, 16, 4, 2, 1], roundedBoundary: false });
  assert.deepEqual(logStarSteps(1), { count: 0, values: [1], roundedBoundary: false });
  for (const n of [0, -1, Infinity, -Infinity, NaN]) assert.throws(() => logStar(n), RangeError);
});

test('second-moment upper bounds approach one half monotonically', () => {
  assert.equal(secondMomentBound(1), 2 / 3);
  assert.equal(secondMomentBound(10), 0.5 + 1 / 42);
  assert.equal(secondMomentBound(100), 0.5 + 1 / 402);
  assert.equal(secondMomentBound(20, 0), 0.5);
  let previous = 1;
  for (let mu = 1; mu <= 100; mu++) {
    const bound = secondMomentBound(mu);
    assert.ok(bound > 0.5 && bound < previous);
    assert.ok(Math.abs(bound - (1 - mu ** 2 / (2 * mu ** 2 + mu))) < 1e-14);
    previous = bound;
  }
  for (const mu of [0, -1, Infinity, NaN]) assert.throws(() => secondMomentBound(mu), RangeError);
  assert.throws(() => secondMomentBound(10, -1), RangeError);
});

test('the recurrence is explicitly an idealized halving and tower-level proxy', () => {
  for (let steps = 0; steps <= 8; steps++) {
    assert.deepEqual(idealizedRecurrence(steps), { steps, phi: 2 ** -steps, denominator: 2 ** steps, towerLevelIncrement: steps });
  }
  for (const steps of [-1, 9, 1.5, NaN]) assert.throws(() => idealizedRecurrence(steps), RangeError);
});

test('the UI module imports without a browser or third-party dependencies', async () => {
  const { mountExplorers } = await import('../assets/explorers.mjs');
  assert.equal(typeof mountExplorers, 'function');
});

test('theta links give exact zero-cut marginals, joint probabilities and correlation', () => {
  for (let links = 1; links <= 4; links++) {
    const distribution = thetaCutDistribution(links);
    assert.equal(distribution.total, 2 ** (links - 1));
    assert.equal(graphStats(distribution.n, distribution.edges).rank, links - 1);
    assert.deepEqual(distribution.words.map(({ word }) => wordKey(word)).sort(), bruteEvenSets(distribution.n, distribution.edges));
    assert.equal(distribution.countA, 1);
    assert.equal(distribution.countB, 1);
    assert.equal(distribution.countBoth, 1);
    assert.equal(distribution.probabilityA, 2 ** (1 - links));
    assert.equal(distribution.probabilityB, 2 ** (1 - links));
    assert.equal(distribution.probabilityBoth, 2 ** (1 - links));
    assert.equal(distribution.correlationRatio, 2 ** (links - 1));
    for (const { word, selectedPaths, zeroA, zeroB } of distribution.words) {
      assert.equal(selectedPaths.length % 2, 0);
      assert.equal(word.length, selectedPaths.length * 2);
      assert.equal(zeroA, word.length === 0);
      assert.equal(zeroB, word.length === 0);
    }
  }
  for (const links of [0, 5, 2.5, NaN]) assert.throws(() => thetaCutDistribution(links), RangeError);
});

test('walk analysis separates closed nonbacktracking walks from simple cycles', () => {
  const figureEight = analyzeWalk(5, bowTie, [0, 1, 2, 0, 3, 4, 0]);
  assert.equal(figureEight.length, 6);
  assert.equal(figureEight.closed, true);
  assert.equal(figureEight.nonbacktracking, true);
  assert.equal(figureEight.cyclicallyNonbacktracking, true);
  assert.equal(figureEight.closureBacktracks, false);
  assert.equal(figureEight.simpleCycle, false);
  assert.deepEqual(figureEight.repeatedVertices, [0]);
  const triangle = analyzeWalk(5, bowTie, [0, 1, 2, 0]);
  assert.equal(triangle.cyclicallyNonbacktracking, true);
  assert.equal(triangle.simpleCycle, true);
  assert.deepEqual(triangle.repeatedVertices, []);
  const backtracking = analyzeWalk(5, bowTie, [0, 1, 0, 3, 4, 0]);
  assert.deepEqual(backtracking.reversals, [1]);
  assert.equal(backtracking.nonbacktracking, false);
  assert.equal(backtracking.cyclicallyNonbacktracking, false);
  const seamOnly = analyzeWalk(5, bowTie, [1, 0, 3, 4, 0, 1]);
  assert.equal(seamOnly.nonbacktracking, true);
  assert.equal(seamOnly.closureBacktracks, true);
  assert.equal(seamOnly.cyclicallyNonbacktracking, false);
  assert.equal(seamOnly.simpleCycle, false);
  const open = analyzeWalk(5, bowTie, [0, 1, 2]);
  assert.equal(open.closed, false);
  assert.equal(open.cyclicallyNonbacktracking, false);
  assert.equal(analyzeWalk(5, bowTie, [0]).length, 0);
  assert.throws(() => analyzeWalk(5, bowTie, []), RangeError);
  assert.throws(() => analyzeWalk(5, bowTie, [0, 1, 4]), RangeError);
  assert.throws(() => analyzeWalk(5, bowTie, [0, 5]), RangeError);
});

test('XOR cancellation and restriction can leave an odd-degree forest', () => {
  const first = [[0, 1], [1, 2], [2, 0]];
  const second = [[0, 2], [2, 3], [3, 0]];
  const witness = new Set(first.map(edgeKey));
  const both = xorEdgeSets(first, second);
  assert.equal(both.length, 4);
  assert.equal(both.some((edge) => edgeKey(edge) === '0-2'), false);
  assert.equal(isSimpleCycle(4, both), true);
  const outside = both.filter((edge) => !witness.has(edgeKey(edge)));
  assert.deepEqual(outside, [[0, 3], [2, 3]]);
  assert.deepEqual(edgeDegrees(4, outside), [1, 0, 1, 2]);
  assert.equal(isEvenEdgeSet(4, outside), false);
  assert.equal(isForest(4, outside), true);
  for (let mask = 0; mask < 4; mask++) {
    const word = xorEdgeSets(mask & 1 ? first : [], mask & 2 ? second : []);
    assert.equal(isEvenEdgeSet(4, word), true);
    assert.equal(isForest(4, word.filter((edge) => !witness.has(edgeKey(edge)))), true);
  }
});
