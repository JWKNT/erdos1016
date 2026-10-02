import assert from 'node:assert/strict';
import test from 'node:test';
import { mountExplorers } from '../assets/explorers.mjs';

// A small DOM fixture exercises the real input handler without a browser dependency.
// It does not emulate layout, focus, or native number-input validation.
class Node {
  constructor(tag) {
    this.tag = tag;
    this.attributes = new Map();
    this.children = [];
    this.dataset = {};
    this.listeners = new Map();
    this.textContent = '';
    this.value = '';
  }
  setAttribute(name, value) {
    this.attributes.set(name, String(value));
    if (name === 'value') this.value = String(value);
  }
  getAttribute(name) { return this.attributes.get(name) ?? null; }
  removeAttribute(name) { this.attributes.delete(name); }
  get id() { return this.getAttribute('id'); }
  set id(value) { this.setAttribute('id', value); }
  get valueAsNumber() { return this.value.trim() === '' ? NaN : Number(this.value); }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = nodes; }
  addEventListener(type, callback) { this.listeners.set(type, callback); }
  find(predicate) {
    if (predicate(this)) return this;
    for (const child of this.children) {
      const found = child.find(predicate);
      if (found) return found;
    }
  }
}

function logStarFixture() {
  const root = new Node('div');
  root.id = 'logstar-demo';
  const previous = globalThis.document;
  globalThis.document = {
    createElement: (tag) => new Node(tag),
    createElementNS: (_, tag) => new Node(tag),
    getElementById: (id) => root.find((node) => node.id === id),
  };
  mountExplorers();
  return {
    root,
    input: root.find((node) => node.id === 'logstar-number'),
    output: root.find((node) => node.id === 'logstar-output'),
    restore() {
      if (previous === undefined) delete globalThis.document;
      else globalThis.document = previous;
    },
  };
}

test('log-star output preserves the represented input at both sides of every finite threshold', () => {
  const fixture = logStarFixture();
  try {
    const thresholds = [1, 2, 4, 16, 65536];
    const cases = thresholds.flatMap((n) => [n - n * Number.EPSILON, n, n + n * Number.EPSILON]);
    cases.push(Number.MIN_VALUE, 1e100, Number.MAX_VALUE);
    for (const n of cases) {
      fixture.input.value = String(n);
      fixture.input.listeners.get('input')();
      const [, displayed, count] = fixture.output.textContent.match(/^log\*₂\(([^)]+)\) = (\d+)\./);
      assert.equal(Number(displayed.replaceAll(',', '')), n, `Input rounded in output for ${n}`);
      const threshold = thresholds.findIndex((limit) => n <= limit);
      assert.equal(Number(count), threshold < 0 ? 5 : threshold);
      const svg = fixture.root.find((node) => node.tag === 'svg');
      assert.ok(svg.getAttribute('aria-label').includes(`log-star of ${displayed} equals ${count}`));
      if (Number(count) > 0) {
        assert.ok(fixture.output.textContent.includes(Number(count) === 1 ? '1 repeated base-2 logarithm brings n' : `${count} repeated base-2 logarithms bring n`));
        const steps = fixture.root.find((node) => node.textContent.startsWith('Successive values'));
        assert.ok(steps, 'Rounded logarithm steps must be identified as rounded');
        assert.ok(steps.textContent.startsWith(`Successive values (logarithms rounded): ${displayed} → `));
      }
    }
  } finally { fixture.restore(); }
});

test('log-star invalid input clears the diagram and a threshold preset recovers it', () => {
  const fixture = logStarFixture();
  try {
    for (const value of ['', '0', '-1', '1e309']) {
      fixture.input.value = value;
      fixture.input.listeners.get('input')();
      assert.equal(fixture.input.getAttribute('aria-invalid'), 'true');
      assert.equal(fixture.output.textContent, 'Enter a finite number greater than 0.');
      assert.equal(fixture.root.find((node) => node.tag === 'svg'), undefined);
    }
    fixture.root.find((node) => node.tag === 'button' && node.textContent === '65,536').listeners.get('click')();
    assert.equal(fixture.input.getAttribute('aria-invalid'), null);
    assert.match(fixture.output.textContent, /^log\*₂\(65,536\) = 4\./);
    assert.ok(fixture.root.find((node) => node.tag === 'svg'));
  } finally { fixture.restore(); }
});
