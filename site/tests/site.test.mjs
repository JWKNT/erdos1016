import assert from 'node:assert/strict';
import test from 'node:test';
import { readFile, access } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { ringGraph, forestDistribution, horakKim } from '../assets/math-core.mjs';

const site = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const repo = resolve(site, '..');
const read = (path) => readFile(resolve(site, path), 'utf8');

// The three tours, by their folder below the site root. The Erdős 1016 tour is the root page,
// because other sites link the address jehlp.net/erdos1016. `paper` is the file in site/papers,
// `source` is its place in the repository.
const TOURS = {
  '': {
    title: 'Erdős 1016', stops: 10, demos: ['graph', 'binary', 'logstar', 'restriction', 'recurrence'],
    paper: 'pancyclic.pdf', pages: 7, source: 'paper/minimal/pancyclic/pancyclic.pdf',
  },
  forest: {
    title: 'Forest Estimate', stops: 11, demos: ['space', 'forest', 'cut', 'moment', 'walk'],
    paper: 'forest.pdf', pages: 12, source: 'paper/minimal/forest/forest.pdf',
  },
  'exact-maximums': {
    title: 'Exact Maximums', stops: 10, demos: ['ring'],
    paper: 'exact-maximum.pdf', pages: 36, source: 'paper/minimal/exact-maximum/exact-maximum.pdf',
  },
};
const PAGE_COUNT = Object.fromEntries(Object.values(TOURS).map(({ paper, pages }) => [paper, pages]));
const slugs = Object.keys(TOURS);
const prefix = (slug) => (slug ? '../' : '');
const name = (slug) => slug || 'root page';
const html = Object.fromEntries(await Promise.all(slugs.map(async (slug) => [slug, await read(slug ? `${slug}/index.html` : 'index.html')])));
const everyPage = slugs.map((slug) => [slug, html[slug]]);
const sections = (page) => [...page.matchAll(/<section id="([\w-]+)">([\s\S]*?)<\/section>/g)].map(([, id, body]) => ({ id, body }));
const text = (fragment) => fragment.replace(/<[^>]+>/g, '');

test('each tour has its numbered stops, unique IDs and working internal navigation', () => {
  for (const slug of slugs) {
    const page = html[slug];
    const ids = [...page.matchAll(/\bid="([^"]+)"/g)].map((m) => m[1]);
    assert.equal(ids.length, new Set(ids).size, `${name(slug)}: repeated id`);
    const numbers = [...page.matchAll(/<h2><span class="chapter-number">(\d+)<\/span>/g)].map((m) => Number(m[1]));
    assert.deepEqual(numbers, Array.from({ length: TOURS[slug].stops }, (_, i) => i + 1), name(slug));
    const listed = [...page.match(/<aside id="contents"[\s\S]*?<\/aside>/)[0].matchAll(/href="#([\w-]+)"/g)].map((m) => m[1]);
    assert.equal(listed.length, TOURS[slug].stops, `${name(slug)}: the contents list every stop`);
    for (const [, id] of page.matchAll(/href="#([^"]+)"/g)) assert.ok(ids.includes(id), `${name(slug)}: unknown anchor ${id}`);
    // The lead states the number of stops in words.
    const words = ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten', 'eleven', 'twelve'];
    assert.ok(page.includes(`The tour has ${words[TOURS[slug].stops]} stops.`), `${name(slug)}: number of stops in the lead`);
    // A reference to a stop by number names a stop that exists.
    for (const [, n] of text(page).matchAll(/\b[Ss]top (\d+)\b/g)) assert.ok(Number(n) >= 1 && Number(n) <= TOURS[slug].stops, `${name(slug)}: stop ${n}`);
  }
});

test('each stop starts with one first sentence and ends with a link to its place in the paper', () => {
  for (const slug of slugs) {
    const stops = sections(html[slug]).filter(({ body }) => body.includes('class="chapter-number"'));
    assert.equal(stops.length, TOURS[slug].stops, name(slug));
    for (const { id, body } of stops) {
      assert.equal((body.match(/class="stop-sentence"/g) || []).length, 1, `${name(slug)}#${id}: one first sentence`);
      assert.match(body, /<\/h2>\s*<p class="stop-sentence">/, `${name(slug)}#${id}: the first sentence follows the heading`);
      assert.match(body, /<p class="in-paper">[\s\S]*<\/p>\s*$/, `${name(slug)}#${id}: the stop ends with the link to the paper`);
      assert.ok(body.includes(`href="${prefix(slug)}papers/${TOURS[slug].paper}#page=`), `${name(slug)}#${id}: link to its own paper`);
    }
  }
});

test('every link to a paper names a file and a page that exist', async () => {
  let links = 0;
  for (const [slug, page] of everyPage) {
    for (const [, file, pageNumber] of page.matchAll(/href="(?:\.\.\/)?papers\/([\w.-]+)(?:#page=(\d+))?"/g)) {
      links += 1;
      assert.ok(Object.hasOwn(PAGE_COUNT, file), `${name(slug)}: unknown paper ${file}`);
      if (pageNumber !== undefined) assert.ok(Number(pageNumber) >= 1 && Number(pageNumber) <= PAGE_COUNT[file], `${file} has no page ${pageNumber}`);
    }
  }
  assert.ok(links >= 60, `only ${links} links to the papers`);
  for (const slug of slugs) {
    const header = html[slug].match(/<header\b[\s\S]*?<\/header>/)[0];
    assert.ok(header.includes(`href="${prefix(slug)}papers/${TOURS[slug].paper}">Paper</a>`), `${name(slug)}: the header links the paper`);
    assert.ok(html[slug].includes(`PDF, ${TOURS[slug].pages} pages`), `${name(slug)}: the lead gives the length of the paper`);
  }
});

test('the published papers are the papers of the repository', async () => {
  for (const { paper, source } of Object.values(TOURS)) {
    const pdf = await readFile(resolve(site, 'papers', paper));
    assert.equal(pdf.subarray(0, 5).toString(), '%PDF-');
    assert.deepEqual(pdf, await readFile(resolve(repo, source)), `${paper} differs from ${source}`);
  }
  // The first manuscript of September 2026 stays at its address.
  assert.ok(html[''].includes('href="paper.pdf"'));
  assert.deepEqual(await readFile(resolve(site, 'paper.pdf')), await readFile(resolve(repo, 'paper/erdos1016.pdf')));
});

test('local linked resources exist; no external runtime dependencies', async () => {
  for (const [slug, page] of everyPage) {
    for (const [, url] of page.matchAll(/(?:src|href)="([^"]+)"/g)) {
      if (url.startsWith('#') || url.startsWith('https://')) continue;
      const target = url.split(/[?#]/)[0];
      await access(resolve(site, slug, target.endsWith('/') ? `${target}index.html` : target));
    }
    // Scripts, style sheets and the icon are local files. The canonical address is not a resource.
    for (const [tag] of page.matchAll(/<script[^>]*src="[^"]+"[^>]*>|<link[^>]*rel="(?:stylesheet|icon)"[^>]*>|<img[^>]*>/g)) {
      assert.doesNotMatch(tag, /(?:src|href)="(?:https?:)?\/\//, `${name(slug)}: external resource in ${tag}`);
    }
  }
});

test('every page has the identity header, a canonical address under /erdos1016/ and no footer', () => {
  for (const [slug, page] of everyPage) {
    const label = name(slug);
    assert.match(page, /^<!doctype html>\n<html lang="en">/, label);
    assert.match(page, /name="viewport"/, label);
    assert.match(page, /<a class="skip-link" href="#main">/, label);
    assert.ok(page.includes(`<link rel="canonical" href="https://jehlp.net/erdos1016/${slug ? `${slug}/` : ''}">`), `${label}: canonical`);
    const header = page.match(/<header class="site-header site-header--identity">[\s\S]*?<\/header>/)[0];
    assert.match(header, /<img class="site-mark" src="[^"]*assets\/mark\.png" alt="" width="32" height="32">/, label);
    assert.match(header, /<a class="site-home" aria-label="Home — jehlp.net" href="https:\/\/jehlp\.net\/">/, label);
    assert.match(header, /<button type="button" data-theme-toggle="" class="theme-toggle"/, label);
    assert.doesNotMatch(header, /github\.com|href="#contents"/, label);
    assert.doesNotMatch(page, /<footer|class="eyebrow"|class="introduction"/, label);
    assert.equal((page.match(/<h1\b/g) || []).length, 1, `${label}: one h1`);
    assert.ok(header.includes(`<h1 class="site-title">${TOURS[slug].title}</h1>`), label);
    assert.ok(page.includes(`<title>${TOURS[slug].title} · jehlp.net</title>`), label);
    // The header links the two other tours by relative addresses and omits the page itself.
    const links = [...header.matchAll(/<a href="([^"]*)">/g)].map((m) => m[1]);
    const others = slugs.filter((other) => other !== slug).map((other) => `${prefix(slug)}${other ? `${other}/` : ''}`);
    assert.deepEqual(links, [...others, `${prefix(slug)}papers/${TOURS[slug].paper}`], `${label}: header links`);
  }
  // Names on jehlp.net have a capital letter on each word, as the homepage list has them.
  for (const { title } of Object.values(TOURS)) assert.match(title, /^(?:\p{Lu}[\p{L}]*|\d+)(?: (?:\p{Lu}[\p{L}]*|\d+))*$/u, title);
  // Other sites link the address jehlp.net/erdos1016. It stays the page on Erdős problem 1016.
  assert.equal(TOURS[''].title, 'Erdős 1016');
  assert.ok(html[''].includes('Erdős problem 1016 asks for the least number of edges'));
});

test('mathematics is native MathML from the build, with the local math font', async () => {
  for (const [slug, page] of everyPage) {
    const label = name(slug);
    assert.doesNotMatch(page, /\\\(|\\\)|\\\[|\\\]|\$\$|\{\{|href="~/, `${label}: TeX or a directive remains`);
    // Formulas are MathML, not hand-built spans or Unicode subscripts.
    assert.doesNotMatch(page, /class="math-inline"|<var>|log₂|[₀-₉]/, label);
    assert.doesNotMatch(page, /<script[^>]*(?:temml|katex|mathjax)/i, `${label}: no typesetter in the browser`);
  }
  for (const slug of slugs) {
    assert.ok((html[slug].match(/<math[\s>]/g) || []).length >= 60, `${name(slug)}: inline formulas`);
    const displays = (html[slug].match(/<div class="equation" role="group" aria-label="Formula" tabindex="0"><math display="block"/g) || []).length;
    assert.ok(displays >= 2, `${name(slug)}: ${displays} display formulas`);
    assert.equal(displays, (html[slug].match(/class="equation"/g) || []).length, `${name(slug)}: every display has the keyboard scroll region`);
  }
  assert.ok(html.forest.includes('<mfrac>') && html.forest.includes('<msup>') && html[''].includes('<msub>'));
  const css = await read('assets/guide.css');
  assert.match(css, /font-family: "Guide Math"/);
  await access(resolve(site, 'assets/fonts/latinmodern-math.otf'));
  await access(resolve(site, 'assets/fonts/LICENSE-Latin-Modern.txt'));
});

test('every interactive example has its code and a text for readers without scripts', async () => {
  const explorers = await read('assets/explorers.mjs');
  const mounted = new Set([...explorers.matchAll(/'([\w-]+-demo)': mount\w+,/g)].map((m) => m[1]));
  const used = new Set();
  for (const slug of slugs) {
    const ids = [...html[slug].matchAll(/<div id="([\w-]+)-demo"><\/div>/g)].map((m) => m[1]);
    assert.deepEqual(ids.sort(), [...TOURS[slug].demos].sort(), name(slug));
    for (const id of ids) {
      used.add(`${id}-demo`);
      assert.ok(mounted.has(`${id}-demo`), `${name(slug)}: no code for ${id}-demo`);
      assert.match(html[slug], new RegExp(`<div class="experiment">\\s*<h3>[^<]+</h3>\\s*<div id="${id}-demo"></div>\\s*<noscript><p>[^<]{40,}</p></noscript></div>`), `${name(slug)}: ${id}-demo`);
    }
    assert.ok(new RegExp(`<script type="module" src="${prefix(slug).replace(/\./g, '\\.')}assets/explorers\\.mjs\\?v=[\\w-]+"></script>`).test(html[slug]), name(slug));
  }
  assert.deepEqual([...mounted].sort(), [...used].sort(), 'each example of the code is on one page');
});

test('the numbers in the text are the numbers that the code computes', () => {
  // Forest tour: the table of the rings with one marked square.
  for (const squares of [2, 3, 4, 5, 6]) {
    const ring = ringGraph(squares);
    const marked = new Set([...ring.tiles[0].left, ...ring.tiles[0].right]);
    const { favorable, total } = forestDistribution(ring.n, ring.edges, ring.edges.filter(([u, v]) => marked.has(u) || marked.has(v)));
    assert.equal(total, 2 ** ring.rank);
    assert.ok(2 * favorable > total, 'more than half, as the lower bound says');
    const row = `<tr><td>${squares}</td><td>${total.toLocaleString('en-US')}</td><td>${favorable.toLocaleString('en-US')}</td><td>${(favorable / total).toFixed(3)}</td></tr>`;
    assert.ok(html.forest.includes(row), `row for ${squares} squares`);
  }
  assert.ok(html.forest.includes('<td>30</td><td>0.938</td>') && html.forest.includes('<td>4,802</td><td>0.586</td>'));
  // Exact maximums: the values of H in the text.
  const exact = text(html['exact-maximums']);
  assert.ok(exact.includes(`The ring of rank 9 has four squares and ${horakKim(9)} cycles.`));
  assert.ok(exact.includes(`one single rung and ${horakKim(10)} cycles`));
  assert.ok(exact.includes(`is ${horakKim(27).toLocaleString('en-US')}.`));
  assert.ok(exact.includes('67,959,973 cycles') && 67959973 > horakKim(27));
  // Forest tour: the values of the second-moment bound in the text without scripts.
  assert.ok(text(html.forest).includes('For the mean 1 the bound is 0.75. For the mean 10 it is about 0.545. For the mean 100 it is about 0.505.'));
});

test('the tour styles keep the theme: thin rules, no shadow, no rounded corner', async () => {
  const css = await read('assets/guide.css');
  assert.doesNotMatch(css, /box-shadow|border-radius:(?!0)|linear-gradient|radial-gradient/);
  assert.match(css, /\.stop-sentence \{[^}]*border-left:3px solid var\(--tone-ochre\)/);
  assert.match(css, /\.statement \{[^}]*border-left:3px solid var\(--blue\); background:var\(--surface-blue\)/);
  assert.match(css, /\.in-paper \{[^}]*border-top:1px solid var\(--line\)/);
  // Figure colours come from theme tokens, so both colour modes have them.
  for (const rule of css.match(/\.fig-[\w-]+ \{[^}]*\}/g)) assert.doesNotMatch(rule, /#[0-9a-f]{3,8}\b|rgb\(/i, rule);
});

test('selected demo controls retain contrast on hover and 44-pixel minimum width', async () => {
  const css = await read('assets/guide.css');
  assert.match(css, /\.demo-button\[aria-pressed=true\]:hover:not\(:disabled\)\{background:var\(--ink\);color:var\(--paper\)\}/);
  assert.match(css, /\.demo-controls button,\.demo-button\{min-width:44px/);
});

test('disabled demo buttons are distinct and all control rows are hidden in print', async () => {
  const css = await read('assets/guide.css');
  assert.match(css, /\.demo-button:disabled\s*\{[^}]*color:var\(--muted\);[^}]*border-color:var\(--line\);[^}]*cursor:default;/);
  assert.match(css, /@media print\s*\{\s*\.contents,\.demo-controls,\.demo-button-row,\.site-header nav\s*\{\s*display:none;/);
});

test('mathematics uses prose ink with neutral display shading', async () => {
  const css = await read('assets/guide.css');
  assert.match(css, /--math-ink: var\(--ink\)/);
  assert.match(css, /background:var\(--surface\); color:var\(--ink\)/);
  assert.doesNotMatch(css, /#315f68|#aacdd1/);
});

test('vendored theme includes the exact Home door and Wrenfold assets with math kept separate', async () => {
  const hash = async (path) => createHash('sha256').update(await readFile(resolve(site, path))).digest('hex');
  assert.equal(await hash('assets/theme/fonts/WrenfoldText-Regular.woff2'), '826f6c238521bfbf98d897a8f81810a78ed2d6571fec0ef86d0d51edba0212be');
  for (const name of ['home-doorway.svg', 'home-folio-scroll.svg', 'home-compass.svg', 'home-emblem.svg', 'home.svg']) {
    assert.equal(await hash(`assets/theme/icons/${name}`), '2baa87caf29834e155af108d7743c410e2a3b1775edf6c7671ec24918a7810db');
  }
  const css = await read('assets/theme/base.css');
  assert.match(css, /--serif: Georgia, "Times New Roman", serif/);
  assert.match(css, /--reading: "Wrenfold Text"/);
  assert.match(css, /--display: "Palatino Linotype"/);
  assert.match(css, /icons\/home-doorway\.svg/);
  for (const name of ['OFL-1.1.txt', 'Noto-Debian-copyright.txt', 'Wrenfold-README.txt']) await access(resolve(site, `assets/theme/fonts/${name}`));
  const guide = await read('assets/guide.css');
  assert.match(guide, /math \{ font-family:var\(--math-face\)/);
  assert.match(guide, /\.graph-label \{[^}]*font-family:var\(--sans\)/);
  assert.match(guide, /main \{ font-family:var\(--reading, var\(--serif\)\)/);
  assert.match(guide, /main :is\(h2, h3\) \{ font-family:var\(--reading, var\(--serif\)\)/);
  assert.match(guide, /main :is\(button, input, select, textarea, summary, legend\), \.demo-controls, \.demo-output \{ font-family:var\(--ui, var\(--serif\)\)/);
});

// The pages are built from site-src/pages with Temml. The check runs where Temml is present:
// after npm install in site-src/, or with the path of dist/temml.mjs in the variable TEMML.
test('the written pages are the build of their sources', async (t) => {
  const { buildPages } = await import(pathToFileURL(resolve(repo, 'site-src/build.mjs')).href);
  let pages;
  try {
    pages = await buildPages();
  } catch (error) {
    if (/Temml is not available/.test(error.message)) return t.skip('Temml is not installed here');
    throw error;
  }
  assert.equal(pages.length, 3);
  for (const { file, html: built } of pages) assert.equal(await readFile(file, 'utf8'), built, `${file} is not the build of its source`);
});
