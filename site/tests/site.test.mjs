import assert from 'node:assert/strict';
import test from 'node:test';
import {readFile,access} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
const site=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const html=await readFile(resolve(site,'index.html'),'utf8');
test('eleven chapters, unique IDs and working internal navigation',()=>{
 const ids=[...html.matchAll(/\bid="([^"]+)"/g)].map(m=>m[1]);
 assert.equal(ids.length,new Set(ids).size);assert.equal((html.match(/<section id=/g)||[]).length,11);
 for(const [,id] of html.matchAll(/href="#([^"]+)"/g))assert.ok(ids.includes(id),`Unknown anchor: ${id}`);
});
test('ten progressive experiments and precise exposition remain present',()=>{
 for(const id of ['graph','space','forest','binary','logstar','moment','recurrence','cut','walk','restriction'])assert.ok(html.includes(`id="${id}-demo"`),id);
 for(const phrase of ['sufficiently large','supremum','nonbacktracking','Cauchy'])assert.ok(html.includes(phrase),phrase);
 assert.match(html,/lang="en"/);assert.match(html,/name="viewport"/);assert.match(html,/class="skip-link"/);
});
test('local linked resources exist; no external runtime dependencies',async()=>{
 for(const [,url] of html.matchAll(/(?:src|href)="([^"]+)"/g)){
  if(url.startsWith('#')||url.startsWith('https://'))continue;
  await access(resolve(site,url));
 }
 for(const [,src] of html.matchAll(/<script[^>]*src="([^"]+)"/g))assert.ok(!src.startsWith('http'));
});

test('selected demo controls retain contrast on hover and 44-pixel minimum width',async()=>{
 const css=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(css,/\.demo-button\[aria-pressed=true\]:hover:not\(:disabled\)\{background:var\(--ink\);color:var\(--paper\)\}/);
 assert.match(css,/\.demo-controls button,\.demo-button\{min-width:44px/);
});

test('restrained structure removes redundant and provenance-only sections',()=>{
 assert.doesNotMatch(html,/id="sources"|href="#sources"|<footer|class="introduction"|class="eyebrow"/);
 assert.match(html,/<h1 class="site-title">Erdős problem 1016<\/h1>/);
 assert.doesNotMatch(html,/How few edges can hold|One graph\. Every possible loop length|Experiment ·/);
});
test('display mathematics uses native fractions, scripts and locally licensed math font',async()=>{
 assert.equal((html.match(/class="equation(?: conclusion)?"/g)||[]).length,20);
 assert.ok((html.match(/<math /g)||[]).length>=50);
 assert.ok(html.includes('<mfrac>'));assert.ok(html.includes('<msup>'));assert.ok(html.includes('<msub>'));
 const css=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(css,/font-family: "Guide Math"/);
 await access(resolve(site,'assets/fonts/latinmodern-math.otf'));
 await access(resolve(site,'assets/fonts/LICENSE-Latin-Modern.txt'));
});
