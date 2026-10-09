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
  await access(resolve(site,url.split(/[?#]/)[0]));
 }
 for(const [,src] of html.matchAll(/<script[^>]*src="([^"]+)"/g))assert.ok(!src.startsWith('http'));
});

test('selected demo controls retain contrast on hover and 44-pixel minimum width',async()=>{
 const css=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(css,/\.demo-button\[aria-pressed=true\]:hover:not\(:disabled\)\{background:var\(--ink\);color:var\(--paper\)\}/);
 assert.match(css,/\.demo-controls button,\.demo-button\{min-width:44px/);
});

test('disabled demo buttons are distinct and all control rows are hidden in print',async()=>{
 const css=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(css,/\.demo-button:disabled\s*\{[^}]*color:var\(--muted\);[^}]*border-color:var\(--line\);[^}]*cursor:default;/);
 assert.match(css,/@media print\s*\{\s*\.contents,\.demo-controls,\.demo-button-row,\.site-header nav\s*\{\s*display:none;/);
});

test('restrained structure removes redundant and provenance-only sections',()=>{
 assert.doesNotMatch(html,/id="sources"|href="#sources"|<footer|class="introduction"|class="eyebrow"/);
 assert.match(html,/<h1 class="site-title">Erdős 1016<\/h1>/);
 assert.doesNotMatch(html,/How few edges can hold|One graph\. Every possible loop length|Experiment ·/);
});
test('display mathematics uses native fractions, scripts and locally licensed math font',async()=>{
 assert.equal((html.match(/class="equation(?: conclusion)?"/g)||[]).length,32);
 assert.ok((html.match(/<math[\s>]/g)||[]).length>=300);
 // Inline formulas are MathML too, not hand-built spans or Unicode subscripts.
 assert.doesNotMatch(html,/class="math-inline"|<var>|log₂|[₀-₉]/);
 assert.ok(html.includes('<mfrac>'));assert.ok(html.includes('<msup>'));assert.ok(html.includes('<msub>'));
 const css=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(css,/font-family: "Guide Math"/);
 await access(resolve(site,'assets/fonts/latinmodern-math.otf'));
 await access(resolve(site,'assets/fonts/LICENSE-Latin-Modern.txt'));
});

test('paper is served directly and byte-identical to the repository manuscript',async()=>{
 assert.match(html,/href="paper.pdf">Paper<\/a>/);
 const pdf=await readFile(resolve(site,'paper.pdf'));
 assert.equal(pdf.subarray(0,5).toString(),'%PDF-');
 assert.deepEqual(pdf,await readFile(resolve(site,'../paper/erdos1016.pdf')));
});

test('mathematics uses prose ink with neutral display shading',async()=>{
 const css=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(css,/--math-ink: var\(--ink\)/);
 assert.match(css,/background:var\(--surface\); color:var\(--ink\)/);
 assert.doesNotMatch(css,/#315f68|#aacdd1/);
});

 test('masthead omits the redundant contents jump and keeps the paper link', () => {
 const header=html.match(/<header\b[\s\S]*?<\/header>/)[0];
 assert.doesNotMatch(header,/href="#contents"/);
 assert.match(header,/href="paper.pdf"/);
 assert.match(html,/<aside id="contents"/);
 });

test('vendored theme includes the exact folio and Wrenfold assets with math kept separate', async () => {
 const {createHash}=await import('node:crypto');
 const hash=async(path)=>createHash('sha256').update(await readFile(resolve(site,path))).digest('hex');
 assert.equal(await hash('assets/theme/fonts/WrenfoldText-Regular.woff2'),'826f6c238521bfbf98d897a8f81810a78ed2d6571fec0ef86d0d51edba0212be');
 for(const name of ['home-folio-scroll.svg','home-compass.svg','home-emblem.svg','home.svg']){
  assert.equal(await hash(`assets/theme/icons/${name}`),'ff757b439e901db80d320d5fd1422edb63525b0ff46e235ab2dd5c52b2dad55f');
 }
 const css=await readFile(resolve(site,'assets/theme/base.css'),'utf8');
 assert.match(css,/--serif: "Wrenfold Text"/);
 assert.match(css,/--display: var\(--serif\)/);
 assert.match(css,/icons\/home-folio-scroll\.svg/);
 for(const name of ['OFL-1.1.txt','Noto-Debian-copyright.txt','Wrenfold-README.txt'])await access(resolve(site,`assets/theme/fonts/${name}`));
 const guide=await readFile(resolve(site,'assets/guide.css'),'utf8');
 assert.match(guide,/math \{ font-family:var\(--math-face\)/);
 assert.match(guide,/\.graph-label \{[^}]*font-family:var\(--ui, var\(--serif\)\)/);
});
