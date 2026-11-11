"""Test minimal supports in small binary codes; not a graph theorem."""
from pathlib import Path
import json, random

def probe(r,selections):
 full=[sum(1<<(s-1) for s in range(1,1<<r) if (u&s).bit_count()%2) for u in range(1,1<<r)]
 checked=0; examples=[]
 for S in selections:
  supports=[f&S for f in full]
  if 0 in supports: continue
  checked+=1
  minimal=[i for i,a in enumerate(supports) if not any(a!=b and a&b==b for b in supports)]
  good=all(2*sum(full[i]>>s&1 for i in minimal)>len(minimal) for s in range((1<<r)-1) if S>>s&1)
  if good and len(minimal)<(1<<r)-1:
   examples.append({'rank':r,'columns':[s+1 for s in range((1<<r)-1) if S>>s&1],'minimal_words':[i+1 for i in minimal],'count':len(minimal),'below_half':len(minimal)<=(1<<(r-1))})
   if examples[-1]['below_half']:break
 return {'rank':r,'spanning_selections_checked':checked,'all_biased_nonminimal_examples':examples[:8],'total_examples':len(examples)}

rng=random.Random(20261111)
rows=[probe(4,range(1,1<<15)),probe(5,(rng.getrandbits(31) for _ in range(20000)))]
Path('root-minimal-code-probe.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows:print(json.dumps(row),flush=True)
