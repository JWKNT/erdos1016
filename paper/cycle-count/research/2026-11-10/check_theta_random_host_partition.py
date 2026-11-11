"""Exact check of the explicit middle-interval theta partition."""
import json
from pathlib import Path


def main():
    blocks=0
    for q in range(1,1001):
        d=9*q;m=2*q-1;h=q-1;A=3*q+2
        pi=[(i+h)%m for i in range(m)]
        sigma=[3*h-i-pi[i] for i in range(m)]
        assert sorted(pi)==list(range(m))
        assert sorted(sigma)==list(range(m))
        lengths=[]
        for i in range(m):
            triple=[A+i,A+m+pi[i],A+2*m+sigma[i]]
            assert sum(triple)==2*d
            arms=[d-value for value in triple]
            assert min(arms)>=2 and sum(arms)==d
            assert sorted([arms[0]+arms[1],arms[0]+arms[2],arms[1]+arms[2]])==sorted(triple)
            lengths.extend(triple);blocks+=1
        assert sorted(lengths)==list(range(d//3+2,d-1))
        assert 2*m==4*d//9-2
    result={'status':'all exact checks passed','q_values':[1,1000],'theta_blocks_checked':blocks}
    Path(__file__).with_name('theta-random-host-partition-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
