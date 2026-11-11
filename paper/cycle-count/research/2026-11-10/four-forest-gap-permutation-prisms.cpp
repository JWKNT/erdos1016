// Bounded exact search on two equal cycles joined by a permutation matching.
// Delete two edges of the outer cycle; retain their four endpoints as ports.
#define main switch_driver
#include "four-forest-gap-switch.cpp"
#undef main
#include <cmath>

Graph prism(const vector<int>& p,int cut) {
  int L=p.size();Graph g{2*L,{}, {L,L+1,L+cut,L+(cut+1)%L}};
  for(int i=0;i<L;++i) {
    g.edges.push_back({i,(i+1)%L});g.edges.push_back({i,L+p[i]});
    if(i!=0&&i!=cut)g.edges.push_back({L+i,L+(i+1)%L});
  }
  return g;
}

int main(int argc,char**argv) {
  int steps=argc>1?stoi(argv[1]):5000;mt19937_64 rng(1511241);
  for(int L:{6,8,10,12,14}) {
    vector<int> p(L);iota(p.begin(),p.end(),0);
    vector<int> best_perm=p;int cut=L/2,best_cut=cut;
    long long best=bad_count(prism(p,cut),1LL<<L),current=best,checked=1;
    print_graph(prism(p,cut),best,"ordinary_prism",0);
    for(int t=1;t<=steps;++t) {
      if(t%500==0) {
        if(t%1000==0){p=best_perm;cut=best_cut;current=best;}
        else {shuffle(p.begin(),p.end(),rng);cut=2+rng()%(L-3);current=bad_count(prism(p,cut),1LL<<L);++checked;}
      }
      vector<int> q=p;int next_cut=cut;
      if(rng()%5==0)next_cut=2+rng()%(L-3);
      else {int a=rng()%L,b=rng()%L;swap(q[a],q[b]);}
      long long budget=current+max(2LL,current/8);
      long long value=bad_count(prism(q,next_cut),budget+1);++checked;
      if(value<=budget && (value<=current || rng()%8==0)) {p=q;cut=next_cut;current=value;}
      if(value<best) {
        best=value;best_perm=q;best_cut=next_cut;
        print_graph(prism(q,next_cut),best,"improved_prism",t);
      }
    }
    cout<<"{\"kind\":\"prism_summary\",\"cycle_length\":"<<L
        <<",\"rank\":"<<L-1<<",\"checked\":"<<checked<<",\"bad\":"<<best
        <<",\"total\":"<<(1LL<<(L-1))<<",\"cut\":"<<best_cut<<",\"permutation\":[";
    for(int i=0;i<L;++i)cout<<(i?",":"")<<best_perm[i];cout<<"]}"<<endl;
  }
  return 0;
}
