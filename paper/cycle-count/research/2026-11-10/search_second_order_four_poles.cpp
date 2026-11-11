// Exact objective, heuristic search. This does not certify an extremum.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <utility>
#include <vector>
using namespace std;

struct Search {
  int b,n;
  vector<pair<int,int>> edges,best_edges;
  vector<uint64_t> adj;
  mt19937_64 rng;
  long long best=-1;
  Search(int rank,int seed):b(rank),n(2*rank-1),adj(n),rng(seed){}
  void add(int u,int v){adj[u]|=1ULL<<v;adj[v]|=1ULL<<u;}
  void del(int u,int v){adj[u]&=~(1ULL<<v);adj[v]&=~(1ULL<<u);}
  bool has(int u,int v){return (adj[u]>>v)&1;}
  long long dfs(int u,uint64_t seen){
    if(u==n-2)return 1;
    uint64_t avail=adj[u]&~seen;
    long long count=0;
    while(avail){int v=__builtin_ctzll(avail);avail&=avail-1;count+=dfs(v,seen|(1ULL<<v));}
    return count;
  }
  long long count(){
    uint64_t reached=1,frontier=1,kmask=(1ULL<<(n-3))-1;
    while(frontier){int u=__builtin_ctzll(frontier);frontier&=frontier-1;uint64_t fresh=adj[u]&kmask&~reached;reached|=fresh;frontier|=fresh;}
    if(reached!=kmask)return 0;
    return dfs(n-3,1ULL<<(n-3));
  }
  void start(){
    fill(adj.begin(),adj.end(),0);edges.clear();
    // K has four degree-two ports 0,1,2,3; its other vertices have degree three.
    int k=n-3;
    vector<int> cyc(k);iota(cyc.begin(),cyc.end(),0);shuffle(cyc.begin(),cyc.end(),rng);
    for(int i=0;i<k;++i){int u=cyc[i],v=cyc[(i+1)%k];edges.push_back({u,v});add(u,v);}
    vector<int> inner;for(int i=4;i<k;++i)inner.push_back(i);
    for(;;){
      shuffle(inner.begin(),inner.end(),rng);bool ok=true;
      for(int i=0;i<(int)inner.size();i+=2)if(has(inner[i],inner[i+1]))ok=false;
      if(ok)break;
    }
    for(int i=0;i<(int)inner.size();i+=2){int u=inner[i],v=inner[i+1];edges.push_back({u,v});add(u,v);}
    int s=n-3,t=n-2,w=n-1;
    for(auto [u,v]:vector<pair<int,int>>{{s,w},{t,w},{s,0},{t,1},{w,2},{w,3}})add(u,v);
  }
  void run(int steps,int restarts){
    for(int restart=0;restart<restarts;++restart){
      start();long long cur=count();
      for(int it=0;it<steps;++it){
        int i=rng()%edges.size(),j=rng()%edges.size();if(i==j)continue;
        auto [a,b0]=edges[i];auto [c,d]=edges[j];if(rng()&1)swap(c,d);
        if(a==c||a==d||b0==c||b0==d||has(a,d)||has(c,b0))continue;
        del(a,b0);del(c,d);add(a,d);add(c,b0);
        long long val=count();
        double temperature=max(0.08,5.0*(1.0-double(it)/steps));
        bool accept=val>=cur || generate_canonical<double,64>(rng)<exp((val-cur)/temperature);
        if(accept){edges[i]={a,d};edges[j]={c,b0};cur=val;}
        else {del(a,d);del(c,b0);add(a,b0);add(c,d);}
        if(cur>best){best=cur;best_edges=edges;}
      }
    }
    cout<<"{\"rank\":"<<b<<",\"paths\":"<<best<<",\"excess\":"<<best-(1LL<<(b-1))<<",\"K_edges\":[";
    bool first=true;for(auto [u,v]:best_edges){if(!first)cout<<",";first=false;cout<<"["<<u<<","<<v<<"]";}
    cout<<"]}"<<endl;
  }
};
int main(int argc,char**argv){
  int lo=argc>1?atoi(argv[1]):7,hi=argc>2?atoi(argv[2]):10;
  int steps=argc>3?atoi(argv[3]):10000,restarts=argc>4?atoi(argv[4]):8;
  int seed=argc>5?atoi(argv[5]):1016;
  if(lo<6 || hi>30)return 2;
  for(int b=lo;b<=hi;++b){Search s(b,seed+b);s.run(steps,restarts);}
  return 0;
}
