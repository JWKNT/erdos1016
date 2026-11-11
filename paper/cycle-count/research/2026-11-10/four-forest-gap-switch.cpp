// Exact affine-join checks inside an exploratory degree-preserving switch walk.
// A completed count certifies each printed witness; the search is not exhaustive.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <utility>
#include <vector>
using namespace std;
using Mask = __uint128_t;
using Edge = pair<int,int>;
struct Graph { int n; vector<Edge> edges; vector<int> terminals; };

long long bad_count(const Graph& g, long long cutoff) {
  vector<vector<Edge>> adjacency(g.n);
  for (int e=0;e<(int)g.edges.size();++e) {
    auto [u,v]=g.edges[e];
    adjacency[u].push_back({v,e}); adjacency[v].push_back({u,e});
  }
  vector<int> reached(g.n), tree(g.edges.size());
  vector<Mask> root(g.n);
  vector<int> queue{0}; reached[0]=1;
  for (int j=0;j<(int)queue.size();++j) for (auto [v,e]:adjacency[queue[j]]) {
    if (!reached[v]) {
      reached[v]=1; tree[e]=1; root[v]=root[queue[j]]^(Mask(1)<<e); queue.push_back(v);
    }
  }
  if ((int)queue.size()!=g.n) return cutoff;
  vector<Mask> basis;
  for (int e=0;e<(int)g.edges.size();++e) if (!tree[e]) {
    auto [u,v]=g.edges[e]; basis.push_back(root[u]^root[v]^(Mask(1)<<e));
  }
  Mask selected=0;
  for (int v:g.terminals) selected^=root[v];
  long long bad=0;
  vector<int> uf(g.n);
  for (uint64_t word=0;word<(uint64_t(1)<<basis.size());++word) {
    if (word) selected^=basis[__builtin_ctzll(word)];
    iota(uf.begin(),uf.end(),0);
    auto find=[&](int v) { while (uf[v]!=v) { uf[v]=uf[uf[v]];v=uf[v]; }return v; };
    for (int e=0;e<(int)g.edges.size();++e) if ((selected>>e)&1) {
      auto [u,v]=g.edges[e];u=find(u);v=find(v);
      if (u==v) { if (++bad>=cutoff) return bad; break; }
      uf[u]=v;
    }
  }
  return bad;
}

Graph diamond(Graph g) {
  int t=g.terminals[0],a=g.n,b=g.n+1,c=g.n+2,d=g.n+3;
  g.edges.insert(g.edges.end(),{{t,a},{a,c},{a,d},{b,c},{b,d},{c,d}});
  g.terminals[0]=b;g.n+=4;return g;
}

Graph extension(const Graph& g,int i,int j) {
  Graph result{g.n+2,{},g.terminals};
  for (int e=0;e<(int)g.edges.size();++e) {
    auto [u,v]=g.edges[e];
    if (e==i) { result.edges.push_back({u,g.n});result.edges.push_back({g.n,v}); }
    else if (e==j) { result.edges.push_back({u,g.n+1});result.edges.push_back({g.n+1,v}); }
    else result.edges.push_back(g.edges[e]);
  }
  result.edges.push_back({g.n,g.n+1});return result;
}

void print_graph(const Graph& g,long long bad,const string& kind,long long iteration) {
  cout<<"{\"kind\":\""<<kind<<"\",\"rank\":"<<g.edges.size()-g.n+1
      <<",\"bad\":"<<bad<<",\"iteration\":"<<iteration<<",\"vertices\":"<<g.n<<",\"terminals\":[";
  for (int i=0;i<(int)g.terminals.size();++i) cout<<(i?",":"")<<g.terminals[i];
  cout<<"],\"edges\":[";
  for (int i=0;i<(int)g.edges.size();++i) cout<<(i?",":"")<<"["<<g.edges[i].first<<","<<g.edges[i].second<<"]";
  cout<<"]}"<<endl;
}

int main(int argc,char**argv) {
  if (argc<5) return 2;
  ifstream in(argv[1]);int m,k;Graph seed;in>>seed.n>>m>>k;
  seed.terminals.resize(k);for (int&v:seed.terminals) in>>v;
  seed.edges.resize(m);for (auto&[u,v]:seed.edges) in>>u>>v;
  int rank=stoi(argv[2]);long long iterations=stoll(argv[3]);mt19937_64 rng(stoull(argv[4]));
  if ((rank-(m-seed.n+1))%2==1) {
    long long best=1LL<<30;Graph chosen;
    for (int i=0;i<m;++i) for (int j=i+1;j<m;++j) {
      Graph candidate=extension(seed,i,j);long long value=bad_count(candidate,best);
      if (value>0 && value<best) {best=value;chosen=std::move(candidate);}
    }
    seed=std::move(chosen);
  }
  while ((int)seed.edges.size()-seed.n+1<rank) seed=diamond(std::move(seed));
  long long denominator=argc>5?stoll(argv[5]):128;
  long long threshold=(1LL<<rank)/denominator;
  long long initial=bad_count(seed,1LL<<rank);
  if (!initial || initial>threshold) { cerr<<"Invalid seed "<<initial<<" "<<threshold<<endl;return 3; }
  print_graph(seed,initial,"seed",0);
  Graph current=seed;long long best=initial,accepted=0,full=0,valid=0;
  for (long long step=1;step<=iterations;++step) {
    if (step%5000==0) current=seed;
    int i=rng()%current.edges.size(),j=rng()%current.edges.size();if (i==j)continue;
    auto [a,b]=current.edges[i];auto[c,d]=current.edges[j];if (rng()&1)swap(c,d);
    if (a==d || c==b)continue;
    Graph candidate=current;candidate.edges[i]={a,d};candidate.edges[j]={c,b};
    vector<Edge> sorted=candidate.edges;
    for(auto&[u,v]:sorted)if(u>v)swap(u,v);sort(sorted.begin(),sorted.end());
    if(adjacent_find(sorted.begin(),sorted.end())!=sorted.end())continue;
    ++valid;
    long long value=bad_count(candidate,threshold+1);
    if (value<=threshold) {
      ++accepted;full+=value==0;current=std::move(candidate);
      if (value>0 && value<best) { best=value; print_graph(current,best,"improved_nonfull",step); }
    }
  }
  cout<<"{\"kind\":\"summary\",\"rank\":"<<rank<<",\"iterations\":"<<iterations
      <<",\"valid_switches\":"<<valid<<",\"accepted\":"<<accepted<<",\"full_accepted\":"<<full
      <<",\"minimum_nonfull_bad\":"<<best<<",\"total_states\":"<<(1LL<<rank)<<"}"<<endl;
  return 0;
}
