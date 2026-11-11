// Exact rank-increasing search: subdivide two edges and join the new vertices.
// Prints a graph only after enumerating its full affine T-join space.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <utility>
#include <vector>
using namespace std;
using Mask=__uint128_t;
using Edge=pair<int,int>;
struct Graph{int n;vector<Edge> edges;vector<int> terminals;};
long long bad_count(const Graph&g,long long stop=2){
 vector<vector<Edge>>a(g.n);
 for(int i=0;i<(int)g.edges.size();++i){auto[u,v]=g.edges[i];a[u].push_back({v,i});a[v].push_back({u,i});}
 vector<int>par(g.n,-1),tree(g.edges.size());vector<Mask>root(g.n);vector<int>todo{0};par[0]=0;
 for(int k=0;k<(int)todo.size();++k){int u=todo[k];for(auto[v,e]:a[u])if(par[v]<0){par[v]=u;tree[e]=1;root[v]=root[u]^(Mask(1)<<e);todo.push_back(v);}}
 if((int)todo.size()!=g.n)return stop;
 vector<Mask>basis;for(int i=0;i<(int)g.edges.size();++i)if(!tree[i]){auto[u,v]=g.edges[i];basis.push_back(root[u]^root[v]^(Mask(1)<<i));}
 Mask f=0;for(int t:g.terminals)f^=root[t];long long bad=0;
 vector<int>uf(g.n);
 for(uint64_t k=0;k<(1ULL<<basis.size());++k){
  if(k)f^=basis[__builtin_ctzll(k)];
  iota(uf.begin(),uf.end(),0);bool cyclic=false;
  auto find=[&](int v){while(uf[v]!=v){uf[v]=uf[uf[v]];v=uf[v];}return v;};
  for(int i=0;i<(int)g.edges.size();++i)if((f>>i)&1){auto[u,v]=g.edges[i];u=find(u);v=find(v);if(u==v){cyclic=true;break;}uf[u]=v;}
  if(cyclic&&++bad>=stop)return bad;
 }
 return bad;
}
void output(const Graph&g){cout<<"{\"rank\":"<<g.edges.size()-g.n+1<<",\"vertices\":"<<g.n<<",\"bad\":"<<bad_count(g)<<",\"terminals\":[";for(int i=0;i<(int)g.terminals.size();++i)cout<<(i?",":"")<<g.terminals[i];cout<<"],\"edges\":[";for(int i=0;i<(int)g.edges.size();++i)cout<<(i?",":"")<<"["<<g.edges[i].first<<","<<g.edges[i].second<<"]";cout<<"]}"<<endl;}
int main(int argc,char**argv){
 int hi=argc>1?atoi(argv[1]):18,beam=argc>2?atoi(argv[2]):20;
 Graph g{8,{}, {0,1,2,4}};for(int i=0;i<8;++i)g.edges.push_back({i,(i+1)%8});g.edges.push_back({3,6});g.edges.push_back({5,7});
 int terminals=argc>3?atoi(argv[3]):4;
 for(int count=4;count<terminals;count+=2){auto[u,v]=g.edges[0];int p=g.n,q=g.n+1;g.edges[0]={u,p};g.edges.push_back({p,q});g.edges.push_back({q,v});g.terminals.push_back(p);g.terminals.push_back(q);g.n+=2;}
 vector<Graph>current{g};mt19937 rng(734235);output(g);
 for(int rank=4;rank<=hi;++rank){
  vector<Graph>next;
  shuffle(current.begin(),current.end(),rng);
  for(const auto&old:current){
   vector<Edge>pairs;int m=old.edges.size();for(int i=0;i<m;++i)for(int j=i+1;j<m;++j)pairs.push_back({i,j});shuffle(pairs.begin(),pairs.end(),rng);
   for(auto[i,j]:pairs){Graph n=old;n.n+=2;n.edges.clear();for(int k=0;k<m;++k){auto[u,v]=old.edges[k];if(k==i){n.edges.push_back({u,old.n});n.edges.push_back({old.n,v});}else if(k==j){n.edges.push_back({u,old.n+1});n.edges.push_back({old.n+1,v});}else n.edges.push_back({u,v});}n.edges.push_back({old.n,old.n+1});
    if(bad_count(n)==1){next.push_back(n);if((int)next.size()>=beam)break;}
   }
   if((int)next.size()>=beam)break;
  }
  cerr<<"rank "<<rank<<" retained "<<next.size()<<"\n";
  if(next.empty())break;current=std::move(next);output(current[0]);
 }
}
