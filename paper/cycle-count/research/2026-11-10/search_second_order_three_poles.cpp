// Heuristic search for three-poles with two saturated path counts.
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
struct ThreePole {
 int h,n;vector<pair<int,int>> edges;vector<uint64_t> adj;mt19937_64 rng;
 ThreePole(int hh,int seed):h(hh),n(2*hh+1),adj(n),rng(seed){}
 void add(int a,int b){adj[a]|=1ULL<<b;adj[b]|=1ULL<<a;}
 void del(int a,int b){adj[a]&=~(1ULL<<b);adj[b]&=~(1ULL<<a);}
 bool has(int a,int b){return(adj[a]>>b)&1;}
 long long dfs(int u,int t,uint64_t seen){if(u==t)return 1;uint64_t z=adj[u]&~seen;long long ans=0;while(z){int v=__builtin_ctzll(z);z&=z-1;ans+=dfs(v,t,seen|(1ULL<<v));}return ans;}
 long long path(int s,int t){return dfs(s,t,1ULL<<s);}
 bool connected(){uint64_t seen=1,todo=1;while(todo){int u=__builtin_ctzll(todo);todo&=todo-1;auto z=adj[u]&~seen;seen|=z;todo|=z;}return seen==(1ULL<<n)-1;}
 void start(){
  edges.clear();fill(adj.begin(),adj.end(),0);
  int k,c=2;
  if(h%2){k=3;edges={{0,1},{0,2},{1,2}};}
  else{k=5;edges={{0,3},{0,4},{1,3},{1,4},{2,3},{2,4}};}
  while(k<n){
   int x=k,y=k+1,z=k+2,w=k+3;
   edges.insert(edges.end(),{{c,x},{x,z},{x,w},{y,z},{y,w},{z,w}});c=y;k+=4;
  }
  if(c!=2)for(auto &e:edges){for(int *v:{&e.first,&e.second}){if(*v==2)*v=c;else if(*v==c)*v=2;}}
  for(auto [u,v]:edges)add(u,v);
 }
 void run(int steps,int restarts){
  long long capbest=-1;vector<pair<int,int>> winner;long long full=1LL<<h;
  for(int restart=0;restart<restarts;++restart){
   start();double cur=path(0,2)+path(1,2)+double(path(0,1))/full;
   for(int it=0;it<steps;++it){
    int i=rng()%edges.size(),j=rng()%edges.size();if(i==j)continue;
    auto[a,b]=edges[i];auto[c,d]=edges[j];if(rng()&1)swap(c,d);
    if(a==c||a==d||b==c||b==d||has(a,d)||has(c,b))continue;
    del(a,b);del(c,d);add(a,d);add(c,b);
    long long ac=0,bc=0,ab=0;
    if(connected()){ac=path(0,2);bc=path(1,2);ab=path(0,1);}
    double score=ac+bc+double(ab)/full;
    double temp=max(0.02,2.0*(1.0-double(it)/steps));
    bool accept=score>=cur || generate_canonical<double,64>(rng)<exp((score-cur)/temp);
    if(accept){edges[i]={a,d};edges[j]={c,b};cur=score;}
    else{del(a,d);del(c,b);add(a,b);add(c,d);}
    if(accept&&ac==full&&bc==full&&ab>capbest){capbest=ab;winner=edges;}
   }
  }
  cout<<"{\"rank\":"<<h<<",\"cap_paths\":"<<capbest<<",\"edges\":[";
  bool first=true;for(auto[u,v]:winner){if(!first)cout<<",";first=false;cout<<"["<<u<<","<<v<<"]";}cout<<"]}"<<endl;
 }
};
int main(int argc,char**argv){int lo=argc>1?atoi(argv[1]):2,hi=argc>2?atoi(argv[2]):10,steps=argc>3?atoi(argv[3]):10000,restarts=argc>4?atoi(argv[4]):12;for(int h=lo;h<=hi;++h){ThreePole s(h,1016+h);s.run(steps,restarts);}return 0;}
