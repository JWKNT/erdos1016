// Exact cycle-space enumeration for cubic graph6 catalogues.
// Adapted for rank-distance path excess; original catalogue source remains unchanged.
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <map>
#include <queue>
#include <iomanip>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
string escaped(const string &s) { string out; for(char c:s) { if(c=='\\')out+='\\';out+=c;} return out; }
struct Record { uint64_t excess=0, paths=0; int b=0, ell=0, edge=0; long double scaled=-1; string graph; };
int main() {
  map<int,Record> by_deficit;
  Record best_scaled, best_scaled_per_rank;
  string line, best_c_g, best_g_g, best_p_g;
  uint64_t graphs=0, states=0, best_c=0, best_g=0, best_p=0;
  int best_p_edge=-1, order=0, rank=0;
  while (getline(cin,line)) {
    if(line.empty() || line[0]=='>') continue;
    int n=(unsigned char)line[0]-63;
    if(n<1 || n>32) return 2;
    order=n;
    vector<pair<int,int>> edges;
    vector<vector<pair<int,int>>> adj(n);
    int bit=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++,bit++) {
      int ch=(unsigned char)line[1+bit/6]-63;
      if((ch>>(5-bit%6))&1) {
        int e=edges.size(); edges.push_back({i,j});
        adj[i].push_back({j,e}); adj[j].push_back({i,e});
      }
    }
    for(auto &a:adj) if(a.size()!=3) return 3;
    int m=edges.size(); rank=m-n+1;
    vector<int> parent(n,-1), pe(n,-1), depth(n);
    vector<int> stack{0}; parent[0]=0;
    vector<bool> tree(m,false);
    while(!stack.empty()) {
      int v=stack.back(); stack.pop_back();
      for(auto [w,e]:adj[v]) if(parent[w]<0) {
        parent[w]=v; pe[w]=e; depth[w]=depth[v]+1;
        tree[e]=true; stack.push_back(w);
      }
    }
    for(int p:parent) if(p<0) return 4;
    vector<uint64_t> basis;
    for(int e=0;e<m;e++) if(!tree[e]) {
      auto [u,v]=edges[e]; uint64_t mask=uint64_t(1)<<e;
      while(u!=v) {
        if(depth[u]<depth[v]) swap(u,v);
        mask^=uint64_t(1)<<pe[u]; u=parent[u];
      }
      basis.push_back(mask);
    }
    vector<uint64_t> frequencies(m,0);
    uint64_t count=0, mask=0, limit=uint64_t(1)<<rank;
    for(uint64_t x=1;x<limit;x++) {
      mask^=basis[__builtin_ctzll(x)];
      int first=__builtin_ctzll(mask), start=edges[first].first;
      uint32_t seen=uint32_t(1)<<start;
      uint64_t reached=0; vector<int> todo{start};
      while(!todo.empty()) {
        int v=todo.back();todo.pop_back();
        for(auto [w,e]:adj[v]) if((mask>>e)&1) {
          reached|=uint64_t(1)<<e;
          if(!((seen>>w)&1)) {seen|=uint32_t(1)<<w;todo.push_back(w);}
        }
      }
      if(reached!=mask) continue;
      count++;
      uint64_t rem=mask;
      while(rem) {int e=__builtin_ctzll(rem);frequencies[e]++;rem&=rem-1;}
    }

    for(int removed=0;removed<m;removed++) {
      int b=rank-1;
      uint64_t half=uint64_t(1)<<(b-1);
      if(frequencies[removed]<=half) continue;
      auto [source,target]=edges[removed];
      vector<int> dist(n,-1); queue<int> bfs; dist[source]=0;bfs.push(source);
      while(!bfs.empty()) {
        int v=bfs.front();bfs.pop();
        for(auto [w,e]:adj[v]) if(e!=removed && dist[w]<0) {
          dist[w]=dist[v]+1;bfs.push(w);
        }
      }
      if(dist[target]<0) return 5;
      int ell=dist[target], deficit=b-ell;
      uint64_t excess=frequencies[removed]-half;
      long double scaled=ldexp((long double)excess,-b)*pow((long double)2,deficit/(long double)2);
      Record rec{excess,frequencies[removed],b,ell,removed,scaled,line};
      if(!by_deficit.count(deficit) || scaled>by_deficit[deficit].scaled) by_deficit[deficit]=rec;
      if(scaled>best_scaled.scaled) best_scaled=rec;
      if(scaled/b>best_scaled_per_rank.scaled) {best_scaled_per_rank=rec;best_scaled_per_rank.scaled=scaled/b;}
    }
    graphs++;states+=limit;
    if(count>best_c){best_c=count;best_c_g=line;}
    uint64_t mn=*min_element(frequencies.begin(),frequencies.end());
    if(mn>best_g){best_g=mn;best_g_g=line;}
    for(int e=0;e<m;e++) if(frequencies[e]<limit/2 && frequencies[e]>best_p){
      best_p=frequencies[e];best_p_g=line;best_p_edge=e;
    }
  }

  auto print_record=[](const Record &a) {
    cout<<"{\"b\":"<<a.b<<",\"ell\":"<<a.ell<<",\"paths\":"<<a.paths
        <<",\"excess_count\":"<<a.excess<<",\"scaled\":"<<setprecision(18)<<a.scaled
        <<",\"edge\":"<<a.edge<<",\"graph6\":\""<<escaped(a.graph)<<"\"}";
  };
  cout<<"{\"order\":"<<order<<",\"graphs\":"<<graphs<<",\"cycle_space_states\":"<<states;
  cout<<",\"maximum_scaled_excess\":";print_record(best_scaled);
  cout<<",\"maximum_scaled_excess_per_rank\":";print_record(best_scaled_per_rank);
  cout<<",\"by_rank_distance_deficit\":{";
  bool first=true;
  for(auto &[d,a]:by_deficit) {if(!first)cout<<",";first=false;cout<<"\""<<d<<"\":";print_record(a);}
  cout<<"}}\n";
}
