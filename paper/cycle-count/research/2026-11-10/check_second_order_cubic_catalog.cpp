// Exact cycle-space enumeration for cubic graph6 catalogues.
// Reports cycle counts, minimum edge excess, and the largest nonfull edge density.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
string escaped(const string &s) { string out; for(char c:s) { if(c=='\\')out+='\\';out+=c;} return out; }
int main() {
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
    graphs++;states+=limit;
    if(count>best_c){best_c=count;best_c_g=line;}
    uint64_t mn=*min_element(frequencies.begin(),frequencies.end());
    if(mn>best_g){best_g=mn;best_g_g=line;}
    for(int e=0;e<m;e++) if(frequencies[e]<limit/2 && frequencies[e]>best_p){
      best_p=frequencies[e];best_p_g=line;best_p_edge=e;
    }
  }
  cout<<"{\"order\":"<<order<<",\"rank\":"<<rank<<",\"graphs\":"<<graphs
      <<",\"cycle_space_states\":"<<states<<",\"max_cycles\":"<<best_c
      <<",\"max_cycles_graph6\":\""<<escaped(best_c_g)<<"\",\"max_min_edge_count\":"<<best_g
      <<",\"max_min_edge_graph6\":\""<<escaped(best_g_g)<<"\",\"max_nonfull_edge_count\":"<<best_p
      <<",\"nonfull_denominator\":"<<(uint64_t(1)<<(rank-1))
      <<",\"nonfull_graph6\":\""<<escaped(best_p_g)<<"\",\"nonfull_edge_index\":"<<best_p_edge<<"}\n";
}
