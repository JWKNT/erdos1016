// Exact counts for vertex-deleted poles in connected simple cubic graphs.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char** argv) {
  bool filtered=argc>1 && string(argv[1])=="--only-nonuniversal";
  bool terminal_filtered=argc>1 && string(argv[1])=="--only-terminal-failures";
  uint64_t graphcount=0,polecount=0,universalcount=0;
  string line;
  while(getline(cin,line)) {
    if(line.empty() || line[0]=='>') continue;
    int n=(unsigned char)line[0]-63;
    if(n<4 || n>38) return 2;
    vector<pair<int,int>> edges;
    vector<vector<pair<int,int>>> adj(n);
    int bit=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++,bit++)
      if((((unsigned char)line[1+bit/6]-63)>>(5-bit%6))&1) {
        int e=edges.size(); edges.push_back({i,j});
        adj[i].push_back({j,e}); adj[j].push_back({i,e});
      }
    int m=edges.size();
    for(auto &a:adj) if(a.size()!=3) return 3;
    vector<int> par(n,-1),pe(n,-1),dep(n),todo{0};
    vector<bool> tree(m,false);
    par[0]=0;
    while(!todo.empty()) {
      int v=todo.back();todo.pop_back();
      for(auto [w,e]:adj[v]) if(par[w]<0) {
        par[w]=v;pe[w]=e;dep[w]=dep[v]+1;tree[e]=true;todo.push_back(w);
      }
    }
    for(int p:par) if(p<0) return 4;
    vector<uint64_t> basis;
    for(int e=0;e<m;e++) if(!tree[e]) {
      auto [u,v]=edges[e]; uint64_t mask=uint64_t(1)<<e;
      while(u!=v) {
        if(dep[u]<dep[v]) swap(u,v);
        mask^=uint64_t(1)<<pe[u];u=par[u];
      }
      basis.push_back(mask);
    }
    vector<array<uint64_t,4>> totals(n);
    vector<vector<array<uint64_t,4>>> freq(n,vector<array<uint64_t,4>>(m));
    uint64_t mask=0,lim=uint64_t(1)<<basis.size();
    for(uint64_t x=1;x<lim;x++) {
      mask^=basis[__builtin_ctzll(x)];
      int first=__builtin_ctzll(mask),v=edges[first].first;
      uint64_t reached=0,seen=uint64_t(1)<<v;todo={v};
      while(!todo.empty()) {
        int a=todo.back();todo.pop_back();
        for(auto [b,e]:adj[a]) if((mask>>e)&1) {
          reached|=uint64_t(1)<<e;
          if(!((seen>>b)&1)){seen|=uint64_t(1)<<b;todo.push_back(b);}
        }
      }
      if(reached!=mask) continue;
      for(int a=0;a<n;a++) {
        int state=0,pat=0;
        for(int j=0;j<3;j++) if((mask>>adj[a][j].second)&1) pat|=1<<j;
        if(pat==3) state=1; else if(pat==5) state=2; else if(pat==6) state=3;
        else if(pat!=0) return 5;
        totals[a][state]++;
        for(uint64_t rem=mask;rem;rem&=rem-1)
          freq[a][__builtin_ctzll(rem)][state]++;
      }
    }
    graphcount++;
    for(int a=0;a<n;a++) {
      int start=(a==0?1:0);uint64_t seen=uint64_t(1)<<start;todo={start};
      while(!todo.empty()) {
        int v=todo.back();todo.pop_back();
        for(auto [w,e]:adj[v]) if(w!=a && !((seen>>w)&1))
          {seen|=uint64_t(1)<<w;todo.push_back(w);}
      }
      if(__builtin_popcountll(seen)!=n-1) continue;
      polecount++;
      bool universal=false;
      for(int e=0;e<m;e++) if(edges[e].first!=a && edges[e].second!=a) {
        bool good=true;
        for(int j=0;j<4;j++)
          if(2*int64_t(freq[a][e][j])>int64_t(totals[a][j])+(j==0)) good=false;
        if(good){universal=true;break;}
      }
      if(universal)universalcount++;
      if(filtered && universal)continue;
      bool terminal_good=false;
      if(terminal_filtered) {
        for(int j=0;j<3;j++) {
          int v=adj[a][j].first,e=-1;
          for(auto [w,f]:adj[v])if(w!=a){e=f;break;}
          int other=3-j;
          if(2*freq[a][e][0]<=totals[a][0]+1 &&
             2*freq[a][e][other]<=totals[a][other])terminal_good=true;
        }
        if(terminal_good)continue;
      }
      cout<<line<<" "<<a;
      for(auto x:totals[a]) cout<<" "<<x;
      for(int e=0;e<m;e++) if(edges[e].first!=a && edges[e].second!=a)
        for(auto x:freq[a][e]) cout<<" "<<x;
      cout<<"\n";
    }
  }
  cerr<<"{\"graphs\":"<<graphcount<<",\"poles\":"<<polecount
      <<",\"universal_edges\":"<<universalcount<<"}\n";
}
