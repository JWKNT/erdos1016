// Stream graph6 graphs from nauty geng. The degree-3 vertices must be
// paired by existing edges; double each matched edge to obtain degree 4.
// Exact vertex-simple-cycle enumeration counts parallel edge choices.
// Compile: c++ -O3 -std=c++17 check_four_regular_finite.cpp -o /tmp/check_four_regular_finite
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using U = uint64_t;
struct Graph {
  int n, k; unsigned adj[20]{}; unsigned char mult[20][20]{};
  U bylen[21]{};
  void walk(int start,int v,unsigned used,int len,U weight,int stop) {
    if(len==stop) { bylen[len]+=weight*mult[v][start]; return; }
    unsigned avail=adj[v]&~used&~((1u<<(start+1))-1);
    while(avail) { int w=__builtin_ctz(avail); avail&=avail-1;
      walk(start,w,used|(1u<<w),len+1,weight*mult[v][w],stop);
    }
  }
  U cycles(int len) {
    if(len==2) return k;
    bylen[len]=0;
    for(int s=0;s<n;s++) walk(s,s,1u<<s,1,1,len);
    assert(bylen[len]%2==0); bylen[len]/=2; return bylen[len];
  }
};
// Text certificates: n k S g followed by floor(U_l) for l=3,...,g-1.
struct Cert { int n,k,g; U S; vector<U> upper; };
int main(int argc,char**argv) {
  vector<Cert> certs;
  bool emit=argc>2&&string(argv[2])=="--emit";
  if(argc>1&&string(argv[1])!="-") { ifstream in(argv[1]); assert(in); Cert c;
    while(in>>c.n>>c.k>>c.S>>c.g) { c.upper.assign(c.g,0);
      for(int l=3;l<c.g;l++) in>>c.upper[l]; assert(in); certs.push_back(c); }
  }
  U inputs=0, instances=0, rejected=0, full=0, maxfull=0;
  array<U,21> passed{}; string line, maxline; int expectedn=-1,expectedk=-1;
  auto started=chrono::steady_clock::now();
  while(getline(cin,line)) {
    if(line.empty()||line[0]=='>')continue;
    Graph base{}; base.n=(unsigned char)line[0]-63; assert(base.n>=3&&base.n<=19);
    int bit=0; vector<int> odd;
    for(int v=1;v<base.n;v++) for(int u=0;u<v;u++,bit++)
      if(((line[1+bit/6]-63)>>(5-bit%6))&1) {
        base.mult[u][v]=base.mult[v][u]=1;
        base.adj[u]|=1u<<v; base.adj[v]|=1u<<u;
      }
    for(int v=0;v<base.n;v++) { int d=__builtin_popcount(base.adj[v]);
      assert(d==3||d==4); if(d==3)odd.push_back(v); }
    assert(odd.size()%2==0&&odd.size()<=4); base.k=odd.size()/2;
    if(expectedn<0){expectedn=base.n;expectedk=base.k;}
    assert(base.n==expectedn&&base.k==expectedk); inputs++;
    vector<vector<pair<int,int>>> matchings;
    if(odd.empty())matchings.push_back({});
    if(odd.size()==2&&base.mult[odd[0]][odd[1]])matchings.push_back({{odd[0],odd[1]}});
    if(odd.size()==4)for(int j=1;j<4;j++) {
      vector<int> rem; for(int z=1;z<4;z++)if(z!=j)rem.push_back(odd[z]);
      if(base.mult[odd[0]][odd[j]]&&base.mult[rem[0]][rem[1]])
        matchings.push_back({{odd[0],odd[j]},{rem[0],rem[1]}});
    }
    if(matchings.empty())rejected++;
    int mi=0;
    for(auto &matching:matchings) {
      Graph g=base; for(auto [u,v]:matching)g.mult[u][v]=g.mult[v][u]=2;
      for(int v=0;v<g.n;v++){int d=0;for(int u=0;u<g.n;u++)d+=g.mult[v][u];assert(d==4);}
      instances++; U target=(1ull<<g.n)+g.n; bool ok=false;
      g.bylen[2]=g.k;
      for(int upto=2;upto<=g.n;upto++) {
        if(upto>=3)g.cycles(upto);
        for(const auto &c:certs)if(c.n==g.n&&c.k==g.k) {
          U numerator=c.S+(c.g-2)*g.k;
          for(int l=3;l<c.g;l++)numerator+=(c.g-l)*(l<=upto?g.bylen[l]:c.upper[l]);
          if(numerator<=c.g*target){passed[upto]++;ok=true;break;}
        }
        if(ok)break;
      }
      if(!ok) {
        full++; U total=0;for(int l=2;l<=g.n;l++)total+=g.bylen[l];
        if(total>maxfull){maxfull=total;maxline=line;}
        if(total>target) {
          cerr<<"COUNTEREXAMPLE "<<line<<" cycles="<<total<<" matching";
          for(auto [u,v]:matching)cerr<<" "<<u<<","<<v;cerr<<endl;return 2;
        }
      }
      if(emit) {
        for(int l=3;l<=g.n;l++)g.cycles(l);
        cerr<<"CHECK "<<line<<" "<<mi;
        for(int l=2;l<=g.n;l++)cerr<<" "<<g.bylen[l];cerr<<endl;
      }
      mi++;
    }
    if(inputs%1000000==0)cerr<<"progress "<<expectedn<<","<<expectedk<<" inputs="<<inputs<<" instances="<<instances<<endl;
  }
  double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
  cout<<"{\"n\":"<<expectedn<<",\"k\":"<<expectedk<<",\"underlying_graphs\":"<<inputs
      <<",\"without_matching\":"<<rejected<<",\"multigraph_instances\":"<<instances
      <<",\"full_cycle_counts\":"<<full<<",\"maximum_full_count\":"<<maxfull
      <<",\"passed_after_length\":{";
  bool first=true;for(int l=2;l<=19;l++)if(passed[l]){if(!first)cout<<",";first=false;cout<<"\""<<l<<"\":"<<passed[l];}
  cout<<"},\"seconds\":"<<seconds<<"}"<<endl;
}
