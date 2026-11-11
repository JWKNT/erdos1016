// Exhaust Hamiltonian four-poles of each specified order, with a fixed cycle.
// A result is exhaustive only for this construction class.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
int n,h,ports[4];
vector<uint64_t> adj;
vector<pair<int,int>> chords,best;
long long tested,saturated,best_t,max_t,max_tradeoff;
long long tradeoff_defect,tradeoff_through;
long long max_nonfull_forest,max_t_minus_d;
vector<pair<int,int>> forest_chords;
vector<int> forest_ports;
long long dfs(int u,int target,uint64_t seen){
  if(u==target)return 1;
  auto a=adj[u]&~seen;long long ans=0;
  while(a){int v=__builtin_ctzll(a);a&=a-1;ans+=dfs(v,target,seen|(1ULL<<v));}
  return ans;
}
long long disjoint(int u,int target,int s,int t,uint64_t seen){
  if(u==target)return dfs(s,t,seen|(1ULL<<s));
  auto a=adj[u]&~seen&~(1ULL<<s)&~(1ULL<<t);long long ans=0;
  while(a){int v=__builtin_ctzll(a);a&=a-1;ans+=disjoint(v,target,s,t,seen|(1ULL<<v));}
  return ans;
}
void evaluate(){
  ++tested;
  long long sum_t=0;
  long long p[4][4]={};
  for(int a=0;a<4;++a)for(int b=a+1;b<4;++b)p[a][b]=p[b][a]=dfs(ports[a],ports[b],1ULL<<ports[a]);
  for(int mate=1;mate<4;++mate){
    vector<int> r;for(int z=1;z<4;++z)if(z!=mate)r.push_back(z);
    long long defect=4*(1LL<<h)-p[0][r[0]]-p[0][r[1]]-p[mate][r[0]]-p[mate][r[1]];
    long long t=disjoint(ports[0],ports[r[0]],ports[mate],ports[r[1]],1ULL<<ports[0])
               +disjoint(ports[0],ports[r[1]],ports[mate],ports[r[0]],1ULL<<ports[0]);
    sum_t+=t;
    max_t=max(max_t,t);
    max_t_minus_d=max(max_t_minus_d,t-defect);
    if(2*t-defect>max_tradeoff){max_tradeoff=2*t-defect;tradeoff_defect=defect;tradeoff_through=t;}
    if(defect==0){++saturated;if(t>best_t){best_t=t;best=chords;}}
  }
  long long forest=sum_t/2;
  if(forest<(1LL<<h)&&forest>max_nonfull_forest){
    max_nonfull_forest=forest;forest_chords=chords;
    forest_ports.assign(ports,ports+4);
  }
}
void match(uint64_t remaining){
  if(!remaining){evaluate();return;}
  int a=__builtin_ctzll(remaining);remaining&=remaining-1;
  auto choices=remaining&~adj[a];
  while(choices){
    int b=__builtin_ctzll(choices);choices&=choices-1;
    adj[a]|=1ULL<<b;adj[b]|=1ULL<<a;chords.push_back({a,b});
    match(remaining&~(1ULL<<b));
    chords.pop_back();adj[a]&=~(1ULL<<b);adj[b]&=~(1ULL<<a);
  }
}
int main(int argc,char**argv){
  int hi=argc>1?atoi(argv[1]):6;
  for(h=1;h<=hi;++h){
    n=2*h+2;adj.assign(n,0);tested=saturated=best_t=max_t=max_nonfull_forest=0;max_tradeoff=max_t_minus_d=-1000000000;forest_ports.clear();forest_chords.clear();
    for(int i=0;i<n;++i){int j=(i+1)%n;adj[i]|=1ULL<<j;adj[j]|=1ULL<<i;}
    ports[0]=0;
    for(ports[1]=1;ports[1]<n;++ports[1])for(ports[2]=ports[1]+1;ports[2]<n;++ports[2])for(ports[3]=ports[2]+1;ports[3]<n;++ports[3]){
      uint64_t remaining=(1ULL<<n)-1;
      for(int p:ports)remaining&=~(1ULL<<p);
      match(remaining);
    }
    cout<<"{\"rank\":"<<h<<",\"vertices\":"<<n<<",\"tested\":"<<tested<<",\"saturated_port_splits\":"<<saturated<<",\"max_saturated_through_pairs\":"<<best_t<<",\"max_all_through\":"<<max_t<<",\"max_2T_minus_D\":"<<max_tradeoff<<",\"tradeoff_D\":"<<tradeoff_defect<<",\"tradeoff_T\":"<<tradeoff_through<<",\"max_T_minus_D\":"<<max_t_minus_d<<",\"max_nonfull_forest\":"<<max_nonfull_forest<<",\"forest_ports\":[";
    for(size_t i=0;i<forest_ports.size();++i)cout<<(i?",":"")<<forest_ports[i];
    cout<<"],\"forest_chords\":[";
    for(size_t i=0;i<forest_chords.size();++i)cout<<(i?",":"")<<"["<<forest_chords[i].first<<","<<forest_chords[i].second<<"]";
    cout<<"]}"<<endl;
  }
}
