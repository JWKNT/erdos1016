// Exact affine-forest census after deleting two nonincident edges.
#define main switch_driver
#include "four-forest-gap-switch.cpp"
#undef main
#include <set>
#include <queue>

int main() {
  for(auto [n,shifts]:vector<pair<int,vector<int>>>{{14,{5,-5}},{24,{12,7,-7}}}) {
    set<Edge> unique;
    auto put=[&](int a,int b){if(a>b)swap(a,b);unique.insert({a,b});};
    for(int i=0;i<n;++i) {
      put(i,(i+1)%n);
      put(i,(i+shifts[i%shifts.size()]+n)%n);
    }
    Graph core{n,vector<Edge>(unique.begin(),unique.end()),{}};
    vector<int> degree(n);
    for(auto[a,b]:core.edges){++degree[a];++degree[b];}
    if(any_of(degree.begin(),degree.end(),[](int d){return d!=3;}))return 2;
    int girth=n+1;
    for(int ignored=0;ignored<(int)core.edges.size();++ignored) {
      auto[a,b]=core.edges[ignored];vector<int> dist(n,-1);dist[a]=0;queue<int> q;q.push(a);
      while(!q.empty()) {
        int u=q.front();q.pop();
        for(int e=0;e<(int)core.edges.size();++e)if(e!=ignored) {
          auto[x,y]=core.edges[e];int v=x==u?y:y==u?x:-1;
          if(v>=0&&dist[v]<0){dist[v]=dist[u]+1;q.push(v);}
        }
      }
      if(dist[b]>=0)girth=min(girth,dist[b]+1);
    }
    int rank=core.edges.size()-n-1;long long best=1LL<<rank,checked=0,full=0;
    Graph witness;
    for(int i=0;i<(int)core.edges.size();++i)for(int j=i+1;j<(int)core.edges.size();++j) {
      auto[a,b]=core.edges[i];auto[c,d]=core.edges[j];
      if(a==c||a==d||b==c||b==d)continue;
      Graph graph{n,{}, {a,b,c,d}};
      for(int k=0;k<(int)core.edges.size();++k)if(k!=i&&k!=j)graph.edges.push_back(core.edges[k]);
      long long bad=bad_count(graph,(1LL<<rank)+1);
      if(bad>(1LL<<rank))continue; // disconnected deletion
      ++checked;full+=bad==0;
      if(bad<best){best=bad;witness=graph;}
    }
    cout<<"{\"kind\":\"high_girth_summary\",\"core_vertices\":"<<n
        <<",\"core_girth\":"<<girth<<",\"rank\":"<<rank<<",\"checked_poles\":"<<checked
        <<",\"full_poles\":"<<full<<",\"minimum_bad\":"<<best
        <<",\"total\":"<<(1LL<<rank)<<"}"<<endl;
    print_graph(witness,best,"high_girth_best",0);
  }
  return 0;
}
