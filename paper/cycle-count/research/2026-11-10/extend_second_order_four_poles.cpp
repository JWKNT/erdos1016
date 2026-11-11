// Exhaust all one-square insertions at each step; greedy between steps.
// This does not certify the maximum over graphs of the resulting rank.
#define main unused_search_main
#include "search_second_order_four_poles.cpp"
#undef main

int main(int argc,char**argv){
  int b,m;cin>>b>>m;
  vector<pair<int,int>> edges(m);for(auto &e:edges)cin>>e.first>>e.second;
  int target=argc>1?atoi(argv[1]):15;
  for(;b+2<=target;b+=2){
    Search s(b+2,0);int k=s.n-7;long long best=-1;
    vector<pair<int,int>> winner;
    for(int i=0;i<(int)edges.size();++i)for(int j=i+1;j<(int)edges.size();++j){
      vector<int> ends{edges[i].first,edges[i].second,edges[j].first,edges[j].second};
      for(int mate=1;mate<4;++mate){
        vector<int> order{ends[0],ends[mate]};
        for(int z=1;z<4;++z)if(z!=mate)order.push_back(ends[z]);
        vector<pair<int,int>> candidate;
        for(int z=0;z<(int)edges.size();++z)if(z!=i&&z!=j)candidate.push_back(edges[z]);
        for(int u=0;u<2;++u)for(int v=2;v<4;++v)candidate.push_back({k+u,k+v});
        for(int z=0;z<4;++z)candidate.push_back({order[z],k+z});
        fill(s.adj.begin(),s.adj.end(),0);
        for(auto [u,v]:candidate)s.add(u,v);
        int src=s.n-3,dst=s.n-2,w=s.n-1;
        for(auto [u,v]:vector<pair<int,int>>{{src,w},{dst,w},{src,0},{dst,1},{w,2},{w,3}})s.add(u,v);
        long long val=s.count();
        if(val>best){best=val;winner=candidate;}
      }
    }
    edges=winner;
    cout<<"{\"rank\":"<<b+2<<",\"paths\":"<<best<<",\"excess\":"<<best-(1LL<<(b+1))<<",\"K_edges\":[";
    bool first=true;for(auto [u,v]:edges){if(!first)cout<<",";first=false;cout<<"["<<u<<","<<v<<"]";}
    cout<<"]}"<<endl;
  }
}
