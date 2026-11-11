// Exploratory extensions of an input witness, with exact affine-join counts.
#define main switch_driver
#include "four-forest-gap-switch.cpp"
#undef main

int main(int argc, char** argv) {
  if (argc < 4) return 2;
  ifstream in(argv[1]); Graph seed; int m,k;
  in >> seed.n >> m >> k;
  seed.terminals.resize(k); for (int& v:seed.terminals) in >> v;
  seed.edges.resize(m); for(auto& [u,v]:seed.edges) in >> u >> v;
  int maximum=stoi(argv[2]), width=stoi(argv[3]);
  mt19937_64 rng(326451);
  vector<Graph> current{seed};
  for (int rank=m-seed.n+2; rank<=maximum; ++rank) {
    vector<Graph> next; long long tested=0; bool capped=false;
    shuffle(current.begin(),current.end(),rng);
    for (const Graph& old:current) {
      vector<Edge> pairs;
      for(int i=0;i<(int)old.edges.size();++i)
        for(int j=i+1;j<(int)old.edges.size();++j) pairs.push_back({i,j});
      shuffle(pairs.begin(),pairs.end(),rng);
      for(auto [i,j]:pairs) {
        Graph candidate=extension(old,i,j); ++tested;
        if (bad_count(candidate,2)==1) {
          next.push_back(std::move(candidate));
          if ((int)next.size()>=width) { capped=true; break; }
        }
      }
      if(capped) break;
    }
    cout << "{\"kind\":\"extension_summary\",\"rank\":" << rank
         << ",\"tested\":" << tested << ",\"retained\":" << next.size()
         << ",\"width_reached\":" << (capped?"true":"false") << "}" << endl;
    if(next.empty()) break;
    print_graph(next[0],1,"unique_bad_extension",0);
    current=std::move(next);
  }
}
