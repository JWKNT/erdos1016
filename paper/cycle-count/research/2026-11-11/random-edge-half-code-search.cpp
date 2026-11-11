// Random projective binary codes: exact minimal-support and coordinate counts.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
int main(int argc,char**argv) {
  int r=argc>1?atoi(argv[1]):6, trials=argc>2?atoi(argv[2]):200000;
  mt19937_64 rng(10161111+r);
  int q=(1<<r)-1,checked=0,proper=0,best=-1000000,bestm=0,bestsize=0;
  vector<int> universe(q),bestcols,bestwords;
  iota(universe.begin(),universe.end(),1);
  for(int rep=0;rep<trials;rep++) {
    int m=r+int(rng()%min(q-r+1,3*r+1));
    m=min(m,63);
    shuffle(universe.begin(),universe.end(),rng);
    vector<int> cols(universe.begin(),universe.begin()+m);
    vector<pair<uint64_t,int>> code;bool spanning=true;
    for(int w=1;w<=q;w++) {
      uint64_t a=0;
      for(int j=0;j<m;j++) if(__builtin_parity(unsigned(w&cols[j])))a|=uint64_t(1)<<j;
      if(!a){spanning=false;break;}
      code.push_back({a,w});
    }
    if(!spanning)continue;
    checked++;
    sort(code.begin(),code.end(),[](auto a,auto b){
      int ca=__builtin_popcountll(a.first),cb=__builtin_popcountll(b.first);
      return ca<cb || (ca==cb && a.first<b.first);
    });
    vector<pair<uint64_t,int>> minimal;
    for(auto a:code) {
      bool good=true;
      for(auto b:minimal) if((a.first&b.first)==b.first){good=false;break;}
      if(good)minimal.push_back(a);
    }
    if(int(minimal.size())==q)continue;
    proper++;
    vector<int> frequencies(m);
    for(auto a:minimal) for(uint64_t rem=a.first;rem;rem&=rem-1)
      frequencies[__builtin_ctzll(rem)]++;
    int score=2**min_element(frequencies.begin(),frequencies.end())-minimal.size();
    if(score>best) {
      best=score;bestm=m;bestsize=minimal.size();bestcols=cols;bestwords.clear();
      for(auto a:minimal)bestwords.push_back(a.second);
    }
    if(score>0) {
      cout<<"{\"status\":\"EXACT COUNTEREXAMPLE\",\"rank\":"<<r<<",\"columns\":[";
      for(int j=0;j<m;j++)cout<<(j?",":"")<<cols[j];
      cout<<"],\"minimal_words\":[";
      for(int j=0;j<int(minimal.size());j++)cout<<(j?",":"")<<minimal[j].second;
      cout<<"],\"coordinate_counts\":[";
      for(int j=0;j<m;j++)cout<<(j?",":"")<<frequencies[j];
      cout<<"]}\n";return 0;
    }
  }
  cout<<"{\"status\":\"no counterexample found\",\"rank\":"<<r
      <<",\"trials\":"<<trials<<",\"spanning_checked\":"<<checked
      <<",\"proper_minimal_sets\":"<<proper<<",\"best_minimum_double_surplus\":"<<best
      <<",\"best_columns\":[";
  for(int j=0;j<int(bestcols.size());j++)cout<<(j?",":"")<<bestcols[j];
  cout<<"],\"best_minimal_words\":[";
  for(int j=0;j<int(bestwords.size());j++)cout<<(j?",":"")<<bestwords[j];
  cout<<"]}\n";
}
