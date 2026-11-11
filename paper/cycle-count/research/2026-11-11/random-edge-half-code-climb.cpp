// Adversarial mutations and structured families of projective binary codes.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
struct Result {
  bool valid=false; int count=0,bad=999999,margin=-999999;
  double quality=-1e20;
  vector<int> words,freq;
};
Result evaluate(const vector<int>& cols,int r) {
  Result out; int q=(1<<r)-1,m=cols.size();
  if(m<r || m>63)return out;
  vector<pair<uint64_t,int>> code;
  for(int w=1;w<=q;w++) {
    uint64_t a=0;
    for(int j=0;j<m;j++) if(__builtin_parity(unsigned(w&cols[j])))a|=uint64_t(1)<<j;
    if(!a)return out;
    code.push_back({a,w});
  }
  sort(code.begin(),code.end(),[](auto a,auto b){
    int ca=__builtin_popcountll(a.first),cb=__builtin_popcountll(b.first);
    return ca<cb || (ca==cb && a.first<b.first);
  });
  vector<uint64_t> minimal;
  out.freq.assign(m,0);
  for(auto a:code) {
    bool good=true;
    for(auto b:minimal) if((a.first&b)==b){good=false;break;}
    if(good) {
      minimal.push_back(a.first);out.words.push_back(a.second);
      for(uint64_t rem=a.first;rem;rem&=rem-1)out.freq[__builtin_ctzll(rem)]++;
    }
  }
  out.count=minimal.size();
  if(out.count==q)return out;
  out.valid=true;out.bad=0;out.margin=q;int deficit=0;
  for(int f:out.freq) {
    int d=2*f-out.count;
    out.margin=min(out.margin,d);
    if(d<=0){out.bad++;deficit+=1-d;}
  }
  out.quality=-out.bad-double(deficit)/(4*m*q);
  return out;
}
void print(const vector<int>&cols,const Result&a,int r,int evaluated,const char*status) {
  cout<<"{\"status\":\""<<status<<"\",\"rank\":"<<r<<",\"evaluated\":"<<evaluated
      <<",\"nonmajority_coordinates\":"<<a.bad<<",\"minimum_double_surplus\":"<<a.margin
      <<",\"minimal_count\":"<<a.count<<",\"columns\":[";
  for(int j=0;j<int(cols.size());j++)cout<<(j?",":"")<<cols[j];
  cout<<"],\"minimal_words\":[";
  for(int j=0;j<int(a.words.size());j++)cout<<(j?",":"")<<a.words[j];
  cout<<"],\"coordinate_counts\":[";
  for(int j=0;j<int(a.freq.size());j++)cout<<(j?",":"")<<a.freq[j];
  cout<<"]}\n";
}
int main(int argc,char**argv) {
  int r=argc>1?atoi(argv[1]):6,steps=argc>2?atoi(argv[2]):100000;
  int q=(1<<r)-1,evaluated=0;
  mt19937_64 rng(20261111+r);
  vector<int> universe(q);iota(universe.begin(),universe.end(),1);
  vector<vector<int>> starts;
  // Spikes and structured subfamilies of the complete-graph cut code.
  for(int kind=0;kind<8;kind++) {
    vector<int> s;
    for(int x=1;x<=q;x++) {
      int w=__builtin_popcount(unsigned(x));
      bool take=kind==0?(w==1 || w==r-1 || w==r):
        kind==1?(w==1 || w==r-1):
        kind==2?(w==1 || w==2):
        kind==3?(w==1 || w==2 || w==r):
        kind==4?(w==1 || w==r-2):
        kind==5?(w==1 || (x&3)!=3):
        kind==6?(w==1 || (w%2==1)):
                  (w==1 || w==r/2);
      if(take)s.push_back(x);
    }
    if(s.size()<=63)starts.push_back(s);
  }
  Result best;vector<int> bestcols;
  Result cur;vector<int> cols;
  for(int i=0;i<steps;i++) {
    if(i%1000==0 || !cur.valid) {
      if(i/1000<int(starts.size()))cols=starts[i/1000];
      else {
        shuffle(universe.begin(),universe.end(),rng);
        int m=r+2+int(rng()%min(q-r-1,2*r));
        cols.assign(universe.begin(),universe.begin()+m);
      }
      cur=evaluate(cols,r);evaluated++;
      if(!cur.valid)continue;
    }
    if(cur.quality>best.quality){best=cur;bestcols=cols;}
    if(cur.bad==0){print(cols,cur,r,evaluated,"EXACT COUNTEREXAMPLE");return 0;}
    vector<int> trial=cols;
    int mode=rng()%4;
    if(mode==0 && trial.size()>size_t(r))trial.erase(trial.begin()+rng()%trial.size());
    else if(mode==1 && trial.size()<size_t(min(q,63))) {
      int x;
      do{x=1+rng()%q;}while(find(trial.begin(),trial.end(),x)!=trial.end());
      trial.push_back(x);
    } else {
      int pos=rng()%trial.size(),x;
      do{x=1+rng()%q;}while(find(trial.begin(),trial.end(),x)!=trial.end());
      trial[pos]=x;
    }
    Result next=evaluate(trial,r);evaluated++;
    if(!next.valid)continue;
    double temp=0.15*(1.0-(i%1000)/1000.0)+0.005;
    double u=(rng()+0.5)/(double(UINT64_MAX)+1);
    if(next.quality>=cur.quality || log(u)<(next.quality-cur.quality)/temp) {
      cols=move(trial);cur=move(next);
    }
  }
  print(bestcols,best,r,evaluated,"no counterexample found");
}
