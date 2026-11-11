// Exhaustive missing-sector patterns, using an exploratory local-cost table.
// The table's mathematical lower bounds require separate exact proofs.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <vector>
using namespace std;

int main(int argc,char** argv) {
  if(argc<3)return 2;
  ifstream in(argv[1]); array<int,1024> cost; for(int&v:cost)in>>v;
  int maximum=stoi(argv[2]);
  vector<int> pairs,fours;
  for(int mask=0;mask<128;++mask) {
    if(__builtin_popcount((unsigned)mask)==2)pairs.push_back(mask);
    if(__builtin_popcount((unsigned)mask)==4)fours.push_back(mask);
  }
  vector<array<int,21>> removal(35);
  for(int j=0;j<21;++j) {
    vector<int> complement_pairs;
    for(int e:pairs)if(!(e&pairs[j]))complement_pairs.push_back(e);
    for(int i=0;i<35;++i) {
      removal[i][j]=0;
      for(int k=0;k<10;++k)if((pairs[j]|complement_pairs[k])==fours[i])
        removal[i][j]=1<<k;
    }
  }
  // The mask order above differs from lexicographic edge order. Relabel the
  // local lookup once, consistently for every complementary five-set.
  vector<int> lex;
  for(int a=0;a<5;++a)for(int b=a+1;b<5;++b)lex.push_back((1<<a)|(1<<b));
  vector<int> numeric=lex; sort(numeric.begin(),numeric.end());
  array<int,1024> relabeled;
  for(int mask=0;mask<1024;++mask) {
    int converted=0;
    for(int i=0;i<10;++i)if(mask&(1<<i))
      for(int j=0;j<10;++j)if(numeric[i]==lex[j])converted|=1<<j;
    relabeled[mask]=cost[converted];
  }
  for(int d=3;d<=maximum;++d) {
    array<int,21> masks; masks.fill(1023);
    vector<int> chosen,best_example; long long checked=0,minimum_count=0,passed=0;
    int best=1000,target=4*(35-d),filtered_best=1000;
    long long filtered_count=0,filtered_passed=0;
    function<void(int,int)> visit=[&](int start,int remain) {
      if(!remain) {
        ++checked; int value=0;for(int mask:masks)value+=relabeled[mask];
        passed+=value<=target;
        if(value<best){best=value;minimum_count=0;best_example=chosen;}
        minimum_count+=value==best;
        int eligible_vertices=0;
        for(int v=0;v<7;++v) {
          int degree=0;for(int mask:chosen)degree+=(mask>>v)&1;
          eligible_vertices+=degree<=d-3;
        }
        if(eligible_vertices>=d-3) {
          ++filtered_count;filtered_best=min(filtered_best,value);
          filtered_passed+=value<=target;
        }
        return;
      }
      for(int i=start;i<=35-remain;++i) {
        for(int j=0;j<21;++j)masks[j]^=removal[i][j];
        chosen.push_back(fours[i]);visit(i+1,remain-1);chosen.pop_back();
        for(int j=0;j<21;++j)masks[j]^=removal[i][j];
      }
    };
    visit(0,d);
    cout<<"{\"missing_four_sectors\":"<<d<<",\"patterns\":"<<checked
        <<",\"minimum_local_cost\":"<<best<<",\"minimum_count\":"<<minimum_count
        <<",\"global_available_mass\":"<<target<<",\"patterns_passing_local_cost\":"<<passed
        <<",\"prism_count_eligible_patterns\":"<<filtered_count
        <<",\"prism_count_minimum_local_cost\":"<<filtered_best
        <<",\"prism_count_patterns_passing_local_cost\":"<<filtered_passed
        <<",\"example_port_masks\":[";
    for(int i=0;i<(int)best_example.size();++i)cout<<(i?",":"")<<best_example[i];
    cout<<"]}"<<endl;
  }
}
