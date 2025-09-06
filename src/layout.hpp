    #pragma once

struct layout {
  int size = 0;
  int num_dups = 0;
  vector<int> tag;
  vector<array<int, 6>> graph;
  int start;

  void generate(int size_, int num_dups_) {
    size = size_;
    num_dups = num_dups_;
    tag.resize(size*num_dups);
    graph.resize(size*num_dups);

    vector<int> tag0(size);
    FOR(i, size) tag0[i] = i%4;
    rng.shuffle(tag0);
    FOR(i, size*num_dups) tag[i] = tag0[i%size];

    vector<array<int, 2>> doors0;
    FOR(i, size) FOR(j, 6) doors0.pb({i,j});
    rng.shuffle(doors0);
    while(!doors0.empty()) {
      auto [x,a] = doors0.back(); doors0.pop_back();
      auto [y,b] = doors0.back(); doors0.pop_back();
      vector<int> P(num_dups); iota(all(P),0); rng.shuffle(P);
      FOR(i, num_dups) {
        int x1 = x + i * size;
        int y1 = y + P[i] * size;
        graph[x1][a] = y1;
        graph[y1][b] = x1;
      }
    }

    start = rng.random32(size*num_dups);
  }

  vector<int> evaluate_query(vector<array<int,2>> const& q) const {
    auto tag_tmp = tag;
    vector<int> out;
    int x = start;
    out.pb(tag_tmp[x]);
    for(auto [i,t] : q) {
      x = graph[x][i];
      out.pb(tag_tmp[x]);
      if(t != -1) tag_tmp[x] = t;
    }
    return out;
  }

  vector<int> evaluate_query_full(vector<array<int,2>> const& q) const {
    vector<int> out;
    int x = start;
    out.pb(x);
    for(auto [i,t] : q) {
      x = graph[x][i];
      out.pb(x);
    }
    return out;
  }


  vector<array<int, 4>> get_doors() const {
    vector<array<int, 4>> out;
    map<array<int, 2>, vector<int>> S;
    FOR(x, size*num_dups) FOR(k, 6) {
      if(graph[x][k] == x) {
        out.pb({x,k,x,k});
      }else {
        array<int,2> key1 = {x,graph[x][k]};
        array<int,2> key2 = {graph[x][k],x};
        if(S.count(key1)) {
          int k2 = S[key1].back(); S[key1].pop_back();
          out.pb({x,k,graph[x][k],k2});
        }else{
          S[key2].pb(k);
        }
      }
    }
    // for(auto const& p : S) runtime_assert(p.second.empty());
    return out;
  }
};
