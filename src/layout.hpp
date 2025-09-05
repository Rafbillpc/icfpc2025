#pragma once

struct layout {
  int size = 0;
  vector<int> tag;
  vector<array<int, 6>> graph;
  int start;

  void generate(int size_) {
    size = size_;
    tag.resize(size);
    FOR(i, size) tag[i] = i%4;
    rng.shuffle(tag);

    graph.resize(size);

    vector<array<int, 2>> doors;
    FOR(i, size) FOR(j, 6) doors.pb({i,j});
    rng.shuffle(doors);
    while(!doors.empty()) {
      auto [x,a] = doors.back(); doors.pop_back();
      auto [y,b] = doors.back(); doors.pop_back();
      graph[x][a] = y;
      graph[y][b] = x;
    }
    start = rng.random32(size);
  }

  vector<int> evaluate_query(vector<int> const& q) const {
    vector<int> out;
    int x = start;
    out.pb(tag[x]);
    for(int i : q) {
      x = graph[x][i];
      out.pb(tag[x]);
    }
    return out;
  }

  vector<int> evaluate_query_full(vector<int> const& q) {
    vector<int> out;
    int x = start;
    out.pb(x);
    for(int i : q) {
      x = graph[x][i];
      out.pb(x);
    }
    return out;
  }

  vector<array<int, 4>> get_doors() const {
    vector<array<int, 4>> out;
    map<array<int, 2>, vector<int>> S;
    FOR(x, size) FOR(k, 6) {
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
    // for(auto const& p : S) {
    //   runtime_assert(p.second.empty());
    // }
    return out;
  }
};
