#include "header.hpp"
#include "backward.hpp"
#include <cadical.hpp>

struct max_clique {
  int n;
  int goal;
  vector<vector<unsigned char>> adj;

  vector<vector<int>> es;
  vector<vector<tuple<int,int> > > vs;

  struct vertex {
    vertex() = default;
    vertex(int id_) {
      id = id_;
    }

    int       id;
    int       bound;
  };

  vector<vector<vertex>> P;
  vector<int> level;

  vector<int> colors;
  vector<vector<vertex>> colorVertices;
  vector<int> vertexColor;
  vector<int> vertexExplored;

  vector<int> maxClique;

  max_clique(int goal_, vector<vector<int>> G) {
    goal = goal_;
    maxClique = {0};

    n = G.size();
    adj.assign(n, vector<unsigned char>(n,0));
    FOR(i,n) for(int j : G[i]) adj[i][j] = 1;

    es.resize(1); vs.resize(1); vs[0].resize(n);

    FOR(i,n) {
      get<0>(vs[0][i]) = es[0].size();
      FOR(j,n) {
        if(adj[i][j]) {
          es[0].emplace_back(j);
        }
      }
      get<1>(vs[0][i]) = es[0].size();
    }

    P.resize(2);
    level.assign(n,0);

    colors.assign(n+3,0);
    colorVertices.resize(n+3);
    vertexColor.assign(n,0);
    vertexExplored.assign(n,0);
  }

  void initial_sort(vector<int> const& s) {
    int sz = s.size();
    sort(all(P[sz]), [&](vertex const& a, vertex const& b) {
      return get<1>(vs[sz][a.id]) - get<0>(vs[sz][a.id])
        > get<1>(vs[sz][b.id]) - get<0>(vs[sz][b.id]);
      });
  }


  void induce(vector<int> const& s) {
    int sz = s.size();
    if((int)es.size() == sz) {
      es.emplace_back();
      vs.emplace_back(n);
    }
    auto const& Pcur = P[sz];
    auto const& esPrev = es[sz-1];
    auto const& vsPrev = vs[sz-1];
    auto& esCur = es[sz];
    auto& vsCur = vs[sz];


    esCur.clear();
    FOR(w,Pcur.size()) {
      int i = Pcur[w].id;
      get<0>(vsCur[i]) = esCur.size();
      int from = get<0>(vsPrev[i]), to = get<1>(vsPrev[i])-1;
      FORU(ei,from,to) {
        auto const& e = esPrev[ei];
        if(level[e] == sz) {
          esCur.pb(e);
        }
      }
      get<1>(vsCur[i]) = esCur.size();
    }
  }

  void color(vector<int> const& s) {
    int sz = s.size();
    int max_k = 1;
    colors[1] = colors[2] = 0;
    int date = 0;

    FOR(w, P[sz].size()) {
      int i = P[sz][w].id;
      date += 1;
      int from = get<0>(vs[sz][i]), to = get<1>(vs[sz][i])-1;

      if(sz+1+(to-from+1) < (int)maxClique.size()+1) {
        level[i]--;
      }else{
        FORU(jk,from,to) if(vertexExplored[es[sz][jk]]) colors[vertexColor[es[sz][jk]]] = date;

        int k = 1; while(colors[k] == date) k += 1;
        if(k > max_k) { max_k += 1; colors[max_k+1] = 0; }
        vertexExplored[i] = 1; vertexColor[i] = k;
        colorVertices[k].pb(P[sz][w]);
      }
    }

    P[sz].clear();
    FORU(k,1,max_k) {
      for(auto const& v : colorVertices[k]) {
        vertexExplored[v.id] = 0;
        P[sz].pb(v);
        P[sz].back().bound = k;
      }
      colorVertices[k].clear();
    }
  }

  void searchAt(int i) {
    vector<int> s; s.pb(i);
    FOR(j,i) if(adj[i][j]) {
      level[j]++;
      P[1].pb(vertex { (int)j });
    }
    induce(s);
    initial_sort(s);
    color(s);
    branch(s);
    assert(P[1].empty());
  }

  void search(){
    FOR(i,n) {
      searchAt(i);
    }
  }

  void branch(vector<int> const& s){
    int sz = s.size();
    while((int)maxClique.size() < goal
          && !P[sz].empty()
          && sz + P[sz].size() >= (maxClique.size()+1)) {
      vertex v = P[sz].back();

      level[v.id]--;
      P[sz].pop_back();

      if((int)P.size() == sz+1) P.emplace_back();

      if(sz + v.bound <= (int)maxClique.size()) continue;
      for(auto const& w : P[sz]) if(adj[v.id][w.id]) {
          level[w.id]++;
          P[sz+1].emplace_back(w);
        }
      vector<int> s2 = s; s2.pb(v.id);
      if(sz+1 > (int)maxClique.size()) { maxClique = s2; }
      induce(s2);
      color(s2);
      if(!P[sz+1].empty()) branch(s2);
    }
    while(!P[sz].empty()) {
      vertex const& v = P[sz].back();
      level[v.id]--;
      P[sz].pop_back();
    }
  }
};


struct union_find {
  vector<int> A;
  vector<int> SZ;

  union_find(int n) : A(n), SZ(n, 1) {
    iota(all(A), 0);
  }

  void add_node() {
    A.pb(A.size());
    SZ.pb(1);
  }

  int find(int a) {
    return A[a] == a ? a : A[a] = find(A[a]);
  }

  bool unite(int a, int b) {
    a = find(a); b = find(b);
    if(SZ[a] > SZ[b]) swap(a,b);
    if(a == b) return false;
    A[a] = b;
    SZ[b] += SZ[a];
    return true;
  }
};

struct layout {
  int size;
  vector<int> tag;
  vector<array<int, 6>> graph;
  int start;

  void generate(int size_) {
    size = size_;
    tag.resize(size);
    FOR(i, size) tag[i] = i%4;
    rng.shuffle(tag);
    graph.resize(size);
    FOR(i, size) FOR(j, 6) graph[i][j] = rng.random32(size);
    start = rng.random32(size);
  }

  vector<int> evaluate_query(vector<int> const& q) {
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
};

bool test_equivalence(layout const& a, layout const& b) {
  int size = a.size;
  set<array<int, 2>> pairs;
  auto dfs = [&](auto &&dfs, int i, int j) -> void {
    if(pairs.insert({i,j}).second) {
      FOR(k, 6) {
        dfs(dfs, a.graph[i][k], b.graph[j][k]);
      }
    }
  };
  dfs(dfs, a.start, b.start);
  for(auto [x,y] : pairs) if(a.tag[x] != b.tag[y]) {
      return false;
    }
  return true;
}

const int num_patterns = 100;
const int pattern_size = 24*18-1; // 16
const int num_queries  = 3;

void solve(int size) {
  layout L;
  L.generate(size);

  const int query_size = 18 * size;
  const int patterns_per_query = query_size / (1+pattern_size);

  vector<vector<int>> patterns(num_patterns);
  FOR(i, num_patterns) FOR(j, pattern_size) patterns[i].pb(rng.random32(6));

  vector<vector<array<int, 2>>> queries_data(num_queries);
  vector<vector<int>> queries(num_queries);
  FOR(i, num_queries) FOR(j, patterns_per_query) {
    int x = rng.random32(6);
    int ipat = rng.random32(patterns.size());
    queries_data[i].pb({x,ipat});
    queries[i].pb(x);
    queries[i].insert(end(queries[i]), all(patterns[ipat]));
  }

  vector<vector<int>> answers(num_queries);
  FOR(i, num_queries) answers[i] = L.evaluate_query(queries[i]);

  vector<vector<int>> answers_full(num_queries);
  FOR(i, num_queries) answers_full[i] = L.evaluate_query_full(queries[i]);
  vector<int> concat_full;
  FOR(i, num_queries) concat_full.insert(end(concat_full), all(answers_full[i]));

  int N = 0;

  vector<int> tag;
  vector<array<int, 2>> to;
  map<tuple<int, vector<int>>, vector<int>> by_key;

  FOR(i, num_queries) {
    by_key[{-1, {}}].pb(N);
    FOR(j, queries[i].size()) {
      to.pb({ queries[i][j], N+1+j });
    }
    to.pb({-1, -1});
    N += 1;

    FOR(j, answers[i].size()) tag.pb(answers[i][j]);

    FOR(j, patterns_per_query) {
      auto [x,y] = queries_data[i][j];

      vector<int> k;
      FOR(x, pattern_size+1) {
        k.pb(answers[i][1+j*(pattern_size+1)+x]);
      }

      by_key[{y, k}].pb(N + pattern_size);
      N += 1+pattern_size;
    }
  }
  debug(N, to.size());

  union_find uf(N);

  for(auto const& p : by_key) {
    for(int i : p.second) {
      if(concat_full[i] != concat_full[p.second[0]]){
        return;
      }
      uf.unite(i, p.second[0]);
    }
  }

  while(1) {
    bool imp = 0;
    map<array<int,2>, vector<int>> part;
    FOR(i, N) if(to[i][0] != -1) part[{uf.find(i), to[i][0]}].pb(to[i][1]);
    for(auto const& p : part) {
      for(int i : p.second) {
        if(uf.unite(i, p.second[0])) {
          imp = 1;
        }
      }
    }
    if(!imp) break;
  }

  FOR(i, N) {
    runtime_assert(concat_full[i] == concat_full[uf.find(i)]);
  }

  FOR(i, N) runtime_assert(tag[i] == tag[uf.find(i)]);

  int M = 0;
  vector<int> root(N, -1);
  vector<int> root_tag(N);
  FOR(i, N) if(root[uf.find(i)] == -1) {
    root[uf.find(i)] = M;
    root_tag[M] = tag[uf.find(i)];
    M += 1;
  }

  vector<array<int, 6>> root_to(M);
  FOR(i, M) FOR(j, 6) root_to[i][j] = -1;

  map<array<int,2>, vector<int>> part;
  FOR(i, N) if(to[i][0] != -1) part[{uf.find(i), to[i][0]}].pb(to[i][1]);

  FOR(i, N) if(uf.find(i) == i) {
    FOR(j, 6) {
      array<int, 2> key = {i, j};
      if(part.count(key)) {
        root_to[root[i]][j] = root[uf.find(part[key][0])];
      }
    }
  }
  debug(M);

  vector<vector<int>> DIFF(M, vector<int>(M, 0));
  vector<vector<int>> G(M);
  FOR(i, M) FOR(j, i) if(root_tag[i] != root_tag[j]) DIFF[i][j] = DIFF[j][i] = 1;
  while(1) {
    bool imp = 0;
    FOR(i, M) FOR(j, i) if(!DIFF[i][j]) FOR(k, 6) {
        if(root_to[i][k] != -1 && root_to[j][k] != -1
           && DIFF[root_to[i][k]][root_to[j][k]]) {
          imp = 1;
          DIFF[i][j] = DIFF[j][i] = 1;
        }
    }
    if(!imp) break;
  }
  int ndiff = 0;
  FOR(i, M) FOR(j, i) if(DIFF[i][j]) {
    ndiff += 1;
    G[i].pb(j);
    G[j].pb(i);
  }
  debug(ndiff);
  max_clique MC(size, G);
  MC.search();
  debug(MC.maxClique.size());

  if((int)MC.maxClique.size() < size) return;

  for(int a : MC.maxClique) for(int b : MC.maxClique) if(a != b) {
        runtime_assert(DIFF[a][b]);
    }

  unique_ptr<CaDiCaL::Solver> solver = make_unique<CaDiCaL::Solver>();

  debug(root_to);

  int nv = 0;
  vector<vector<int>> V(M, vector<int>(size));
  FOR(i, M) FOR(j, size) V[i][j] = ++nv;
  vector<vector<array<int, 6>>> TO(size);
  FOR(i, size) TO[i].resize(size);
  FOR(i, size) FOR(j, size) FOR(k, 6) TO[i][j][k] = ++nv;

  debug(MC.maxClique);
  FOR(i, size) {
    solver->add(V[MC.maxClique[i]][i]);
    solver->add(0);
  }
  FOR(i, M) FOR(j, size) if(DIFF[i][MC.maxClique[j]]) {
    solver->add(-V[i][j]);
    solver->add(0);
  }
  FOR(i, M) {
    FOR(j, size) solver->add(V[i][j]);
    solver->add(0);
  }
  FOR(i, M) FOR(j1, size) FOR(j2, j1) {
    solver->add(- V[i][j1]);
    solver->add(- V[i][j2]);
    solver->add(0);
  }
  FOR(i, M) FOR(k, 6) if(root_to[i][k] != -1) {
    FOR(a, size) FOR(b, size) {
      solver->add(- TO[a][b][k]);
      solver->add(- V[i][a]);
      solver->add(V[root_to[i][k]][b]);
      solver->add(0);
    }
  }
  FOR(i, size) FOR(k, 6) {
    FOR(j, size) solver->add(TO[i][j][k]);
    solver->add(0);
  }
  FOR(i, size) FOR(k, 6) {
    FOR(j1, size) FOR(j2, j1){
      solver->add(-TO[i][j1][k]);
      solver->add(-TO[i][j2][k]);
      solver->add(0);
    }
  }

  int res = solver->solve();
  debug(res);

  if(res == 10) {
    // FOR(i, M) FOR(j, size) if(solver->val(V[i][j]) > 0) {
    //   debug(i,j);
    // }
    
    // FOR(a, size) FOR(k, 6) FOR(b, size) if(solver->val(TO[a][b][k]) > 0) {
    //   debug(a,k,b);
    // }

    layout out_layout;
    out_layout.size = size;
    out_layout.tag.resize(size);
    FOR(i, size) out_layout.tag[i] = root_tag[MC.maxClique[i]];
    out_layout.graph.resize(size);
    FOR(a, size) FOR(k, 6) FOR(b, size) if(solver->val(TO[a][b][k]) > 0) {
      out_layout.graph[a][k] = b;
    }
    if(int i = root[0]; 1) FOR(j, size) if(solver->val(V[i][j]) > 0) {
        out_layout.start = j;
      }

    FOR(i, num_queries) {
      auto a = out_layout.evaluate_query(queries[i]);
      debug(answers[i]);
      debug(a);
      debug(answers[i] == a);
    }

    bool ok = test_equivalence(L, out_layout);
    debug(ok);

    if(!ok) return;

    exit(0);
  }
}

int main() {
  backward::SignalHandling sh;

  while(1) {
    solve(24);
  }

  return 0;
}
