#include "header.hpp"
#include "api.hpp"
#include "layout.hpp"
#include "backward.hpp"
#include "kissat.h"

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

bool test_equivalence(layout const& a, layout const& b) {
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

struct QUERIES {
  virtual vector<vector<int>> query(vector<vector<array<int,2>>> const& q) const = 0;
};

struct layout_queries : QUERIES {
  layout const& L;
  layout_queries(layout const& L_) : L(L_) { }
  virtual vector<vector<int>> query(vector<vector<array<int,2>>> const& q) const override final {
    vector<vector<int>> R;
    for(auto const& v : q) R.pb(L.evaluate_query(v));
    return R;
  }
};

struct api_queries : QUERIES {
  virtual vector<vector<int>> query(vector<vector<array<int,2>>> const& q) const override final {
    vector<string> R;
    for(auto const& v : q) {
      R.eb();
      for(auto [i,t] : v) {
        R.back() += ('0'+i);
        if(t != -1) {
          R.back() += "[";
          R.back() += ('0'+t);
          R.back() += "]";
        }
      }
    }
    return api_explore(R);
  }
};

layout solve_base(QUERIES const& Q, int size, int num_dups, int num_queries) {
  const int query_size = 6 * size;

  vector<vector<array<int,2>>> queries(num_queries);
  FOR(i, num_queries) FOR(j, query_size) {
    queries[i].pb({(int)rng.random32(6), -1});
  }

  vector<vector<int>> answers = Q.query(queries);

  int N = 0;

  vector<int> tag;
  vector<array<int, 6>> to;

  FOR(i, num_queries) {
    FOR(j, queries[i].size()) {
      to.pb({-1,-1,-1,-1,-1,-1});
      to.back()[queries[i][j][0]] = N+1+j;
    }
    to.pb({-1,-1,-1,-1,-1,-1});
    N += queries[i].size()+1;

    FOR(j, answers[i].size()) tag.pb(answers[i][j]);
  }

  vector<u64> h(N);
  FOR(i, N) h[i] = rng.randomInt64();

  map<u64, vector<int>> cache;
  auto max_clique = [&](auto &&max_clique, vector<int> elems) -> vector<int> {
    if(elems.empty()) return {};
    u64 key = 0;
    for(int i : elems) key ^= h[i];
    
    sort(all(elems));
    if(cache.count(key)) return cache[key];
    vector<int> part[4];
    for(int i : elems) {
      part[tag[i]].pb(i);
    }
    vector<int> res;
    FOR(t, 4) if(!part[t].empty()) {
      vector<int> cur = {part[t][0]};
      FOR(j, 6) {
        vector<int> sub;
        map<int,int> pre;
        for(int i : part[t]) {
          if(to[i][j] != -1) {
            sub.pb(to[i][j]);
            pre[to[i][j]] = i;
          }
        }
        vector<int> tmp = max_clique(max_clique, sub);
        if(tmp.size() > cur.size()) {
          cur.clear();
          for(int i : tmp) cur.pb(pre[i]);
        }
      }
      res.insert(end(res), all(cur));
    }
    return cache[key] = res;
  };
  vector<int> E(N); iota(all(E),0);
  auto maxClique = max_clique(max_clique, E);

  debug(maxClique.size());
  if((int)maxClique.size() < size) return {};

  kissat* solver = kissat_init();
  // kissat_set_option(solver, "quiet", 1);

  // unique_ptr<CaDiCaL::Solver> solver = make_unique<CaDiCaL::Solver>();

  int nv = 0;
  vector<vector<int>> V(N, vector<int>(size));
  FOR(i, N) FOR(j, size) V[i][j] = ++nv;
  vector<vector<array<int, 6>>> TO(size);
  FOR(i, size) TO[i].resize(size);
  FOR(i, size) FOR(j, size) FOR(k, 6) TO[i][j][k] = ++nv;

  debug(maxClique);
  FOR(i, size) {
    kissat_add(solver, V[maxClique[i]][i]);
    kissat_add(solver, 0);
  }
  FOR(i, N) FOR(j, size) if(tag[i] != tag[maxClique[j]]) {
    kissat_add(solver, -V[i][j]);
    kissat_add(solver, 0);
  }
  FOR(i, N) {
    FOR(j, size) kissat_add(solver, V[i][j]);
    kissat_add(solver, 0);
  }
  FOR(i, N) FOR(j1, size) FOR(j2, j1) {
    kissat_add(solver, - V[i][j1]);
    kissat_add(solver, - V[i][j2]);
    kissat_add(solver, 0);
  }
  FOR(i, N) FOR(k, 6) if(to[i][k] != -1) {
    FOR(a, size) FOR(b, size) {
      kissat_add(solver, - TO[a][b][k]);
      kissat_add(solver, - V[i][a]);
      kissat_add(solver, V[to[i][k]][b]);
      kissat_add(solver, 0);
    }
  }
  FOR(i, size) FOR(k, 6) {
    FOR(j, size) kissat_add(solver, TO[i][j][k]);
    kissat_add(solver, 0);
  }
  FOR(i, size) FOR(k, 6) {
    FOR(j1, size) FOR(j2, j1){
      kissat_add(solver, -TO[i][j1][k]);
      kissat_add(solver, -TO[i][j2][k]);
      kissat_add(solver, 0);
    }
  }

  FOR(i, size) FOR(j, size) FOR(k, 6) {
    kissat_add(solver, -TO[i][j][k]);
    FOR(k2, 6) {
      kissat_add(solver, TO[j][i][k2]);
    }
    kissat_add(solver, 0);
  }

  debug("start SAT");
  int res = kissat_solve(solver);
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
    FOR(i, size) out_layout.tag[i] = tag[maxClique[i]];
    out_layout.graph.resize(size);
    FOR(a, size) FOR(k, 6) FOR(b, size) if(kissat_value(solver, TO[a][b][k]) > 0) {
      out_layout.graph[a][k] = b;
    }
    if(int i = 0; 1) FOR(j, size) if(kissat_value(solver, V[i][j]) > 0) {
        out_layout.start = j;
      }

    return out_layout;
  }

  return {};
}

layout solve_dup
(QUERIES const& Q, int size, int num_dups, int num_queries, layout const& base_layout)
{
  debug("HERE");
  exit(0);
  return {};
}

int main() {
  backward::SignalHandling sh;

  int size = 6;
  int num_dups = 2;
  int num_queries1 = 3;
  int num_queries2 = 3;

  // test
  while(1) {
    layout L; L.generate(size, num_dups);
    layout_queries Q(L);
    auto R1 = solve_base(Q, size, num_dups, num_queries1);
    if(R1.size == 0) continue;
    auto R2 = solve_dup(Q, size, num_dups, num_queries2, R1);
    if(R2.size == 0) continue;

    if(test_equivalence(L, R2)) {
      debug("FOUND");
      break;
    }
  }

  // interact
  // int size = 12;
  // int num_queries = 3;
  // auto problem_name = "aleph"; get_problem_name(size);
  // while(1) {
  //   api_queries Q;
  //   api_select(problem_name);
  //   auto R = solve_base(Q, size, num_queries);

  //   if(R.size != 0) {
  //     debug("candidate");
  //     bool correct = api_guess(R);
  //     debug(correct);
  //     if(correct) break;
  //   }
  // }

  return 0;
}
