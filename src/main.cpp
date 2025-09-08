#include "header.hpp"
#include "api.hpp"
#include "layout.hpp"
#include "kissat.h"

bool test_equivalence(layout const& a, layout const& b) {
  runtime_assert(a.size == b.size && a.num_dups == b.num_dups);
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
  return (int)pairs.size() == a.size * b.num_dups;
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
    auto RET = api_explore(R);
    vector<vector<int>> out;
    FOR(i, q.size()) {
      int at = 1;
      out.eb();
      out.back().pb(RET[i][0]);
      FOR(j, q[i].size()) {
        out.back().pb(RET[i][at]);
        if(q[i][j][1] != -1) at += 1;
        at += 1;
      }
      runtime_assert(at == (int)(RET[i].size()));
    }
    return out;
  }
};

struct queries_t {
  vector<vector<array<int,2>>> queries;
  vector<vector<int>> answers;
};

queries_t make_queries
(QUERIES const& Q, int size, int num_dups, int num_queries, f32 ratio_query1)
{
  const int query_size = num_dups == 1 ? 18 * size : 6 * size * num_dups;

  vector<vector<array<int,2>>> queries(num_queries);
  FOR(i, num_queries) FOR(j, query_size) {
    queries[i].pb({(int)rng.random32(6), -1});
    if(1.0*(i*query_size+j)/query_size/num_queries > ratio_query1) {
      queries[i].back()[1] = rng.random32(4);
    }
  }
  auto answers = Q.query(queries);
  return queries_t {
    queries, answers
  };
}

layout solve_base(queries_t const& Q, int size, int num_dups, int num_queries) {
  auto queries = Q.queries;
  auto answers = Q.answers;

  int N = 0;

  vector<int> tag;
  vector<array<int, 6>> to;

  FOR(i, num_queries) {
    N += 1;
    to.pb({-1,-1,-1,-1,-1,-1});
    tag.pb(answers[i][0]);
    FOR(j, queries[i].size()) {
      if(queries[i][j][1] != -1) break;
      to.back()[queries[i][j][0]] = N;
      N += 1;
      to.pb({-1,-1,-1,-1,-1,-1});
      tag.pb(answers[i][j+1]);
    }
  }

  vector<u64> h(N);
  FOR(i, N) h[i] = rng.randomInt64();

  map<u64, vector<int>> cache;
  auto max_clique = [&](auto &&max_clique, vector<int> elems) -> vector<int> {
    if(elems.empty()) return {};
    if(elems.size() == 1) return elems;
    u64 key = 0;
    for(int i : elems) key ^= h[i];
    
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

  if((int)maxClique.size() < size) return {};

  kissat* solver = kissat_init();
  kissat_set_option(solver, "quiet", 1);
  kissat_set_option(solver, "time", 120);

  int nv = 0;
  vector<vector<int>> V(N, vector<int>(size));
  FOR(i, N) FOR(j, size) V[i][j] = ++nv;
  vector<vector<array<int, 6>>> TO(size);
  FOR(i, size) TO[i].resize(size);
  FOR(i, size) FOR(j, size) FOR(k, 6) TO[i][j][k] = ++nv;

  // V[-][-] is the graph of a function.
  FOR(i, N) {
    FOR(j, size) kissat_add(solver, V[i][j]);
    kissat_add(solver, 0);
  }
  FOR(i, N) FOR(j1, size) FOR(j2, j1) {
    kissat_add(solver, - V[i][j1]);
    kissat_add(solver, - V[i][j2]);
    kissat_add(solver, 0);
  }
  // breaking the symmetry using the maximum clique
  FOR(i, size) {
    kissat_add(solver, V[maxClique[i]][i]);
    kissat_add(solver, 0);
  }
  // if V[i][j] then i mush have the correct label
  FOR(i, N) FOR(j, size) if(tag[i] != tag[maxClique[j]]) {
    kissat_add(solver, -V[i][j]);
    kissat_add(solver, 0);
  }
  // 
  FOR(i, N) FOR(k, 6) if(to[i][k] != -1) {
    FOR(a, size) FOR(b, size) {
      kissat_add(solver, - TO[a][b][k]);
      kissat_add(solver, - V[i][a]);
      kissat_add(solver, V[to[i][k]][b]);
      kissat_add(solver, 0);
    }
  }
  // TO[-][-][-] is the graph of a function (sending (i,k) to j)
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
  // if there exists an edge (i -> j), then there exists an edge (j -> i).
  // (additional constraints would be needed to ensure
  //  that this correspondence is bijective).
  FOR(i, size) FOR(j, size) FOR(k, 6) {
    kissat_add(solver, -TO[i][j][k]);
    FOR(k2, 6) {
      kissat_add(solver, TO[j][i][k2]);
    }
    kissat_add(solver, 0);
  }

  int res = kissat_solve(solver);

  if(res == 10) { // SAT
    layout out_layout;
    out_layout.size = size;
    out_layout.num_dups = 1;
    out_layout.tag.resize(size);
    FOR(i, size) out_layout.tag[i] = tag[maxClique[i]];
    out_layout.graph.resize(size);
    FOR(a, size) FOR(k, 6) FOR(b, size) if(kissat_value(solver, TO[a][b][k]) > 0) {
      out_layout.graph[a][k] = b;
    }
    if(int i = 0; 1) FOR(j, size) if(kissat_value(solver, V[i][j]) > 0) {
        out_layout.start = j;
      }

    kissat_release(solver);
    return out_layout;
  }

  kissat_release(solver);
  return {};
}

layout solve_dup
(queries_t const& Q, int size, int num_dups, int num_queries, layout const& base_layout)
{
  auto queries = Q.queries;
  auto answers = Q.answers;
  int query_size = queries[0].size();

  int N = 0;
  vector<array<int, 6>> to;
  vector<int> at;
  vector<int> is_start;
  vector<vector<int>> rev(num_queries);
  FOR(i, num_queries) {
    int x = base_layout.start;
    at.pb(x);
    is_start.pb(1);
    FOR(j, query_size+1) {
      if(j < query_size) {
        x = base_layout.graph[x][queries[i][j][0]];
        at.pb(x);
        is_start.pb(0);
      }
      to.pb({-1,-1,-1,-1,-1,-1});
      rev[i].pb(N);
      N += 1;
      if(j < query_size) to.back()[queries[i][j][0]] = N;
    }
  }

  kissat* solver = kissat_init();
  kissat_set_option(solver, "quiet", 1);

  int nv = 0;
  vector<vector<int>> V(N, vector<int>(num_dups));
  FOR(i, N) FOR(j, num_dups) V[i][j] = ++nv;
  vector<vector<vector<array<int, 6>>>> TO(size);
  FOR(i, size) TO[i].resize(num_dups);
  FOR(i, size) FOR(a, num_dups) TO[i][a].resize(num_dups);
  FOR(i, size) FOR(a, num_dups) FOR(b, num_dups) FOR(k, 6) TO[i][a][b][k] = ++nv;

  FOR(i, N) {
    FOR(j, num_dups) kissat_add(solver, V[i][j]);
    kissat_add(solver, 0);
  }
  FOR(i, N) {
    FOR(j1, num_dups) FOR(j2, j1) {
      kissat_add(solver, -V[i][j1]);
      kissat_add(solver, -V[i][j2]);
      kissat_add(solver, 0);
    }
  }
  FOR(i, size) FOR(k, 6) {
    FOR(a, num_dups) {
      { FOR(b, num_dups) kissat_add(solver, TO[i][a][b][k]);
        kissat_add(solver, 0);
      }
      FOR(b1, num_dups) FOR(b2, b1) {
        kissat_add(solver, - TO[i][a][b1][k]);
        kissat_add(solver, - TO[i][a][b2][k]);
        kissat_add(solver, 0);
      }
      { FOR(b, num_dups) kissat_add(solver, TO[i][b][a][k]);
        kissat_add(solver, 0);
      }
      FOR(b1, num_dups) FOR(b2, b1) {
        kissat_add(solver, - TO[i][b1][a][k]);
        kissat_add(solver, - TO[i][b2][a][k]);
        kissat_add(solver, 0);
      }
    }
  }
  FOR(i, N) FOR(a, num_dups) FOR(b, num_dups) FOR(k, 6) if(to[i][k] != -1) {
    kissat_add(solver, - TO[at[i]][a][b][k]);
    kissat_add(solver, - V[i][a]);
    kissat_add(solver, V[to[i][k]][b]);
    kissat_add(solver, 0);
  }
  FOR(i, N) if(is_start[i]) {
    kissat_add(solver, V[i][0]);
    kissat_add(solver, 0);
  }

  FOR(i, num_queries) {
    vector<vector<array<int,3>>> X(size);
    FOR(j, query_size) {
      int ans = answers[i][j+1];
      int wrote = queries[i][j][1] == -1 ? ans : queries[i][j][1];
      int when = rev[i][j+1];
      int elem = at[when];
      int k = X[elem].size()-1;
      while(k >= 0 && X[elem][k][2] != ans) {
        // we learn that "X[elem][k][0]" and "when" are different
        // copies of the same node from the base graph
        FOR(a, num_dups) {
          kissat_add(solver, - V[X[elem][k][0]][a]);
          kissat_add(solver, - V[when][a]);
          kissat_add(solver, 0);
        }
        k -= 1;
      }
      X[elem].pb({when, ans, wrote});
    }
  }

  FOR(i, size) FOR(k, 6) FOR(a, num_dups) FOR(b, num_dups) {
    int j = base_layout.graph[i][k];
    kissat_add(solver, -TO[i][a][b][k]);
    FOR(k2, 6) if(base_layout.graph[j][k2] == i) {
      kissat_add(solver, TO[j][b][a][k2]);
    }
    kissat_add(solver, 0);
  }

  int res = kissat_solve(solver);

  if(res == 10) {
    layout out_layout;
    out_layout.size = size;
    out_layout.num_dups = num_dups;
    out_layout.tag.resize(size * num_dups);
    out_layout.graph.resize(size * num_dups);
    out_layout.start = base_layout.start;

    FOR(i, size*num_dups) out_layout.tag[i] = base_layout.tag[i%size];

    FOR(i, size) FOR(a, num_dups) FOR(k, 6) FOR(b, num_dups) {
      if(kissat_value(solver, TO[i][a][b][k]) > 0) {
        out_layout.graph[i+a*size][k] = base_layout.graph[i][k]+b*size;
      }
    }

    kissat_release(solver);

    return out_layout;
  }
  kissat_release(solver);

  return {};
}

int main(int argc, char** argv) {
  backward::SignalHandling sh;

  runtime_assert(argc >= 6);
  int size = atoi(argv[1]);
  int num_dups = atoi(argv[2]);
  int num_queries = atoi(argv[3]);
  f32 ratio = atof(argv[4]);
  int use_api = atoi(argv[5]);
  runtime_assert(3 <= size && size <= 90);
  runtime_assert(1 <= num_dups && num_dups <= 3);
  runtime_assert(1 <= num_queries && num_queries < 10);
  runtime_assert(0.0 <= ratio && ratio <= 1.0);
  runtime_assert(0 <= use_api && use_api <= 1);

  int ntest = 0, nreach1 = 0, nreach2 = 0;

  if(!use_api) {

    while(1) {
      ntest += 1;
      debug(ntest, nreach1, nreach2);
      layout L; L.generate(size, num_dups);
      layout_queries Q(L);
      auto QS = make_queries(Q,size,num_dups,num_queries,ratio);

      auto R1 = solve_base(QS, size, num_dups, num_queries);
      if(R1.size == 0) continue;
      nreach1 += 1;
      debug("reach1");

      auto R2 = solve_dup(QS, size, num_dups, num_queries, R1);
      if(R2.size == 0) continue;
      nreach2 += 1;
      debug("reach2");

      if(test_equivalence(L, R2)) {
        debug("FOUND", ntest);
        break;
      }
    }

  }else {

    auto problem_name = get_problem_name(size, num_dups);
    debug(problem_name);
    while(1) {
      ntest += 1;
      debug(ntest, nreach1, nreach2);
      api_select(problem_name);
      api_queries Q;
      auto QS = make_queries(Q,size,num_dups,num_queries,ratio);

      auto R1 = solve_base(QS, size, num_dups, num_queries);
      if(R1.size == 0) continue;
      nreach1 += 1;
      debug("reach1");

      auto R2 = solve_dup(QS, size, num_dups, num_queries, R1);
      if(R2.size == 0) continue;
      nreach2 += 1;
      debug("reach2");

      bool correct = api_guess(R2);
      debug(correct);
      if(correct) break;
    }
  }

  return 0;
}
