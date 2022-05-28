#include <algorithm>
#include <utility>
#include <vector>
#include <iostream>
#include <array>
#include <set>
#include <numeric>
#include <memory>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <sys/time.h>

#ifdef LOCAL
#ifndef NDEBUG
// #define MEASURE_TIME
#define DEBUG
#endif
#else
#define NDEBUG
// #define DEBUG
#endif
#include <cassert>

using namespace std;
using u8=uint8_t;
using u16=uint16_t;
using u32=uint32_t;
using u64=uint64_t;
using i64=int64_t;
using ll=int64_t;
using ull=uint64_t;
using vi=vector<int>;
using vvi=vector<vi>;

namespace {

#ifdef LOCAL
constexpr double CLOCK_PER_SEC = 3.126448e9;
constexpr ll TL = 1000;
#else
constexpr double CLOCK_PER_SEC = 2.5e9;
constexpr ll TL = 2500;
#endif

ll start_time; // msec

inline ll get_time() {
  struct timeval tv;
  gettimeofday(&tv, NULL);
  ll result =  tv.tv_sec * 1000LL + tv.tv_usec / 1000LL;
  return result;
}

inline ll get_elapsed_msec() {
  return get_time() - start_time;
}

inline bool reach_time_limit() {
  return get_elapsed_msec() >= TL;
}

inline ull get_tsc() {
#ifdef __i386
  ull ret;
  __asm__ volatile ("rdtsc" : "=A" (ret));
  return ret;
#else
  ull high,low;
  __asm__ volatile ("rdtsc" : "=a" (low), "=d" (high));
  return (high << 32) | low;
#endif
}

struct XorShift {
  uint32_t x,y,z,w;
  static const double TO_DOUBLE;

  XorShift() {
    x = 123456789;
    y = 362436069;
    z = 521288629;
    w = 88675123;
  }

  uint32_t nextUInt(uint32_t n) {
    uint32_t t = x ^ (x << 11);
    x = y;
    y = z;
    z = w;
    w = (w ^ (w >> 19)) ^ (t ^ (t >> 8));
    return w % n;
  }

  uint32_t nextUInt() {
    uint32_t t = x ^ (x << 11);
    x = y;
    y = z;
    z = w;
    return w = (w ^ (w >> 19)) ^ (t ^ (t >> 8));
  }

  double nextDouble() {
    return nextUInt() * TO_DOUBLE;
  }
};
const double XorShift::TO_DOUBLE = 1.0 / (1LL << 32);

struct Counter {
  vector<ull> cnt;

  void add(int i) {
    if (i >= cnt.size()) {
      cnt.resize(i+1);
    }
    ++cnt[i];
  }

  void print() {
    cerr << "counter:[";
    for (int i = 0; i < cnt.size(); ++i) {
      cerr << cnt[i] << ", ";
      if (i % 10 == 9) cerr << endl;
    }
    cerr << "]" << endl;
  }
};

struct Timer {
  vector<ull> at;
  vector<ull> sum;

  void start(int i) {
    if (i >= at.size()) {
      at.resize(i+1);
      sum.resize(i+1);
    }
    at[i] = get_tsc();
  }

  void stop(int i) {
    sum[i] += (get_tsc() - at[i]);
  }

  void print() {
    cerr << "timer:[";
    for (int i = 0; i < at.size(); ++i) {
      cerr << (int)(sum[i] / CLOCK_PER_SEC * 1000) << ", ";
      if (i % 10 == 9) cerr << endl;
    }
    cerr << "]" << endl;
  }
};

}

#ifdef MEASURE_TIME
#define START_TIMER(i) (timer.start(i))
#define STOP_TIMER(i) (timer.stop(i))
#define PRINT_TIMER() (timer.print())
#define ADD_COUNTER(i) (counter.add(i))
#define PRINT_COUNTER() (counter.print())
#else
#define START_TIMER(i)
#define STOP_TIMER(i)
#define PRINT_TIMER()
#define ADD_COUNTER(i)
#define PRINT_COUNTER()
#endif

#ifdef DEBUG
#define debug(format, ...) fprintf(stderr, format, __VA_ARGS__)
#define debugStr(str) fprintf(stderr, str)
#define debugln() fprintf(stderr, "\n")
#else
#define debug(format, ...)
#define debugStr(str)
#define debugln()
#endif

template<class T>
constexpr inline T sq(T v) { return v * v; }

void debug_vec(const vi& vec) {
  debugStr("[");
  for (int i = 0; i < vec.size(); ++i) {
    debug("%d ", vec[i]);
  }
  debugStr("]");
}

XorShift rnd;
Timer timer;
Counter counter;

//////// end of template ////////

constexpr int INF = 1 << 28;
constexpr int EMPTY = 0;
constexpr array<int, 4> DR = {0, -1, 0, 1};
constexpr array<int, 4> DC = {-1, 0, 1, 0};
constexpr int LEFT = 0;
constexpr int UP = 1;
constexpr int RIGHT = 2;
constexpr int DOWN = 3;
constexpr array<char, 4> DIR_CHARS = {'L', 'U', 'R', 'D'};

int N, T;
array<array<int, 12>, 12> orig_tiles;

inline bool in_grid(int p) {
  return 0 <= p && p < N;
}

struct UnionFind {
  vi root_;
  UnionFind(int n) : root_(n, -1) {}

  void unite(int i, int j) {
    int a = root(i);
    int b = root(j);
    if (a != b) {
      root_[a] += root_[b];
      root_[b] = a;
    }
  }

  bool find(int i, int j) {
    return root(i) == root(j);
  }

  int root(int i) {
    if (root_[i] < 0) return i;
    root_[i] = root(root_[i]);
    return root_[i];
  }

  int size(int i) {
    return -root_[root(i)];
  }
};

struct Result {
  vector<int> moves;
  int tree_size;

  int score() const {
    int s = N * N - 1;
    if (tree_size == s) {
      return 5000ll * 2 - (5000ll * moves.size() + T / 2) / T;
    } else {
      return (5000ll * tree_size + s / 2) / s;
    }
  }
};

template<class T>
bool has_edge(const T& tiles, int r, int c, int dir) {
  return (tiles[r][c] & (1 << dir)) && (tiles[r + DR[dir]][c + DC[dir]] & (1 << (dir ^ 2)));
}

template<class T>
void randomize(vector<T>& v) {
  for (int i = 0; i < v.size() - 1; ++i) {
    int pos = rnd.nextUInt(v.size() - i) + i;
    swap(v[i], v[pos]);
  }
}

template<class T>
void print_tiles(const T& tiles, bool with_sentinel) {
#ifdef DEBUG
  int base = with_sentinel ? 1 : 0;
  for (int i = base; i < base + N; ++i) {
    for (int j = base; j < base + N; ++j) {
      debug("%x", tiles[i][j]);
    }
    debugln();
  }
#endif
}

// maximize
bool accept(int diff, double cooler) {
  if (diff >= 0) return true;
  double v = diff * cooler;
  if (v < -10) return false;
  return rnd.nextDouble() < exp(v);
}

int verify(const vector<int>& moves) {
  int cr = -1;
  int cc = -1;
  vvi tiles(N, vi(N, 0));
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      tiles[i][j] = orig_tiles[i][j];
      if (tiles[i][j] == EMPTY) {
        cr = i;
        cc = j;
      }
    }
  }
  for (int i = 0; i < moves.size(); ++i) {
    int m = moves[i];
    int nr = cr + DR[m];
    int nc = cc + DC[m];
    if (!in_grid(nr) || !in_grid(nc)) {
      return -1;
    }
    swap(tiles[cr][cc], tiles[nr][nc]);
    cr = nr;
    cc = nc;
    if (i > 0 && (moves[i - 1] ^ 2) == moves[i]) {
      debug("redundant move at %d\n", i);
    }
  }
  vector<vector<bool>> visited(N, vector<bool>(N, false));
  int tree_size = 0;
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      if (tiles[i][j] == EMPTY || visited[i][j]) continue;
      bool loop = false;
      vi q = {(i << 8) | j};
      int qi = 0;
      while (qi < q.size()) {
        int pr = q[qi] >> 8;
        int pc = q[qi] & 0xFF;
        for (int d = 0; d < 4; ++d) {
          int nr = pr + DR[d];
          int nc = pc + DC[d];
          if (in_grid(nr) && in_grid(cc) && has_edge(tiles, i, j, d)) {
            if (visited[nr][nc]) {
              loop = true;
            } else {
              q.push_back((nr << 8) | nc);
            }
          }
        }
        qi++;
      }
      if (!loop && q.size() > tree_size) {
        tree_size = q.size();
      }
    }
  }
  debug("tree_size:%d\n", tree_size);
  int s = N * N - 1;
  if (tree_size == s) {
    return 5000 * 2 - (5000 * moves.size() + T / 2) / T;
  } else {
    return (5000 * tree_size + s / 2) / s;
  }
}

struct TreePlacer {
  vi orig_count;
  vvi bfs_from;
  vvi bfs_cnt;
  vvi tiles;
  int bfs_counter;

  TreePlacer() : bfs_counter(0) {
    orig_count.assign(16, 0);
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        orig_count[orig_tiles[i][j]]++;
      }
    }
    bfs_from.assign(N + 2, vi(N + 2, 0));
    bfs_cnt.assign(N + 2, vi(N + 2, 0));
  }

  void create_random() {
    tiles.assign(N + 2, vi(N + 2, EMPTY));
    vector<pair<int, int>> es;
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < ((i == N - 1) ? N - 2 : N - 1); ++j) {
        es.push_back({i * N + j, i * N + j + 1});
      }
    }
    for (int i = 0; i < N - 1; ++i) {
      for (int j = 0; j < ((i == N - 2) ? N - 1 : N); ++j) {
        es.push_back({i * N + j, (i + 1) * N + j});
      }
    }
    randomize(es);
    UnionFind uf(N * N - 1);
    for (const auto& e : es) {
      if (uf.find(e.first, e.second)) continue;
      uf.unite(e.first, e.second);
      int r0 = e.first / N + 1;
      int c0 = e.first % N + 1;
      int r1 = e.second / N + 1;
      int c1 = e.second % N + 1;
      if (r0 == r1) {
        tiles[r0][c0] |= 1 << RIGHT;
        tiles[r1][c1] |= 1 << LEFT;
      } else {
        tiles[r0][c0] |= 1 << DOWN;
        tiles[r1][c1] |= 1 << UP;
      }
    }
  }

  inline void decrease(vi& count, int& diff, int v) {
    if (count[v] > orig_count[v]) {
      diff--;
    } else {
      diff++;
    }
    count[v]--;
  }

  inline void increase(vi& count, int& diff, int v) {
    if (count[v] < orig_count[v]) {
      diff--;
    } else {
      diff++;
    }
    count[v]++;
  }

  int find_cut_pos(const vi& count, int sr, int sc, int gr, int gc) {
    // debug("find_cut_pos sr:%d sc:%d gr:%d gc:%d\n", sr, sc, gr, gc);
    static vi cut_pos_cands;
    cut_pos_cands.clear();
    int cut_r = sr;
    int cut_c = sc;
    int cut_diff_min = INF;
    while (cut_r != gr || cut_c != gc) {
      int prev_dir = bfs_from[cut_r][cut_c];
      int ncut_r = cut_r + DR[prev_dir];
      int ncut_c = cut_c + DC[prev_dir];
      int tile0 = tiles[cut_r][cut_c];
      int tile1 = tiles[ncut_r][ncut_c];
      assert(tile0 & (1 << prev_dir));
      assert(tile1 & (1 << (prev_dir ^ 2)));
      int cut_diff = 0;
      if (count[tile0] > orig_count[tile0]) {
        cut_diff--;
      } else {
        cut_diff++;
      }
      if (count[tile1] > orig_count[tile1]) {
        cut_diff--;
      } else {
        cut_diff++;
      }
      if (count[tile0 ^ (1 << prev_dir)] < orig_count[tile0 ^ (1 << prev_dir)]) {
        cut_diff--;
      } else {
        cut_diff++;
      }
      if (count[tile1 ^ (1 << (prev_dir ^ 2))] < orig_count[tile1 ^ (1 << (prev_dir ^ 2))]) {
        cut_diff--;
      } else {
        cut_diff++;
      }
      if (cut_diff < cut_diff_min) {
        cut_diff_min = cut_diff;
        cut_pos_cands.clear();
        cut_pos_cands.push_back((cut_r << 8) | cut_c);
      } else if (cut_diff == cut_diff_min) {
        cut_pos_cands.push_back((cut_r << 8) | cut_c);
      }
      cut_r = ncut_r;
      cut_c = ncut_c;
    }
    return cut_pos_cands[rnd.nextUInt(cut_pos_cands.size())];
  }

  vvi find() {
    create_random();
    vi count(16, 0);
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        count[tiles[i + 1][j + 1]]++;
      }
    }
    int cur_diff = 0;
    for (int i = 1; i <= 15; ++i) {
      cur_diff += abs(orig_count[i] - count[i]);
    }
    const double initial_cooler_log = log(0.1);
    const double final_cooler_log = log(5.0);
    double cooler = 1.0;
    const int max_turn = 100000;
    vi cand_dir;
    vi bfs_que;
    vi cut_pos_cands;
    for (int turn = 0; turn < max_turn; ++turn) {
      if ((turn & 0xFF) == 0) {
        double ratio = turn * 1.0 / max_turn;
        cooler = exp((1.0 - ratio) * initial_cooler_log + ratio * final_cooler_log);
      }
      const int pos = rnd.nextUInt(N * N - 1);
      const int cr = pos / N + 1;
      const int cc = pos % N + 1;
      cand_dir.clear();
      const int tile = tiles[cr][cc];
      for (int i = 0; i < 4; ++i) {
        if (tile & (1 << i)) continue;
        int nr = cr + DR[i];
        int nc = cc + DC[i];
        if (tiles[nr][nc] == 0) continue;
        cand_dir.push_back(i);
      }
      if (cand_dir.empty()) continue;
      int dir = cand_dir[rnd.nextUInt(cand_dir.size())];
      const int nr = cr + DR[dir];
      const int nc = cc + DC[dir];
      const int ntile = tiles[nr][nc];
      int diff = 0;
      decrease(count, diff, tile);
      decrease(count, diff, ntile);
      const int tile_new = tile | (1 << dir);
      const int ntile_new = ntile | (1 << (dir ^ 2));
      increase(count, diff, tile_new);
      increase(count, diff, ntile_new);
      bfs_counter++;
      bfs_que.clear();
      bfs_que.push_back((cr << 8) | cc);
      bfs_cnt[cr][cc] = bfs_counter;
      int qi = 0;
      // debug("bfs cr:%d cc:%d nr:%d nc:%d\n", cr, cc, nr, nc);
      while (true) {
        int r0 = bfs_que[qi] >> 8;
        int c0 = bfs_que[qi] & 0xFF;
        if (r0 == nr && c0 == nc) break;
        for (int i = 0; i < 4; ++i) {
          if (!(tiles[r0][c0] & (1 << i))) continue;
          int r1 = r0 + DR[i];
          int c1 = c0 + DC[i];
          if (bfs_cnt[r1][c1] == bfs_counter) continue;
          bfs_cnt[r1][c1] = bfs_counter;
          bfs_from[r1][c1] = i ^ 2;
          bfs_que.push_back((r1 << 8) | c1);
        }
        qi++;
      }
      tiles[cr][cc] |= 1 << dir;
      tiles[nr][nc] |= 1 << (dir ^ 2);
      const int cut_pos = find_cut_pos(count, nr, nc, cr, cc);
      const int cut_r = cut_pos >> 8;
      const int cut_c = cut_pos & 0xFF;
      const int prev_dir = bfs_from[cut_r][cut_c];
      const int ncut_r = cut_r + DR[prev_dir];
      const int ncut_c = cut_c + DC[prev_dir];
      decrease(count, diff, tiles[cut_r][cut_c]);
      decrease(count, diff, tiles[ncut_r][ncut_c]);
      increase(count, diff, tiles[cut_r][cut_c] ^ (1 << prev_dir));
      increase(count, diff, tiles[ncut_r][ncut_c] ^ (1 << (prev_dir ^ 2)));
      if (accept(-diff, cooler)) {
        tiles[cut_r][cut_c] ^= 1 << prev_dir;
        tiles[ncut_r][ncut_c] ^= 1 << (prev_dir ^ 2);
        cur_diff += diff;
        debug("cur_diff:%d at turn %d\n", cur_diff, turn);
        if (cur_diff == 0) {
          assert(count == orig_count);
          break;  
        }
      } else {
        count[tiles[cut_r][cut_c] ^ (1 << prev_dir)]--;
        count[tiles[ncut_r][ncut_c] ^ (1 << (prev_dir ^ 2))]--;
        count[tiles[cut_r][cut_c]]++;
        count[tiles[ncut_r][ncut_c]]++;
        tiles[cr][cc] = tile;
        tiles[nr][nc] = ntile;
        count[tile_new]--;
        count[ntile_new]--;
        count[tile]++;
        count[ntile]++;
      }
    }
    if (cur_diff == 0) {
      return tiles;
    } else {
      return vvi();
    }
  }

  // bool dfs(int r, int c, vvi& tiles) {
  //   vi cands;
  //   for (int i = 1; i <= 15; ++i) {
  //     if (count[i] == 0) continue;
  //     bool ok = true;
  //     for (int j = 0; j < 4; ++j) {
  //       int nr = r + DR[j];
  //       int nc = c + DC[j];
  //       if (i & (1 << j)) {
  //         if (tiles[nr][nc] == WAITING) {
  //           ok = false;
  //           break;
  //         } else if (tiles[nr][nc] != YET) {
  //           if ((tiles[nr][nc] & (1 << (j ^ 2))) == 0) {
  //             ok = false;
  //             break;
  //           }
  //         }
  //       } else {
  //         if (tiles[nr][nc] > 0 && (tiles[nr][nc] & (1 << (j ^ 2)))) {
  //           ok = false;
  //           break;
  //         }
  //       }
  //     }
  //     if (ok) {
  //       cands.push_back(i);
  //     }
  //   }
  //   if (cands.empty()) return false;
  //   randomize(cands);
  //   vi nds;
  //   for (int nt : cands) {
  //     nds.clear();
  //     count[nt]--;
  //     for (int i = 0; i < 4; ++i) {
  //       if ((nt & (1 << i)) && tiles[r + DR[i]][c + DC[i]] == YET) {
  //         tiles[r + DR[i]][c + DC[i]] = WAITING;
  //         nds.push_back(i);
  //       }
  //     }
  //     if (nds.empty()) return true;
  //     randomize(nds);
  //     for (int nd : nds) {

  //     }
  //     count[nt]++;
  //   }
  // }
};

struct State {
  vvi tiles;
  int evaluation;
  int er, ec;
  int prev_move;
};

struct SlidingBlockPuzzle {
  vvi tiles;
  int sr, sc;
  SlidingBlockPuzzle(vvi tiles_, int sr_, int sc_) : tiles(tiles_), sr(sr_), sc(sc_) {}

  vi solve() {
    int initial_eval = 0;
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        initial_eval += abs((tiles[i][j] >> 8) - i) + abs((tiles[i][j] & 0xFF) - j);
      }
    }
    if (initial_eval == 0) return vi();  // tenho
    State initial_state = {tiles, initial_eval, sr, sc, -1};
    vector<State> cur_states = {initial_state};

  }
}

struct Solver {
  array<array<int, 12>, 12> tiles;
  Solver() {
  }

  Result solve() {
    TreePlacer tree_placer;
    vvi target_tiles = tree_placer.find();
    if (target_tiles.empty()) {
      exit(1);
    }

    // remove sentinel
    target_tiles.pop_back();
    target_tiles.erase(target_tiles.begin());
    for (auto& row : target_tiles) {
      row.pop_back();
      row.erase(row.begin());
    }

    // create matching from original tiles
    vector<vector<pair<int, int>>> orig_tile_pos(16);
    vector<vector<pair<int, int>>> target_tile_pos(16);
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        orig_tile_pos[orig_tiles[i][j]].push_back({i, j});
        target_tile_pos[target_tiles[i][j]].push_back({i, j});
      }
    }
    for (int i = 1; i <= 15; ++i) {
      vector<pair<int, int>>& orig_pos = orig_tile_pos[i];
      vector<pair<int, int>>& target_pos = target_tile_pos[i];
      if (orig_pos.size() <= 1) continue;
      for (int turn = 0; turn < orig_pos.size() * 100; ++turn) {
        int pos0 = rnd.nextUInt(orig_pos.size());
        int pos1 = rnd.nextUInt(orig_pos.size() - 1);
        if (pos0 <= pos1) pos1++;
        int cur_dist = abs(orig_pos[pos0].first - target_pos[pos0].first) + abs(orig_pos[pos0].second - target_pos[pos0].second);
        cur_dist += abs(orig_pos[pos1].first - target_pos[pos1].first) + abs(orig_pos[pos1].second - target_pos[pos1].second);
        int new_dist = abs(orig_pos[pos0].first - target_pos[pos1].first) + abs(orig_pos[pos0].second - target_pos[pos1].second);
        new_dist += abs(orig_pos[pos1].first - target_pos[pos0].first) + abs(orig_pos[pos1].second - target_pos[pos0].second);
        if (new_dist <= cur_dist) {
          swap(target_pos[pos0], target_pos[pos1]);
        }
      }
    }
    vvi tile_number(N, vi(N, 0));
    for (int i = 0; i <= 15; ++i) {
      debug("tile:%d\n", i);
      for (int j = 0; j < orig_tile_pos[i].size(); ++j) {
        auto orig_p = orig_tile_pos[i][j];
        auto target_p = target_tile_pos[i][j];
        debug("(%d %d) -> (%d %d)\n", orig_p.first, orig_p.second, target_p.first, target_p.second);
        tile_number[orig_p.first][orig_p.second] = (target_p.first << 8) | target_p.second;
      }
    }

    Result res;
    SlidingBlockPuzzle puzzle(tile_number, orig_tile_pos[0][0].first, orig_tile_pos[0][0].second);
    res.moves = puzzle.solve();
    res.tree_size = N * N - 1;
    return res;
  }

  // void create_target() {
  //   fill(tiles[0].begin(), tiles[0].begin() + N + 2, 0);
  //   fill(tiles[N + 1].begin(), tiles[N + 1].begin() + N + 2, 0);
  //   for (int i = 0; i < N; ++i) {
  //     tiles[i + 1][0] = 0;
  //     tiles[i + 1][N + 1] = 0;
  //     copy(orig_tiles[i].begin(), orig_tiles[i].begin() + N, tiles[i + 1].begin() + 1);
  //   }
  //   int edges = 0;
  //   for (int i = 0; i < N; ++i) {
  //     for (int j = 0; j < N - 1; ++j) {
  //       if (has_edge(tiles, i + 1, j + 1, RIGHT)) {
  //         edges++;
  //       }
  //     }
  //   }
  //   for (int i = 0; i < N - 1; ++i) {
  //     for (int j = 0; j < N; ++j) {
  //       if (has_edge(tiles, i + 1, j + 1, DOWN)) {
  //         edges++;
  //       }
  //     }
  //   }
  //   const double initial_cooler_log = log(0.1);
  //   const double final_cooler_log = log(5.0);
  //   double cooler = 1.0;
  //   const int max_turn = 100000;
  //   for (int turn = 0; turn < max_turn; ++turn) {
  //     if ((turn & 0xFF) == 0) {
  //       double ratio = turn * 1.0 / max_turn;
  //       cooler = exp((1.0 - ratio) * initial_cooler_log + ratio * final_cooler_log);
  //     }
  //     int pos0 = rnd.nextUInt(N * N);
  //     int pos1 = rnd.nextUInt(N * N - 1);
  //     if (pos1 >= pos0) pos1++;
  //     int r0 = pos0 / N + 1;
  //     int c0 = pos0 % N + 1;
  //     int r1 = pos1 / N + 1;
  //     int c1 = pos1 % N + 1;
  //     if (tiles[r0][c0] == tiles[r1][c1]) {
  //       continue;
  //     }
  //     if (abs(r0 - r1) + abs(c0 - c1) == 1) {
  //       continue;
  //     } 
  //     int diff = 0;
  //     for (int i = 0; i < 4; ++i) {
  //       if (has_edge(tiles, r0, c0, i)) diff--;
  //       if (has_edge(tiles, r1, c1, i)) diff--;
  //     }
  //     swap(tiles[r0][c0], tiles[r1][c1]);
  //     for (int i = 0; i < 4; ++i) {
  //       if (has_edge(tiles, r0, c0, i)) diff++;
  //       if (has_edge(tiles, r1, c1, i)) diff++;
  //     }
  //     if (accept(diff, cooler)) {
  //       edges += diff;
  //       debug("edges:%d at turn %d\n", edges, turn);
  //       if (edges == N * N - 2) {
  //         break;  
  //       }
  //     } else {
  //       swap(tiles[r0][c0], tiles[r1][c1]);
  //     }
  //   }
  //   for (int i = 0; i < N; ++i) {
  //     copy(tiles[i + 1].begin() + 1, tiles[i + 1].begin() + N + 1, target_tiles[i].begin());
  //   }
  // }

};

int main() {
  start_time = get_time();
  scanf("%d %d", &N, &T);

  for (int i = 0; i < N; ++i) {
    char row[11];
    scanf("%s", row);
    for (int j = 0; j < N; ++j) {
      char tile = row[j];
      int t = ('0' <= tile && tile <= '9') ? (tile - '0') : (tile - 'a' + 10);
      orig_tiles[i][j] = t;
    }
  }

  auto solver = unique_ptr<Solver>(new Solver());
  Result res = solver->solve();
  debug("score=%d\n", res.score());
  for (int m : res.moves) {
    printf("%c", DIR_CHARS[m]);
  }
  printf("\n");
  fflush(stdout);
}