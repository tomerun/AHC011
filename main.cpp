#include <algorithm>
#include <utility>
#include <vector>
#include <iostream>
#include <array>
#include <unordered_set>
#include <numeric>
#include <memory>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <sys/time.h>

#ifdef LOCAL
#ifndef NDEBUG
#define MEASURE_TIME
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
      vi q = {(5 << 16) | (i << 8) | j};
      int qi = 0;
      visited[i][j] = true;
      while (qi < q.size()) {
        int pd = (q[qi] >> 16) & 0xFF;
        int pr = (q[qi] >> 8) & 0xFF;
        int pc = q[qi] & 0xFF;
        for (int d = 0; d < 4; ++d) {
          if (d == pd) continue;
          int nr = pr + DR[d];
          int nc = pc + DC[d];
          if (in_grid(nr) && in_grid(cc) && has_edge(tiles, pr, pc, d)) {
            if (visited[nr][nc]) {
              loop = true;
            } else {
              q.push_back(((d ^ 2) << 16) | (nr << 8) | nc);
              visited[nr][nc] = true;
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
      }
      if (count[tile1] > orig_count[tile1]) {
        cut_diff--;
      }
      if (count[tile0 ^ (1 << prev_dir)] < orig_count[tile0 ^ (1 << prev_dir)]) {
        cut_diff--;
      }
      if (count[tile1 ^ (1 << (prev_dir ^ 2))] < orig_count[tile1 ^ (1 << (prev_dir ^ 2))]) {
        cut_diff--;
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
    const double initial_cooler_log = log(0.5);
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
        // debug("cur_diff:%d at turn %d\n", cur_diff, turn);
        if (cur_diff == 0) {
          // debug("found valid tree at turn %d\n", turn);
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
};

struct State {
  vvi tiles;
  int penalty;
  int er, ec;
  int back_move;
  uint64_t hash;
};

struct SingleMove {
  int penalty;
  int dir;
  int state_idx;
};

bool operator<(const SingleMove& m0, const SingleMove& m1) { return m0.penalty < m1.penalty; };

struct History {
  int prev_idx;
  int dir;
};

array<array<uint64_t, 10>, 10> cell_hash;
constexpr int BEAM_SIZE = 100;
array<array<History, BEAM_SIZE>, 2000> beam_history;

struct PuzzleSolver {
  vvi tiles;
  vvi target;
  vi ans;
  vector<vector<bool>> protect;
  int er;
  int ec;
  vvi bfs_from;
  vvi bfs_cnt;
  int bfs_counter;

  PuzzleSolver(vvi& initial_tiles_, vvi& target_)
   : tiles(initial_tiles_), target(target_), protect(N, vector<bool>(N, false)), bfs_counter(0) {
    bfs_from.assign(N, vi(N, -1));
    bfs_cnt.assign(N, vi(N, 0));
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        if (tiles[i][j] == EMPTY) {
          er = i;
          ec = j;
        }
      }
    }
  }

  void convey(const int level, const int r, const int c, const int t) {
    // debug("convey r:%d c:%d\n", r, c);
    // print_tiles(tiles, false);
    int pos0 = 0;
    int pos1 = 0;
    int dist0 = INF;
    int dist1 = INF;
    for (int i = level; i < N; ++i) {
      for (int j = level; j < N; ++j) {
        if (tiles[i][j] != t) continue;
        if (protect[i][j]) continue;
        int dist_r = abs(r - i);
        int dist_c = abs(c - j);
        int dist = min(dist_r, dist_c) * 2 * 5 + (dist_r + dist_c - min(dist_r, dist_c) * 2) * 5 + abs(er - i) + abs(ec - j);
        if (dist < dist0) {
          dist1 = dist0;
          pos1 = pos0;
          dist0 = dist;
          pos0 = (i << 8) | j;
        } else if (dist < dist1) {
          dist1 = dist;
          pos1 = (i << 8) | j;
        }
      }
    }
    assert(dist0 != INF);
    // TODO: select second pos
    // if (dist1 != INF && (rnd.nextUInt() & 1)) {
    //   pos0 = pos1;
    // }
    int tr = pos0 >> 8;
    int tc = pos0 & 0xFF;
    // debug("convey r:%d c:%d tr:%d tc:%d\n", r, c, tr, tc);
    // for (int i = 0; i < N; ++i) {
    //   for (int j = 0; j < N; ++j) {
    //     debug("%d", (int)protect[i][j]);
    //   }
    //   debugln();
    // }
    while (tr != r || tc != c) {
      protect[tr][tc] = true;
      int order_base = rnd.nextUInt() & 3;
      for (int i = 0; i < 4; ++i) {
        int dir = (i + order_base) & 3;
        if ((r - tr) * DR[dir] + (c - tc) * DC[dir] > 0 && !protect[tr + DR[dir]][tc + DC[dir]]) {
          move_to(tr + DR[dir], tc + DC[dir]);
          protect[tr][tc] = false;
          step(dir ^ 2);
          tr += DR[dir];
          tc += DC[dir];
          break;
        }
      }
      assert(!protect[tr][tc]);
    }
    assert(tiles[r][c] == t);
  }

  void move_to(const int r, const int c) {
    // debug("move_to r:%d c:%d er:%d ec:%d\n", r, c, er, ec);
    assert(!protect[r][c]);
    static vi path;
    path.clear();
    if (move_to_dfs(r, c, er, ec, path)) {
      for (int dir : path) {
        step(dir);
      }
      assert(er == r);
      assert(ec == c);
      return;
    }
    assert(path.empty());
    // debugStr("move_to_bfs\n");
    // for (int i = 0; i < N; ++i) {
    //   for (int j = 0; j < N; ++j) {
    //     debug("%d", (int)protect[i][j]);
    //   }
    //   debugln();
    // }
    static vi bfs_que;
    bfs_que.clear();
    bfs_que.push_back((er << 8) | ec);
    bfs_counter++;
    bfs_cnt[er][ec] = bfs_counter;
    int qi = 0;
    while (true) {
      int cr = bfs_que[qi] >> 8;
      int cc = bfs_que[qi] & 0xFF;
      // debug("cr:%d cc:%d\n", cr, cc);
      if (cr == r && cc == c) break;
      for (int i = 0; i < 4; ++i) {
        int nr = cr + DR[i];
        int nc = cc + DC[i];
        if (!in_grid(nr) || !in_grid(nc)) continue;
        if (protect[nr][nc]) continue;
        if (bfs_cnt[nr][nc] == bfs_counter) continue;
        bfs_from[nr][nc] = i;
        bfs_cnt[nr][nc] = bfs_counter;
        bfs_que.push_back((nr << 8) | nc);
      }
      qi++;
    }
    int cr = r;
    int cc = c;
    while (cr != er || cc != ec) {
      // debug("back cr:%d cc:%d\n", cr, cc);
      path.push_back(bfs_from[cr][cc]);
      cr -= DR[path.back()];
      cc -= DC[path.back()];
    }
    for (auto itr = path.rbegin(); itr != path.rend(); ++itr) {
      step(*itr);
    }
    assert(er == r);
    assert(ec == c);
  }

  bool move_to_dfs(const int tr, const int tc, const int cr, const int cc, vi& path) {
    // debug("move_to_dfs tr:%d tc:%d cr:%d cc:%d\n", tr, tc, cr, cc);
    if (tr == cr && tc == cc) return true;
    int order = rnd.nextUInt() & 1;
    for (int i = 0; i < 2; ++i) {
      if ((i + order) & 1) {
        if (tr != cr) {
          int dir = tr < cr ? UP : DOWN;
          int nr = cr + DR[dir];
          if (!protect[nr][cc]) {
            path.push_back(dir);
            if (move_to_dfs(tr, tc, nr, cc, path)) {
              return true;
            }
            path.pop_back();
          }
        }
      } else {
        if (tc != cc) {
          int dir = tc < cc ? LEFT : RIGHT;
          int nc = cc + DC[dir];
          if (!protect[cr][nc]) {
            path.push_back(dir);
            if (move_to_dfs(tr, tc, cr, nc, path)) {
              return true;
            }
            path.pop_back();
          }
        }
      }
    }
    return false;
  }

  void step(int dir) {
    ans.push_back(dir);
    int nr = er + DR[dir];
    int nc = ec + DC[dir];
    // assert(!protect[nr][nc]);
    swap(tiles[er][ec], tiles[nr][nc]);
    er = nr;
    ec = nc;
  }

  void solve_cw(int level) {
    for (int i = N - 1; i >= level + 2; --i) {
      convey(level, i, level, target[i][level]);
      protect[i][level] = true;
    }
    if (tiles[level + 1][level] == target[level + 1][level] && tiles[level][level] == target[level][level]) {
      // ok
      protect[level + 1][level] = true;
      protect[level][level] = true;
    } else {
      convey(level, level + 1, level, target[level][level]);
      protect[level + 1][level] = true;
      bool skip = false;
      if (er == level && ec == level) {
        if (tiles[level + 1][level + 1] == target[level + 1][level]) {
          step(DOWN);
          step(RIGHT);
          skip = true;
        } else {
          step(RIGHT);
        }
      }
      if (!skip) {
        if (tiles[level][level] == target[level + 1][level]) {
          move_to(level + 1, level + 1);
          step(LEFT);
          step(DOWN);
          step(RIGHT);
          step(RIGHT);
          step(UP);
          step(UP);
          step(LEFT);
          step(DOWN);
          step(DOWN);
          step(LEFT);
          step(UP);
          step(UP);
          step(RIGHT);
        } else {
          convey(level, level + 1, level + 1, target[level + 1][level]);
          protect[level + 1][level + 1] = true;
          move_to(level, level);
          protect[level + 1][level + 1] = false;
          step(DOWN);
          step(RIGHT);
        }
      }
      protect[level][level] = true;
    }

    for (int i = level + 1; i < N - 2; ++i) {
      convey(level, level, i, target[level][i]);
      protect[level][i] = true;
    }
    if (tiles[level][N - 2] == target[level][N - 2] && tiles[level][N - 1] == target[level][N - 1]) {
      // ok
      protect[level][N - 2] = true;
      protect[level][N - 1] = true;
    } else {
      convey(level, level, N - 2, target[level][N - 1]);
      protect[level][N - 2] = true;
      bool skip = false;
      if (er == level && ec == N - 1) {
        if (tiles[level + 1][N - 2] == target[level][N - 2]) {
          step(LEFT);
          step(DOWN);
          skip = true;
        } else {
          step(DOWN);
        }
      }
      if (!skip) {
        if (tiles[level][N - 1] == target[level][N - 2]) {
          move_to(level + 1, N - 2);
          step(UP);
          step(LEFT);
          step(DOWN);
          step(DOWN);
          step(RIGHT);
          step(RIGHT);
          step(UP);
          step(LEFT);
          step(LEFT);
          step(UP);
          step(RIGHT);
          step(RIGHT);
          step(DOWN);
        } else {
          convey(level, level + 1, N - 2, target[level][N - 2]);
          protect[level + 1][N - 2] = true;
          move_to(level, N - 1);
          protect[level + 1][N - 2] = false;
          step(LEFT);
          step(DOWN);
        }
      }
      protect[level][N - 1] = true;
    }
  }

  void solve_ccw(int level) {
    for (int i = N - 1; i >= level + 2; --i) {
      convey(level, level, i, target[level][i]);
      protect[level][i] = true;
    }
    if (tiles[level][level + 1] == target[level][level + 1] && tiles[level][level] == target[level][level]) {
      // ok
      protect[level][level + 1] = true;
      protect[level][level] = true;
    } else {
      convey(level, level, level + 1, target[level][level]);
      protect[level][level + 1] = true;
      bool skip = false;
      if (er == level && ec == level) {
        if (tiles[level + 1][level + 1] == target[level][level + 1]) {
          step(RIGHT);
          step(DOWN);
          skip = true;
        } else {
          step(DOWN);
        }
      }
      if (!skip) {
        if (tiles[level][level] == target[level][level + 1]) {
          move_to(level + 1, level + 1);
          step(UP);
          step(RIGHT);
          step(DOWN);
          step(DOWN);
          step(LEFT);
          step(LEFT);
          step(UP);
          step(RIGHT);
          step(RIGHT);
          step(UP);
          step(LEFT);
          step(LEFT);
          step(DOWN);
        } else {
          convey(level, level + 1, level + 1, target[level][level + 1]);
          protect[level + 1][level + 1] = true;
          move_to(level, level);
          protect[level + 1][level + 1] = false;
          step(RIGHT);
          step(DOWN);
        }
      }
      protect[level][level] = true;
    }

    for (int i = level + 1; i < N - 2; ++i) {
      convey(level, i, level, target[i][level]);
      protect[i][level] = true;
    }
    if (tiles[N - 2][level] == target[N - 2][level] && tiles[N - 1][level] == target[N - 1][level]) {
      // ok
      protect[N - 2][level] = true;
      protect[N - 1][level] = true;
    } else {
      convey(level, N - 2, level, target[N - 1][level]);
      protect[N - 2][level] = true;
      bool skip = false;
      if (er == N - 1 && ec == level) {
        if (tiles[N - 2][level + 1] == target[N - 2][level]) {
          step(UP);
          step(RIGHT);
          skip = true;
        } else {
          step(RIGHT);
        }
      }
      if (!skip) {
        if (tiles[N - 1][level] == target[N - 2][level]) {
          move_to(N - 2, level + 1);
          step(LEFT);
          step(UP);
          step(RIGHT);
          step(RIGHT);
          step(DOWN);
          step(DOWN);
          step(LEFT);
          step(UP);
          step(UP);
          step(LEFT);
          step(DOWN);
          step(DOWN);
          step(RIGHT);
        } else {
          convey(level, N - 2, level + 1, target[N - 2][level]);
          protect[N - 2][level + 1] = true;
          move_to(N - 1, level);
          protect[N - 2][level + 1] = false;
          step(UP);
          step(RIGHT);
        }
      }
      protect[N - 1][level] = true;
    }
  }

  bool solve_whole(int size, int best_len) {
    const uint64_t mask = (1ull << (4 * size * size)) - 1;
    const int base_coord = N - size;
    const int GOAL_LEN = 10;
    uint64_t target_state = 0ull;
    uint64_t initial_state = 0ull;
    for (int i = N - 1; i >= N - 3; --i) {
      for (int j = N - 1; j >= N - 3; --j) {
        target_state <<= 4;
        target_state |= target[i][j];
        initial_state <<= 4;
        initial_state |= tiles[i][j];
      }
    }

    unordered_map<uint64_t, int8_t> goal_states;
    goal_states[target_state] = -1;
    vector<uint64_t> cur_goal_queue;
    cur_goal_queue.push_back(target_state | ((uint64_t)(N - 1) << 40) | ((uint64_t)(N - 1) << 36));
    for (int turn = 0; !cur_goal_queue.empty() && turn < GOAL_LEN && goal_states.count(initial_state) == 0; ++turn) {
      // debug("turn:%d cur_goal_queue.size:%lu goal_states.size:%lu\n", turn, cur_goal_queue.size(), goal_states.size());
      vector<uint64_t> next_queue;
      for (uint64_t cur_state : cur_goal_queue) {
        int cr = (int)(cur_state >> 40);
        int cc = (int)(cur_state >> 36) & 0xF;
        cur_state &= mask;
        int cur_bit_pos = ((cr - base_coord) * size + (cc - base_coord)) * 4;
        for (int dir = 0; dir < 4; ++dir) {
          int nr = cr + DR[dir];
          int nc = cc + DC[dir];
          if (nr < base_coord || N <= nr || nc < base_coord || N <= nc) continue;
          int next_bit_pos = ((nr - base_coord) * size + (nc - base_coord)) * 4;
          uint64_t tile = (cur_state >> next_bit_pos) & 0xF;
          uint64_t next_state = (cur_state ^ (tile << next_bit_pos)) | (tile << cur_bit_pos);
          if (goal_states.count(next_state) == 0) {
            goal_states[next_state] = dir;
            next_queue.push_back(next_state | ((uint64_t)nr << 40) | ((uint64_t)nc << 36));
          }
        }
      }
      swap(cur_goal_queue, next_queue);
    }

    uint64_t finish_state = 0ull;
    unordered_map<uint64_t, int8_t> visited_states;
    if (goal_states.count(initial_state) != 0) {
      finish_state = initial_state;
    } else {
      visited_states[initial_state] = -1;
      vector<uint64_t> cur_states;
      cur_states.push_back(initial_state | ((uint64_t)er << 40) | ((uint64_t)ec << 36));
      for (int turn = 0; !cur_states.empty() && turn < 20 && ans.size() + turn + GOAL_LEN <= best_len + 4; ++turn) {
        // debug("turn:%d cur_states.size:%lu visited_states.size:%lu\n", turn, cur_states.size(), visited_states.size());
        vector<uint64_t> next_states;
        for (uint64_t cur_state : cur_states) {
          int cr = (int)(cur_state >> 40);
          int cc = (int)(cur_state >> 36) & 0xF;
          cur_state &= mask;
          int cur_bit_pos = ((cr - base_coord) * size + (cc - base_coord)) * 4;
          for (int dir = 0; dir < 4; ++dir) {
            int nr = cr + DR[dir];
            int nc = cc + DC[dir];
            if (nr < base_coord || N <= nr || nc < base_coord || N <= nc) continue;
            int next_bit_pos = ((nr - base_coord) * size + (nc - base_coord)) * 4;
            uint64_t tile = (cur_state >> next_bit_pos) & 0xF;
            uint64_t next_state = (cur_state ^ (tile << next_bit_pos)) | (tile << cur_bit_pos);
            if (visited_states.count(next_state) == 0) {
              visited_states[next_state] = dir;
              if (goal_states.count(next_state) != 0) {
                finish_state = next_state;
                goto FOUND;
              }
              next_states.push_back(next_state | ((uint64_t)nr << 40) | ((uint64_t)nc << 36));
            }
          }
        }
        swap(cur_states, next_states);
      }
      return false;
    }
FOUND:
    vi path;
    uint64_t s = finish_state;
    while (s != initial_state) {
      for (int i = 0; i < size * size; ++i) {
        if (((s >> (i * 4)) & 0xF) == 0) {
          int r = i / size;
          int c = i % size;
          int dir = visited_states[s];
          path.push_back(dir);
          int nr = r - DR[dir];
          int nc = c - DC[dir];
          uint64_t tile = (s >> ((nr * size + nc) * 4)) & 0xF;
          s ^= tile << ((nr * size + nc) * 4);
          s |= tile << ((r * size + c) * 4);
          break;
        }
      }
    }
    for (auto itr = path.rbegin(); itr != path.rend(); ++itr) {
      ans.push_back(*itr);
    }

    s = finish_state;
    while (s != target_state) {
      for (int i = 0; i < size * size; ++i) {
        if (((s >> (i * 4)) & 0xF) == 0) {
          int r = i / size;
          int c = i % size;
          int dir = goal_states[s] ^ 2;
          ans.push_back(dir);
          int nr = r + DR[dir];
          int nc = c + DC[dir];
          uint64_t tile = (s >> ((nr * size + nc) * 4)) & 0xF;
          s ^= tile << ((nr * size + nc) * 4);
          s |= tile << ((r * size + c) * 4);
          break;
        }
      }
    }

    return true;
  }

  vi solve(bool& success, int best_len) {
    START_TIMER(1);
    for (int level = 0; level < N - 3; ++level) {
      int dist_bl = abs(N - 1 - er) + ec;
      int dist_tr = er + abs(N - 1 - ec);
      if (dist_bl < dist_tr) {
        solve_cw(level);
      } else {
        solve_ccw(level);
      }
      if (ans.size() > best_len) {
        success = false;
        return ans;
      }
    }
    STOP_TIMER(1);
    START_TIMER(2);
    success = solve_whole(3, best_len);
    STOP_TIMER(2);
    return ans;
  }
};

struct SlidingBlockPuzzle {
  vvi tiles;
  SlidingBlockPuzzle(vvi tiles_) : tiles(tiles_) {}

  vi solve_line(vvi initial_tiles, int line) {
    int initial_pena = 0;
    uint64_t initial_hash = 0ull;
    unordered_set<uint64_t> visited_states;
    int sr = 0;
    int sc = 0;
    for (int i = line; i < N; ++i) {
      for (int j = line; j < N; ++j) {
        if (initial_tiles[i][j] == (((N - 1) << 8) | (N - 1))) {
          sr = i;
          sc = j;
        } else {
          int tr = initial_tiles[i][j] >> 8;
          int tc = initial_tiles[i][j] & 0xFF;
          if (tr == line || tc == line) {
            initial_pena += sq(abs(tr - i) + abs(tc - j));
          }
        }
        initial_hash ^= cell_hash[i][j] * initial_tiles[i][j];
      }
    }
    if (initial_pena == 0) return vi();
    visited_states.insert(initial_hash);
    State initial_state = {initial_tiles, initial_pena, sr, sc, -1, initial_hash};
    vector<State> cur_states = {initial_state};
    int turn = 0;
    for (; turn < T; ++turn) {
      debug("turn:%d\n", turn);
      vector<SingleMove> moves;
      for (int i = 0; i < cur_states.size(); ++i) {
        const State& cur_state = cur_states[i];
        // debug("er:%d ec:%d back_move:%d\n", cur_state.er, cur_state.ec, cur_state.back_move);
        for (int dir = 0; dir < 4; ++dir) {
          if (dir == cur_state.back_move) continue;
          int nr = cur_state.er + DR[dir];
          int nc = cur_state.ec + DC[dir];
          if (nr < line || N <= nr || nc < line || N <= nc) continue;
          int tr = cur_state.tiles[nr][nc] >> 8;
          int tc = cur_state.tiles[nr][nc] & 0xFF;
          uint64_t new_hash = cur_state.hash;
          new_hash ^= cur_state.tiles[cur_state.er][cur_state.ec] * cell_hash[cur_state.er][cur_state.ec];
          new_hash ^= cur_state.tiles[nr][nc] * cell_hash[nr][nc];
          new_hash ^= cur_state.tiles[cur_state.er][cur_state.ec] * cell_hash[nr][nc];
          new_hash ^= cur_state.tiles[nr][nc] * cell_hash[cur_state.er][cur_state.ec];
          if (visited_states.count(new_hash) != 0) {
            continue;
          }
          int diff = 0;
          if (tr == line || tc == line) {
            diff = sq(abs(tr - cur_state.er) + abs(tc - cur_state.ec)) - sq(abs(tr - nr) + abs(tc - nc));
          }
          int move_pena = cur_state.penalty + diff;
          if (move_pena == 0) {
            vi ans = {dir};
            int t = turn - 1;
            int si = i;
            while (t >= 0) {
              ans.push_back(beam_history[t][si].dir);
              si = beam_history[t][si].prev_idx;
              --t;
            }
            reverse(ans.begin(), ans.end());
            return ans;
          }
          moves.push_back({move_pena, dir, i});
        }
      }
      if (moves.empty()) {
        debugStr("give up\n");
        break;
      }
      // sort(moves.begin(), moves.end());
      if (moves.size() > BEAM_SIZE) {
        nth_element(moves.begin(), moves.begin() + BEAM_SIZE, moves.end());
      }
      debug("turn:%d penalty:%d\n", turn, moves[0].penalty);
      vector<State> next_states;
      for (int i = 0; i < min((int)moves.size(), BEAM_SIZE); ++i) {
        const auto& move = moves[i];
        const State& parent_state = cur_states[move.state_idx];
        State next_state = {parent_state.tiles, move.penalty, parent_state.er + DR[move.dir], parent_state.ec + DC[move.dir], move.dir ^ 2, 0ull};
        uint64_t new_hash = parent_state.hash;
        new_hash ^= parent_state.tiles[parent_state.er][parent_state.ec] * cell_hash[parent_state.er][parent_state.ec];
        new_hash ^= parent_state.tiles[next_state.er][next_state.ec] * cell_hash[next_state.er][next_state.ec];
        new_hash ^= parent_state.tiles[parent_state.er][parent_state.ec] * cell_hash[next_state.er][next_state.ec];
        new_hash ^= parent_state.tiles[next_state.er][next_state.ec] * cell_hash[parent_state.er][parent_state.ec];
        next_state.hash = new_hash;
        if (visited_states.count(new_hash) != 0) {
          continue;
        }
        // visited_states.insert(new_hash);
        swap(next_state.tiles[parent_state.er][parent_state.ec], next_state.tiles[next_state.er][next_state.ec]);
        next_states.push_back(next_state);
        beam_history[turn][next_states.size() - 1].prev_idx = move.state_idx;
        beam_history[turn][next_states.size() - 1].dir = move.dir;
      }
      swap(cur_states, next_states);
    }
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        debug("(%2d %2d) ", cur_states[0].tiles[i][j] >> 8, cur_states[0].tiles[i][j] & 0xFF);
      }
      debugln();
    }
    return vi();
    // vi ans;
    // int t = turn - 1;
    // int si = 0;
    // while (t >= 0) {
    //   ans.push_back(beam_history[t][si].dir);
    //   si = beam_history[t][si].prev_idx;
    //   --t;
    // }
    // reverse(ans.begin(), ans.end());
    // return ans;
  }

  vi solve_whole(vvi initial_tiles, int line) {
    // bidirectional search?
    int initial_pena = 0;
    uint64_t initial_hash = 0ull;
    unordered_set<uint64_t> visited_states;
    int sr = 0;
    int sc = 0;
    for (int i = line; i < N; ++i) {
      for (int j = line; j < N; ++j) {
        if (initial_tiles[i][j] == (((N - 1) << 8) | (N - 1))) {
          sr = i;
          sc = j;
        } else {
          int tr = initial_tiles[i][j] >> 8;
          int tc = initial_tiles[i][j] & 0xFF;
          initial_pena += (abs(tr - i) + abs(tc - j));
        }
        initial_hash ^= cell_hash[i][j] * initial_tiles[i][j];
      }
    }
    debug("initial_pena:%d\n", initial_pena);
    if (initial_pena == 0) return vi();
    visited_states.insert(initial_hash);
    State initial_state = {initial_tiles, initial_pena, sr, sc, -1, initial_hash};
    vector<State> cur_states = {initial_state};
    int turn = 0;
    for (; turn < T; ++turn) {
      debug("turn:%d\n", turn);
      vector<SingleMove> moves;
      for (int i = 0; i < cur_states.size(); ++i) {
        const State& cur_state = cur_states[i];
        // debug("er:%d ec:%d back_move:%d\n", cur_state.er, cur_state.ec, cur_state.back_move);
        for (int dir = 0; dir < 4; ++dir) {
          if (dir == cur_state.back_move) continue;
          int nr = cur_state.er + DR[dir];
          int nc = cur_state.ec + DC[dir];
          if (nr < line || N <= nr || nc < line || N <= nc) continue;
          int tr = cur_state.tiles[nr][nc] >> 8;
          int tc = cur_state.tiles[nr][nc] & 0xFF;
          uint64_t new_hash = cur_state.hash;
          new_hash ^= cur_state.tiles[cur_state.er][cur_state.ec] * cell_hash[cur_state.er][cur_state.ec];
          new_hash ^= cur_state.tiles[nr][nc] * cell_hash[nr][nc];
          new_hash ^= cur_state.tiles[cur_state.er][cur_state.ec] * cell_hash[nr][nc];
          new_hash ^= cur_state.tiles[nr][nc] * cell_hash[cur_state.er][cur_state.ec];
          if (visited_states.count(new_hash) != 0) {
            continue;
          }
          int diff = ((abs(tr - cur_state.er) + abs(tc - cur_state.ec)) - (abs(tr - nr) + abs(tc - nc)));
          int move_pena = cur_state.penalty + diff;
          if (move_pena == 0) {
            vi ans = {dir};
            int t = turn - 1;
            int si = i;
            while (t >= 0) {
              ans.push_back(beam_history[t][si].dir);
              si = beam_history[t][si].prev_idx;
              --t;
            }
            reverse(ans.begin(), ans.end());
            return ans;
          }
          moves.push_back({move_pena, dir, i});
        }
      }
      if (moves.empty()) {
        debugStr("give up\n");
        break;
      }
      // sort(moves.begin(), moves.end());
      if (moves.size() > BEAM_SIZE) {
        nth_element(moves.begin(), moves.begin() + BEAM_SIZE, moves.end());
      }
      debug("turn:%d penalty:%d\n", turn, moves[0].penalty);
      vector<State> next_states;
      for (int i = 0; i < min((int)moves.size(), BEAM_SIZE); ++i) {
        const auto& move = moves[i];
        const State& parent_state = cur_states[move.state_idx];
        State next_state = {parent_state.tiles, move.penalty, parent_state.er + DR[move.dir], parent_state.ec + DC[move.dir], move.dir ^ 2, 0ull};
        uint64_t new_hash = parent_state.hash;
        new_hash ^= parent_state.tiles[parent_state.er][parent_state.ec] * cell_hash[parent_state.er][parent_state.ec];
        new_hash ^= parent_state.tiles[next_state.er][next_state.ec] * cell_hash[next_state.er][next_state.ec];
        new_hash ^= parent_state.tiles[parent_state.er][parent_state.ec] * cell_hash[next_state.er][next_state.ec];
        new_hash ^= parent_state.tiles[next_state.er][next_state.ec] * cell_hash[parent_state.er][parent_state.ec];
        next_state.hash = new_hash;
        if (visited_states.count(new_hash) != 0) {
          continue;
        }
        visited_states.insert(new_hash);
        swap(next_state.tiles[parent_state.er][parent_state.ec], next_state.tiles[next_state.er][next_state.ec]);
        next_states.push_back(next_state);
        beam_history[turn][next_states.size() - 1].prev_idx = move.state_idx;
        beam_history[turn][next_states.size() - 1].dir = move.dir;
      }
      swap(cur_states, next_states);
    }

    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        debug("(%2d %2d) ", cur_states[0].tiles[i][j] >> 8, cur_states[0].tiles[i][j] & 0xFF);
      }
      debugln();
    }
    vi ans;
    int t = turn - 1;
    int si = 0;
    while (t >= 0) {
      ans.push_back(beam_history[t][si].dir);
      si = beam_history[t][si].prev_idx;
      --t;
    }
    reverse(ans.begin(), ans.end());
    return ans;
  }

  vi solve() {

    vi ret;
    // for (int line = 0; line < N - 4; ++line) {
    //   vi line_ans = solve_line(tiles, line);
    //   int er = 0;
    //   int ec = 0;
    //   for (int r = 0; r < N; ++r) {
    //     for (int c = 0; c < N; ++c) {
    //       if (tiles[r][c] == ((N - 1) << 8 | (N - 1))) {
    //         er = r;
    //         ec = c;
    //       }
    //     }
    //   }
    //   for (int move : line_ans) {
    //     int nr = er + DR[move];
    //     int nc = ec + DC[move];
    //     swap(tiles[er][ec], tiles[nr][nc]);
    //     er = nr;
    //     ec = nc;
    //   }
    //   for (int i = 0; i < N; ++i){
    //     if (tiles[line][i] != ((line << 8) | i)) {
    //       return ret;
    //     }
    //     if (tiles[i][line] != ((i << 8) | line)) {
    //       return ret;
    //     }
    //   }
    //   ret.insert(ret.end(), line_ans.begin(), line_ans.end());
    // }
    vi last_ans = solve_whole(tiles, 0);
    ret.insert(ret.end(), last_ans.begin(), last_ans.end());
    return ret;
  }
};

struct Solver {
  Solver() {}

  void remove_redundant_moves(vi& moves) {
    vi moves_tmp;
    for (int i = 0; i < moves.size(); ++i) {
      if (!moves_tmp.empty() && moves_tmp.back() == (moves[i] ^ 2)) {
        // debug("redundant moves at %d\n", i);
        moves_tmp.pop_back();
      } else {
        moves_tmp.push_back(moves[i]);
      }
    }
    swap(moves, moves_tmp);
  }

  Result solve() {
    vi best_ans(T + 1, 0);
    int turn = 0;
    uint64_t worst_time = 0;
    uint64_t before_time = get_elapsed_msec();
    while (true) {
      if (get_elapsed_msec() + worst_time > TL * 3 / 4) {
        debug("total_first_turn:%d\n", turn);
        break;
      }
      bool success = false;
      vi ans = solve_one(success, best_ans.size());
      if (success) {
        remove_redundant_moves(ans);
        if (ans.size() < best_ans.size()) {
          swap(ans, best_ans);
          debug("best_ans:%lu at turn %d\n", best_ans.size(), turn);
        }
      }
      turn++;
      uint64_t after_time = get_elapsed_msec();
      worst_time = max(worst_time, after_time - before_time);
      before_time = after_time;
    }

    turn = 0;
    worst_time = 0;
    before_time = get_elapsed_msec();
    vvi target_tiles;
    vvi initial_tiles;
    for (int i = 0; i < N; ++i) {
      initial_tiles.push_back(vi(orig_tiles[i].begin(), orig_tiles[i].begin() + N));
      target_tiles.push_back(vi(orig_tiles[i].begin(), orig_tiles[i].begin() + N));
    }
    int er = 0;
    int ec = 0;
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        if (initial_tiles[i][j] == EMPTY) {
          er = i;
          ec = j;
        }
      }
    }
    for (int dir : best_ans) {
      int nr = er + DR[dir];
      int nc = ec + DC[dir];
      swap(target_tiles[er][ec], target_tiles[nr][nc]);
      er = nr;
      ec = nc;
    }
    while (true) {
      if (get_elapsed_msec() + worst_time > TL) {
        debug("total_second_turn:%d\n", turn);
        break;
      }
      bool success = false;
      PuzzleSolver puzzle_solver(initial_tiles, target_tiles);
      vi ans = puzzle_solver.solve(success, best_ans.size());
      if (success) {
        remove_redundant_moves(ans);
        if (ans.size() < best_ans.size()) {
          swap(ans, best_ans);
          debug("best_ans:%lu at turn %d\n", best_ans.size(), turn);
        }
      }
      turn++;
      uint64_t after_time = get_elapsed_msec();
      worst_time = max(worst_time, after_time - before_time);
      before_time = after_time;
    }

    return {best_ans, N * N - 1};
  }

  vi solve_one(bool& success, int best_len) {
    START_TIMER(0);
    TreePlacer tree_placer;
    vvi target_tiles = tree_placer.find();
    STOP_TIMER(0);
    if (target_tiles.empty()) {
      debugStr("faile to find target tree\n");
      success = false;
      return vi();
    }

    // remove sentinel
    target_tiles.pop_back();
    target_tiles.erase(target_tiles.begin());
    for (auto& row : target_tiles) {
      row.pop_back();
      row.erase(row.begin());
    }
    // print_tiles(target_tiles, false);

    vvi tiles;
    for (int i = 0; i < N; ++i) {
      tiles.push_back(vi(orig_tiles[i].begin(), orig_tiles[i].begin() + N));
    }
    PuzzleSolver puzzle_solver(tiles, target_tiles);
    return puzzle_solver.solve(success, best_len);
  }
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
      cell_hash[i][j] = ((uint64_t)rnd.nextUInt() << 32) | rnd.nextUInt();
    }
  }

  auto solver = unique_ptr<Solver>(new Solver());
  Result res = solver->solve();
  for (int m : res.moves) {
    printf("%c", DIR_CHARS[m]);
  }
  printf("\n");
  fflush(stdout);
  PRINT_TIMER();
#ifdef LOCAL
  int verify_score = verify(res.moves);
  debug("verify score=%d\n", verify_score);
  debug("score=%d\n", res.score());
  assert(res.score() == verify_score);
#endif
}