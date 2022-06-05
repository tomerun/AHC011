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
constexpr ll TL = 2000;
#endif

inline ll get_time() {
  struct timeval tv;
  gettimeofday(&tv, NULL);
  ll result =  tv.tv_sec * 1000LL + tv.tv_usec / 1000LL;
  return result;
}

const ll start_time = get_time(); // msec

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
void print_tiles(const T& tiles, bool with_sentinel = false) {
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

constexpr int EMBED_SIZE = 8;
array<array<int, 1 << (3 * 6)>, EMBED_SIZE - 1> embed_pattern;
constexpr int EMBED_SIZE_3 = 6;
array<array<array<array<array<array<array<array<int, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3> embed_pattern_3;
array<array<array<array<array<array<array<array<int, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3>, EMBED_SIZE_3> embed_pattern_3_bottom;

inline int pack_embed_pos(int sr, int sc, int tr0, int tc0, int tr1, int tc1) {
  return (sr << 15) | (sc << 12) | (tr0 << 9) | (tc0 << 6) | (tr1 << 3) | tc1;
}

void precalc_pattern() {
  for (int i = 0; i <= EMBED_SIZE - 2; ++i) {
    auto& pat = embed_pattern[i];
    fill(pat.begin(), pat.end(), -1);
    vi cur_que = {
      pack_embed_pos(i, 1, i, 0, i + 1, 0),
      pack_embed_pos(i + 1, 1, i, 0, i + 1, 0)
    };
    if (i != 0) {
      cur_que.push_back(pack_embed_pos(i - 1, 0, i, 0, i + 1, 0));
    }
    for (int p : cur_que) {
      pat[p] = 0;
    }
    vi dirs = {0, 1, 3, 2};
    for (int dist = 1; !cur_que.empty(); ++dist) {
      // debug("dist:%d que_size:%lu\n", dist, cur_que.size());
      vi next_que;
      for (int p : cur_que) {
        int sr = p >> 15;
        int sc = (p >> 12) & 7;
        int tr0 = (p >> 9) & 7;
        int tc0 = (p >> 6) & 7;
        int tr1 = (p >> 3) & 7;
        int tc1 = (p >> 0) & 7;
        for (int dir : dirs) {
          int nr = sr + DR[dir];
          int nc = sc + DC[dir];
          if (nr < 0 || EMBED_SIZE <= nr || nc < 0 || EMBED_SIZE <= nc) continue;
          if (nc == 0 && nr > i + 1) continue;
          int ntr0, ntc0, ntr1, ntc1;
          if (nr == tr0 && nc == tc0) {
            ntr0 = sr;
            ntc0 = sc;
          } else {
            ntr0 = tr0;
            ntc0 = tc0;
          }
          if (nr == tr1 && nc == tc1) {
            ntr1 = sr;
            ntc1 = sc;
          } else {
            ntr1 = tr1;
            ntc1 = tc1;
          }
          int np = pack_embed_pos(nr, nc, ntr0, ntc0, ntr1, ntc1);
          if (pat[np] == -1) {
            pat[np] = (dist << 2) | dir;
            next_que.push_back(np);
          }
        }
      }
      swap(cur_que, next_que);
    }
    // verify
    // for (int l = 0; l < 10000; ++l) {
    //   int sr = rnd.nextUInt(EMBED_SIZE);
    //   int sc = rnd.nextUInt(EMBED_SIZE - 1) + 1;
    //   int tr0 = rnd.nextUInt(EMBED_SIZE);
    //   int tc0 = rnd.nextUInt(EMBED_SIZE - 1) + 1;
    //   while (tr0 == sr && tc0 == sc) {
    //     tr0 = rnd.nextUInt(EMBED_SIZE);
    //     tc0 = rnd.nextUInt(EMBED_SIZE - 1) + 1;
    //   }
    //   int tr1 = rnd.nextUInt(EMBED_SIZE);
    //   int tc1 = rnd.nextUInt(EMBED_SIZE - 1) + 1;
    //   while ((tr1 == sr && tc1 == sc) || (tr1 == tr0 && tc1 == tc0)) {
    //     tr1 = rnd.nextUInt(EMBED_SIZE);
    //     tc1 = rnd.nextUInt(EMBED_SIZE - 1) + 1;
    //   }
    //   int ini_max_r = max({2, i + 1, sr, tr0, tr1});
    //   int ini_max_c = max({3, sc, tc0, tc1});
    //   int p = pack_embed_pos(sr, sc, tr0, tc0, tr1, tc1);
    //   int len = pat[p] >> 2;
    //   int max_r = 0;
    //   int max_c = 0;
    //   // debugln();
    //   debug("%d %d %d %d %d %d\n", sr, sc, tr0, tc0, tr1, tc1);
    //   while (true) {
    //     max_r = max(max_r, sr);
    //     max_c = max(max_c, sc);
    //     if ((pat[p] >> 2) == 0) {
    //       assert(len == 0);
    //       if (max_r > ini_max_r) {
    //         debug("max_r %d %d\n", max_r, ini_max_r);
    //       }
    //       if (max_c > ini_max_c) {
    //         debug("max_c %d %d\n", max_c, ini_max_c);
    //       }
    //       break;
    //     }
    //     int dir = pat[p] & 3;
    //     sr -= DR[dir];
    //     sc -= DC[dir];
    //     if (sr == tr0 && sc == tc0) {
    //       tr0 += DR[dir];
    //       tc0 += DC[dir];
    //     } else if (sr == tr1 && sc == tc1) {
    //       tr1 += DR[dir];
    //       tc1 += DC[dir];
    //     }
    //     len--;
    //     p = pack_embed_pos(sr, sc, tr0, tc0, tr1, tc1);
    //   }
    // }
  }
}

inline int pack_embed_pos_3(int sr, int sc, int tr0, int tc0, int tr1, int tc1, int tr2, int tc2) {
  return (sr << 21) | (sc << 18) | (tr0 << 15) | (tc0 << 12) | (tr1 << 9) | (tc1 << 6) | (tr2 << 3) | tc2;
}

void precalc_pattern_3() {
  for (int type = 0; type <= 1; ++type) {
    auto& pat = type == 0 ? embed_pattern_3 : embed_pattern_3_bottom;
    int shift = type == 0 ? 1 : 3;
    vi cur_que = {
      pack_embed_pos_3(shift - 1 + 1, 1, shift, 0, shift + 1, 0, shift + 2, 0),
      pack_embed_pos_3(shift - 1 + 2, 1, shift, 0, shift + 1, 0, shift + 2, 0),
      pack_embed_pos_3(shift - 1 + 3, 1, shift, 0, shift + 1, 0, shift + 2, 0),
      pack_embed_pos_3(shift - 1 + 0, 0, shift, 0, shift + 1, 0, shift + 2, 0),
    };
    // hack
    pat[shift - 1 + 1][1][shift][0][shift + 1][0][shift + 2][0] = -1;
    pat[shift - 1 + 2][1][shift][0][shift + 1][0][shift + 2][0] = -1;
    pat[shift - 1 + 3][1][shift][0][shift + 1][0][shift + 2][0] = -1;
    pat[shift - 1 + 0][0][shift][0][shift + 1][0][shift + 2][0] = -1;
    vi dirs = {0, 1, 3, 2};
    for (int dist = 1; !cur_que.empty(); ++dist) {
      // debug("dist:%d que_size:%lu\n", dist, cur_que.size());
      vi next_que;
      for (int p : cur_que) {
        int sr = p >> 21;
        int sc = (p >> 18) & 7;
        int tr0 = (p >> 15) & 7;
        int tc0 = (p >> 12) & 7;
        int tr1 = (p >> 9) & 7;
        int tc1 = (p >> 6) & 7;
        int tr2 = (p >> 3) & 7;
        int tc2 = (p >> 0) & 7;
        for (int dir : dirs) {
          int nr = sr + DR[dir];
          int nc = sc + DC[dir];
          if (nr < 0 || EMBED_SIZE_3 <= nr || nc < 0 || EMBED_SIZE_3 <= nc) continue;
          if (nc == 0 && nr > shift + 2) continue;
          int ntr0, ntc0, ntr1, ntc1, ntr2, ntc2;
          if (nr == tr0 && nc == tc0) {
            ntr0 = sr;
            ntc0 = sc;
          } else {
            ntr0 = tr0;
            ntc0 = tc0;
          }
          if (nr == tr1 && nc == tc1) {
            ntr1 = sr;
            ntc1 = sc;
          } else {
            ntr1 = tr1;
            ntc1 = tc1;
          }
          if (nr == tr2 && nc == tc2) {
            ntr2 = sr;
            ntc2 = sc;
          } else {
            ntr2 = tr2;
            ntc2 = tc2;
          }
          if (pat[nr][nc][ntr0][ntc0][ntr1][ntc1][ntr2][ntc2] == 0) {
            pat[nr][nc][ntr0][ntc0][ntr1][ntc1][ntr2][ntc2] = (dist << 2) | dir;
            int np = pack_embed_pos_3(nr, nc, ntr0, ntc0, ntr1, ntc1, ntr2, ntc2);
            next_que.push_back(np);
          }
        }
      }
      swap(cur_que, next_que);
    }
    pat[shift - 1 + 1][1][shift][0][shift + 1][0][shift + 2][0] = 0;
    pat[shift - 1 + 2][1][shift][0][shift + 1][0][shift + 2][0] = 0;
    pat[shift - 1 + 3][1][shift][0][shift + 1][0][shift + 2][0] = 0;
    pat[shift - 1 + 0][0][shift][0][shift + 1][0][shift + 2][0] = 0;
  }
}

// maximize
bool accept(int diff, double cooler) {
  if (diff >= 0) return true;
  double v = diff * cooler;
  if (v < -10) return false;
  return rnd.nextDouble() < exp(v);
}

bool is_tree(const vvi& tiles) {
  UnionFind uf(N * N);
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      int t = tiles[i][j];
      for (int k = 0; k < 4; ++k) {
        if ((t & (1 << k)) == 0) continue;
        int nr = i + DR[k];
        int nc = j + DC[k];
        if (!in_grid(nr) || !in_grid(nc)) return false;
        if ((tiles[nr][nc] & (1 << (k ^ 2))) == 0) return false;
        uf.unite(i * N + j, nr * N + nc);
      }
    }
  }
  return uf.size(tiles[0][0] == 0 ? 1 : 0) == N * N - 1;
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
    if (i < moves.size() - 1 && is_tree(tiles)) {
      debug("is_tree %d\n", i);
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
  vi count;
  vvi bfs_from;
  vvi tiles;
  vector<pair<int, int>> es;

  TreePlacer() {
    orig_count.assign(16, 0);
    count.assign(16, 0);
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        orig_count[orig_tiles[i][j]]++;
      }
    }
    bfs_from.assign(N + 2, vi(N + 2, 0));
    tiles.assign(N + 2, vi(N + 2, EMPTY));
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
    create_random();
  }

  void create_random() {
    randomize(es);
    UnionFind uf(N * N - 1);
    for (int i = 1; i <= N; ++i) {
      fill(tiles[i].begin(), tiles[i].end(), EMPTY);
    }
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
    fill(count.begin(), count.end(), 0);
    for (int i = 0; i < N; ++i) {
      for (int j = 0; j < N; ++j) {
        count[tiles[i + 1][j + 1]]++;
      }
    }
  }

  inline void decrease(int& diff, int v) {
    if (count[v] > orig_count[v]) {
      diff--;
    } else {
      diff++;
    }
    count[v]--;
  }

  inline void increase(int& diff, int v) {
    if (count[v] < orig_count[v]) {
      diff--;
    } else {
      diff++;
    }
    count[v]++;
  }

  template <bool greedy>
  int find_cut_pos(int sr, int sc, int gr, int gc) {
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
      if (greedy) {
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
      } else {
        cut_pos_cands.push_back((cut_r << 8) | cut_c);
      }
      cut_r = ncut_r;
      cut_c = ncut_c;
    }
    return cut_pos_cands[rnd.nextUInt(cut_pos_cands.size())];
  }

  void set(const vvi& target) {
    for (int i = 0; i < N; ++i) {
      copy(target[i].begin(), target[i].end(), tiles[i + 1].begin() + 1);
    }
    count = orig_count;
  }

  vvi find(bool reset=false) {
    if (reset) {
      create_random();
    }
    int cur_diff = 0;
    for (int i = 1; i <= 15; ++i) {
      cur_diff += abs(orig_count[i] - count[i]);
    }
    const double initial_cooler_log = log(2.0);
    const double final_cooler_log = log(3.0);
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
      decrease(diff, tile);
      decrease(diff, ntile);
      const int tile_new = tile | (1 << dir);
      const int ntile_new = ntile | (1 << (dir ^ 2));
      increase(diff, tile_new);
      increase(diff, ntile_new);
      bfs_que.clear();
      bfs_que.push_back((tiles[cr][cc] << 16) | (cr << 8) | cc);
      int qi = 0;
      // debug("bfs cr:%d cc:%d nr:%d nc:%d\n", cr, cc, nr, nc);
      while (true) {
        int r0 = (bfs_que[qi] >> 8) & 0xFF;
        int c0 = bfs_que[qi] & 0xFF;
        int t = bfs_que[qi] >> 16;
        while (t) {
          int i = __builtin_ctz(t);
          t &= t - 1;
          int r1 = r0 + DR[i];
          int c1 = c0 + DC[i];
          bfs_from[r1][c1] = i ^ 2;
          if (r1 == nr && c1 == nc) {
            goto END_BFS;
          }
          int t2 = tiles[r1][c1] ^ (1 << (i ^ 2));
          if (t2) {
            bfs_que.push_back((t2 << 16) | (r1 << 8) | c1);
          }
        }
        qi++;
      }
END_BFS:
      tiles[cr][cc] |= 1 << dir;
      tiles[nr][nc] |= 1 << (dir ^ 2);
      const bool force = !reset && turn < 1;
      const int cut_pos = force ? find_cut_pos<true>(nr, nc, cr, cc) : find_cut_pos<true>(nr, nc, cr, cc);
      const int cut_r = cut_pos >> 8;
      const int cut_c = cut_pos & 0xFF;
      const int prev_dir = bfs_from[cut_r][cut_c];
      const int ncut_r = cut_r + DR[prev_dir];
      const int ncut_c = cut_c + DC[prev_dir];
      decrease(diff, tiles[cut_r][cut_c]);
      decrease(diff, tiles[ncut_r][ncut_c]);
      increase(diff, tiles[cut_r][cut_c] ^ (1 << prev_dir));
      increase(diff, tiles[ncut_r][ncut_c] ^ (1 << (prev_dir ^ 2)));
      if (force || accept(-diff, cooler)) {
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
      // remove sentinel
      vvi target_tiles;
      for (int i = 1; i <= N; ++i) {
        target_tiles.push_back(vi(tiles[i].begin() + 1, tiles[i].begin() + N + 1));
      }
      return target_tiles;
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

array<array<array<uint64_t, 16>, 10>, 10> cell_hash;
constexpr int BEAM_SIZE = 100;
array<array<History, BEAM_SIZE>, 2000> beam_history;
array<array<int, 16>, 16> manhattan;

struct PuzzleSolver {
  // rule base + exhaustive search for final 3x3 area
  vvi tiles;
  vvi target;
  vi ans;
  vector<vector<bool>> protect;
  int er;
  int ec;
  vvi bfs_from;
  vvi bfs_cnt;
  int bfs_counter;
  array<int, 100> pattern_result;
  bool is_flipped;

  PuzzleSolver(const vvi& initial_tiles_, const vvi& target_)
   : tiles(initial_tiles_), target(target_), protect(N, vector<bool>(N, false)), bfs_counter(0), is_flipped(false) {
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
    int real_dir = convert_dir(dir);
    if (!ans.empty() && ans.back() == (real_dir ^ 2)) {
      ans.pop_back();
    } else {
      ans.push_back(real_dir);
    }
    int nr = er + DR[dir];
    int nc = ec + DC[dir];
    // assert(!protect[nr][nc]);
    swap(tiles[er][ec], tiles[nr][nc]);
    er = nr;
    ec = nc;
  }

  int recover_pattern(int shift, int sr, int sc, int tr0, int tc0, int tr1, int tc1) {
    // debug("recover_pattern %d\n", shift);
    const auto& pat = embed_pattern[shift];
    int p = pack_embed_pos(sr, sc, tr0, tc0, tr1, tc1);
    int ri = 0;
    while (true) {
      // debug("%d %d %d %d %d %d\n", sr, sc, tr0, tc0, tr1, tc1);
      int len = pat[p] >> 2;
      if (len == 0) break;
      int dir = pat[p] & 3;
      sr -= DR[dir];
      sc -= DC[dir];
      if (sr == tr0 && sc == tc0) {
        tr0 += DR[dir];
        tc0 += DC[dir];
      } else if (sr == tr1 && sc == tc1) {
        tr1 += DR[dir];
        tc1 += DC[dir];
      }
      pattern_result[ri++] = dir ^ 2;
      p = pack_embed_pos(sr, sc, tr0, tc0, tr1, tc1);
    }
    return ri;
  }

  bool solve_pattern_up(int level, int pos) {
    int top = max(level, max(pos + 1, er) - EMBED_SIZE + 1);
    if (top > pos) return false;
    int sr = er - top;
    int sc = ec - level;
    // debug("level:%d top:%d sr:%d sc:%d\n", level, top, sr, sc);
    int sp = (sr << 15) | (sc << 12);
    vi cands0;
    vi cands1;
    for (int r = top; r < min(top + EMBED_SIZE, N); ++r) {
      for (int c = (r <= pos + 1 ? level : level + 1); c < min(level + EMBED_SIZE, N); ++c) {
        if (tiles[r][c] == target[pos][level]) {
          cands0.push_back(((r - top) << 3) | (c - level));
        } else if (tiles[r][c] == target[pos + 1][level]) {
          cands1.push_back(((r - top) << 3) | (c - level));
        }
      }
    }
    const int shift = pos - top;
    int best_len = INF;
    int best_st = 0;
    if (target[pos][level] == target[pos + 1][level]) {
      for (int i = 0; i < cands0.size(); ++i) {
        for (int j = 0; j < cands0.size(); ++j) {
          if (i == j) continue;
          int st = sp | (cands0[i] << 6) | cands0[j];
          if (embed_pattern[shift][st] < best_len) {
            best_len = embed_pattern[shift][st];
            best_st = st;
          }
        }
      }
    } else {
      for (int i = 0; i < cands0.size(); ++i) {
        for (int j = 0; j < cands1.size(); ++j) {
          int st = sp | (cands0[i] << 6) | cands1[j];
          if (embed_pattern[shift][st] < best_len) {
            best_len = embed_pattern[shift][st];
            best_st = st;
          }
        }
      }
    }
    if (best_len == INF) {
      return false;
    }
    int len = recover_pattern(shift, sr, sc, (best_st >> 9) & 7, (best_st >> 6) & 7, (best_st >> 3) & 7, (best_st >> 0) & 7);
    for (int i = 0; i < len; ++i) {
      int dir = pattern_result[i];
      int nr = er + DR[dir];
      int nc = ec + DC[dir];
      if (nr == N || nc == N) {
        // debug("fail_up %d %d %d\n", nr, nc, len);
        for (int j = i - 1; j >= 0; --j) {
          step(pattern_result[j] ^ 2);
        }
        return false;
      }
      step(dir);
    }
    return true;
  }

  bool solve_pattern_right(int level, int pos) {
    int right = min(N - 1, max(pos, level + EMBED_SIZE));
    if (ec <= right - EMBED_SIZE) return false;
    int sr = right - ec;
    int sc = er - level;
    int sp = (sr << 15) | (sc << 12);
    // debug("level:%d right:%d sr:%d sc:%d\n", level, right, sr, sc);
    vi cands0;
    vi cands1;
    for (int r = level; r < min(level + EMBED_SIZE, N); ++r) {
      for (int c = (r == level ? pos - 1 : max(level + 1, right - EMBED_SIZE + 1)); c <= right; ++c) {
        if (tiles[r][c] == target[level][pos]) {
          cands0.push_back(((right - c) << 3) | (r - level));
        } else if (tiles[r][c] == target[level][pos - 1]) {
          cands1.push_back(((right - c) << 3) | (r - level));
        }
      }
    }
    const int shift = right - pos;
    int best_len = INF;
    int best_st = 0;
    if (target[level][pos] == target[level][pos - 1]) {
      for (int i = 0; i < cands0.size(); ++i) {
        for (int j = 0; j < cands0.size(); ++j) {
          if (i == j) continue;
          int st = sp | (cands0[i] << 6) | cands0[j];
          if (embed_pattern[shift][st] < best_len) {
            best_len = embed_pattern[shift][st];
            best_st = st;
          }
        }
      }
    } else {
      for (int i = 0; i < cands0.size(); ++i) {
        for (int j = 0; j < cands1.size(); ++j) {
          int st = sp | (cands0[i] << 6) | cands1[j];
          if (embed_pattern[shift][st] < best_len) {
            best_len = embed_pattern[shift][st];
            best_st = st;
          }
        }
      }
    }
    if (best_len == INF) {
      return false;
    }
    int len = recover_pattern(shift, sr, sc, (best_st >> 9) & 7, (best_st >> 6) & 7, (best_st >> 3) & 7, (best_st >> 0) & 7);
    for (int i = 0; i < len; ++i) {
      int dir = (pattern_result[i] + 1) & 3;
      int nr = er + DR[dir];
      int nc = ec + DC[dir];
      if (nr == N || nc == N || protect[nr][nc]) {
        // debug("fail_right %d %d %d\n", nr, nc, len);
        for (int j = i - 1; j >= 0; --j) {
          step((pattern_result[j] + 3) & 3);
        }
        return false;
      }
      step(dir);
    }
    return true;
  }

  int recover_pattern_3(bool bottom, int sr, int sc, int tr0, int tc0, int tr1, int tc1, int tr2, int tc2) {
    // debugStr("recover_pattern_3\n");
    const auto& pat = bottom ? embed_pattern_3_bottom : embed_pattern_3;
    int ri = 0;
    while (true) {
      // debug("%d %d %d %d %d %d %d %d\n", sr, sc, tr0, tc0, tr1, tc1, tr2, tc2);
      int v = pat[sr][sc][tr0][tc0][tr1][tc1][tr2][tc2];
      int len = v >> 2;
      if (len == 0) break;
      int dir = v & 3;
      sr -= DR[dir];
      sc -= DC[dir];
      if (sr == tr0 && sc == tc0) {
        tr0 += DR[dir];
        tc0 += DC[dir];
      } else if (sr == tr1 && sc == tc1) {
        tr1 += DR[dir];
        tc1 += DC[dir];
      } else if (sr == tr2 && sc == tc2) {
        tr2 += DR[dir];
        tc2 += DC[dir];
      }
      pattern_result[ri++] = dir ^ 2;
    }
    return ri;
  }

  int find_best_pos_pattern_3(
    bool bottom, int sr, int sc, int t0, int t1, int t2,
    const vi& cands0, const vi& cands1, const vi& cands2, array<int, 6>& best_pos
  ) {
    const auto& pat = bottom ? embed_pattern_3_bottom[sr][sc] : embed_pattern_3[sr][sc];
    int best_len = INF;
    if (t0 == t1 && t0 == t2) {
      for (int i = 0; i < cands0.size(); ++i) {
        int r0 = cands0[i] >> 3;
        int c0 = cands0[i] & 7;
        for (int j = 0; j < cands0.size(); ++j) {
          if (i == j) continue;
          int r1 = cands0[j] >> 3;
          int c1 = cands0[j] & 7;
          for (int k = 0; k < cands0.size(); ++k) {
            if (k == i || k == j) continue;
            int r2 = cands0[k] >> 3;
            int c2 = cands0[k] & 7;
            if (pat[r0][c0][r1][c1][r2][c2] < best_len) {
              best_len = pat[r0][c0][r1][c1][r2][c2];
              best_pos = {r0, c0, r1, c1, r2, c2};
            }
          }
        }
      }
    } else if (t0 == t1) {
      for (int i = 0; i < cands0.size(); ++i) {
        int r0 = cands0[i] >> 3;
        int c0 = cands0[i] & 7;
        for (int j = 0; j < cands0.size(); ++j) {
          if (i == j) continue;
          int r1 = cands0[j] >> 3;
          int c1 = cands0[j] & 7;
          for (int k = 0; k < cands2.size(); ++k) {
            int r2 = cands2[k] >> 3;
            int c2 = cands2[k] & 7;
            if (pat[r0][c0][r1][c1][r2][c2] < best_len) {
              best_len = pat[r0][c0][r1][c1][r2][c2];
              best_pos = {r0, c0, r1, c1, r2, c2};
            }
          }
        }
      }
    } else if (t0 == t2) {
      for (int i = 0; i < cands0.size(); ++i) {
        int r0 = cands0[i] >> 3;
        int c0 = cands0[i] & 7;
        for (int j = 0; j < cands0.size(); ++j) {
          if (i == j) continue;
          int r2 = cands0[j] >> 3;
          int c2 = cands0[j] & 7;
          for (int k = 0; k < cands1.size(); ++k) {
            int r1 = cands1[k] >> 3;
            int c1 = cands1[k] & 7;
            if (pat[r0][c0][r1][c1][r2][c2] < best_len) {
              best_len = pat[r0][c0][r1][c1][r2][c2];
              best_pos = {r0, c0, r1, c1, r2, c2};
            }
          }
        }
      }
    } else if (t1 == t2) {
      for (int i = 0; i < cands1.size(); ++i) {
        int r1 = cands1[i] >> 3;
        int c1 = cands1[i] & 7;
        for (int j = 0; j < cands1.size(); ++j) {
          if (i == j) continue;
          int r2 = cands1[j] >> 3;
          int c2 = cands1[j] & 7;
          for (int k = 0; k < cands0.size(); ++k) {
            int r0 = cands0[k] >> 3;
            int c0 = cands0[k] & 7;
            if (pat[r0][c0][r1][c1][r2][c2] < best_len) {
              best_len = pat[r0][c0][r1][c1][r2][c2];
              best_pos = {r0, c0, r1, c1, r2, c2};
            }
          }
        }
      }
    } else {
      for (int i = 0; i < cands0.size(); ++i) {
        int r0 = cands0[i] >> 3;
        int c0 = cands0[i] & 7;
        for (int j = 0; j < cands1.size(); ++j) {
          int r1 = cands1[j] >> 3;
          int c1 = cands1[j] & 7;
          for (int k = 0; k < cands2.size(); ++k) {
            int r2 = cands2[k] >> 3;
            int c2 = cands2[k] & 7;
            if (pat[r0][c0][r1][c1][r2][c2] < best_len) {
              best_len = pat[r0][c0][r1][c1][r2][c2];
              best_pos = {r0, c0, r1, c1, r2, c2};
            }
          }
        }
      }
    }
    return best_len;
  }

  bool solve_pattern_3_up(int level, int pos) {
    const bool bottom = pos == N - 3;
    int top = bottom ? pos - 3 : pos - 1;
    if (er < top || top + EMBED_SIZE_3 <= er || level + EMBED_SIZE_3 <= ec) return false;
    int sr = er - top;
    int sc = ec - level;
    // debug("level:%d top:%d sr:%d sc:%d\n", level, top, sr, sc);
    int t0 = target[pos][level];
    int t1 = target[pos + 1][level];
    int t2 = target[pos + 2][level];
    vi cands0;
    vi cands1;
    vi cands2;
    for (int r = max(level, top); r < min(top + EMBED_SIZE_3, N); ++r) {
      for (int c = (r <= pos + 2 ? level : level + 1); c < min(level + EMBED_SIZE_3, N); ++c) {
        if (tiles[r][c] == t0) {
          cands0.push_back(((r - top) << 3) | (c - level));
        } else if (tiles[r][c] == t1) {
          cands1.push_back(((r - top) << 3) | (c - level));
        } else if (tiles[r][c] == t2) {
          cands2.push_back(((r - top) << 3) | (c - level));
        }
      }
    }
    array<int, 6> best_pos;
    int best_len = find_best_pos_pattern_3(bottom, sr, sc, t0, t1, t2, cands0, cands1, cands2, best_pos);
    if (best_len == INF) {
      return false;
    }
    int len = recover_pattern_3(bottom, sr, sc, best_pos[0], best_pos[1], best_pos[2], best_pos[3], best_pos[4], best_pos[5]);
    for (int i = 0; i < len; ++i) {
      int dir = pattern_result[i];
      int nr = er + DR[dir];
      int nc = ec + DC[dir];
      if (nr == N || nc == N || nr < level) {
        // debug("fail_up %d %d %d\n", nr, nc, len);
        for (int j = i - 1; j >= 0; --j) {
          step(pattern_result[j] ^ 2);
        }
        return false;
      }
      step(dir);
    }
    return true;
  }

  bool solve_pattern_3_right(int level, int pos) {
    bool bottom = pos == level + 3;
    int right = bottom ? pos + 3 : pos + 1;
    if (er >= level + EMBED_SIZE_3 || ec > right || ec <= right - EMBED_SIZE_3) return false;
    int sr = right - ec;
    int sc = er - level;
    // debug("level:%d right:%d sr:%d sc:%d\n", level, right, sr, sc);
    int t0 = target[level][pos];
    int t1 = target[level][pos - 1];
    int t2 = target[level][pos - 2];
    vi cands0;
    vi cands1;
    vi cands2;
    for (int r = level; r < min(level + EMBED_SIZE_3, N); ++r) {
      for (int c = (r == level ? pos - 2 : max(level + 1, right - EMBED_SIZE_3 + 1)); c <= min(right, N - 1); ++c) {
        if (tiles[r][c] == t0) {
          cands0.push_back(((right - c) << 3) | (r - level));
        } else if (tiles[r][c] == t1) {
          cands1.push_back(((right - c) << 3) | (r - level));
        } else if (tiles[r][c] == t2) {
          cands2.push_back(((right - c) << 3) | (r - level));
        }
      }
    }
    array<int, 6> best_pos;
    int best_len = find_best_pos_pattern_3(bottom, sr, sc, t0, t1, t2, cands0, cands1, cands2, best_pos);
    if (best_len == INF) {
      return false;
    }
    int len = recover_pattern_3(bottom, sr, sc, best_pos[0], best_pos[1], best_pos[2], best_pos[3], best_pos[4], best_pos[5]);
    for (int i = 0; i < len; ++i) {
      int dir = (pattern_result[i] + 1) & 3;
      int nr = er + DR[dir];
      int nc = ec + DC[dir];
      if (nr == N || nc == N || nc <= level) {
        // debug("fail_right %d %d %d\n", nr, nc, len);
        for (int j = i - 1; j >= 0; --j) {
          step((pattern_result[j] + 3) & 3);
        }
        return false;
      }
      step(dir);
    }
    return true;
  }

  void solve_cw(int level) {
    for (int i = N - 1; i >= level + 2; --i) {
      if (tiles[i][level] == target[i][level]) {
        protect[i][level] = true;
        continue;
      }
      if (i != level + 3 && (rnd.nextUInt() & 3)) {
        bool found_pattern = solve_pattern_3_up(level, i - 2);
        if (found_pattern) {
          assert(tiles[i][level] == target[i][level]);
          assert(tiles[i - 1][level] == target[i - 1][level]);
          assert(tiles[i - 2][level] == target[i - 2][level]);
          protect[i][level] = true;
          protect[i - 1][level] = true;
          protect[i - 2][level] = true;
          i -= 2;
          continue;
        }
      }
      if (i > level + 2 && (rnd.nextUInt() & 7)) {
        bool found_pattern = solve_pattern_up(level, i - 1);
        if (found_pattern) {
          assert(tiles[i][level] == target[i][level]);
          assert(tiles[i - 1][level] == target[i - 1][level]);
          protect[i][level] = true;
          protect[i - 1][level] = true;
          --i;
          continue;
        }
      }
      convey(level, i, level, target[i][level]);
      protect[i][level] = true;
    }
    if (tiles[level][level] != target[level][level] || tiles[level + 1][level] != target[level + 1][level]) {
      bool found_pattern = solve_pattern_up(level, level);
      if (found_pattern) {
        assert(tiles[level][level] == target[level][level]);
        assert(tiles[level + 1][level] == target[level + 1][level]);
      } else {
        if (tiles[level + 1][level] == target[level + 1][level] && tiles[level][level] == target[level][level]) {
          // ok
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
        }
      }
    }
    protect[level + 1][level] = true;
    protect[level][level] = true;

    for (int i = level + 1; i < N - 2; ++i) {
      if (i != N - 4 && (rnd.nextUInt() & 3)) {
        bool found_pattern = solve_pattern_3_right(level, i + 2);
        if (found_pattern) {
          assert(tiles[level][i] == target[level][i]);
          assert(tiles[level][i + 1] == target[level][i + 1]);
          assert(tiles[level][i + 2] == target[level][i + 2]);
          protect[level][i] = true;
          protect[level][i + 1] = true;
          protect[level][i + 2] = true;
          i += 2;
          continue;
        }
      }
      if (i < N - 3 && (rnd.nextUInt() & 7)) {
        bool found_pattern = solve_pattern_right(level, i + 1);
        if (found_pattern) {
          assert(tiles[level][i] == target[level][i]);
          assert(tiles[level][i + 1] == target[level][i + 1]);
          protect[level][i] = true;
          protect[level][i + 1] = true;
          ++i;
          continue;
        }
      }
      convey(level, level, i, target[level][i]);
      protect[level][i] = true;
    }
    if (tiles[level][N - 1] != target[level][N - 1] || tiles[level][N - 2] != target[level][N - 2]) {
      bool found_pattern = solve_pattern_right(level, N - 1);
      if (found_pattern) {
        assert(tiles[level][N - 2] == target[level][N - 2]);
        assert(tiles[level][N - 1] == target[level][N - 1]);
        protect[level][N - 2] = true;
        protect[level][N - 1] = true;
      } else {
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
    }
  }

  bool solve_whole(int best_len) {
    const uint64_t mask = (1ull << (4 * 3 * 3)) - 1;
    const int base_coord = N - 3;
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
        int cur_bit_pos = ((cr - base_coord) * 3 + (cc - base_coord)) * 4;
        for (int dir = 0; dir < 4; ++dir) {
          int nr = cr + DR[dir];
          int nc = cc + DC[dir];
          if (nr < base_coord || N <= nr || nc < base_coord || N <= nc) continue;
          int next_bit_pos = ((nr - base_coord) * 3 + (nc - base_coord)) * 4;
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
          int cur_bit_pos = ((cr - base_coord) * 3 + (cc - base_coord)) * 4;
          for (int dir = 0; dir < 4; ++dir) {
            int nr = cr + DR[dir];
            int nc = cc + DC[dir];
            if (nr < base_coord || N <= nr || nc < base_coord || N <= nc) continue;
            int next_bit_pos = ((nr - base_coord) * 3 + (nc - base_coord)) * 4;
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
      for (int i = 0; i < 3 * 3; ++i) {
        if (((s >> (i * 4)) & 0xF) == 0) {
          int r = i / 3;
          int c = i % 3;
          int dir = visited_states[s];
          path.push_back(dir);
          int nr = r - DR[dir];
          int nc = c - DC[dir];
          uint64_t tile = (s >> ((nr * 3 + nc) * 4)) & 0xF;
          s ^= tile << ((nr * 3 + nc) * 4);
          s |= tile << ((r * 3 + c) * 4);
          break;
        }
      }
    }
    for (auto itr = path.rbegin(); itr != path.rend(); ++itr) {
      ans.push_back(convert_dir(*itr));
    }

    s = finish_state;
    while (s != target_state) {
      for (int i = 0; i < 3 * 3; ++i) {
        if (((s >> (i * 4)) & 0xF) == 0) {
          int r = i / 3;
          int c = i % 3;
          int dir = goal_states[s] ^ 2;
          ans.push_back(convert_dir(dir));
          int nr = r + DR[dir];
          int nc = c + DC[dir];
          uint64_t tile = (s >> ((nr * 3 + nc) * 4)) & 0xF;
          s ^= tile << ((nr * 3 + nc) * 4);
          s |= tile << ((r * 3 + c) * 4);
          break;
        }
      }
    }

    return true;
  }

  int convert_dir(int dir) {
    if (is_flipped) {
      return dir ^ 1;
    } else {
      return dir;
    }
  }

  inline void flip_tile(int& t) {
    t = ((t & 5) << 1) | ((t >> 1) & 5);
  }

  void flip() {
    for (int i = 1; i < N; ++i) {
      for (int j = 0; j < i; ++j) {
        swap(tiles[i][j], tiles[j][i]);
        swap(target[i][j], target[j][i]);
        flip_tile(tiles[i][j]);
        flip_tile(tiles[j][i]);
        flip_tile(target[i][j]);
        flip_tile(target[j][i]);
      }
      flip_tile(tiles[i][i]);
      flip_tile(target[i][i]);
    }
    swap(er, ec);
    is_flipped ^= true;
  }

  vi solve(bool& success, const vi& best_len, vi& cur_lens) {
    // debugStr("target\n");
    // print_tiles(target);
    // debugStr("tiles\n");
    // print_tiles(tiles);
    START_TIMER(1);
    for (int level = 0; level < N - 3; ++level) {
      solve_cw(level);
      // debug("level:%d len:%lu\n", level, ans.size());
      if (ans.size() > best_len[level] + 20) {
        success = false;
        STOP_TIMER(1);
        return ans;
      }
      cur_lens.push_back(ans.size());
      flip();
    }
    STOP_TIMER(1);
    START_TIMER(2);
    success = solve_whole(best_len.back());
    cur_lens.push_back(ans.size());
    STOP_TIMER(2);
    return ans;
  }
};

int pos_dist(int p0, int p1) {
  return abs((p0 >> 4) - (p1 >> 4)) + abs((p0 & 0xF) - (p1 & 0xF));
}

int calc_tiles_dist(const vvi target_tiles) {
  vvi orig_pos(16);
  vvi target_pos(16);
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      orig_pos[orig_tiles[i][j]].push_back((i << 4) | j);
      target_pos[target_tiles[i][j]].push_back((i << 4) | j);
    }
  }
  int sum = 0;
  for (int i = 1; i < 16; ++i) {
    if (target_pos[i].empty()) continue;
    int n = target_pos[i].size();
    int m = orig_pos[i].size();
    vi l2r(n, -1);
    vi r2l(m, -1);
    vvi dists(n, vi(m, 0));
    for (int j = 0; j < n; ++j) {
      for (int k = 0; k < m; ++k) {
        dists[j][k] = pos_dist(target_pos[i][j], orig_pos[i][k]);
      }
    }
    int pena = 0;
    for (int j = 0; j < n; ++j) {
      int min = INF;
      int mi = 0;
      for (int k = 0; k < m; ++k) {
        if (r2l[k] != -1) continue;
        if (dists[j][k] < min) {
          min = dists[j][k];
          mi = k;
        }
      }
      l2r[j] = mi;
      r2l[mi] = j;
      pena += min;
    }
    for (int turn = 0; turn < (n - 1) * m * 2; ++turn) {
      int i0 = rnd.nextUInt(n);
      int j0 = rnd.nextUInt(m - 1);
      if (j0 >= l2r[i0]) j0++;
      if (r2l[j0] == -1) {
        if (dists[i0][j0] <= dists[i0][l2r[i0]]) {
          pena += dists[i0][j0] - dists[i0][l2r[i0]];
          r2l[l2r[i0]] = -1;
          l2r[i0] = j0;
          r2l[j0] = i0;
        }
      } else {
        int i1 = r2l[j0];
        int j1 = l2r[i0];
        int diff = dists[i0][j0] + dists[i1][j1] - dists[i0][j1] - dists[i1][j0];
        if (diff <= 0) {
          l2r[i0] = j0;
          l2r[i1] = j1;
          r2l[j0] = i0;
          r2l[j1] = i1;
          pena += diff;
        }
      }
    }
    sum += pena;
  }
  return sum;
}

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

  vector<vvi> generate_targets() {
    ll elapsed = get_elapsed_msec();
    ll until = (TL - elapsed) / 4 + elapsed;
    unordered_set<uint64_t> visited;
    TreePlacer tree_placer;
    vector<vvi> targets;
    vector<pair<int, int>> penas;
    int prev_dist = INF;
    vvi prev_target;
    for (int i = 0; ; ++i) {
      // if (penas.size() > 100) break;
      if (get_elapsed_msec() > until) {
        break;
      }
      for (int j = 0; j < 1000; ++j) {
        // if (penas.size() > 100) break;
        if (get_elapsed_msec() > until) {
          debug("gen turn:%d %d\n", i, j);
          break;
        }
        vvi target = tree_placer.find(j == 0);
        if (j == 0) {
          prev_target = target;
        }
        uint64_t hash = 0;
        for (int r = 0; r < N; ++r) {
          for (int c = 0; c < N; ++c) {
            hash ^= cell_hash[r][c][target[r][c]];
          }
        }
        if (visited.count(hash)) {
          continue;
        }
        visited.insert(hash);
        START_TIMER(6);
        int d = calc_tiles_dist(target);
        penas.push_back({d, (int)targets.size()});
        STOP_TIMER(6);
        targets.push_back(target);
        if (d <= prev_dist) {
          prev_dist = d;
          prev_target = target;
        } else {
          tree_placer.set(prev_target);
        }
      }
    }
    const int CNT = 100;
    debug("count:%lu\n", penas.size());
    if (penas.size() > CNT) {
      vector<vvi> ret(CNT);
      nth_element(penas.begin(), penas.begin() + CNT, penas.end());
      for (int i = 0; i < CNT; ++i) {
        // debug("dist:%d\n", penas[i].first);
        swap(ret[i], targets[penas[i].second]);
      }
      return ret;
    } else {
      return targets;
    }
  }

  Result solve() {
    vi best_ans(T, 0);
    vi best_lens(N - 2, INF);
    vi cur_lens;
    // TreePlacer tree_placer;
    vvi initial_tiles;
    for (int i = 0; i < N; ++i) {
      initial_tiles.push_back(vi(orig_tiles[i].begin(), orig_tiles[i].begin() + N));
    }
    START_TIMER(0);
    vector<vvi> targets = generate_targets();
    STOP_TIMER(0);
    int best_target_idx = 0;
    int turn = 0;
    uint64_t worst_time = 0;
    uint64_t before_time = get_elapsed_msec();
    while (true) {
      if (get_elapsed_msec() + worst_time > TL * 9 / 10) {
        debug("total_first_turn:%d\n", turn);
        break;
      }
      vvi target_tiles = targets[turn % targets.size()];
      bool success = false;
      PuzzleSolver puzzle_solver(initial_tiles, target_tiles);
      cur_lens.clear();
      vi ans = puzzle_solver.solve(success, best_lens, cur_lens);
      if (success) {
        remove_redundant_moves(ans);
        if (ans.size() < best_ans.size()) {
          swap(ans, best_ans);
          swap(best_lens, cur_lens);
          best_target_idx = turn % targets.size();
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
    vvi target_tiles = targets[best_target_idx];
    while (true) {
      if (get_elapsed_msec() + worst_time > TL) {
        debug("total_second_turn:%d\n", turn);
        break;
      }
      bool success = false;
      PuzzleSolver puzzle_solver(initial_tiles, target_tiles);
      cur_lens.clear();
      vi ans = puzzle_solver.solve(success, best_lens, cur_lens);
      if (success) {
        remove_redundant_moves(ans);
        if (ans.size() < best_ans.size()) {
          swap(ans, best_ans);
          swap(best_lens, cur_lens);
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

};

void rot_orig_tiles() {
  vvi orig_tiles_tmp(N, vi(N, 0));
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      int t = orig_tiles[N - 1 - j][i];
      t = (t << 1) | (t >> 3);
      orig_tiles_tmp[i][j] = t & 0xF;
    }
  }
  for (int i = 0; i < N; ++i) {
    copy(orig_tiles_tmp[i].begin(), orig_tiles_tmp[i].end(), orig_tiles[i].begin());
  }
}

int main() {
  for (int i = 0; i < 16; ++i) {
    for (int j = 0; j < 16; ++j) {
      manhattan[i][j] = abs((i >> 2) - (j >> 2)) + abs((i & 3) - (j & 3));
    }
  }
  scanf("%d %d", &N, &T);
  int er = 0;
  int ec = 0;
  for (int i = 0; i < N; ++i) {
    char row[11];
    scanf("%s", row);
    for (int j = 0; j < N; ++j) {
      char tile = row[j];
      int t = ('0' <= tile && tile <= '9') ? (tile - '0') : (tile - 'a' + 10);
      orig_tiles[i][j] = t;
      for (int k = 0; k < 16; ++k) {
        cell_hash[i][j][k] = ((uint64_t)rnd.nextUInt() << 32) | rnd.nextUInt();
      }
      if (t == 0) {
        er = i;
        ec = j;
      }
    }
  }
  int dist_tl = er + ec;
  int dist_tr = er + (N - 1 - ec);
  int dist_bl = (N - 1 - er) + ec;
  int dist_br = (N - 1 - er) + (N - 1 - ec);
  int dist_min = min({dist_tl, dist_tr, dist_bl, dist_br});
  int rot;
  if (dist_bl == dist_min) {
    rot = 0;
  } else if (dist_br == dist_min) {
    rot = 1;
  } else if (dist_tr == dist_min) {
    rot = 2;
  } else {
    rot = 3;
  }
  debug("rot:%d\n", rot);
  for (int i = 0; i < rot; ++i) {
    rot_orig_tiles();
  }
  START_TIMER(7);
  precalc_pattern();
  precalc_pattern_3();
  STOP_TIMER(7);

  auto solver = unique_ptr<Solver>(new Solver());
  Result res = solver->solve();
  for (int i = 0; i < rot; ++i) {
    for (int j = 0; j < res.moves.size(); ++j) {
      res.moves[j] = (res.moves[j] + 3) & 3;
    }
  }
  for (int m : res.moves) {
    printf("%c", DIR_CHARS[m]);
  }
  printf("\n");
  fflush(stdout);
  PRINT_TIMER();
#ifdef LOCAL
  for (int i = 0; i < ((4 - rot) & 3); ++i) {
    rot_orig_tiles();
  }
  int verify_score = verify(res.moves);
  debug("verify score=%d\n", verify_score);
  debug("score=%d\n", res.score());
  assert(res.score() == verify_score);
#endif
}
