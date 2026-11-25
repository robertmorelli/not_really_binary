/* scan.c -- magnitude sweep for numbers whose digits are all 0/1 in every base 2..TOPBASE.
 *
 *   TOPBASE=6 : a(6) of OEIS A258107
 *   TOPBASE=5 : next term of A146025 after 82000 (any a(6) is also one of these)
 *
 * For each L we ask: is there N in [B^L, 2*B^L) (B = TOPBASE) with only 0/1 digits in
 * bases 3..B?  Writing N = B^L * u, the base-B condition says u lies in a Cantor set
 * C_B inside [1, B/(B-1)], and each other base b says u lies in s_b * C_b with
 * s_b = b^m / B^L.  We prove the intersection empty by interval refinement, in four
 * stages of increasing cost; every stage only ever rejects when padded intervals are
 * disjoint, so a rejection is a proof (given correct constants and libm exp to a few ulp).
 *
 *   1. arcs    : frac(L*log_b B) must fall in a fixed arc          (64-bit adds, ~all L)
 *   2. bitmaps : per-base table of phases compatible with base B   (lookup)
 *   3. ddfs    : joint refinement in doubles down to width 2e-12
 *   4. mdfs    : joint refinement in 192-bit fixed point down to width 2^-150
 *   5. anything left is handed to verify.py (exact / 320-bit integer intervals)
 *
 * build: cc -O3 -DTOPBASE=6 scan.c -o scan6 -lpthread
 */
#include <libgen.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef TOPBASE
#define TOPBASE 6
#endif
#define NB (TOPBASE - 3) /* other bases 3..TOPBASE-1 */
#define NA (NB + 1)      /* index NB is TOPBASE itself (scale 1) */

typedef uint64_t u64;
typedef int64_t i64;
typedef unsigned __int128 u128;

#include "consts.h"

#define LMAX (1ULL << 56) /* padding analysis assumes L below this */
#define BLK 4096          /* exact phase refresh interval for the 64-bit adds */
#define ARC_PAD (1ULL << 24)
#ifndef BM_BITS
#define BM_BITS 20
#endif

static int BASE[NA];
static double LNB[NA];

/* ---------- stage 1: arcs ---------- */
static u64 A64[NB], ARC_V[NB], ARC_R[NB];

/* theta = frac(L * log_b B) to 256 bits */
static inline void theta256(u64 L, int i, u64 out[4]) {
  const u64 *a = ALPHA_T[TOPBASE][BASE[i]];
  u128 c = 0;
  for (int j = 0; j < 4; j++) {
    c += (u128)a[j] * L;
    out[j] = (u64)c;
    c >>= 64;
  }
}

/* ---------- double-precision joint refinement ---------- */
#define KD 40
#define EPS 2e-14
#define STOP_PT 2e-12
static double INV[NA][KD], INVW[NA][KD];
static int KDMAX[NA];

typedef struct {
  int n;
  int id[NA];
  double slo[NA], shi[NA];
  u64 p[NA];
  int k[NA];
  double stop;
} dctx;

static int ddfs(dctx *c, double lo, double hi) {
  int w = -1;
  double ww = -1;
  for (int a = 0; a < c->n; a++) {
    int i = c->id[a], k = c->k[a];
    double wd = c->shi[a] * ((double)(c->p[a] * (u64)(BASE[i] - 1) + 1) * INVW[i][k]) -
                c->slo[a] * ((double)c->p[a] * INV[i][k]);
    if (wd > ww) ww = wd, w = a;
  }
  if (ww < c->stop) return 1;
  int i = c->id[w], k = c->k[w];
  u64 b = (u64)BASE[i], p = c->p[w];
  if (k + 1 >= KDMAX[i]) return 1; /* cannot refine further: keep (conservative) */
  for (u64 d = 0; d < 2; d++) {
    u64 q = p * b + d;
    double clo = c->slo[w] * ((double)q * INV[i][k + 1]) - EPS;
    double chi = c->shi[w] * ((double)(q * (b - 1) + 1) * INVW[i][k + 1]) + EPS;
    double nlo = lo > clo ? lo : clo, nhi = hi < chi ? hi : chi;
    if (nlo <= nhi) {
      c->p[w] = q;
      c->k[w] = k + 1;
      if (ddfs(c, nlo, nhi)) {
        c->p[w] = p;
        c->k[w] = k;
        return 1;
      }
    }
  }
  c->p[w] = p;
  c->k[w] = k;
  return 0;
}

static int ddfs_root(dctx *c) {
  double lo = 0, hi = 1e300;
  for (int a = 0; a < c->n; a++) {
    int i = c->id[a];
    c->p[a] = 1;
    c->k[a] = 0;
    double l = c->slo[a] - EPS, h = c->shi[a] * (double)BASE[i] / (double)(BASE[i] - 1) + EPS;
    if (l > lo) lo = l;
    if (h < hi) hi = h;
  }
  if (lo > hi) return 0;
  return ddfs(c, lo, hi);
}

/* ---------- stage 2: per-base bitmaps ---------- */
static u64 *BM[NB];

static void build_bitmaps(void) {
  const double pad = ldexp(1.0, -40), bw = ldexp(1.0, -BM_BITS);
  for (int i = 0; i < NB; i++) {
    size_t nbk = (size_t)1 << BM_BITS;
    BM[i] = calloc(nbk / 64, 8);
    for (size_t k = 0; k < nbk; k++) {
      i64 t = (i64)((u64)k << (64 - BM_BITS));
      double ta = ldexp((double)t, -64) - pad, tb = ta + bw + 2 * pad;
      dctx c;
      c.n = 2;
      c.id[0] = NB;
      c.slo[0] = c.shi[0] = 1.0;
      c.id[1] = i;
      c.slo[1] = exp(-tb * LNB[i]) * (1 - 1e-15);
      c.shi[1] = exp(-ta * LNB[i]) * (1 + 1e-15);
      c.stop = 8 * (c.shi[1] - c.slo[1]);
      if (ddfs_root(&c)) BM[i][k >> 6] |= 1ULL << (k & 63);
    }
  }
}

/* ---------- stage 4: 192-bit fixed point (value = X / 2^192) ---------- */
typedef struct {
  u64 l[4];
} fx;

static inline fx fx_add(fx a, fx b) {
  fx r;
  u128 c = 0;
  for (int i = 0; i < 4; i++) {
    c += (u128)a.l[i] + b.l[i];
    r.l[i] = (u64)c;
    c >>= 64;
  }
  return r;
}
static inline fx fx_sub(fx a, fx b) { /* requires a >= b */
  fx r;
  u64 br = 0;
  for (int i = 0; i < 4; i++) {
    u64 x = a.l[i] - b.l[i], b1 = a.l[i] < b.l[i];
    u64 y = x - br, b2 = x < br;
    r.l[i] = y;
    br = b1 | b2;
  }
  return r;
}
static inline int fx_cmp(fx a, fx b) {
  for (int i = 3; i >= 0; i--)
    if (a.l[i] != b.l[i]) return a.l[i] < b.l[i] ? -1 : 1;
  return 0;
}
static inline fx fx_divs(fx a, u64 d) {
  fx r;
  u64 rem = 0;
  for (int i = 3; i >= 0; i--) {
    u128 cur = ((u128)rem << 64) | a.l[i];
    r.l[i] = (u64)(cur / d);
    rem = (u64)(cur % d);
  }
  return r;
}
static fx fx_mul(fx a, fx b) { /* floor(a*b), product must stay below 2^64 */
  u64 p[9] = {0};
  for (int i = 0; i < 4; i++) {
    u128 c = 0;
    for (int j = 0; j < 4; j++) {
      c += (u128)a.l[i] * b.l[j] + p[i + j];
      p[i + j] = (u64)c;
      c >>= 64;
    }
    p[i + 4] = (u64)c;
  }
  fx r = {{p[3], p[4], p[5], p[6]}};
  return r;
}
static inline int fx_zero(fx a) { return !(a.l[0] | a.l[1] | a.l[2] | a.l[3]); }

/* s_i = b^m / B^L for the unique feasible m, error well below 2^-180 */
static fx fx_scale(u64 L, int i) {
  u64 th[4];
  theta256(L, i, th);
  /* om = 1 - theta, 192 fraction bits */
  u64 ng[4];
  u128 c = 1;
  for (int j = 0; j < 4; j++) {
    c += (u64)~th[j];
    ng[j] = (u64)c;
    c >>= 64;
  }
  fx om = {{ng[1], ng[2], ng[3], 0}};
  fx ln = {{LN_T[BASE[i]][0], LN_T[BASE[i]][1], LN_T[BASE[i]][2], LN_T[BASE[i]][3]}};
  fx y = fx_mul(om, ln);
  fx one = {{0, 0, 0, 1}};
  fx e = one, term = one;
  for (u64 n = 1; n < 200; n++) {
    term = fx_divs(fx_mul(term, y), n);
    if (fx_zero(term)) break;
    e = fx_add(e, term);
  }
  /* e = b^(1-theta).  theta in lower arc -> s = b^(-theta); upper arc -> s = b^(1-theta) */
  if ((i64)th[3] >= 0) e = fx_divs(e, (u64)BASE[i]);
  return e;
}

#define KM 128
static const fx M_EPS = {{1ULL << 22, 0, 0, 0}}; /* 2^-170 */
#define M_STOP (1ULL << 42)                     /* 2^-150 */

typedef struct {
  fx sb[NA][KM], wb[NA][KM];
  int filled[NA];
  fx nlo[NA];
  int k[NA];
} mctx;

static inline void m_ensure(mctx *m, int i, int k) {
  while (m->filled[i] < k) {
    int f = m->filled[i];
    m->sb[i][f + 1] = fx_divs(m->sb[i][f], (u64)BASE[i]);
    m->wb[i][f + 1] = fx_divs(m->sb[i][f + 1], (u64)(BASE[i] - 1));
    m->filled[i] = f + 1;
  }
}

static int mdfs(mctx *m, fx lo, fx hi) {
  int w = 0;
  for (int i = 1; i < NA; i++)
    if (fx_cmp(m->wb[i][m->k[i]], m->wb[w][m->k[w]]) > 0) w = i;
  fx ww = m->wb[w][m->k[w]];
  if (!(ww.l[3] | ww.l[2] | ww.l[1]) && ww.l[0] < M_STOP) return 1;
  int k = m->k[w];
  if (k + 2 >= KM) return 1;
  m_ensure(m, w, k + 1);
  fx base = m->nlo[w];
  for (int d = 0; d < 2; d++) {
    fx cl = d ? fx_add(base, m->sb[w][k + 1]) : base;
    fx clo = fx_sub(cl, M_EPS);
    fx chi = fx_add(fx_add(cl, m->wb[w][k + 1]), M_EPS);
    fx nlo = fx_cmp(lo, clo) > 0 ? lo : clo;
    fx nhi = fx_cmp(hi, chi) < 0 ? hi : chi;
    if (fx_cmp(nlo, nhi) <= 0) {
      m->nlo[w] = cl;
      m->k[w] = k + 1;
      if (mdfs(m, nlo, nhi)) return 1;
    }
  }
  m->nlo[w] = base;
  m->k[w] = k;
  return 0;
}

static int mid_survives(u64 L, mctx *m) {
  fx lo = {{0, 0, 0, 0}}, hi = {{0, 0, 0, ~0ULL >> 1}};
  for (int i = 0; i < NA; i++) {
    fx s;
    if (i == NB) {
      fx one = {{0, 0, 0, 1}};
      s = one;
    } else
      s = fx_scale(L, i);
    m->sb[i][0] = s;
    m->wb[i][0] = fx_divs(s, (u64)(BASE[i] - 1));
    m->filled[i] = 0;
    m->nlo[i] = s;
    m->k[i] = 0;
    fx l = fx_sub(s, M_EPS), h = fx_add(fx_add(s, m->wb[i][0]), M_EPS);
    if (fx_cmp(l, lo) > 0) lo = l;
    if (fx_cmp(h, hi) < 0) hi = h;
  }
  if (fx_cmp(lo, hi) > 0) return 0;
  return mdfs(m, lo, hi);
}

/* ---------- per-L check after the arc test ---------- */
typedef struct {
  u64 n_arc, n_bm, n_dd, n_mid;
  u64 *cand;
  size_t ncand, capcand;
  mctx m;
} tstate;

/* tq[] are the block-incremented phases (drift < 2^-52, far inside the 2^-40 bitmap pad) */
static void check(u64 L, const u64 *tq, tstate *ts) {
  u64 t[NB];
  ts->n_arc++;
  for (int i = NB - 1; i >= 0; i--) { /* highest base is the most selective */
    u64 k = tq[i] >> (64 - BM_BITS);
    if (!((BM[i][k >> 6] >> (k & 63)) & 1)) return;
  }
  ts->n_bm++;
  for (int i = 0; i < NB; i++) {
    u64 th[4];
    theta256(L, i, th);
    t[i] = th[3];
  }
  dctx c;
  c.n = NA;
  c.stop = STOP_PT;
  for (int i = 0; i < NB; i++) {
    c.id[i] = i;
    c.slo[i] = c.shi[i] = exp(-ldexp((double)(i64)t[i], -64) * LNB[i]);
  }
  c.id[NB] = NB;
  c.slo[NB] = c.shi[NB] = 1.0;
  if (!ddfs_root(&c)) return;
  ts->n_dd++;
  if (!mid_survives(L, &ts->m)) return;
  ts->n_mid++;
  if (ts->ncand == ts->capcand) {
    ts->capcand = ts->capcand ? 2 * ts->capcand : 16;
    ts->cand = realloc(ts->cand, ts->capcand * 8);
  }
  ts->cand[ts->ncand++] = L;
}

static void scan_range(u64 Lb, u64 Le, tstate *ts) {
  for (u64 base = Lb; base < Le; base += BLK) {
    u64 t[NB];
    for (int i = 0; i < NB; i++) {
      u64 th[4];
      theta256(base, i, th);
      t[i] = th[3];
    }
    u64 n = Le - base < BLK ? Le - base : BLK;
    for (u64 j0 = 0; j0 < n; j0 += 64) {
      u64 m = n - j0 < 64 ? n - j0 : 64, mask = 0, t0[NB];
      for (int i = 0; i < NB; i++) t0[i] = t[i];
      for (u64 j = 0; j < m; j++) {
        u64 ok = 1;
        for (int i = 0; i < NB; i++) {
          ok &= (u64)((t[i] - ARC_V[i]) <= ARC_R[i]);
          t[i] += A64[i];
        }
        mask |= ok << j;
      }
      while (mask) {
        u64 j = (u64)__builtin_ctzll(mask), tq[NB];
        mask &= mask - 1;
        for (int i = 0; i < NB; i++) tq[i] = t0[i] + j * A64[i];
        check(base + j0 + j, tq, ts);
      }
    }
  }
}

/* ---------- threading / driver ---------- */
static _Atomic u64 g_next;
static u64 g_end, g_chunk;

static void *worker(void *arg) {
  tstate *ts = arg;
  for (;;) {
    u64 b = atomic_fetch_add(&g_next, g_chunk);
    if (b >= g_end) break;
    u64 e = b + g_chunk < g_end ? b + g_chunk : g_end;
    scan_range(b, e, ts);
  }
  return 0;
}

static volatile sig_atomic_t g_stop;
static void on_sig(int s) {
  (void)s;
  g_stop = 1;
}

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int cmp_u64(const void *a, const void *b) {
  u64 x = *(const u64 *)a, y = *(const u64 *)b;
  return x < y ? -1 : x > y;
}

static void init_tables(void) {
  for (int i = 0; i < NB; i++) BASE[i] = 3 + i;
  BASE[NB] = TOPBASE;
  for (int i = 0; i < NA; i++) {
    LNB[i] = log((double)BASE[i]);
    u64 pw = 1;
    KDMAX[i] = 0;
    for (int k = 0; k < KD; k++) {
      if (pw > (1ULL << 50) / (u64)BASE[i]) break;
      INV[i][k] = 1.0 / (double)pw;
      INVW[i][k] = 1.0 / (double)(pw * (u64)(BASE[i] - 1));
      KDMAX[i] = k + 1;
      pw *= (u64)BASE[i];
    }
  }
  for (int i = 0; i < NB; i++) {
    double b = BASE[i];
    double W = log(b / (b - 1)) / log(b);
    double U = log((double)TOPBASE / (TOPBASE - 1)) / log(b);
    u64 Wq = (u64)ldexp(W, 64) + ARC_PAD, Uq = (u64)ldexp(U, 64) + ARC_PAD;
    ARC_V[i] = (u64)0 - Uq;
    ARC_R[i] = Wq + Uq;
    A64[i] = ALPHA_T[TOPBASE][BASE[i]][3];
  }
}

int main(int argc, char **argv) {
  u64 start = 0, end = LMAX;
  int threads = 8, quiet = 0, use_state = 1, have_start = 0;
  char statefile[64], dir[1024];
  snprintf(statefile, sizeof statefile, "state_b%d.txt", TOPBASE);
  strncpy(dir, argv[0], sizeof dir - 1);
  dir[sizeof dir - 1] = 0;
  char *dn = dirname(dir);
  char vdir[1024];
  snprintf(vdir, sizeof vdir, "%s", dn);

  init_tables();
  for (int a = 1; a < argc; a++) {
    if (!strcmp(argv[a], "--start") && a + 1 < argc) start = strtoull(argv[++a], 0, 10), have_start = 1;
    else if (!strcmp(argv[a], "--end") && a + 1 < argc) end = strtoull(argv[++a], 0, 10);
    else if (!strcmp(argv[a], "--threads") && a + 1 < argc) threads = atoi(argv[++a]);
    else if (!strcmp(argv[a], "--quiet")) quiet = 1;
    else if (!strcmp(argv[a], "--no-state")) use_state = 0;
    else if (!strcmp(argv[a], "--dump-s") && a + 1 < argc) {
      u64 L = strtoull(argv[++a], 0, 10);
      for (int i = 0; i < NB; i++) {
        fx s = fx_scale(L, i);
        printf("%d %llx%016llx%016llx%016llx\n", BASE[i], (unsigned long long)s.l[3],
               (unsigned long long)s.l[2], (unsigned long long)s.l[1], (unsigned long long)s.l[0]);
      }
      return 0;
    } else {
      fprintf(stderr, "usage: %s [--start L] [--end L] [--threads T] [--quiet] [--no-state] [--dump-s L]\n", argv[0]);
      return 2;
    }
  }
  if (!have_start) {
    start = 1;
    FILE *f = use_state ? fopen(statefile, "r") : 0;
    if (f) {
      unsigned long long v;
      if (fscanf(f, "%llu", &v) == 1) start = v;
      fclose(f);
    }
  }
  if (end > LMAX) end = LMAX;
  if (threads < 1) threads = 1;
  if (threads > 256) threads = 256;

  double t0 = now();
  build_bitmaps();
  if (!quiet)
    fprintf(stderr, "top base %d, %d threads, start L=%llu, bitmaps built in %.2fs\n", TOPBASE, threads,
            (unsigned long long)start, now() - t0);
  signal(SIGINT, on_sig);
  signal(SIGTERM, on_sig);

  tstate *ts = calloc((size_t)threads, sizeof *ts);
  pthread_t *th = malloc((size_t)threads * sizeof *th);
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, 8u << 20);

  u64 cur = start, super = (u64)threads * 16 * BLK * 16, unresolved = 0;
  u64 tot_arc = 0, tot_bm = 0, tot_dd = 0, tot_mid = 0;
  double tstart = now(), tlast = tstart;
  while (cur < end && !g_stop) {
    u64 se = end - cur < super ? end : cur + super;
    atomic_store(&g_next, cur);
    g_end = se;
    g_chunk = (super / ((u64)threads * 16) / BLK) * BLK;
    if (g_chunk < BLK) g_chunk = BLK;
    /* chunk starts must stay BLK-aligned relative to cur; any alignment is fine */
    double ts0 = now();
    for (int i = 0; i < threads; i++) pthread_create(&th[i], &attr, worker, &ts[i]);
    for (int i = 0; i < threads; i++) pthread_join(th[i], 0);
    double dt = now() - ts0;

    /* resolve candidates */
    size_t nc = 0;
    for (int i = 0; i < threads; i++) nc += ts[i].ncand;
    if (nc) {
      u64 *all = malloc(nc * 8);
      size_t q = 0;
      for (int i = 0; i < threads; i++) {
        memcpy(all + q, ts[i].cand, ts[i].ncand * 8);
        q += ts[i].ncand;
        ts[i].ncand = 0;
      }
      qsort(all, nc, 8, cmp_u64);
      for (size_t j = 0; j < nc; j++) {
        char cmd[1400], line[4096] = "";
        snprintf(cmd, sizeof cmd, "python3 '%s/verify.py' %d %llu", vdir, TOPBASE, (unsigned long long)all[j]);
        FILE *p = popen(cmd, "r");
        if (p) {
          if (!fgets(line, sizeof line, p)) line[0] = 0;
          pclose(p);
        }
        line[strcspn(line, "\n")] = 0;
        int dead = !strcmp(line, "DEAD");
        char fn[64];
        snprintf(fn, sizeof fn, "candidates_b%d.log", TOPBASE);
        FILE *lg = fopen(fn, "a");
        if (lg) {
          fprintf(lg, "L=%llu %s\n", (unsigned long long)all[j], line[0] ? line : "VERIFIER-FAILED");
          fclose(lg);
        }
        if (!dead) {
          unresolved++;
          printf("*** L=%llu: %s\n", (unsigned long long)all[j], line[0] ? line : "VERIFIER-FAILED");
          fflush(stdout);
        }
      }
      free(all);
    }
    for (int i = 0; i < threads; i++) {
      tot_arc += ts[i].n_arc, tot_bm += ts[i].n_bm, tot_dd += ts[i].n_dd, tot_mid += ts[i].n_mid;
      ts[i].n_arc = ts[i].n_bm = ts[i].n_dd = ts[i].n_mid = 0;
    }
    cur = se;
    if (use_state) {
      char tmp[80];
      snprintf(tmp, sizeof tmp, "%s.tmp", statefile);
      FILE *f = fopen(tmp, "w");
      if (f) {
        fprintf(f, "%llu\n", (unsigned long long)cur);
        fclose(f);
        rename(tmp, statefile);
      }
    }
    double tn = now();
    if (!quiet && (tn - tlast > 2.0 || cur >= end)) {
      double done = (double)(cur - start);
      fprintf(stderr,
              "L < %llu done  (10^%.4g decimal digits)  %.3g L/s  pass: arc %.3g bm %.3g dbl %.3g mid %.3g\n",
              (unsigned long long)cur, log10((double)cur * log10((double)TOPBASE)), done / (tn - tstart),
              tot_arc / done, tot_bm / done, tot_dd / done, tot_mid / done);
      tlast = tn;
    }
    /* aim for ~4 s per superchunk */
    if (dt < 2.0 && super < (1ULL << 44)) super *= 2;
    else if (dt > 8.0 && super > (u64)threads * 16 * BLK) super /= 2;
  }
  printf("searched L in [%llu, %llu) for top base %d: %llu stage-4 survivors, %llu not proved dead\n",
         (unsigned long long)start, (unsigned long long)cur, TOPBASE, (unsigned long long)tot_mid,
         (unsigned long long)unresolved);
  return 0;
}
