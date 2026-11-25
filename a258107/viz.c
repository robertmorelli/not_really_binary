/* viz.c -- draw the filter results for lengths 1..W*H as a W x H palette PNG.
 * One pixel per length L (row-major, L = 1 at top left), top base 6.
 *
 *   dim magenta / teal / amber : base 3 / 4 / 5 band overlaps the base-6 band (mixes where two do)
 *   grey                       : each base overlaps base 6, but there is no common overlap
 *   white                      : all four bands overlap; dies when 1 more digit is fixed
 *   yellow / orange / red      : survives 1 / 2 / 3 or more further digits
 *
 * build: cc -O3 viz.c -o viz -lz     run: ./viz 16384 16384 out.png
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>
typedef uint64_t u64;
typedef unsigned __int128 u128;
#include "consts.h"

static const int BS[3] = {3, 4, 5};
static u64 A128hi[3], A128lo[3], ARC_V[3], ARC_R[3];

static u64 phase(u64 L, int i) { /* top 64 bits of frac(L * log_b 6) */
  u128 lo = (u128)A128lo[i] * L;
  return (u64)(lo >> 64) + A128hi[i] * L;
}

typedef struct { double lo, hi; } iv;
static int bands(int b, double s, int d, iv *out) {
  int n = 1 << d;
  double w = pow(b, -d) / (b - 1);
  for (int i = 0; i < n; i++) {
    double c = 1;
    for (int j = 1; j <= d; j++) if ((i >> (d - j)) & 1) c += pow(b, -j);
    out[i].lo = s * c; out[i].hi = s * (c + w);
  }
  return n;
}
static int inter(const iv *A, int na, const iv *B, int nb, iv *out) {
  int i = 0, j = 0, n = 0;
  while (i < na && j < nb) {
    double lo = A[i].lo > B[j].lo ? A[i].lo : B[j].lo, hi = A[i].hi < B[j].hi ? A[i].hi : B[j].hi;
    if (lo <= hi) out[n].lo = lo, out[n].hi = hi, n++;
    if (A[i].hi < B[j].hi) i++; else j++;
  }
  return n;
}
/* number of digit levels (0..4) at which a common overlap still exists; 0 = none even at the top */
static int alive_levels(const u64 *t) {
  iv a[64], b[64], c[64];
  for (int d = 0; d <= 3; d++) {
    int n = bands(6, 1.0, d, a);
    for (int i = 0; i < 3 && n; i++) {
      double s = exp(-ldexp((double)(int64_t)t[i], -64) * log(BS[i]));
      int m = bands(BS[i], s, d, b);
      n = inter(a, n, b, m, c);
      memcpy(a, c, sizeof(iv) * (size_t)n);
    }
    if (!n) return d;
  }
  return 4;
}

static FILE *out;
static void chunk(const char *type, const unsigned char *data, size_t len) {
  unsigned char h[8] = {len >> 24, len >> 16, len >> 8, len, type[0], type[1], type[2], type[3]};
  fwrite(h, 1, 8, out);
  if (len) fwrite(data, 1, len, out);
  uLong crc = crc32(0, h + 4, 4);
  if (len) crc = crc32(crc, data, (uInt)len);
  unsigned char c[4] = {crc >> 24, crc >> 16, crc >> 8, crc};
  fwrite(c, 1, 4, out);
}

static u64 W;
static u64 counts[12];
/* classes of the lengths in row y, columns x0 .. x0+w-1 */
static void row_classes(u64 y, u64 x0, u64 w, unsigned char *dst) {
  u64 L0 = y * W + x0 + 1, t[3];
  for (u64 x = 0; x < w; x++) {
    if ((x & 1023) == 0) for (int i = 0; i < 3; i++) t[i] = phase(L0 + x, i);
    int m = 0;
    for (int i = 0; i < 3; i++) m |= ((t[i] - ARC_V[i]) <= ARC_R[i]) << i;
    if (m == 7) m = 7 + alive_levels(t);
    dst[x] = (unsigned char)m; counts[m]++;
    for (int i = 0; i < 3; i++) t[i] += A128hi[i];
  }
}

/* usage: viz W H out.png [x0 y0 w h scale]
 * With a region, only that part is drawn; scale > 1 averages scale x scale blocks (RGB output). */
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s W H out.png [x0 y0 w h scale]\n", argv[0]); return 2; }
  W = strtoull(argv[1], 0, 10);
  u64 H = strtoull(argv[2], 0, 10), x0 = 0, y0 = 0, w = W, h = H, sc = 1;
  if (argc >= 9) {
    x0 = strtoull(argv[4], 0, 10); y0 = strtoull(argv[5], 0, 10);
    w = strtoull(argv[6], 0, 10); h = strtoull(argv[7], 0, 10); sc = strtoull(argv[8], 0, 10);
    if (x0 + w > W) w = W - x0;
    if (y0 + h > H) h = H - y0;
  }
  out = fopen(argv[3], "wb");
  if (!out) { perror("open"); return 1; }
  for (int i = 0; i < 3; i++) {
    A128hi[i] = ALPHA_T[6][BS[i]][3]; A128lo[i] = ALPHA_T[6][BS[i]][2];
    double b = BS[i], Wd = log(b / (b - 1)) / log(b), U = log(6.0 / 5.0) / log(b);
    u64 Wq = (u64)ldexp(Wd, 64), Uq = (u64)ldexp(U, 64);
    ARC_V[i] = (u64)0 - Uq; ARC_R[i] = Wq + Uq;
  }
  static const unsigned char pal[12][3] = {
    {11, 13, 18},    /* 0 nothing */
    {96, 38, 86},    /* 1 base 3 */
    {26, 92, 74},    /* 2 base 4 */
    {150, 70, 110},  /* 3 base 3+4 */
    {116, 76, 22},   /* 4 base 5 */
    {170, 92, 70},   /* 5 base 3+5 */
    {110, 130, 60},  /* 6 base 4+5 */
    {138, 143, 156}, /* 7 all pairwise, no common overlap */
    {255, 255, 255}, /* 8 common overlap, dies at +1 */
    {255, 225, 74},  /* 9 dies at +2 */
    {255, 138, 31},  /* 10 dies at +3 */
    {255, 45, 45}};  /* 11 survives 3 more */
  u64 ow = (w + sc - 1) / sc, oh = (h + sc - 1) / sc;
  int rgb = sc > 1;
  fwrite("\x89PNG\r\n\x1a\n", 1, 8, out);
  unsigned char ih[13] = {ow >> 24, ow >> 16, ow >> 8, ow, oh >> 24, oh >> 16, oh >> 8, oh, 8, rgb ? 2 : 3, 0, 0, 0};
  chunk("IHDR", ih, 13);
  if (!rgb) chunk("PLTE", &pal[0][0], 36);

  z_stream z; memset(&z, 0, sizeof z);
  deflateInit(&z, 6);
  size_t ob = 1 << 20, rl = (size_t)(rgb ? 3 * ow : ow) + 1;
  unsigned char *obuf = malloc(ob), *row = malloc(rl), *cls = malloc(w);
  uint32_t *acc = calloc(3 * ow, sizeof *acc), *cnt = calloc(ow, sizeof *cnt);
  for (u64 oy = 0; oy < oh; oy++) {
    row[0] = 0;
    if (!rgb) row_classes(y0 + oy, x0, w, row + 1);
    else {
      memset(acc, 0, 3 * ow * sizeof *acc); memset(cnt, 0, ow * sizeof *cnt);
      for (u64 sy = 0; sy < sc && oy * sc + sy < h; sy++) {
        row_classes(y0 + oy * sc + sy, x0, w, cls);
        for (u64 x = 0; x < w; x++) {
          u64 ox = x / sc; const unsigned char *p = pal[cls[x]];
          acc[3 * ox] += p[0]; acc[3 * ox + 1] += p[1]; acc[3 * ox + 2] += p[2]; cnt[ox]++;
        }
      }
      for (u64 ox = 0; ox < ow; ox++)
        for (int c = 0; c < 3; c++) row[1 + 3 * ox + c] = (unsigned char)(acc[3 * ox + c] / cnt[ox]);
    }
    z.next_in = row; z.avail_in = (uInt)rl;
    int fl = oy == oh - 1 ? Z_FINISH : Z_NO_FLUSH;
    do {
      z.next_out = obuf; z.avail_out = (uInt)ob;
      deflate(&z, fl);
      if (ob - z.avail_out) chunk("IDAT", obuf, ob - z.avail_out);
    } while (z.avail_out == 0);
  }
  deflateEnd(&z);
  chunk("IEND", 0, 0);
  fclose(out);
  if (argc < 9) for (int i = 0; i < 12; i++) printf("class %2d: %llu\n", i, (unsigned long long)counts[i]);
  return 0;
}
