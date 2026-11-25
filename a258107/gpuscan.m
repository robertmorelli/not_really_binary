/* gpuscan.m -- GPU front end for the scanner, with the CPU finishing the survivors.
 *
 * GPU (Metal compute):  stage 1 arc test and stage 2 bitmap lookup for every length.
 *   Hot loop uses 32-bit phases with widened arcs and jumps straight over the lengths
 *   whose base-5 phase is outside its arc; anything that passes is re-tested with the
 *   exact 64-bit phase, so the survivor set is identical to scan.c's.
 * CPU ("copilot"):  takes each batch's survivor list and runs scan.c's stages 3-5 on it
 *   in parallel while the GPU is already working on the next batch.
 *
 * build: /usr/bin/clang -O3 -fobjc-arc -DTOPBASE=6 gpuscan.m -framework Metal -framework Foundation -lpthread -o gpuscan
 * run:   ./gpuscan [--batches N] [--start L] [--no-state] [--check]
 */
#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
/* scan.c defines short macro names (NA, NB, ...) that clash with system headers, so it comes second */
#ifndef BM_BITS
#define BM_BITS 22 /* larger tables than scan.c's default: fewer survivors for the CPU */
#endif
#define main scan_main
#include "scan.c"
#undef main

static NSString *SRC = @
"#include <metal_stdlib>\n"
"using namespace metal;\n"
"static inline ulong mulhi64(ulong a, ulong b) {\n"
"  ulong al = a & 0xFFFFFFFFul, ah = a >> 32, bl = b & 0xFFFFFFFFul, bh = b >> 32;\n"
"  ulong ll = al * bl, lh = al * bh, hl = ah * bl, hh = ah * bh;\n"
"  ulong mid = (ll >> 32) + (lh & 0xFFFFFFFFul) + (hl & 0xFFFFFFFFul);\n"
"  return hh + (lh >> 32) + (hl >> 32) + (mid >> 32);\n"
"}\n"
"static inline bool bit(const device uint *bm, uint base, ulong t, uint bits) {\n"
"  uint k = (uint)(t >> (64u - bits));\n"
"  return (bm[base * (1u << (bits - 5u)) + (k >> 5)] >> (k & 31u)) & 1u;\n"
"}\n"
"kernel void scan(device uint *list [[buffer(0)]], constant ulong *P [[buffer(1)]],\n"
"                 const device uint *bm [[buffer(2)]], device atomic_uint *ctr [[buffer(3)]],\n"
"                 uint gid [[thread_position_in_grid]]) {\n"
"  uint ch = (uint)P[13], bits = (uint)P[14], cap = (uint)P[15];\n"
"  ulong L0 = P[0] + (ulong)gid * P[13];\n"
"  ulong T0 = L0 * P[1] + mulhi64(L0, P[4]);\n"
"  ulong T1 = L0 * P[2] + mulhi64(L0, P[5]);\n"
"  ulong T2 = L0 * P[3] + mulhi64(L0, P[6]);\n"
"  uint a0 = (uint)(P[1] >> 32), a1 = (uint)(P[2] >> 32), a2 = (uint)(P[3] >> 32);\n"
"  uint t0 = (uint)(T0 >> 32), t1 = (uint)(T1 >> 32), t2 = (uint)(T2 >> 32);\n"
"  uint v0 = (uint)P[16], v1 = (uint)P[17], v2 = (uint)P[18];\n"
"  uint r0 = (uint)P[19], r1 = (uint)P[20], r2 = (uint)P[21];\n"
"  ulong inv = P[22];\n"
"  uint na = 0, nb = 0, j = 0;\n"
"  while (j < ch) {\n"
"    if (t2 - v2 > r2) {\n"                                  /* base 5 outside its arc: jump to just before it re-enters */
"      uint n = (uint)(((ulong)(v2 - t2) * inv) >> 48);\n"
"      n = max(n, 1u);\n"
"      j += n; t0 += n * a0; t1 += n * a1; t2 += n * a2;\n"
"      continue;\n"
"    }\n"
"    if ((t0 - v0 <= r0) & (t1 - v1 <= r1)) {\n"
"      ulong e0 = T0 + (ulong)j * P[1], e1 = T1 + (ulong)j * P[2], e2 = T2 + (ulong)j * P[3];\n"
"      if ((e0 - P[7] <= P[10]) & (e1 - P[8] <= P[11]) & (e2 - P[9] <= P[12])) {\n"
"        na++;\n"
"        if (bit(bm, 2, e2, bits) && bit(bm, 1, e1, bits) && bit(bm, 0, e0, bits)) {\n"
"          nb++;\n"
"          uint slot = atomic_fetch_add_explicit(&ctr[0], 1u, memory_order_relaxed);\n"
"          if (slot < cap) list[slot] = gid * ch + j;\n"
"        }\n"
"      }\n"
"    }\n"
"    j++; t0 += a0; t1 += a1; t2 += a2;\n"
"  }\n"
"  atomic_fetch_add_explicit(&ctr[1], na, memory_order_relaxed);\n"
"  atomic_fetch_add_explicit(&ctr[2], nb, memory_order_relaxed);\n"
"}\n";

#define CH 4096u
#define NSLICE 16
static tstate g_ts[NSLICE];
static char g_dir[1024];

/* stages 3-5 for one batch's survivors; returns lengths that reached the exact verifier */
static void copilot(u64 base, const uint32_t *list, u64 n) {
  dispatch_apply(NSLICE, dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^(size_t s) {
    tstate *ts = &g_ts[s];
    u64 lo = n * s / NSLICE, hi = n * (s + 1) / NSLICE;
    for (u64 i = lo; i < hi; i++) {
      u64 L = base + list[i], tq[NB];
      for (int b = 0; b < NB; b++) { u64 th[4]; theta256(L, b, th); tq[b] = th[3]; }
      check(L, tq, ts);
    }
  });
}

static int resolve(u64 L) { /* 1 = proved dead by verify.py */
  char cmd[1400], line[4096] = "";
  snprintf(cmd, sizeof cmd, "python3 '%s/verify.py' %d %llu", g_dir, TOPBASE, (unsigned long long)L);
  FILE *p = popen(cmd, "r");
  if (p) { if (!fgets(line, sizeof line, p)) line[0] = 0; pclose(p); }
  line[strcspn(line, "\n")] = 0;
  FILE *lg = fopen("candidates_gpu_b6.log", "a");
  if (lg) { fprintf(lg, "L=%llu %s\n", (unsigned long long)L, line[0] ? line : "VERIFIER-FAILED"); fclose(lg); }
  if (strcmp(line, "DEAD")) { printf("*** L=%llu: %s\n", (unsigned long long)L, line[0] ? line : "VERIFIER-FAILED"); fflush(stdout); return 0; }
  return 1;
}

int main(int argc, char **argv) {
  @autoreleasepool {
    if (NB != 3) { fprintf(stderr, "build with -DTOPBASE=6\n"); return 2; }
    long batches = -1; int use_state = 1, do_check = 0, have_start = 0, lg = 19;
    u64 start = 1;
    char tmp[1024]; strncpy(tmp, argv[0], sizeof tmp - 1); tmp[sizeof tmp - 1] = 0;
    snprintf(g_dir, sizeof g_dir, "%s", dirname(tmp));
    for (int a = 1; a < argc; a++) {
      if (!strcmp(argv[a], "--batches") && a + 1 < argc) batches = atol(argv[++a]);
      else if (!strcmp(argv[a], "--start") && a + 1 < argc) start = strtoull(argv[++a], 0, 10), have_start = 1;
      else if (!strcmp(argv[a], "--threads-log2") && a + 1 < argc) lg = atoi(argv[++a]);
      else if (!strcmp(argv[a], "--no-state")) use_state = 0;
      else if (!strcmp(argv[a], "--check")) do_check = 1;
      else { fprintf(stderr, "usage: %s [--batches N] [--start L] [--threads-log2 K] [--no-state] [--check]\n", argv[0]); return 2; }
    }
    const char *statefile = "state_gpu_b6.txt";
    if (!have_start && use_state) { FILE *f = fopen(statefile, "r"); if (f) { unsigned long long v; if (fscanf(f, "%llu", &v) == 1) start = v; fclose(f); } }
    u64 threads = 1ULL << lg, per = threads * CH;
    uint32_t cap = 1u << 23;

    double tb = now();
    init_tables();
    build_bitmaps();
    fprintf(stderr, "tables built in %.2f s (bitmap bits %d)\n", now() - tb, BM_BITS);

    id<MTLDevice> dev = MTLCreateSystemDefaultDevice();
    if (!dev) { fprintf(stderr, "no Metal device\n"); return 1; }
    NSError *err = nil;
    id<MTLLibrary> lib = [dev newLibraryWithSource:SRC options:nil error:&err];
    if (!lib) { fprintf(stderr, "shader compile failed: %s\n", err.localizedDescription.UTF8String); return 1; }
    id<MTLComputePipelineState> ps = [dev newComputePipelineStateWithFunction:[lib newFunctionWithName:@"scan"] error:&err];
    if (!ps) { fprintf(stderr, "pipeline failed: %s\n", err.localizedDescription.UTF8String); return 1; }
    id<MTLCommandQueue> q = [dev newCommandQueue];

    size_t bmBytes = ((size_t)1 << BM_BITS) / 8;
    id<MTLBuffer> bmB = [dev newBufferWithLength:3 * bmBytes options:MTLResourceStorageModeShared];
    for (int i = 0; i < 3; i++) memcpy((char *)bmB.contents + i * bmBytes, BM[i], bmBytes);
    id<MTLBuffer> listB[2], ctrB[2], parB[2];
    for (int k = 0; k < 2; k++) {
      listB[k] = [dev newBufferWithLength:(size_t)cap * 4 options:MTLResourceStorageModeShared];
      ctrB[k] = [dev newBufferWithLength:16 options:MTLResourceStorageModeShared];
      parB[k] = [dev newBufferWithLength:32 * 8 options:MTLResourceStorageModeShared];
      u64 *P = parB[k].contents;
      for (int i = 0; i < 3; i++) {
        P[1 + i] = ALPHA_T[TOPBASE][BASE[i]][3];
        P[4 + i] = ALPHA_T[TOPBASE][BASE[i]][2];
        P[7 + i] = ARC_V[i];
        P[10 + i] = ARC_R[i];
        /* 32-bit arcs widened by the worst drift of the truncated 32-bit phases over one chunk */
        P[16 + i] = (uint32_t)((uint32_t)(ARC_V[i] >> 32) - (CH + 2));
        P[19 + i] = (uint32_t)(ARC_R[i] >> 32) + (CH + 2) + 3;
      }
      P[13] = CH; P[14] = BM_BITS; P[15] = cap;
      P[22] = (1ULL << 48) / (ALPHA_T[TOPBASE][BASE[2]][3] >> 32); /* floor(2^48 / a32) for base 5 */
    }
    fprintf(stderr, "device: %s; batch = %llu lengths; start L=%llu\n", dev.name.UTF8String, (unsigned long long)per, (unsigned long long)start);
    signal(SIGINT, on_sig); signal(SIGTERM, on_sig);

    NSArray<id<MTLBuffer>> *listA = @[listB[0], listB[1]], *ctrA = @[ctrB[0], ctrB[1]], *parA = @[parB[0], parB[1]];
    id<MTLCommandBuffer> (^submit)(u64, int) = ^(u64 base, int k) {
      ((u64 *)parA[k].contents)[0] = base;
      memset(ctrA[k].contents, 0, 16);
      id<MTLCommandBuffer> cb = [q commandBuffer];
      id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
      [enc setComputePipelineState:ps];
      [enc setBuffer:listA[k] offset:0 atIndex:0];
      [enc setBuffer:parA[k] offset:0 atIndex:1];
      [enc setBuffer:bmB offset:0 atIndex:2];
      [enc setBuffer:ctrA[k] offset:0 atIndex:3];
      [enc dispatchThreads:MTLSizeMake(threads, 1, 1) threadsPerThreadgroup:MTLSizeMake(ps.maxTotalThreadsPerThreadgroup, 1, 1)];
      [enc endEncoding];
      [cb commit];
      return cb;
    };

    u64 totB = 0, unresolved = 0, done = 0, overflow = 0;
    double t0 = now(), tlast = t0, cpuT = 0, gpuT = 0;
    id<MTLCommandBuffer> prev = nil; u64 prevBase = 0; int prevK = 0;
    for (long b = 0;; b++) {
      int more = (batches < 0 || b < batches) && !g_stop && start + (u64)b * per + per < LMAX;
      id<MTLCommandBuffer> cur = nil; u64 curBase = start + (u64)b * per;
      if (more) cur = submit(curBase, (int)(b & 1));
      if (prev) {                         /* finish the previous batch on the CPU while the GPU runs the next */
        [prev waitUntilCompleted];
        if (prev.error) { fprintf(stderr, "GPU error: %s\n", prev.error.localizedDescription.UTF8String); return 1; }
        gpuT += prev.GPUEndTime - prev.GPUStartTime;
        const uint32_t *c = ctrB[prevK].contents;
        u64 n = c[0];
        double c0 = now();
        if (n > cap) { overflow++; scan_range(prevBase, prevBase + per, &g_ts[0]); }  /* list overflowed: redo this batch on the CPU */
        else copilot(prevBase, listB[prevK].contents, n);
        for (int s = 0; s < NSLICE; s++) {
          for (size_t i = 0; i < g_ts[s].ncand; i++) if (!resolve(g_ts[s].cand[i])) unresolved++;
          g_ts[s].ncand = 0;
        }
        cpuT += now() - c0;
        totB += c[2]; done += per;
        if (do_check && prevBase == start) {
          static tstate ref;
          scan_range(prevBase, prevBase + per, &ref);
          u64 cb2 = 0; for (int s = 0; s < NSLICE; s++) cb2 += g_ts[s].n_bm;
          printf("check, first batch: GPU arcs %u bitmaps %u listed %llu | CPU arcs %llu bitmaps %llu | copilot saw %llu -> %s\n", c[1], c[2],
                 (unsigned long long)n, (unsigned long long)ref.n_arc, (unsigned long long)ref.n_bm, (unsigned long long)cb2,
                 (c[1] == ref.n_arc && c[2] == ref.n_bm && n == ref.n_bm && cb2 == ref.n_bm) ? "MATCH" : "MISMATCH");
        }
        if (use_state) { FILE *f = fopen("state_gpu_b6.tmp", "w"); if (f) { fprintf(f, "%llu\n", (unsigned long long)(prevBase + per)); fclose(f); rename("state_gpu_b6.tmp", statefile); } }
        double tn = now();
        if (tn - tlast > 2.0 || !more) {
          u64 dd = 0, mid = 0; for (int s = 0; s < NSLICE; s++) dd += g_ts[s].n_dd, mid += g_ts[s].n_mid;
          fprintf(stderr, "L < %llu done (10^%.4g digits)  %.3g L/s  GPU busy %.0f%%  CPU finishing %.0f%%  bitmaps %.4f%%  dbl %llu  mid %llu\n",
                  (unsigned long long)(prevBase + per), log10((double)(prevBase + per) * log10(6.0)), done / (tn - t0), 100 * gpuT / (tn - t0),
                  100 * cpuT / (tn - t0), 100.0 * totB / done, (unsigned long long)dd, (unsigned long long)mid);
          tlast = tn;
        }
      }
      if (!more) break;
      prev = cur; prevBase = curBase; prevK = (int)(b & 1);
    }
    double wall = now() - t0;
    printf("searched L in [%llu, %llu): %.3g lengths/s; %llu passed bitmaps; %llu not proved dead; %llu batches redone on CPU\n",
           (unsigned long long)start, (unsigned long long)(start + done), done / wall, (unsigned long long)totB, (unsigned long long)unresolved,
           (unsigned long long)overflow);
  }
  return 0;
}
