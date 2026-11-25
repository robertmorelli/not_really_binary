/* gpuscan_cl.c -- OpenCL version of gpuscan.m, for non-Apple GPUs.
 *
 * GPU: stage 1 arc test and stage 2 bitmap lookup for every length (same kernel logic as
 *      the Metal version: 32-bit hot loop with widened arcs, jumps over lengths whose
 *      base-5 phase is outside its arc, exact 64-bit re-test of anything that passes).
 * CPU: scan.c's stages 3-5 on each batch's survivors, in parallel, while the GPU runs
 *      the next batch.
 *
 * build: cc -O3 -DTOPBASE=6 gpuscan_cl.c -o gpuscan_cl -lOpenCL -lpthread -lm
 * run:   ./gpuscan_cl [--batches N] [--start L] [--no-state] [--check] [--cpu-threads T]
 */
#define CL_TARGET_OPENCL_VERSION 120
#include <CL/cl.h>
#ifndef BM_BITS
#define BM_BITS 24
#endif
#define main scan_main
#include "scan.c"
#undef main

static const char *SRC =
"static inline int bit(__global const uint *bm, uint base, ulong t, uint bits) {\n"
"  uint k = (uint)(t >> (64u - bits));\n"
"  return (bm[base * (1u << (bits - 5u)) + (k >> 5)] >> (k & 31u)) & 1u;\n"
"}\n"
"__kernel void scan(__global uint *list, __global const ulong *P, __global const uint *bm,\n"
"                   __global volatile uint *ctr) {\n"
"  uint gid = (uint)get_global_id(0);\n"
"  uint ch = (uint)P[13], bits = (uint)P[14], cap = (uint)P[15];\n"
"  ulong L0 = P[0] + (ulong)gid * P[13];\n"
"  ulong T0 = L0 * P[1] + mul_hi(L0, P[4]);\n"
"  ulong T1 = L0 * P[2] + mul_hi(L0, P[5]);\n"
"  ulong T2 = L0 * P[3] + mul_hi(L0, P[6]);\n"
"  uint a0 = (uint)(P[1] >> 32), a1 = (uint)(P[2] >> 32), a2 = (uint)(P[3] >> 32);\n"
"  uint t0 = (uint)(T0 >> 32), t1 = (uint)(T1 >> 32), t2 = (uint)(T2 >> 32);\n"
"  uint v0 = (uint)P[16], v1 = (uint)P[17], v2 = (uint)P[18];\n"
"  uint r0 = (uint)P[19], r1 = (uint)P[20], r2 = (uint)P[21];\n"
"  ulong inv = P[22];\n"
"  uint na = 0, nb = 0, j = 0;\n"
"  while (j < ch) {\n"
"    if (t2 - v2 > r2) {\n"
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
"          uint slot = atomic_inc(&ctr[0]);\n"
"          if (slot < cap) list[slot] = gid * ch + j;\n"
"        }\n"
"      }\n"
"    }\n"
"    j++; t0 += a0; t1 += a1; t2 += a2;\n"
"  }\n"
"  atomic_add(&ctr[1], na);\n"
"  atomic_add(&ctr[2], nb);\n"
"}\n";

#define CH 4096u
#define MAXT 64
static tstate g_ts[MAXT];
static char g_dir[1024];
static int g_nt = 12;

typedef struct { u64 base; const uint32_t *list; u64 lo, hi; tstate *ts; } job;
static void *job_run(void *p) {
  job *jb = p;
  for (u64 i = jb->lo; i < jb->hi; i++) {
    u64 L = jb->base + jb->list[i], tq[NB];
    for (int b = 0; b < NB; b++) { u64 th[4]; theta256(L, b, th); tq[b] = th[3]; }
    check(L, tq, jb->ts);
  }
  return 0;
}
static void copilot(u64 base, const uint32_t *list, u64 n) {
  pthread_t th[MAXT]; job jb[MAXT];
  for (int s = 0; s < g_nt; s++) {
    jb[s] = (job){base, list, n * (u64)s / (u64)g_nt, n * (u64)(s + 1) / (u64)g_nt, &g_ts[s]};
    pthread_create(&th[s], 0, job_run, &jb[s]);
  }
  for (int s = 0; s < g_nt; s++) pthread_join(th[s], 0);
}
static int resolve(u64 L) {
  char cmd[1400], line[4096] = "";
  snprintf(cmd, sizeof cmd, "python3 '%s/verify.py' %d %llu", g_dir, TOPBASE, (unsigned long long)L);
  FILE *p = popen(cmd, "r");
  if (p) { if (!fgets(line, sizeof line, p)) line[0] = 0; pclose(p); }
  line[strcspn(line, "\n")] = 0;
  FILE *lg = fopen("candidates_cl_b6.log", "a");
  if (lg) { fprintf(lg, "L=%llu %s\n", (unsigned long long)L, line[0] ? line : "VERIFIER-FAILED"); fclose(lg); }
  if (strcmp(line, "DEAD")) { printf("*** L=%llu: %s\n", (unsigned long long)L, line[0] ? line : "VERIFIER-FAILED"); fflush(stdout); return 0; }
  return 1;
}
#define CK(x) do { cl_int e_ = (x); if (e_ != CL_SUCCESS) { fprintf(stderr, "OpenCL error %d at line %d\n", e_, __LINE__); return 1; } } while (0)

int main(int argc, char **argv) {
  if (NB != 3) { fprintf(stderr, "build with -DTOPBASE=6\n"); return 2; }
  long batches = -1; int use_state = 1, do_check = 0, have_start = 0, lg = 20;
  u64 start = 1;
  char tmp[1024]; strncpy(tmp, argv[0], sizeof tmp - 1); tmp[sizeof tmp - 1] = 0;
  snprintf(g_dir, sizeof g_dir, "%s", dirname(tmp));
  for (int a = 1; a < argc; a++) {
    if (!strcmp(argv[a], "--batches") && a + 1 < argc) batches = atol(argv[++a]);
    else if (!strcmp(argv[a], "--start") && a + 1 < argc) start = strtoull(argv[++a], 0, 10), have_start = 1;
    else if (!strcmp(argv[a], "--threads-log2") && a + 1 < argc) lg = atoi(argv[++a]);
    else if (!strcmp(argv[a], "--cpu-threads") && a + 1 < argc) g_nt = atoi(argv[++a]);
    else if (!strcmp(argv[a], "--no-state")) use_state = 0;
    else if (!strcmp(argv[a], "--check")) do_check = 1;
    else { fprintf(stderr, "usage: %s [--batches N] [--start L] [--threads-log2 K] [--cpu-threads T] [--no-state] [--check]\n", argv[0]); return 2; }
  }
  if (g_nt < 1) g_nt = 1;
  if (g_nt > MAXT) g_nt = MAXT;
  const char *statefile = "state_cl_b6.txt";
  if (!have_start && use_state) { FILE *f = fopen(statefile, "r"); if (f) { unsigned long long v; if (fscanf(f, "%llu", &v) == 1) start = v; fclose(f); } }
  size_t threads = (size_t)1 << lg; u64 per = (u64)threads * CH;
  uint32_t cap = 1u << 23;

  double tb = now();
  init_tables();
  build_bitmaps();
  fprintf(stderr, "tables built in %.2f s (bitmap bits %d)\n", now() - tb, BM_BITS);

  cl_int e; cl_platform_id plat[8]; cl_uint np = 0; cl_device_id dev = 0;
  CK(clGetPlatformIDs(8, plat, &np));
  for (cl_uint i = 0; i < np && !dev; i++) if (clGetDeviceIDs(plat[i], CL_DEVICE_TYPE_GPU, 1, &dev, 0) != CL_SUCCESS) dev = 0;
  if (!dev) { fprintf(stderr, "no OpenCL GPU found\n"); return 1; }
  char name[256] = ""; clGetDeviceInfo(dev, CL_DEVICE_NAME, sizeof name, name, 0);
  cl_context ctx = clCreateContext(0, 1, &dev, 0, 0, &e); CK(e);
  cl_command_queue q = clCreateCommandQueue(ctx, dev, 0, &e); CK(e);
  cl_program prog = clCreateProgramWithSource(ctx, 1, &SRC, 0, &e); CK(e);
  if (clBuildProgram(prog, 1, &dev, "", 0, 0) != CL_SUCCESS) {
    static char log[16384]; clGetProgramBuildInfo(prog, dev, CL_PROGRAM_BUILD_LOG, sizeof log, log, 0);
    fprintf(stderr, "kernel build failed:\n%s\n", log); return 1;
  }
  cl_kernel k = clCreateKernel(prog, "scan", &e); CK(e);

  size_t bmBytes = ((size_t)1 << BM_BITS) / 8;
  unsigned char *bmHost = malloc(3 * bmBytes);
  for (int i = 0; i < 3; i++) memcpy(bmHost + i * bmBytes, BM[i], bmBytes);
  cl_mem bmB = clCreateBuffer(ctx, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR, 3 * bmBytes, bmHost, &e); CK(e);
  cl_mem listB[2], ctrB[2], parB[2]; uint32_t *listH[2]; uint32_t ctrH[2][4]; u64 P[32] = {0};
  for (int i = 0; i < 3; i++) {
    P[1 + i] = ALPHA_T[TOPBASE][BASE[i]][3];
    P[4 + i] = ALPHA_T[TOPBASE][BASE[i]][2];
    P[7 + i] = ARC_V[i];
    P[10 + i] = ARC_R[i];
    P[16 + i] = (uint32_t)((uint32_t)(ARC_V[i] >> 32) - (CH + 2));
    P[19 + i] = (uint32_t)(ARC_R[i] >> 32) + (CH + 2) + 3;
  }
  P[13] = CH; P[14] = BM_BITS; P[15] = cap;
  P[22] = (1ULL << 48) / (ALPHA_T[TOPBASE][BASE[2]][3] >> 32);
  for (int s = 0; s < 2; s++) {
    listB[s] = clCreateBuffer(ctx, CL_MEM_READ_WRITE, (size_t)cap * 4, 0, &e); CK(e);
    ctrB[s] = clCreateBuffer(ctx, CL_MEM_READ_WRITE, 16, 0, &e); CK(e);
    parB[s] = clCreateBuffer(ctx, CL_MEM_READ_ONLY, sizeof P, 0, &e); CK(e);
    listH[s] = malloc((size_t)cap * 4);
  }
  fprintf(stderr, "device: %s; batch = %llu lengths; %d CPU threads; start L=%llu\n", name, (unsigned long long)per, g_nt, (unsigned long long)start);
  signal(SIGINT, on_sig); signal(SIGTERM, on_sig);

  u64 totB = 0, unresolved = 0, done = 0, overflow = 0;
  double t0 = now(), tlast = t0, cpuT = 0;
  cl_event prevEv = 0; u64 prevBase = 0; int prevK = 0, havePrev = 0;
  const uint32_t zero[4] = {0, 0, 0, 0};
  for (long b = 0;; b++) {
    int more = (batches < 0 || b < batches) && !g_stop && start + (u64)b * per + per < LMAX;
    cl_event curEv = 0; u64 curBase = start + (u64)b * per; int s = (int)(b & 1);
    if (more) {                     /* queue: kernel, then reads of its counters and list */
      P[0] = curBase;
      CK(clEnqueueWriteBuffer(q, parB[s], CL_TRUE, 0, sizeof P, P, 0, 0, 0));
      CK(clEnqueueWriteBuffer(q, ctrB[s], CL_TRUE, 0, 16, zero, 0, 0, 0));
      CK(clSetKernelArg(k, 0, sizeof(cl_mem), &listB[s])); CK(clSetKernelArg(k, 1, sizeof(cl_mem), &parB[s]));
      CK(clSetKernelArg(k, 2, sizeof(cl_mem), &bmB)); CK(clSetKernelArg(k, 3, sizeof(cl_mem), &ctrB[s]));
      CK(clEnqueueNDRangeKernel(q, k, 1, 0, &threads, 0, 0, 0, 0));
      CK(clEnqueueReadBuffer(q, ctrB[s], CL_FALSE, 0, 16, ctrH[s], 0, 0, 0));
      CK(clEnqueueReadBuffer(q, listB[s], CL_FALSE, 0, (size_t)cap * 4, listH[s], 0, 0, &curEv));
      CK(clFlush(q));
    }
    if (havePrev) {
      CK(clWaitForEvents(1, &prevEv)); clReleaseEvent(prevEv);
      u64 n = ctrH[prevK][0];
      double c0 = now();
      if (n > cap) { overflow++; scan_range(prevBase, prevBase + per, &g_ts[0]); }
      else copilot(prevBase, listH[prevK], n);
      for (int t = 0; t < g_nt; t++) {
        for (size_t i = 0; i < g_ts[t].ncand; i++) if (!resolve(g_ts[t].cand[i])) unresolved++;
        g_ts[t].ncand = 0;
      }
      cpuT += now() - c0;
      totB += ctrH[prevK][2]; done += per;
      if (do_check && prevBase == start) {
        static tstate ref;
        scan_range(prevBase, prevBase + per, &ref);
        u64 cb2 = 0; for (int t = 0; t < g_nt; t++) cb2 += g_ts[t].n_bm;
        printf("check, first batch: GPU arcs %u bitmaps %u listed %llu | CPU arcs %llu bitmaps %llu | copilot saw %llu -> %s\n", ctrH[prevK][1],
               ctrH[prevK][2], (unsigned long long)n, (unsigned long long)ref.n_arc, (unsigned long long)ref.n_bm, (unsigned long long)cb2,
               (ctrH[prevK][1] == ref.n_arc && ctrH[prevK][2] == ref.n_bm && n == ref.n_bm && cb2 == ref.n_bm) ? "MATCH" : "MISMATCH");
      }
      if (use_state) { FILE *f = fopen("state_cl_b6.tmp", "w"); if (f) { fprintf(f, "%llu\n", (unsigned long long)(prevBase + per)); fclose(f); rename("state_cl_b6.tmp", statefile); } }
      double tn = now();
      if (tn - tlast > 2.0 || !more) {
        u64 dd = 0, mid = 0; for (int t = 0; t < g_nt; t++) dd += g_ts[t].n_dd, mid += g_ts[t].n_mid;
        fprintf(stderr, "L < %llu done (10^%.4g digits)  %.3g L/s  CPU finishing %.0f%%  bitmaps %.4f%%  dbl %llu  mid %llu\n",
                (unsigned long long)(prevBase + per), log10((double)(prevBase + per) * log10(6.0)), done / (tn - t0), 100 * cpuT / (tn - t0),
                100.0 * totB / done, (unsigned long long)dd, (unsigned long long)mid);
        tlast = tn;
      }
    }
    if (!more) break;
    prevEv = curEv; prevBase = curBase; prevK = s; havePrev = 1;
  }
  double wall = now() - t0;
  printf("searched L in [%llu, %llu): %.3g lengths/s; %llu passed bitmaps; %llu not proved dead; %llu batches redone on CPU\n",
         (unsigned long long)start, (unsigned long long)(start + done), done / wall, (unsigned long long)totB, (unsigned long long)unresolved,
         (unsigned long long)overflow);
  return 0;
}
