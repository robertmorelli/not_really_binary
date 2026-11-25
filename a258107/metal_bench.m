/* metal_bench.m -- run the scanner's first two filter stages on the GPU and time them.
 *
 * Stage 1 (arc test) and stage 2 (per-base bitmap lookup) are done in a Metal compute
 * kernel using 64-bit integer phases, exactly as scan.c does them.  The tables and
 * constants come from scan.c itself, and the survivor counts are compared with scan.c's
 * CPU code on the first batch.  Survivors are only counted, not passed on to stages 3-5,
 * so this is a throughput benchmark, not a complete scanner.
 *
 * build: clang -O3 -fobjc-arc -DTOPBASE=6 metal_bench.m -framework Metal -framework Foundation -lpthread -o metal_bench
 * run:   ./metal_bench [batches] [log2 threads per batch]
 */
#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
/* scan.c defines short macro names (NA, NB, ...) that clash with system headers, so it comes second */
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
"static inline bool bit(const device uint *bm, uint base, ulong t) {\n"
"  uint k = (uint)(t >> 44);\n"                       /* top 20 bits */
"  return (bm[base * 32768u + (k >> 5)] >> (k & 31u)) & 1u;\n"
"}\n"
"kernel void scan(device uint *out [[buffer(0)]], constant ulong *P [[buffer(1)]],\n"
"                 const device uint *bm [[buffer(2)]], uint gid [[thread_position_in_grid]]) {\n"
"  ulong L0 = P[0] + (ulong)gid * P[13];\n"
"  ulong t0 = L0 * P[1] + mulhi64(L0, P[4]);\n"
"  ulong t1 = L0 * P[2] + mulhi64(L0, P[5]);\n"
"  ulong t2 = L0 * P[3] + mulhi64(L0, P[6]);\n"
"  uint ch = (uint)P[13], na = 0, nb = 0;\n"
"  for (uint j = 0; j < ch; j++) {\n"
"    if ((t0 - P[7] <= P[10]) & (t1 - P[8] <= P[11]) & (t2 - P[9] <= P[12])) {\n"
"      na++;\n"
"      if (bit(bm, 2, t2) && bit(bm, 1, t1) && bit(bm, 0, t0)) nb++;\n"
"    }\n"
"    t0 += P[1]; t1 += P[2]; t2 += P[3];\n"
"  }\n"
"  out[2 * gid] = na; out[2 * gid + 1] = nb;\n"
"}\n";

int main(int argc, char **argv) {
  @autoreleasepool {
    if (NB != 3) { fprintf(stderr, "build with -DTOPBASE=6\n"); return 2; }
    int batches = argc > 1 ? atoi(argv[1]) : 24, lg = argc > 2 ? atoi(argv[2]) : 19;
    u64 threads = 1ULL << lg, per = threads * BLK, start = 1;
    init_tables();
    build_bitmaps();

    id<MTLDevice> dev = MTLCreateSystemDefaultDevice();
    if (!dev) { fprintf(stderr, "no Metal device\n"); return 1; }
    NSError *err = nil;
    id<MTLLibrary> lib = [dev newLibraryWithSource:SRC options:nil error:&err];
    if (!lib) { fprintf(stderr, "shader compile failed: %s\n", err.localizedDescription.UTF8String); return 1; }
    id<MTLComputePipelineState> ps = [dev newComputePipelineStateWithFunction:[lib newFunctionWithName:@"scan"] error:&err];
    if (!ps) { fprintf(stderr, "pipeline failed: %s\n", err.localizedDescription.UTF8String); return 1; }
    id<MTLCommandQueue> q = [dev newCommandQueue];

    id<MTLBuffer> outB = [dev newBufferWithLength:threads * 8 options:MTLResourceStorageModeShared];
    id<MTLBuffer> parB = [dev newBufferWithLength:16 * 8 options:MTLResourceStorageModeShared];
    size_t bmBytes = ((size_t)1 << BM_BITS) / 8;
    id<MTLBuffer> bmB = [dev newBufferWithLength:3 * bmBytes options:MTLResourceStorageModeShared];
    for (int i = 0; i < 3; i++) memcpy((char *)bmB.contents + i * bmBytes, BM[i], bmBytes);
    u64 *P = parB.contents;
    for (int i = 0; i < 3; i++) {
      P[1 + i] = ALPHA_T[TOPBASE][BASE[i]][3];
      P[4 + i] = ALPHA_T[TOPBASE][BASE[i]][2];
      P[7 + i] = ARC_V[i];
      P[10 + i] = ARC_R[i];
    }
    P[13] = BLK;
    printf("device: %s\n", dev.name.UTF8String);
    printf("each batch: %llu GPU threads x %d lengths = %llu lengths\n", (unsigned long long)threads, BLK, (unsigned long long)per);

    u64 totA = 0, totB = 0, firstA = 0, firstB = 0;
    double t0 = now(), gpuTime = 0;
    for (int b = 0; b < batches; b++) {
      P[0] = start + (u64)b * per;
      id<MTLCommandBuffer> cb = [q commandBuffer];
      id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
      [enc setComputePipelineState:ps];
      [enc setBuffer:outB offset:0 atIndex:0];
      [enc setBuffer:parB offset:0 atIndex:1];
      [enc setBuffer:bmB offset:0 atIndex:2];
      NSUInteger w = ps.maxTotalThreadsPerThreadgroup;
      [enc dispatchThreads:MTLSizeMake(threads, 1, 1) threadsPerThreadgroup:MTLSizeMake(w, 1, 1)];
      [enc endEncoding];
      [cb commit];
      [cb waitUntilCompleted];
      if (cb.error) { fprintf(stderr, "GPU error: %s\n", cb.error.localizedDescription.UTF8String); return 1; }
      gpuTime += cb.GPUEndTime - cb.GPUStartTime;
      const uint32_t *o = outB.contents;
      u64 a = 0, c = 0;
      for (u64 i = 0; i < threads; i++) a += o[2 * i], c += o[2 * i + 1];
      if (b == 0) firstA = a, firstB = c;
      totA += a; totB += c;
    }
    double wall = now() - t0;
    u64 total = (u64)batches * per;
    printf("GPU: %llu lengths in %.2f s wall (%.2f s on GPU)\n", (unsigned long long)total, wall, gpuTime);
    printf("     %.3g lengths/s wall, %.3g lengths/s GPU time\n", total / wall, total / gpuTime);
    printf("     passed arcs: %llu (%.4f%%)   passed bitmaps: %llu (%.5f%%)\n", (unsigned long long)totA, 100.0 * totA / total,
           (unsigned long long)totB, 100.0 * totB / total);

    /* CPU reference on the first batch, one thread, same code path as scan.c */
    static tstate ts;
    double c0 = now();
    /* count only stages 1-2: run scan_range and read its counters */
    scan_range(start, start + per, &ts);
    double cpu = now() - c0;
    printf("CPU (1 thread, all stages) first batch: %.3g lengths/s; arcs %llu, bitmaps %llu\n", per / cpu,
           (unsigned long long)ts.n_arc, (unsigned long long)ts.n_bm);
    printf("GPU first batch:                                         arcs %llu, bitmaps %llu  -> %s\n", (unsigned long long)firstA,
           (unsigned long long)firstB, (firstA == ts.n_arc && firstB == ts.n_bm) ? "MATCH" : "MISMATCH");
  }
  return 0;
}
