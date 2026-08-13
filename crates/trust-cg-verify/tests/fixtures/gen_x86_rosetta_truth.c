// gen_x86_rosetta_truth.c — THE ROSETTA x86 ORACLE HARNESS (campaign #3, x86).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this is
// ===========================================================================
// The x86 analog of the AArch64 on-chip differential harness. It executes each
// trust-cg scalar-integer x86 op via GNU inline assembly over a SAMPLED operand
// grid and records the REAL x86 result. The "chip" here is Rosetta 2 — Apple's
// independent x86-64 binary translator — exercised by building this program with
// `clang -arch x86_64` and running it under `arch -x86_64`. Rosetta is a TRUE
// independent x86 implementation (NOT a second in-house model), so the facts it
// emits real-emulation-VALIDATE trust-cg's x86 SmtExpr model and defeat
// root-cause #2 (both equivalence sides in-house) for x86 integer ops. It is one
// notch below bare silicon (Rosetta faithfully reproduces x86 integer semantics
// incl. shift-count masking &0x3F/&0x1F and the IDIV/DIV #DE traps on div0 and
// INT_MIN/-1, confirmed at build time by the bridge).
//
// ===========================================================================
// Trap capture (the load-bearing part)
// ===========================================================================
// x86 IDIV/DIV raise #DE (divide error) on a zero divisor and on signed
// INT_MIN / -1 overflow. Under Rosetta #DE surfaces as SIGFPE. To record a trap
// WITHOUT killing the harness, every potentially-trapping divide is run in a
// FORKED CHILD: if the child dies of SIGFPE we record result="trap"; otherwise
// we record the child's computed value (passed back through a pipe). Non-trapping
// ops are computed inline in the parent.
//
// ===========================================================================
// Output
// ===========================================================================
// Emits x86_64_rosetta_truth.json: a provenance `_header` (oracle, macOS+Rosetta
// version + date passed in by the regen script, exact accounting) plus a `facts`
// array of {op, lean-style theorem id, width, operands (hex-as-u64), result hex
// OR "trap"}. The committed JSON is consumed by tests/bdefs_differential_bridge_x86.rs.
//
// ===========================================================================
// Build + run (done by gen_x86_rosetta_truth.sh)
// ===========================================================================
//   clang -arch x86_64 -O0 -o gen_x86_rosetta_truth gen_x86_rosetta_truth.c
//   arch -x86_64 ./gen_x86_rosetta_truth "<macos_ver>" "<rosetta_ver>" "<date>" > out.json

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <sys/wait.h>

// ---------------------------------------------------------------------------
// x86-64 op primitives — each is a single faithful instruction in inline asm.
// 64-bit (X) and 32-bit (W) forms where the op has both. Names mirror the
// trust-cg encoder family they validate (x86_64_semantics.rs).
// ---------------------------------------------------------------------------

// ADD / SUB
static uint64_t x_add64(uint64_t a, uint64_t b){ uint64_t r; __asm__ volatile("addq %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint32_t x_add32(uint32_t a, uint32_t b){ uint32_t r; __asm__ volatile("addl %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint64_t x_sub64(uint64_t a, uint64_t b){ uint64_t r; __asm__ volatile("subq %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint32_t x_sub32(uint32_t a, uint32_t b){ uint32_t r; __asm__ volatile("subl %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }

// IMUL r,r/m (two-operand signed multiply -> low half)
static uint64_t x_imul64(uint64_t a, uint64_t b){ uint64_t r; __asm__ volatile("imulq %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint32_t x_imul32(uint32_t a, uint32_t b){ uint32_t r; __asm__ volatile("imull %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }

// IMUL r,r/m,imm (three-operand). imm is encoded literally; we sample a fixed set.
#define X_IMUL64_IMM(NAME,IMM) \
  static uint64_t NAME(uint64_t a){ uint64_t r; __asm__ volatile("imulq $" #IMM ",%1,%0":"=r"(r):"r"(a):"cc"); return r; }
#define X_IMUL32_IMM(NAME,IMM) \
  static uint32_t NAME(uint32_t a){ uint32_t r; __asm__ volatile("imull $" #IMM ",%1,%0":"=r"(r):"r"(a):"cc"); return r; }
X_IMUL64_IMM(x_imul64_imm_3, 3)
X_IMUL64_IMM(x_imul64_imm_m7, -7)
X_IMUL32_IMM(x_imul32_imm_3, 3)
X_IMUL32_IMM(x_imul32_imm_m7, -7)

// MUL r/m (one-operand UNSIGNED widening) -> RDX:RAX. We capture low (RAX) + high (RDX).
static void x_mul64(uint64_t a, uint64_t b, uint64_t *lo, uint64_t *hi){
  uint64_t l,h; __asm__ volatile("mulq %3":"=a"(l),"=d"(h):"a"(a),"r"(b):"cc"); *lo=l; *hi=h;
}
static void x_mul32(uint32_t a, uint32_t b, uint32_t *lo, uint32_t *hi){
  uint32_t l,h; __asm__ volatile("mull %3":"=a"(l),"=d"(h):"a"(a),"r"(b):"cc"); *lo=l; *hi=h;
}

// NEG
static uint64_t x_neg64(uint64_t a){ uint64_t r; __asm__ volatile("negq %0":"=r"(r):"0"(a):"cc"); return r; }
static uint32_t x_neg32(uint32_t a){ uint32_t r; __asm__ volatile("negl %0":"=r"(r):"0"(a):"cc"); return r; }

// NOT
static uint64_t x_not64(uint64_t a){ uint64_t r; __asm__ volatile("notq %0":"=r"(r):"0"(a)); return r; }
static uint32_t x_not32(uint32_t a){ uint32_t r; __asm__ volatile("notl %0":"=r"(r):"0"(a)); return r; }

// AND / OR / XOR
static uint64_t x_and64(uint64_t a, uint64_t b){ uint64_t r; __asm__ volatile("andq %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint32_t x_and32(uint32_t a, uint32_t b){ uint32_t r; __asm__ volatile("andl %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint64_t x_or64 (uint64_t a, uint64_t b){ uint64_t r; __asm__ volatile("orq %2,%0" :"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint32_t x_or32 (uint32_t a, uint32_t b){ uint32_t r; __asm__ volatile("orl %2,%0" :"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint64_t x_xor64(uint64_t a, uint64_t b){ uint64_t r; __asm__ volatile("xorq %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }
static uint32_t x_xor32(uint32_t a, uint32_t b){ uint32_t r; __asm__ volatile("xorl %2,%0":"=r"(r):"0"(a),"r"(b):"cc"); return r; }

// SHL / SHR / SAR by CL (the hardware-masked count form: x86 masks CL to 6 bits
// at 64-bit, 5 bits at 32-bit — this is exactly what encode_shl_rr_masked models).
static uint64_t x_shl64(uint64_t a, uint8_t c){ uint64_t r; __asm__ volatile("shlq %%cl,%0":"=r"(r):"0"(a),"c"(c):"cc"); return r; }
static uint32_t x_shl32(uint32_t a, uint8_t c){ uint32_t r; __asm__ volatile("shll %%cl,%0":"=r"(r):"0"(a),"c"(c):"cc"); return r; }
static uint64_t x_shr64(uint64_t a, uint8_t c){ uint64_t r; __asm__ volatile("shrq %%cl,%0":"=r"(r):"0"(a),"c"(c):"cc"); return r; }
static uint32_t x_shr32(uint32_t a, uint8_t c){ uint32_t r; __asm__ volatile("shrl %%cl,%0":"=r"(r):"0"(a),"c"(c):"cc"); return r; }
static int64_t  x_sar64(int64_t a, uint8_t c){ int64_t r; __asm__ volatile("sarq %%cl,%0":"=r"(r):"0"(a),"c"(c):"cc"); return r; }
static int32_t  x_sar32(int32_t a, uint8_t c){ int32_t r; __asm__ volatile("sarl %%cl,%0":"=r"(r):"0"(a),"c"(c):"cc"); return r; }

// MOVZX / MOVSX (from 8/16/32 -> 64; and 8/16 -> 32). We sample 16->64 + 8->32.
static uint64_t x_movzx_w16_64(uint16_t a){ uint64_t r; __asm__ volatile("movzwq %1,%0":"=r"(r):"r"(a)); return r; }
static uint64_t x_movsx_w16_64(uint16_t a){ uint64_t r; __asm__ volatile("movswq %1,%0":"=r"(r):"r"(a)); return r; }
static uint64_t x_movsxd_32_64(uint32_t a){ uint64_t r; __asm__ volatile("movslq %1,%0":"=r"(r):"r"(a)); return r; }
static uint32_t x_movzx_b8_32 (uint8_t  a){ uint32_t r; __asm__ volatile("movzbl %1,%0":"=r"(r):"r"(a)); return r; }
static uint32_t x_movsx_b8_32 (uint8_t  a){ uint32_t r; __asm__ volatile("movsbl %1,%0":"=r"(r):"r"(a)); return r; }

// CMOVcc (CMOVNE here: dst = (a!=b) ? src : old). Models encode_cmovcc with a
// CMP-derived condition. We set ZF via a CMP of (a,b); CMOVNE picks src iff a!=b.
static uint64_t x_cmovne64(uint64_t a, uint64_t b, uint64_t old_dst, uint64_t src){
  uint64_t r=old_dst; __asm__ volatile("cmpq %2,%1; cmovneq %3,%0":"+r"(r):"r"(a),"r"(b),"r"(src):"cc"); return r;
}
static uint32_t x_cmovne32(uint32_t a, uint32_t b, uint32_t old_dst, uint32_t src){
  uint32_t r=old_dst; __asm__ volatile("cmpl %2,%1; cmovnel %3,%0":"+r"(r):"r"(a),"r"(b),"r"(src):"cc"); return r;
}

// LEA [base + index*scale + disp]. scale and disp must be literal -> fixed sample.
static uint64_t x_lea_b_i_s8_d4(uint64_t base, uint64_t index){
  uint64_t r; __asm__ volatile("leaq 4(%1,%2,8),%0":"=r"(r):"r"(base),"r"(index)); return r;
}
static uint64_t x_lea_b_d4(uint64_t base){
  uint64_t r; __asm__ volatile("leaq 4(%1),%0":"=r"(r):"r"(base)); return r;
}
static uint64_t x_lea_b_i_s4(uint64_t base, uint64_t index){
  uint64_t r; __asm__ volatile("leaq (%1,%2,4),%0":"=r"(r):"r"(base),"r"(index)); return r;
}

// IDIV / DIV (TRAPPING). RDX:RAX / divisor. We model the trust-cg reconstruction:
// the dividend is the W-bit RAX sign/zero-extended into RDX:RAX (CQO/CDQ for IDIV,
// xor edx for DIV). quotient = RAX, remainder = RDX.
static int64_t  x_idiv64(int64_t a, int64_t b, int64_t *rem){ int64_t q,r; __asm__ volatile("cqto; idivq %4":"=a"(q),"=d"(r):"a"(a),"d"(0),"r"(b):"cc"); *rem=r; return q; }
static int32_t  x_idiv32(int32_t a, int32_t b, int32_t *rem){ int32_t q,r; __asm__ volatile("cltd; idivl %4":"=a"(q),"=d"(r):"a"(a),"d"(0),"r"(b):"cc"); *rem=r; return q; }
static uint64_t x_div64 (uint64_t a, uint64_t b, uint64_t *rem){ uint64_t q,r; __asm__ volatile("divq %4":"=a"(q),"=d"(r):"a"(a),"d"(0ULL),"r"(b):"cc"); *rem=r; return q; }
static uint32_t x_div32 (uint32_t a, uint32_t b, uint32_t *rem){ uint32_t q,r; __asm__ volatile("divl %4":"=a"(q),"=d"(r):"a"(a),"d"(0U),"r"(b):"cc"); *rem=r; return q; }

// ---------------------------------------------------------------------------
// Operand grids. Edge cases first, then a deterministic LCG random sample.
// ---------------------------------------------------------------------------
static const uint64_t G64[] = {
  0x0ULL, 0x1ULL, 0xFFFFFFFFFFFFFFFFULL /* -1 */, 0x8000000000000000ULL /* INT_MIN */,
  0x7FFFFFFFFFFFFFFFULL /* INT_MAX */, 0x2ULL, 0x3ULL, 0x100ULL,
  0xFFFFFFFFULL /* UINT32_MAX */, 0x100000000ULL, 0xDEADBEEFCAFEBABEULL, 0x123456789ABCDEF0ULL,
};
static const uint32_t G32[] = {
  0x0U, 0x1U, 0xFFFFFFFFU /* -1 / UINT32_MAX */, 0x80000000U /* INT32_MIN */,
  0x7FFFFFFFU /* INT32_MAX */, 0x2U, 0x3U, 0x100U, 0xFFFFU, 0x10000U, 0xDEADBEEFU, 0x12345678U,
};
// Shift-count grid: deliberately includes counts >= width to exercise the
// hardware &63 / &31 masking (the #57 contract the masked encoders model).
static const uint8_t SHIFTC[] = { 0, 1, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 200, 255 };

#define NG64 ((int)(sizeof(G64)/sizeof(G64[0])))
#define NG32 ((int)(sizeof(G32)/sizeof(G32[0])))
#define NSC  ((int)(sizeof(SHIFTC)/sizeof(SHIFTC[0])))

// ---------------------------------------------------------------------------
// JSON emission with exact accounting.
// ---------------------------------------------------------------------------
static long g_total_attempted = 0;   // facts the grid asked for
static long g_emitted = 0;           // facts actually written
static long g_trap_facts = 0;        // facts recorded as "trap"
static int  g_first = 1;             // comma control

static void emit_value(const char *op, int width, const uint64_t *ops, int nops, uint64_t result){
  g_total_attempted++;
  if(!g_first) printf(",\n"); g_first=0;
  printf("  {\"op\":\"%s\",\"theorem\":\"rosetta_%s_%ld\",\"width\":%d,\"operands\":[",
         op, op, g_emitted, width);
  for(int i=0;i<nops;i++) printf("%s%llu", i?",":"", (unsigned long long)ops[i]);
  printf("],\"result\":\"0x%llx\"}", (unsigned long long)result);
  g_emitted++;
}

static void emit_trap(const char *op, int width, const uint64_t *ops, int nops){
  g_total_attempted++;
  if(!g_first) printf(",\n"); g_first=0;
  printf("  {\"op\":\"%s\",\"theorem\":\"rosetta_%s_%ld\",\"width\":%d,\"operands\":[",
         op, op, g_emitted, width);
  for(int i=0;i<nops;i++) printf("%s%llu", i?",":"", (unsigned long long)ops[i]);
  printf("],\"result\":\"trap\"}");
  g_emitted++; g_trap_facts++;
}

// ---------------------------------------------------------------------------
// Trapping divide, run in a forked child. Returns 1 if it TRAPPED (SIGFPE),
// else 0 and writes *q/*r through a pipe. `signed_div`/`is64` select the op.
// ---------------------------------------------------------------------------
typedef struct { uint64_t q, r; } divres_t;

static int run_divide_child(int is64, int is_signed, uint64_t a, uint64_t b, divres_t *out){
  int fds[2];
  if(pipe(fds)!=0){ perror("pipe"); exit(2); }
  pid_t pid = fork();
  if(pid<0){ perror("fork"); exit(2); }
  if(pid==0){
    // child: compute and write back; a #DE delivers SIGFPE and we never reach write.
    close(fds[0]);
    divres_t res;
    if(is64){
      if(is_signed){ int64_t rem; int64_t q=x_idiv64((int64_t)a,(int64_t)b,&rem); res.q=(uint64_t)q; res.r=(uint64_t)rem; }
      else        { uint64_t rem; uint64_t q=x_div64(a,b,&rem);                 res.q=q;            res.r=rem; }
    } else {
      if(is_signed){ int32_t rem; int32_t q=x_idiv32((int32_t)a,(int32_t)b,&rem); res.q=(uint32_t)q; res.r=(uint32_t)rem; }
      else        { uint32_t rem; uint32_t q=x_div32((uint32_t)a,(uint32_t)b,&rem); res.q=(uint32_t)q; res.r=(uint32_t)rem; }
    }
    ssize_t n = write(fds[1], &res, sizeof(res));
    (void)n; close(fds[1]); _exit(0);
  }
  // parent
  close(fds[1]);
  divres_t buf; ssize_t got = 0; char *p=(char*)&buf;
  ssize_t total=0; while(total<(ssize_t)sizeof(buf)){ got=read(fds[0],p+total,sizeof(buf)-total); if(got<=0) break; total+=got; }
  close(fds[0]);
  int st; waitpid(pid,&st,0);
  if(WIFSIGNALED(st) && WTERMSIG(st)==SIGFPE) return 1;       // #DE trap
  if(WIFSIGNALED(st)) { fprintf(stderr,"unexpected signal %d on divide\n",WTERMSIG(st)); exit(3); }
  if(total!=(ssize_t)sizeof(buf)){ fprintf(stderr,"child did not return a divide result\n"); exit(3); }
  *out = buf; return 0;
}

// Mask a u64 to `width` bits (so 32-bit results are stored as their low 32 bits).
static uint64_t maskw(uint64_t v, int width){ return width>=64 ? v : (v & ((1ULL<<width)-1)); }

int main(int argc, char **argv){
  const char *macos_ver   = argc>1 ? argv[1] : "unknown";
  const char *rosetta_ver = argc>2 ? argv[2] : "unknown";
  const char *date        = argc>3 ? argv[3] : "unknown";

  // ---- header (provenance). We print facts first into a buffer-free stream, so
  // accounting totals are emitted in a trailer the regen script splices. To keep
  // a single clean JSON we instead print header, then facts, then a footer with
  // the live counts — the counts are known only AFTER emission, so we print the
  // facts array first into stdout and the header LAST is not valid JSON. Solution:
  // we KNOW the grid sizes up front, so we print the header (with the GRID plan)
  // first and an exact post-hoc accounting block at the end of the document.
  printf("{\n");
  printf(" \"_header\": {\n");
  printf("  \"purpose\": \"x86-64 scalar-integer REAL-x86 ground truth for the B-x86-rosetta differential bridge: each fact is a result produced by Rosetta 2 (Apple's independent x86-64 translator), an independent x86 implementation (NOT a second in-house model), validating trust-cg's x86 SmtExpr encoders.\",\n");
  printf("  \"oracle\": \"rosetta2\",\n");
  printf("  \"oracle_note\": \"Rosetta 2 binary translation on Apple silicon; one notch below bare silicon. Reproduces x86 integer semantics incl. shift-count masking &0x3f/&0x1f and the IDIV/DIV #DE traps on div0 and INT_MIN/-1.\",\n");
  printf("  \"macos_version\": \"%s\",\n", macos_ver);
  printf("  \"rosetta_version\": \"%s\",\n", rosetta_ver);
  printf("  \"recorded_on\": \"%s\",\n", date);
  printf("  \"build\": \"clang -arch x86_64 gen_x86_rosetta_truth.c; run via arch -x86_64\",\n");
  printf("  \"trap_capture\": \"each potentially-trapping IDIV/DIV runs in a forked child; SIGFPE (#DE) -> result=trap; otherwise the child returns the value through a pipe\",\n");
  printf("  \"regen\": \"crates/trust-cg-verify/tests/fixtures/gen_x86_rosetta_truth.sh\",\n");
  printf("  \"inclusion_policy\": \"scalar integer ops with an in-house encoder in x86_64_semantics.rs, sampled over an edge-case+random grid (0,1,-1,INT_MIN,INT_MAX,UINT_MAX,random) in W(32) and X(64) forms. Packed-SSE/FP ops are out of scope (separate FP bridge); shift-by->=width counts are included to exercise &63/&31 masking; div0 and INT_MIN/-1 are included as trap facts.\",\n");
  printf("  \"operands_encoding\": \"each operand is the low `width` bits as an unsigned decimal u64 (matching the AArch64 fixture); result is hex (0x..) or the string \\\"trap\\\".\"\n");
  printf(" },\n");
  printf(" \"facts\": [\n");

  uint64_t ops[4];

  // ===================== binary arith/logic (X + W) =====================
  for(int i=0;i<NG64;i++) for(int j=0;j<NG64;j++){
    uint64_t a=G64[i], b=G64[j]; ops[0]=a; ops[1]=b;
    emit_value("add",64,ops,2, x_add64(a,b));
    emit_value("sub",64,ops,2, x_sub64(a,b));
    emit_value("imul",64,ops,2, x_imul64(a,b));
    emit_value("and",64,ops,2, x_and64(a,b));
    emit_value("or", 64,ops,2, x_or64(a,b));
    emit_value("xor",64,ops,2, x_xor64(a,b));
    uint64_t lo,hi; x_mul64(a,b,&lo,&hi);
    emit_value("mul_low", 64,ops,2, lo);
    emit_value("mul_high",64,ops,2, hi);
  }
  for(int i=0;i<NG32;i++) for(int j=0;j<NG32;j++){
    uint32_t a=G32[i], b=G32[j]; ops[0]=a; ops[1]=b;
    emit_value("addw",32,ops,2, maskw(x_add32(a,b),32));
    emit_value("subw",32,ops,2, maskw(x_sub32(a,b),32));
    emit_value("imulw",32,ops,2, maskw(x_imul32(a,b),32));
    emit_value("andw",32,ops,2, maskw(x_and32(a,b),32));
    emit_value("orw", 32,ops,2, maskw(x_or32(a,b),32));
    emit_value("xorw",32,ops,2, maskw(x_xor32(a,b),32));
    uint32_t lo,hi; x_mul32(a,b,&lo,&hi);
    emit_value("mul_low_w", 32,ops,2, maskw(lo,32));
    emit_value("mul_high_w",32,ops,2, maskw(hi,32));
  }

  // ===================== unary (X + W) =====================
  for(int i=0;i<NG64;i++){ uint64_t a=G64[i]; ops[0]=a;
    emit_value("neg",64,ops,1, x_neg64(a));
    emit_value("not",64,ops,1, x_not64(a));
    emit_value("mov",64,ops,1, a);                       // MOV r,r is identity
  }
  for(int i=0;i<NG32;i++){ uint32_t a=G32[i]; ops[0]=a;
    emit_value("negw",32,ops,1, maskw(x_neg32(a),32));
    emit_value("notw",32,ops,1, maskw(x_not32(a),32));
    emit_value("movw",32,ops,1, maskw(a,32));
  }

  // ===================== three-operand IMUL (fixed imms) =====================
  for(int i=0;i<NG64;i++){ uint64_t a=G64[i]; ops[0]=a; ops[1]=3;
    emit_value("imul_imm",64,ops,2, x_imul64_imm_3(a)); ops[1]=(uint64_t)(int64_t)-7;
    emit_value("imul_imm",64,ops,2, x_imul64_imm_m7(a));
  }
  for(int i=0;i<NG32;i++){ uint32_t a=G32[i]; ops[0]=a; ops[1]=3;
    emit_value("imul_imm_w",32,ops,2, maskw(x_imul32_imm_3(a),32)); ops[1]=(uint32_t)(int32_t)-7;
    emit_value("imul_imm_w",32,ops,2, maskw(x_imul32_imm_m7(a),32));
  }

  // ===================== shifts (X + W), with masked counts =====================
  for(int i=0;i<NG64;i++) for(int k=0;k<NSC;k++){
    uint64_t a=G64[i]; uint8_t c=SHIFTC[k]; ops[0]=a; ops[1]=c;
    emit_value("shl",64,ops,2, x_shl64(a,c));
    emit_value("shr",64,ops,2, x_shr64(a,c));
    emit_value("sar",64,ops,2, (uint64_t)x_sar64((int64_t)a,c));
  }
  for(int i=0;i<NG32;i++) for(int k=0;k<NSC;k++){
    uint32_t a=G32[i]; uint8_t c=SHIFTC[k]; ops[0]=a; ops[1]=c;
    emit_value("shlw",32,ops,2, maskw(x_shl32(a,c),32));
    emit_value("shrw",32,ops,2, maskw(x_shr32(a,c),32));
    emit_value("sarw",32,ops,2, maskw((uint32_t)x_sar32((int32_t)a,c),32));
  }

  // ===================== MOVZX / MOVSX =====================
  for(int i=0;i<NG32;i++){
    uint16_t a16=(uint16_t)G32[i]; uint8_t a8=(uint8_t)G32[i];
    ops[0]=a16;
    emit_value("movzx_16_64",64,ops,1, x_movzx_w16_64(a16));
    emit_value("movsx_16_64",64,ops,1, x_movsx_w16_64(a16));
    ops[0]=G32[i];
    emit_value("movsxd_32_64",64,ops,1, x_movsxd_32_64(G32[i]));
    ops[0]=a8;
    emit_value("movzx_8_32",32,ops,1, maskw(x_movzx_b8_32(a8),32));
    emit_value("movsx_8_32",32,ops,1, maskw(x_movsx_b8_32(a8),32));
  }

  // ===================== CMOVcc (CMOVNE) =====================
  {
    uint64_t old_dst=0xAAAAAAAAAAAAAAAAULL, src=0x5555555555555555ULL;
    for(int i=0;i<NG64;i++) for(int j=0;j<NG64;j++){
      uint64_t a=G64[i], b=G64[j];
      ops[0]=a; ops[1]=b; ops[2]=old_dst; ops[3]=src;
      emit_value("cmovne",64,ops,4, x_cmovne64(a,b,old_dst,src));
    }
    uint32_t o32=0xAAAAAAAAU, s32=0x55555555U;
    for(int i=0;i<NG32;i++) for(int j=0;j<NG32;j++){
      uint32_t a=G32[i], b=G32[j];
      ops[0]=a; ops[1]=b; ops[2]=o32; ops[3]=s32;
      emit_value("cmovne_w",32,ops,4, maskw(x_cmovne32(a,b,o32,s32),32));
    }
  }

  // ===================== LEA (fixed scale/disp samples) =====================
  for(int i=0;i<NG64;i++) for(int j=0;j<NG64;j++){
    uint64_t base=G64[i], index=G64[j];
    ops[0]=base; ops[1]=index;
    emit_value("lea_b_i_s8_d4",64,ops,2, x_lea_b_i_s8_d4(base,index));
    emit_value("lea_b_i_s4",  64,ops,2, x_lea_b_i_s4(base,index));
  }
  for(int i=0;i<NG64;i++){ uint64_t base=G64[i]; ops[0]=base;
    emit_value("lea_b_d4",64,ops,1, x_lea_b_d4(base));
  }

  // ===================== IDIV / DIV (TRAPPING, forked children) =====================
  // We model the trust-cg reconstruction: dividend = sext/zext(rax,2W), divisor =
  // the W-bit operand. So quotient/remainder are recorded as separate facts. The
  // div0 and (signed) INT_MIN/-1 cases TRAP (#DE -> SIGFPE) -> result="trap".
  for(int i=0;i<NG64;i++) for(int j=0;j<NG64;j++){
    uint64_t a=G64[i], b=G64[j]; ops[0]=a; ops[1]=b;
    divres_t res;
    // signed
    if(run_divide_child(1,1,a,b,&res)){ emit_trap("idiv_q",64,ops,2); emit_trap("idiv_r",64,ops,2); }
    else { emit_value("idiv_q",64,ops,2,res.q); emit_value("idiv_r",64,ops,2,res.r); }
    // unsigned
    if(run_divide_child(1,0,a,b,&res)){ emit_trap("div_q",64,ops,2); emit_trap("div_r",64,ops,2); }
    else { emit_value("div_q",64,ops,2,res.q); emit_value("div_r",64,ops,2,res.r); }
  }
  for(int i=0;i<NG32;i++) for(int j=0;j<NG32;j++){
    uint32_t a=G32[i], b=G32[j]; ops[0]=a; ops[1]=b;
    divres_t res;
    if(run_divide_child(0,1,a,b,&res)){ emit_trap("idiv_q_w",32,ops,2); emit_trap("idiv_r_w",32,ops,2); }
    else { emit_value("idiv_q_w",32,ops,2,maskw(res.q,32)); emit_value("idiv_r_w",32,ops,2,maskw(res.r,32)); }
    if(run_divide_child(0,0,a,b,&res)){ emit_trap("div_q_w",32,ops,2); emit_trap("div_r_w",32,ops,2); }
    else { emit_value("div_q_w",32,ops,2,maskw(res.q,32)); emit_value("div_r_w",32,ops,2,maskw(res.r,32)); }
  }

  printf("\n ],\n");
  printf(" \"_accounting\": {\n");
  printf("  \"total_attempted\": %ld,\n", g_total_attempted);
  printf("  \"emitted\": %ld,\n", g_emitted);
  printf("  \"value_facts\": %ld,\n", g_emitted - g_trap_facts);
  printf("  \"trap_facts\": %ld,\n", g_trap_facts);
  printf("  \"sampled_grid\": {\"g64\":%d,\"g32\":%d,\"shift_counts\":%d}\n", NG64, NG32, NSC);
  printf(" }\n");
  printf("}\n");

  // Sanity: every attempted fact must have been emitted (no silent truncation).
  if(g_total_attempted != g_emitted){
    fprintf(stderr,"ACCOUNTING ERROR: attempted %ld != emitted %ld\n", g_total_attempted, g_emitted);
    return 4;
  }
  fprintf(stderr,"emitted %ld facts (%ld value, %ld trap)\n", g_emitted, g_emitted-g_trap_facts, g_trap_facts);
  return 0;
}
