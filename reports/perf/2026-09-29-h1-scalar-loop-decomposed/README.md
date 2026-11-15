# h1's 1.334x scalar component, decomposed instruction by instruction — and a correction to my own note (2026-09-29)

h1_vec_push_sum is 2.488x LLVM, and the earlier decomposition split that into 1.979x
vectorization + 1.334x residual scalar quality. The vectorization half is blocked. This report
does what nobody had done: compares trust-cg's scalar loop against **LLVM's scalar loop**, with
LLVM's vectorizer switched off, so the 1.334x is isolated with no vectorization confound.

## Re-confirming the split, with an in-batch control

h1 scaled 10x (`passes` 300 → 3000, ~86–228 ms, clearing the 50 ms floor), `taskset -c 2`,
15 interleaved rounds. The `-Cno-vectorize-loops -Cno-vectorize-slp` arm is verified effective
(4 `paddq` in `main` → 0).

| arm | min ms | vs LLVM | vs LLVM-scalar |
| --- | ---: | ---: | ---: |
| LLVM -O3 | 86.33 | 1.0000 | 0.5066 |
| LLVM -O3, no vectorize | 170.39 | 1.9738 | 1.0000 |
| trust-cg | 227.52 | 2.6356 | **1.3353** |
| trust-cg, identical copy | 228.47 | 2.6466 | 1.3408 |

So: **1.9738x is LLVM's vectorization, 1.3353x is scalar quality**, control 1.0041.

## The two scalar loops, in full

**LLVM, 5 instructions:**

```
add  (%r9),%rdi      ; acc += *p
inc  %r10            ; k++
add  $0x8,%r9        ; p += 8
cmp  %r8,%r10        ; k vs len   (len in a REGISTER)
jne  loop
```

**trust-cg, 12 instructions:**

```
20b0d:  mov  (%rdi),%rax        ; [1] RELOAD v.len            <- not hoisted
20b10:  cmp  %rax,%rbx          ;     the while condition k <u len
20b13:  jae  exit
20b19:  mov  %rbx,%rcx          ; [2] redundant copy of k
20b1c:  mov  (%r8),%rdx         ; [3] RELOAD v.ptr            <- not hoisted
20b1f:  mov  (%rsi),%rax        ; [4] RELOAD v.len AGAIN      <- second reload
20b22:  cmp  %rax,%rcx          ; [5] the BOUNDS CHECK, same predicate as [20b10]
20b25:  jae  panic
20b2b:  mov  (%rdx,%rcx,8),%rax ;     load v[k]
20b2f:  add  %rax,%r14          ;     acc +=
20b32:  add  $0x1,%rbx          ;     k++
20b36:  jmp  loop               ; [6] unconditional jmp, not a fused conditional back-edge
```

| | insns | span | memory reads | branches |
| --- | ---: | ---: | ---: | ---: |
| LLVM scalar | **5** | 13 B | 1 | 1 |
| trust-cg | **12** | 41 B | 4 | 3 |

LLVM strength-reduced the index into a pointer, hoisted `len` into a register, and eliminated
the bounds check. trust-cg reloads `len` **twice** and `ptr` once, every iteration, and keeps a
bounds check whose predicate the loop condition three instructions earlier already decided.

## The decisive fact: the two `len` loads are provably the same address

`(%rdi)` at 20b0d and `(%rsi)` at 20b1f look like independent loads. They are not. In the loop
preheader:

```
20aff:  mov  -0x60(%rbp),%r10
20b03:  lea  0x10(%r10),%rdi     ; rdi = &v.len
20b07:  mov  %r9,%r8             ; r8  = &v.ptr
20b0a:  mov  %rdi,%rsi           ; rsi IS rdi  <-- a plain register copy
```

**`rsi` is a `MovRR` copy of `rdi`.** So the guard's length and the check's length are loads
from the *same address at the same displacement*, related by one copy that `canon()` already
follows. Likewise the two index operands: `%rcx` at 20b19 is a plain `MovRR` copy of `%rbx`.
And between the two loads there are **no stores of any kind** — a `cmp`, a `jae`, a register
copy and a load.

This matters because it makes the obligation far weaker than I had assumed. Proving these two
loads equal needs no reaching-memory dataflow: it needs *same canonical base register, same
displacement, no store in the region between them* — and the region is the unique fall-through
path from the guard block to the check block, which
`x86_bounds_check_elim::no_aliasing_write_between` already models exactly (its
`cb == window.check_block` arm is precisely this two-range scan).

What blocks it today is narrower than "the analysis is missing": case 4
(`same_value_by_frame_reload`) proves two loads equal only when both resolve to the same **frame
bytes** via `resolve_frame_ref`. h1's loads go through a computed pointer (`lea 0x10(%r10)`),
not a frame slot, so case 4 cannot classify them and declines. The missing piece is a **case 5**:
same canonical `(base vreg, disp)`, base single-def, and no store at all in the between-region
(strictly stronger than case 4's aliasing test, and trivially satisfied here).

## CORRECTION: my recorded claim that "the bounds check is not a cost" was unjustified

`x86-h1-gap-decomposed` states, as a refuted cause:

> **The bounds check is not a cost.** [...] The reason the check is not a cost is the
> decomposition above, which leaves no room for it: 1.979x is vectorization and 1.334x is scalar
> quality.

**That is a non-sequitur, and it is mine.** The 1.334x scalar-quality component is *exactly
where the bounds check lives* — the decomposition does not exclude the check, it contains it.
Nothing in those measurements ever bore on whether the check costs anything.

The diff above replaces the bad inference with a count: the check and its dedicated length
reload are **3 of the 7 excess instructions** ([1] or [4], [5], and the `jae`) in a 12-versus-5
loop. That is not proof they cost 1.334x — instruction count has reversed on this very program
before — but "not a cost" is withdrawn, and the check is a live candidate again.

## The full inventory of h1's scalar excess, ranked

| # | excess | instructions | status |
| --- | --- | ---: | --- |
| [1]+[4] | `v.len` reloaded twice per iteration | 2 | hoisting BOTH was measured: **1.49x SLOWER** (`licm-pointer-loads`, P=0.000, a 9-byte NOP appeared in the body). Do not retry as-is. |
| [5] | bounds check duplicating the loop condition | 2 (`cmp`+`jae`) | **case 5 above is the mechanism**; not yet implemented |
| [3] | `v.ptr` reloaded per iteration | 1 | same LICM arm, same measured reversal |
| [2] | redundant copy of `k` | 1 | copy propagation / coalescing |
| [6] | `jmp` back-edge vs LLVM's fused `jne` | 1 | this is `branch-layout-fallthrough`, measured 23.5% WORSE on p7 globally — needs a per-loop policy |
| — | LLVM additionally strength-reduces the index to a pointer (`p += 8`), removing the scaled-index address | — | trust-cg has `x86_strength_reduce`; it does not do this here |

Note how many of these are already-measured dead ends. The genuinely unexplored ones are the
bounds check (case 5) and the index-to-pointer strength reduction.

## Status of the clause

Unchanged: h1 2.488x, b1 1.1326x, p4 1.0929x, p2 1.0191x versus LLVM. What this adds is the
first instruction-level account of h1's scalar half, the decisive observation that its two length
loads are one `MovRR` apart, and the withdrawal of a claim of mine that was never supported.
