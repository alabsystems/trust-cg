#!/usr/bin/env python3
"""Generate square i32 matmul trust_ir in both loop orders.

  ikj: for i,k,j:  C[i][j] += A[i][k]*B[k][j]   (store-form / saxpy inner)
  ijk: for i,j,k:  C[i][j] += A[i][k]*B[k][j]   (dot-product inner)

Numeric %N SSA + numeric bbN block labels; noalias on all three pointer params;
row-base geps hoisted so the inner index is exactly the inner induction (what
neon_map recognizes).  C assumed pre-zeroed by the driver.  Sig: (C, A, B, N).
"""

HDR = """; TrustIr text format v1
module "mm"
target "aarch64-apple-darwin" 8 little abi="aapcs64"
functy.0 = (ptr, ptr, ptr, i32) -> ()
fn @matmul(functy.0) {
; #param_attrs 0: noalias
; #param_attrs 1: noalias
; #param_attrs 2: noalias
"""

def gen_ikj():
    C,A,B,N = 0,1,2,3
    z,one = 4,5
    i,rowC,crow,rowA,arow = 10,11,12,13,14
    k,ag,s,rowB,brow = 20,21,22,23,24
    j,cg,cv,bg,bv,prod,new,jn = 30,31,32,33,34,35,36,37
    kn,inx = 40,41
    ci,ck,cj = 50,51,52
    return HDR + f"""bb0(%{C}: ptr, %{A}: ptr, %{B}: ptr, %{N}: i32):
    %{z} = const i32 0
    %{one} = const i32 1
    br bb1(%{z})
bb1(%{i}: i32):
    %{ci} = icmp slt i32 %{i}, %{N}
    condbr %{ci}, bb2, bb9
bb2:
    %{rowC} = mul i32 %{i}, %{N}
    %{crow} = gep i32, ptr %{C}, %{rowC}
    %{rowA} = mul i32 %{i}, %{N}
    %{arow} = gep i32, ptr %{A}, %{rowA}
    br bb3(%{z})
bb3(%{k}: i32):
    %{ck} = icmp slt i32 %{k}, %{N}
    condbr %{ck}, bb4, bb8
bb4:
    %{ag} = gep i32, ptr %{arow}, %{k}
    %{s} = load i32, ptr %{ag}
    %{rowB} = mul i32 %{k}, %{N}
    %{brow} = gep i32, ptr %{B}, %{rowB}
    br bb5(%{z})
bb5(%{j}: i32):
    %{cj} = icmp slt i32 %{j}, %{N}
    condbr %{cj}, bb6, bb7
bb6:
    %{cg} = gep i32, ptr %{crow}, %{j}
    %{cv} = load i32, ptr %{cg}
    %{bg} = gep i32, ptr %{brow}, %{j}
    %{bv} = load i32, ptr %{bg}
    %{prod} = mul i32 %{s}, %{bv}
    %{new} = add i32 %{cv}, %{prod}
    store i32 %{new}, ptr %{cg}
    %{jn} = add i32 %{j}, %{one}
    br bb5(%{jn})
bb7:
    %{kn} = add i32 %{k}, %{one}
    br bb3(%{kn})
bb8:
    %{inx} = add i32 %{i}, %{one}
    br bb1(%{inx})
bb9:
    ret
}}
"""

def gen_ijk():
    C,A,B,N = 0,1,2,3
    z,one = 4,5
    i,rowC,crow,rowA,arow = 10,11,12,13,14
    j,cg,acc0 = 20,21,22
    k,ag,s,bg,bv,prod,acc1,kn = 30,31,32,33,34,35,36,37
    rowB,browbase = 38,39
    jn,inx = 40,41
    ci,cj,ck = 50,51,52
    accp = 60
    return HDR + f"""bb0(%{C}: ptr, %{A}: ptr, %{B}: ptr, %{N}: i32):
    %{z} = const i32 0
    %{one} = const i32 1
    br bb1(%{z})
bb1(%{i}: i32):
    %{ci} = icmp slt i32 %{i}, %{N}
    condbr %{ci}, bb2, bb9
bb2:
    %{rowC} = mul i32 %{i}, %{N}
    %{crow} = gep i32, ptr %{C}, %{rowC}
    %{rowA} = mul i32 %{i}, %{N}
    %{arow} = gep i32, ptr %{A}, %{rowA}
    br bb3(%{z})
bb3(%{j}: i32):
    %{cj} = icmp slt i32 %{j}, %{N}
    condbr %{cj}, bb4, bb8
bb4:
    %{cg} = gep i32, ptr %{crow}, %{j}
    %{acc0} = load i32, ptr %{cg}
    br bb5(%{z}, %{acc0})
bb5(%{k}: i32, %{accp}: i32):
    %{ck} = icmp slt i32 %{k}, %{N}
    condbr %{ck}, bb6, bb7
bb6:
    %{ag} = gep i32, ptr %{arow}, %{k}
    %{s} = load i32, ptr %{ag}
    %{rowB} = mul i32 %{k}, %{N}
    %{browbase} = gep i32, ptr %{B}, %{rowB}
    %{bg} = gep i32, ptr %{browbase}, %{j}
    %{bv} = load i32, ptr %{bg}
    %{prod} = mul i32 %{s}, %{bv}
    %{acc1} = add i32 %{accp}, %{prod}
    %{kn} = add i32 %{k}, %{one}
    br bb5(%{kn}, %{acc1})
bb7:
    store i32 %{accp}, ptr %{cg}
    %{jn} = add i32 %{j}, %{one}
    br bb3(%{jn})
bb8:
    %{inx} = add i32 %{i}, %{one}
    br bb1(%{inx})
bb9:
    ret
}}
"""

if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "ikj"
    sys.stdout.write(gen_ikj() if which == "ikj" else gen_ijk())
