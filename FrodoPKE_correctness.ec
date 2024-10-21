require import AllCore Int Real List IntDiv.
require (****) LWE_correctness DynMatrix.
require import ZModP.
require BitWord.
require import Array.
require import Keccak1600_Spec.
require import BitEncoding.
(*---*) import BS2Int.
(*---*) import BitChunking.
require import StdOrder.
import IntOrder.

from Jasmin require import JWord.
from Jasmin require import JArray.

op concatMap (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).
op tobytes (xs: bool list): W8.t list = map W8.bits2w (chunk W8.size xs).

op w8ltoW16l (xs: W8.t list): W16.t list = map W16.bits2w (chunk W16.size (concatMap W8.w2bits xs)).
op w8ltoW128(xs: W8.t list): W128.t = W128.bits2w (concatMap W8.w2bits xs).
op w8ltoW256(xs: W8.t list): W256.t = W256.bits2w (concatMap W8.w2bits xs).
op w128toW8l (x: W128.t): W8.t list = map W8.bits2w (chunk W8.size (W128.w2bits x)).
op w256toW8l (x: W256.t): W8.t list = map W8.bits2w (chunk W8.size (W256.w2bits x)).

op N : { int | 0 < N } as gt0_N.
op Nb : { int | 0 < Nb } as gt0_Nb.
op Mb : { int | 0 < Mb } as gt0_Mb.
op D : { int | 0 < D <= 16 } as D_bound.
op q : int = 2^D. 
op B : { int | 0 < B <= D } as B_bound.

hint exact: gt0_N gt0_Nb gt0_Mb D_bound B_bound.
hint simplify (gt0_N, gt0_Nb, gt0_Mb, D_bound, B_bound).
op CDF_table: int list.

op lenSE: { int | 0 <= lenSE } as ge0_lenSE.
op lenX: int = size CDF_table.
op SHAKE (m: W8.t list, outlen8:int): bool list.

abstract theory FrodoPKE.

abbrev mask5f = W8.of_int 95 (* 95 = 0x5f *).
abbrev mask96 = W8.of_int 150 (* 150 = 0x96 *).

clone DynMatrix as DM.

section.

import DM.

op sample (r: bool list): R =
  let r' = take (size CDF_table) r in
  let t = bs2int (behead r') in
  let sign = (-1)^(b2i (head false r')) in
    ZR.ofint (sign * foldl (fun e x => if x < t then e + 1 else e) 0 CDF_table).

op sample_matrix (r: bool list, m: int, n: int): matrix =
  let rs = chunk (size CDF_table) (take (m * n * size CDF_table) r) in
  let s = map sample rs in
  let vs = map oflist (chunk n s) in
  trmx (ofcols n m vs).

op prg_kg (r: matrix * bool list) : (matrix * matrix * matrix) =
  let A = r.`1 in
  let seedSE = take lenSE r.`2 in
  let rs = SHAKE (mask5f :: tobytes seedSE) (2*N*Nb*lenX) in
  let sT = sample_matrix (take (N*Nb*lenX) rs) Nb N in
  let e = sample_matrix (drop (N*Nb*lenX) rs) N Nb in
  (A, sT, e).

op prg_enc (r: bool list): (matrix * matrix * matrix) =
  let seedSE = take lenSE r in
  let rs = SHAKE (mask96 :: tobytes seedSE) ((2*Mb*N + Mb*Nb) * lenX) in
  let s' = sample_matrix (take (Mb*N*lenX) rs) Mb N in
  let e' = sample_matrix (take (Mb*N*lenX) (drop (Mb*N*lenX) rs)) Mb N in
  let e'' = sample_matrix (drop (2*Mb*N*lenX) rs) Mb Nb in
  (s', e', e'').

op ec (k: int): R = ZR.ofint (k * q %/ (2^B)).

op m_encode (pt: bool list): matrix =
  let pt' = chunk B (take (B*Mb*Nb) pt) in
  let ks = map (fun bs => ec (bs2int bs)) pt' in
  let vs = map oflist (chunk Nb ks) in
  trmx (ofcols Nb Mb vs).

op dc (c : R): int.

op m_decode (m: matrix): bool list =
  let s = foldl (fun xs i => xs ++
    foldl (fun s j => rcons s m.[(i, j)]) [] (range 0 Nb)
  ) [] (range 0 Mb) in
  flatten (map (fun c => int2bs B (dc c)) s).

end section.

import DM.

clone LWE_correctness as LWE_correctness with
  type LWE_.seed <- matrix,
  op LWE_.H <- fun sd m n => subm sd 0 m 0 n,
  op LWE_.n <- N,
  op LWE_.mb <- Mb,
  op LWE_.nb <- Nb,
  type randomness <- (matrix * bool list),
  type plaintext <- bool list,
  type ciphertext <- matrix*matrix, 
  type pkey <- matrix * matrix,
  type skey <- matrix,
  op pk_encode <- idfun, 
  op pk_decode <- idfun,
  op sk_encode <- idfun, 
  op sk_decode <- idfun,
  op m_encode <- m_encode,
  op m_decode <- m_decode,
  op c_encode <- idfun,
  op c_decode <- idfun, 
  op prg_kg <- prg_kg,
  op prg_enc <- fun (r: matrix * bool list) => prg_enc r.`2,
  theory DM <- DM 
  proof
    m_encode_rows,
    m_encode_cols,
    pk_encodeK by done,
    sk_encodeK by done,
    good_c_decode by done,
    LWE_.gt0_n by done,
    LWE_.gt0_nb by done, 
    LWE_.gt0_mb by done,
    LWE_.H_mem,
    LWE_.H_rows,
    LWE_.H_cols.

realize m_encode_rows.
proof.
rewrite /m_encode /= => *.
smt(cols_offunm gt0_Mb).
qed.

realize m_encode_cols.
proof.
rewrite /m_encode /= => *.
smt(rows_offunm gt0_Nb).
qed.

realize LWE_.H_mem.
proof.
move => sd x y *.
rewrite duni_matrix_fu 1,2:// size_subm.
smt().
qed.

realize LWE_.H_rows.
proof.
move => *.
smt(rows_subm).
qed.

realize LWE_.H_cols.
proof.
move => *.
smt(cols_subm).
qed.

end FrodoPKE.

clone import ZModRing as Zq with
  op p <- q
  rename "zmod" as "Zq"
  proof ge2_p.
realize ge2_p.
    rewrite /q.
    rewrite ler_eexpr 2://.
    smt(D_bound).
qed.

op round (x: real): int = floor (x + inv 2%r).
op dc (c: Zq): int = round ((asint c)%r * (2^B)%r / q %r) %% 2^B.

clone FrodoPKE as FrodoPKE_ with
  op dc <- dc,
  theory DM.ZR <- ZModpRing
  proof *.

realize LWE_correctness.good_m_decode.
proof.
move => m e.
admit. 
qed.
