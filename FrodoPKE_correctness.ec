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
import DM.ZR.

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

op toRowVectors (m: matrix): vector list =
  map (row m) (range 0 (rows m)).

op toColVectors (m: matrix): vector list =
  map (col m) (range 0 (cols m)).

lemma cancel_toColVectors_ofcols (vs: vector list) r c: 
    0 <= r => 0 <= c =>
    all (fun (v: vector) => size v = r) vs =>
    size vs = c =>
    toColVectors (ofcols r c vs) = vs.
proof.
move => ? ? h ?.
rewrite /toColVectors.
rewrite cols_offunm lez_maxr 1://.
apply (eq_from_nth witness).
+ rewrite size_map size_range => /#.
+ move => i [#].
  rewrite size_map size_range /= => *.
  rewrite (nth_map witness witness) 1:size_range 1:/# nth_range 1:/#.
  rewrite eq_vectorP.
  rewrite size_col rows_offunm lez_maxr 1://.
  have -> /= : size (nth witness vs i) = r; 1: by smt(List.allP mem_nth).
  move => j [#] *.
  by rewrite get_offunm 1:/#.
qed.

lemma cancel_ofcols_toColVectors (m: matrix):
    ofcols (rows m) (cols m) (toColVectors m) = m.
proof.
rewrite eq_matrixP.
rewrite rows_offunm cols_offunm => /> i j *.
rewrite get_offunm 1:/# /=.
rewrite /toColVectors (nth_map witness) 1:size_range 1:/#.
by rewrite get_offunv 1:/# /= nth_range 1:/#.
qed.

lemma toRowVectors_trmx m:
    toRowVectors (trmx m) = toColVectors m.
proof.
rewrite /toRowVectors /toColVectors /=.
smt(row_trmx).
qed.

lemma cancel_ofcols_toRowVectors (m: matrix):
    trmx (ofcols (cols m) (rows m) (toRowVectors m)) = m.
proof.
rewrite -{3}(trmxK m) -{4}(trmxK m).
apply congr1.
rewrite toRowVectors_trmx.
exact cancel_ofcols_toColVectors.
qed.

lemma subm_ofcols (vs: vector list) r c:
    0 <= c => 0 <= r =>
    all (fun (v: vector) => size v = r) vs =>
    size vs = c =>
    subm (ofcols r c vs) 0 r 0 c = ofcols r c vs.
proof.
move => *.
rewrite eq_matrixP.
rewrite size_subm rows_offunm cols_offunm /= => i j [#] *.
by rewrite get_subm 1,2:/#.
qed.
    
lemma ofcols_add (vs1 vs2: vector list) r c:
    0 <= r =>
    0 <= c =>
    size vs1 = c =>
    size vs2 = c =>
    all (fun (v: vector) => size v = r) vs1 =>
    all (fun (v: vector) => size v = r) vs2 =>
    ofcols r c vs1 + ofcols r c vs2 = ofcols r c (map (fun i => nth witness vs1 i + nth witness vs2 i) (range 0 c)).
proof.
admit.
qed.

op m_decode (m: matrix): bool list =
  let dc' = fun c => int2bs B (dc c) in
  flatten (map dc' (flatten (map tolist (toRowVectors (subm m 0 Mb 0 Nb))))).

axiom good_dc (k: int) (e: R) (p: R -> bool):
     0 <= k < (2^B)
  => p e
  => dc (ec k + e) = k.

end section.

import DM.

lemma subm_addm (m n: matrix) r1 r2 c1 c2:
    0 <= r1 =>
    r1 <= r2 =>
    0 <= c1 =>
    c1 <= c2 =>
    subm (m + n) r1 r2 c1 c2 = subm m r1 r2 c1 c2 + subm n r1 r2 c1 c2.
proof.
move => *.
rewrite eq_matrixP size_addm !size_subm => /> i j *.
rewrite get_subm 1,2:/#.
by rewrite !get_addm !get_subm 1..4:/#.
qed.

lemma tovectors_addm (m1 m2: matrix):
    size m1 = size m2 =>
    toRowVectors (m1 + m2) = map (fun (v: vector * vector) => v.`1 + v.`2) (zip (toRowVectors m1) (toRowVectors m2)).
proof.
move => [#] hr hc.
rewrite /toRowVectors rows_addm.
rewrite  zip_map !hr zipss.
rewrite -!map_comp /(\o) /=.
congr.
smt(rowD).
qed.

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
    LWE_.H_cols,
    good_m_decode.

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

realize good_m_decode.
proof.
move => m e ?.
rewrite /m_encode /=.
pose m'vs := map oflist (chunk Nb _).
pose m' := ofcols _ _ _.
rewrite /m_decode /matrix_tolist /=.
rewrite subm_addm //.
pose e' := subm e 0 Mb 0 Nb.
rewrite -(cancel_ofcols_toRowVectors e') rows_subm cols_subm /=.
rewrite -submT subm_ofcols 1,2://.
+ admit.
+ admit.
rewrite -trmxD toRowVectors_trmx !lez_maxr 1,2://.
rewrite ofcols_add 1,2://.
+ admit.
+ admit.
+ admit.
+ admit.

rewrite cancel_toColVectors_ofcols 1,2://.
+ admit.
+ admit.

pose v := fun i => nth witness m'vs i + nth witness (toRowVectors e') i.

rewrite /tolist.
rewrite map_flatten -!map_comp /(\o) /= .

have -> : (fun x => map (fun c => int2bs B (dc c)) (map (get (v x)) (range 0 (size (v x)))))
     = (fun x => map (fun i => int2bs B (dc (get (v x) i))) (range 0 Mb)).
+ admit.

rewrite /=.
rewrite /flatten.
rewrite foldr_map /=.

have -> : (fun x z => map (fun i => int2bs B (dc (v x).[i])) (range 0 Mb) ++ z)
        = (fun x z => map (fun i => int2bs B (dc (ZR.(+) (nth witness m'vs x).[i] (nth witness (toRowVectors e') x).[i]))) (range 0 Mb) ++ z).
        rewrite fun_ext => x.
        rewrite fun_ext => z.
        congr. congr.
        rewrite fun_ext => i.
        congr. congr. by rewrite get_addv.


rewrite /m'vs.
pose vs := chunk _ _.
admit.
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
