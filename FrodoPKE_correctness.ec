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

lemma gt0_B: 0 < B.
proof. by smt(B_bound). qed.

hint exact: gt0_N gt0_Nb gt0_Mb D_bound B_bound gt0_B.
hint simplify (gt0_N, gt0_Nb, gt0_Mb, D_bound, B_bound, gt0_B).
op CDF_table: int list.

op lenSE: { int | 0 <= lenSE } as ge0_lenSE.
op lenX: int = size CDF_table.
op SHAKE (m: W8.t list, outlen8:int): bool list.

abstract theory FrodoPKE.

abbrev mask5f = W8.of_int 95 (* 95 = 0x5f *).
abbrev mask96 = W8.of_int 150 (* 150 = 0x96 *).

clone DynMatrix as DM.
clone Dmatrix as Dmatrix_ with
  theory DM <- DM.

section.

import DM.
import DM.ZR.
import Dmatrix_.

op toRowVectors (m: matrix): vector list =
  map (row m) (range 0 (rows m)).

op toColVectors (m: matrix): vector list =
  map (col m) (range 0 (cols m)).

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

lemma chunknil ['a] x: chunk x [<:'a>] = [<:'a list>].
proof.
rewrite /chunk /=.
exact mkseq0.
qed.

hint simplify chunknil.

op ec (k: int): R = ZR.ofint (k * q %/ (2^B)).
op dc (c : R): int.

op max_noise: int.
op under_noise_bound : R -> int -> bool.

axiom good_dc (k: int) (e: R):
     0 <= k < (2^B)
  => under_noise_bound e max_noise
  => dc (ec k + e) = k.

op m_encode_B (pt: bool list list) (c: int): matrix =
  let ks = map (fun bs => ec (bs2int bs)) pt in
  offunm (fun i j => nth witness ks (i * c + j), size pt %/ c, c).

op m_decode_B (m: matrix): bool list list =
  let dc' = fun c => int2bs B (dc c) in
  map dc' (flatten (map tolist (toRowVectors m))).

lemma good_m_decode_B0 (e: matrix) c:
    forall r,
    c <= 0 =>
    size e = (r, c) =>
    m_decode_B (m_encode_B [] c + e) = [].
proof.
move => ? [#] *.
rewrite /m_encode_B /m_decode_B /=.
rewrite -size_eq0 size_map.
rewrite -map_comp !rows_offunm /=.
rewrite (EclibExtra.size_flatten' 0). 
+ move => ?.
  rewrite mapP.
  case => ? [#] /= ? ->.
  rewrite size_tolist size_row cols_addm cols_offunm. 
  smt().
+ smt().  
qed.

lemma splitP (pt: 'a list) r c : 0 <= r => 0 <= c =>
    size pt = (r + 1) * (c + 1) =>
    (head witness pt :: take c (behead pt)) ++ drop (c+1) pt = pt.
proof.
move => ? ? hpt.
have <- := EclibExtra.behead_take (c+1) pt. 
have -> : head witness pt = head witness (take (c+1) pt); 1: by smt().
rewrite (head_behead _ witness) 1:/#.
rewrite cat_take_drop => /#.
qed.

lemma good_m_decode_B (pt: bool list list) (e: matrix) c:
    forall (r: int),
    0 < r =>
    size pt = r * c =>
    all (fun (bs: bool list) => size bs = B) pt =>
    size e = (r, c) =>
    (forall i j, mrange e i j => under_noise_bound e.[i,j] max_noise) =>
    m_decode_B (m_encode_B pt c + e) = pt.
proof.
move :c pt e.
elim /natind.
+ move => c ? pt e r ? h0 ? [#] h1 ?.
  have -> : pt = [].
  + rewrite -size_eq0.
    apply ler_asym.
    rewrite size_ge0 /= h0 -h1.
    rewrite mulr_ge0_le0 1:rows_ge0 1://.
  by rewrite (good_m_decode_B0 _ _ r).
+ move => c ? h_rec0 pt e r.
  move :r pt e.
  elim /natind => [r |r ? h_rec1 pt e ?].
  + smt().
  + rewrite /m_decode_B /m_encode_B -!map_comp /(\o) /=.
    rewrite !rows_offunm allP /= => ^ hpt0 -> hpt1 he ?.
    rewrite mulzK 1:addz1_neq0 1,2://.
    pose vs := map _ (range _ _).
    have hvs0 : all (fun (v: R list) => size v = c + 1) vs.
    + rewrite allP => ?.
      rewrite mapP.
      case => ? [#] /= ? ->.
      by rewrite size_tolist size_row cols_addm cols_offunm => /#.
    have hvs1 : size (flatten vs) = (r+1) * (c+1).
    + rewrite (EclibExtra.size_flatten' (c+1)) 1:-allP 1://. 
      rewrite size_map size_range.
      smt().
  have hp : size (head witness pt) = B; 1: by apply hpt1 => /#.
  have <- := splitP pt r c _ _ _; 1..3 : trivial.

  have <- : head witness (map (fun c => int2bs B (dc c)) (flatten vs)) = head witness pt.
  + rewrite -nth0_head (nth_map witness) /= 1:/# (nth_flatten witness (c+1)) 1:// /=.
    rewrite (nth_map witness) 1:size_range 1:/# nth_range 1:/# /=.
    rewrite (nth_tolist witness) 1:/= 1:!cols_offunm 1:/# get_row.
    do 2! rewrite get_offunm 1:/# /=.
    rewrite (nth_map witness) 1:/# nth0_head /= good_dc.
    + by rewrite bs2int_ge0 -hp bs2int_le2Xs.
    + smt().
    by rewrite -hp bs2intK /=.

  have <- : take c (behead (map (fun c => int2bs B (dc c)) (flatten vs))) = take c (behead pt). 
  + rewrite EclibExtra.behead_map.
    have <- := h_rec0 (take c (behead pt)) (subm e 0 1 1 (c+1)) 1 _ _ _ _ _; 1:trivial.
    + by rewrite size_take 1:// EclibExtra.size_behead => /#.
    + rewrite allP => /= *.
      by apply /hpt1/mem_behead/(mem_take c).
    + by rewrite size_subm => /#.
    + by move => i j; smt(get_subm).

    rewrite /m_encode_B /m_decode_B /= -!map_comp /(\o) /= !rows_offunm size_take 1:// !EclibExtra.size_behead hpt0.
    have ^ hc -> : (if c < max 0 ((r+1)*(c+1)-1) then c else max 0 ((r+1)*(c+1)-1)) = c; 1: by smt().
    rewrite divzz.
    pose vs' := map _ (range _ _).
    have hvs'0 : all (fun (v: R list) => size v = c) vs'.
    + rewrite allP => /= ?.
      rewrite mapP.
      case => ? [#] /= ? ->.
      rewrite size_tolist size_row !cols_offunm => /#.
    have hvs'1 : size vs' = 1.
    + rewrite size_map size_range => /#.
    have hvs'2 : size (flatten vs') = c.
    + rewrite (EclibExtra.size_flatten' c) 1:-allP 1,2:/#.

    apply (eq_from_nth witness).
    + by rewrite size_take 1:// !size_map EclibExtra.size_behead hvs1 hvs'2 hc.
    + move => i [#].
      rewrite size_take 1:// size_map EclibExtra.size_behead hvs1 hc /= => *.
      rewrite nth_take 1,2://.
      rewrite !(nth_map witness) 1:EclibExtra.size_behead 1,2:/# /=.
      congr. congr.
      rewrite nth_behead 1://.
      rewrite (nth_flatten witness (c+1)) 1://.
      rewrite (nth_flatten witness c) 1://.
      rewrite !pdiv_small 1,2:/# !modz_small 1,2:/#.
      rewrite !(nth_map witness) 1..4:size_range 2,4: size_row 2,4:!cols_offunm 1..4:/# /=.
      rewrite !nth_range 2,4: !cols_offunm 1..4: /# /=.
      rewrite !get_offunm 1,2:!rows_offunm 1,2:!cols_offunm 1,2:/# /=.
      rewrite !get_offunm 1,2:!rows_offunm 1,2:!cols_offunm 1..3:/# /=.
      rewrite !(nth_map witness) 2: size_take 3: EclibExtra.size_behead 1..3:/#.
      congr. congr. rewrite nth_take 1,2://.
      by rewrite nth_behead 1://.

  have <- : drop (c+1) (map (fun c => int2bs B (dc c)) (flatten vs))
         = drop (c+1) pt.
  + case (r = 0) => *.
    + subst r.
      by rewrite !drop_oversize 1:size_map 1,2:/#.
    + have <- := h_rec1 (drop (c+1) pt) (subm e 1 (r+1) 0 (c+1)) _ _ _ _ _; 1: by smt().
      + rewrite size_drop 1,2:/#.
      + by rewrite allP /= => *; apply /hpt1/(mem_drop (c+1)).
      + rewrite size_subm /#.
      + move => i j. rewrite rows_subm cols_subm /= => [#] *. rewrite get_subm 1,2:/# /#.

      rewrite /m_encode_B /m_decode_B -map_comp /(\o) /=.
      rewrite !rows_offunm size_drop 1:/#.
      have h0 : (r+1)*(c+1) - (c+1) = r * (c+1); 1: by smt().
      have -> : (max 0 (size pt - (c+1)) %/ (c+1)) = r.
      + rewrite hpt0 h0 => /#.

      pose vs' := map _ (range _ _).
      have hvs'0 : all (fun (v: R list) => size v = c + 1) vs'.
      + rewrite allP /= => ?.
        rewrite mapP.
        case => ? /= [#] ? ->.
        rewrite size_tolist size_row !cols_offunm => /#.
      have hvs'1 : size vs' = r.
      + by rewrite size_map size_range /#.
      have hvs'2 : size (flatten vs') = r * (c+1).
      + by rewrite (EclibExtra.size_flatten' (c+1)) 1:-allP 1:// hvs'1 => /#.
  
      apply (eq_from_nth witness).
      + rewrite size_drop 1:/# !size_map hvs1 hvs'2 => /#.
      + move => i [#].
        rewrite size_drop 1:/# size_map hvs1 h0 lez_maxr 1:/# => *.
        rewrite nth_drop 1:/# 1://.
        rewrite !(nth_map witness) 1,2:/# /=.
        congr. congr.
        rewrite !(nth_flatten witness (c+1)) 1,2://.
        rewrite dvdz_modzDl 1:dvdzz.
        rewrite divzDl 1:dvdzz.
        have -> : (c+1) %/ (c+1) = 1; 1: by smt(divzz).
        have ?: i %/ (c+1) < r; 1: by rewrite ltz_divLR 1:/#.
        rewrite !(nth_map witness) 1..4:size_range 2,4:size_row 2,4:!cols_offunm 1..4:/# /=.
        rewrite !cols_offunm !nth_range 1..4:/# /=.
        rewrite !get_offunm 1,2:!rows_offunm 1,2:!cols_offunm 1,2:/# /=.
        rewrite !get_offunm 1,2:!rows_offunm 1,2:!cols_offunm 1..3:/# /=.
        congr; 2: smt().
        rewrite !(nth_map witness) 2:size_drop 1..3:/# /=.
        congr. congr.
        rewrite nth_drop 1,2:/# => /#.
  by rewrite (splitP _ r c) 3:size_map 1..3://.  
qed.
    


op m_encode (pt: bool list): matrix =
  m_encode_B (chunk B (take (B*Mb*Nb) pt)) Nb.

op m_decode (m: matrix): bool list =
  flatten (m_decode_B m).

lemma good_m_decode (pt: bool list) (e: matrix):
  (forall i j, mrange e i j => under_noise_bound e.[i,j] max_noise) =>
  m_decode (m_encode pt + e) = pt.
proof.
move => ?.
rewrite /m_encode /m_decode. 
pose pt' := chunk _ _.
rewrite (good_m_decode_B pt' e Nb Mb) 1,5://.
+ admit.
+ admit.
+ admit.
+ admit.
qed.

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
    LWE_.H_cols,
    good_m_decode.

realize m_encode_rows.
proof.
admit.
qed.

realize m_encode_cols.
proof.
admit.
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
