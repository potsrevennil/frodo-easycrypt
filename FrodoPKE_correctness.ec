require import AllCore Real List IntDiv.
require (****) LWE_correctness DynMatrix.
require import ZModP.
require import Array.
require import BitEncoding.
(*---*) import BS2Int.
(*---*) import BitChunking.
require import StdOrder.
(*---*) import RField IntOrder RealOrder.

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

require Word.

clone import Word as W8 with
  type Alphabet.t <- bool,
  op n <- 8
  proof ge0_n by trivial
  proof getE, setE.

realize getE.
proof.
move => *.
by rewrite /(_.[_]).
qed.
realize setE.
proof.
move => *.
by rewrite /(_.[_<-_]).
qed.

op tobytes (xs: bool list): W8.word list = map W8.mkword (chunk W8.card xs).


op CDF_table: int list.

op lenSE: { int | 0 <= lenSE } as ge0_lenSE.
op lenX: int = size CDF_table.
op SHAKE (m: W8.word list, outlen8:int): bool list.

abstract theory FrodoPKE.

abbrev mask5f = W8.mkword (int2bs W8.card 95) (* 95 = 0x5f *).
abbrev mask96 = W8.mkword (int2bs W8.card 150) (* 150 = 0x96 *).

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

op ec : int -> R.
op dc : R -> int.

op max_noise: int.
op under_noise_bound : R -> int -> bool.

axiom good_dc (k: int) (e: R):
     0 <= k < (2^B)
  => under_noise_bound e max_noise
  => dc (ec k + e) = k.

op m_encode_BV (pt: bool list list) : vector =
  let ks = map (fun bs => ec (bs2int bs)) pt in
  offunv (fun i => nth witness ks i, size pt).

op m_decode_BV (v: vector) c: bool list list =
  let dc' = fun c => int2bs B (dc c) in
  map dc' (tolist (subv v 0 c)).

lemma lt_le_addr_gt0 x y: 0 < x => 0 <= y => 0 < x + y.
proof.
smt().
qed.

lemma max_eq_ge0 x: 0 <= x => max 0 x = x.
proof. smt(). qed.

lemma max_eq_gt0 x: 0 < x => max 0 x = x.
proof. smt(). qed.

hint simplify (max_eq_ge0, max_eq_gt0).
hint exact: max_eq_ge0 max_eq_gt0.

lemma size_decode_encode_BV (s: bool list list) (ev: vector):
    size (m_decode_BV (m_encode_BV s + ev) (size s)) = size s.
proof.
  rewrite /m_decode_BV /m_encode_BV /=.
  by rewrite size_map size_tolist.
qed.

hint simplify size_decode_encode_BV.
hint exact: size_decode_encode_BV.
  
lemma good_m_decode_BV (pt: bool list list) (ev: vector):
    all (fun (bs: bool list) => size bs = B) pt =>
    (forall i, 0 <= i && i < size pt => under_noise_bound ev.[i] max_noise) =>
    m_decode_BV (m_encode_BV pt + ev) (size pt) = pt.
proof.
move :ev.
elim pt.
+ move => /= ev ?.
  rewrite /m_decode_BV /=.
  rewrite (emptyv_unique (subv _ _ _)) 1:/# /= => *.
  by rewrite -map_comp size_emptyv range_geq.
+ move => p pt h_rec ev h0 h1.
  apply (eq_from_nth witness).
  + done.
  + move => i [#].
    rewrite size_decode_encode_BV => *.
    have {3}<- /= := h_rec (subv ev 1 (1+size pt)) _ _; 1,2: by smt(get_subv).
    case (i = 0) => /= [*|hi].
    + subst i => /=.
      rewrite /m_encode_BV /m_decode_BV /=.
      rewrite (nth_map witness) /=.
      + rewrite size_tolist size_subv 1:/#.
      rewrite nth_tolist /= 1:/# get_subv 1://= get_addv get_offunv 1://= /=.
      have ^ hp <-: size p = B; 1: by smt().
      rewrite good_dc.
      + by rewrite bs2int_ge0 -hp bs2int_le2Xs.
      + by apply h1.
      by rewrite bs2intK /=.
    + rewrite /m_encode_BV /m_decode_BV /=.
      rewrite -!map_comp /(\o) /=.
      rewrite !(nth_map witness) 1,2:size_range 1,2:/# /=.
      rewrite !nth_range 1,2:/#.
      rewrite !get_subv 1..3:/= 1,2:/# !get_addv !get_offunv 1..3:/# /= => /#.
qed.

op m_encode_B (pt: bool list list list) r c: matrix =
  trmx (ofcols c r (map m_encode_BV pt)).

op m_decode_B (m: matrix) r c: bool list list list =
  map (fun v => m_decode_BV v c) (toRowVectors (subm m 0 r 0 c)).

lemma size_decode_encode_B (s: bool list list list) (e: matrix) c:
    size (m_decode_B (m_encode_B s (size s) c + e) (size s) c) = size s.
proof.
  rewrite /m_decode_B /m_encode_B /=.
  rewrite -map_comp /(\o) /=.
  rewrite size_map size_range // max_eq_ge0 1:/# //.
qed.

hint simplify size_decode_encode_B.
hint exact: size_decode_encode_B.

lemma subv_row m i c:
    cols m = c =>
    row m i = subv (row m i) 0 c.
proof.
move => <-.
rewrite eq_vectorP size_row size_subv => /> *.
rewrite get_subv /#.
qed.

lemma subm_addm (m1 m2:matrix) r1 r2 c1 c2:
    subm (m1+m2) r1 r2 c1 c2 = subm m1 r1 r2 c1 c2 + subm m2 r1 r2 c1 c2.
proof.
rewrite eq_matrixP size_addm !size_subm => /> *.
rewrite get_addm !get_subm 1..6:/#.
by rewrite get_addm.
qed.

lemma good_m_decode_B (pt: bool list list list) (e: matrix) c:
    0 <= c =>
    all (fun (p: bool list list) => size p = c ) pt =>
    all (all (fun (bs: bool list) => size bs = B)) pt =>
    (forall i j, 0 <= i && i < (size pt) && 0 <= j && j < c => under_noise_bound e.[i, j] max_noise) =>
    m_decode_B (m_encode_B pt (size pt) c + e) (size pt) c = pt.
proof.
move :e c.
elim pt.
+ move => *.
  by rewrite -size_eq0 size_decode_encode_B.
+ move => p pt h_rec e c ? h0 h1 h2.
  apply (eq_from_nth witness).
  + done.
  + rewrite size_decode_encode_B => i /= *.
    have hp0 : size p = c; 1: by smt().
    have hp1 : all (fun (bs: bool list) => size bs = B) p; 1: by smt().
    have hpt0 : all (fun (p: bool list list) => size p = c) pt; 1: by smt().
    have hpt1 : all (all (fun (bs: bool list) => size bs = B)) pt; 1: by smt(). 
    
    have {4}<- := h_rec (subm e 1 (1+size pt) 0 c) c _ _; 1..4:smt(get_subm).
    case (i = 0) => /= hi *.
    + subst i.
      rewrite /m_encode_B /m_decode_B -map_comp /(\o) /=.
      rewrite (nth_map witness) 1:size_range 1:/# /=.
      rewrite subm_addm rowD -submT row_trmx.
      rewrite nth_range 1:/# /=.
      have ->: col (subm (ofcols c (1+size pt) (m_encode_BV p :: map m_encode_BV pt)) 0 c 0 (1+size pt)) 0 = m_encode_BV p.
      + rewrite eq_vectorP size_col rows_subm.
        split => *.
        + rewrite /m_encode_BV /= /#.
        + rewrite get_col get_subm 1,2:/# get_offunm 1:/# //=.
      rewrite -{2}(good_m_decode_BV p (row (subm e 0 (1+size pt) 0 c) 0) _ _) 1://. 
      + move => i *. rewrite get_row get_subm 1,2:/# /=.
        rewrite (h2 0 i) 1:/#.
      congr => /#. 
    + rewrite /m_decode_B /m_encode_B /= -!map_comp /(\o) /=.
      rewrite !(nth_map witness) 1,2:size_range 1,2:/# /=.
      rewrite !nth_range 1,2:/# /=.
      congr.
      rewrite eq_vectorP.
      rewrite !size_row !cols_subm => /= *.
      rewrite !get_subm 1..4:/#.
      rewrite 2!get_addm get_subm 1,2:/# /=.
      rewrite !get_offunm 1,2:/# /= => /#.
qed.

lemma mem_chunk_all (xs: 'a list) c ys:
    0 <= c =>
    ys \in chunk c xs => all (fun y => y \in xs) ys.
proof.
rewrite allP /= => ?.
case (c = 0) => ?.
+ subst c. rewrite chunk_le0 1:// => /#.
+ rewrite (nthP witness).
  case => i.
  rewrite size_chunk 1:/# => [#] ? ?.
  rewrite /chunk nth_mkseq 1:/# /= => <- *.
  by rewrite (mem_drop (c*i)) (mem_take c).
qed.

lemma mem_chunk (xs: 'a list) c ys y:
    0 <= c =>
    y \in ys =>
    ys \in chunk c xs => 
    y \in xs.
proof.
move => *.
have := mem_chunk_all xs c ys _ _; 1,2: trivial.
rewrite allP /= => /#.
qed.

op m_encode (pt: bool list) r c: matrix =
  let pt' = chunk c (chunk B pt) in
  m_encode_B pt' r c.

op m_decode (m: matrix) r c: bool list =
  flatten (flatten (m_decode_B m r c)).

lemma good_m_decode (pt: bool list) (e: matrix) c:
  0 <= c =>
  (B * c) %| size pt =>
  (forall i j, 0 <= i && i < size pt %/ (B * c) && 0 <= j && j < c => under_noise_bound e.[i,j] max_noise) =>
  m_decode (m_encode pt (size pt %/ (B*c)) c + e) (size pt %/ (B*c)) c = pt.
proof.
pose r := size pt %/ (B*c).
move => *.
case (c = 0) => ?.
+ subst c.
  have ? : pt = [].
  + rewrite -size_eq0 -dvd0z => /#.
  subst pt => /=.
  rewrite /m_decode /m_encode /= /m_encode_B /m_decode_B /=.
  rewrite ofcols_zerom_tr -map_comp rows_subm /r /=.
  by rewrite range_geq 1:// /= !flatten_nil.
+ have hr: size pt = B*r*c.
  + rewrite [B*_]mulzC mulzA eqz_mul 1: mulf_neq0 1:lt0r_neq0 1..6://=.

rewrite /m_encode /m_decode /=.
have := (good_m_decode_B (chunk c (chunk B pt)) e c _ _ _ _).
+ trivial.
+ by rewrite allP /= => ?; apply in_chunk_size => /#. 
+ rewrite allP => xs *.
  rewrite allP /= => x *.
  have : x \in (chunk B pt); 1: by smt(mem_chunk).
  by apply in_chunk_size.
+ rewrite !size_chunk 1:/# 1:// -divz_mul 1:// => /#.

+ rewrite !size_chunk 1,2:/# -divz_mul 1:// -/r => ->.
  rewrite !chunkK 1,3:/# //=.
  + by rewrite size_chunk 1:// hr mulzA mulKz 1:lt0r_neq0 1,2:// dvdz_mull dvdzz.
  + by rewrite hr mulzA dvdz_mulr dvdzz.
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
  op m_encode <- fun pt => m_encode pt Mb Nb,
  op m_decode <- fun m => m_decode m Mb Nb,
  op c_encode <- idfun,
  op c_decode <- idfun, 
  op prg_kg <- prg_kg,
  op prg_enc <- fun (r: matrix * bool list) => prg_enc r.`2,
  op valid_plaintext <- fun (m: bool list) => size m = B*Mb*Nb,
  op max_noise <- max_noise,
  op under_noise_bound <- fun (m: matrix) (max_noise: int) => forall i j, 0 <= i && i <= Mb && 0 <= j && j <= Nb => under_noise_bound m.[i,j] max_noise,
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
move => *.
rewrite /m_encode /m_encode_B /=.
by rewrite cols_offunm.
qed.

realize m_encode_cols.
proof.
move => *.
rewrite /m_encode /m_encode_B /=.
by rewrite rows_offunm.
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
move => pt e hpt.
have -> h : Mb = size pt %/ (B*Nb).
+ rewrite hpt mulzA -[Mb*_]mulzC -mulzA mulKz 1:lt0r_neq0 1:mulr_gt0 1..4://.
apply good_m_decode => //.
+ rewrite hpt mulzA [Mb*_]mulzC -mulzA dvdz_mulr dvdzz.
+ rewrite /#.
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

section.

op round (x: real): int = floor (x + inv 2%r).

(* -------------------------------------------------------------------- *)
lemma floor_add_lt1 x y: 0%r <= y < 1%r => floor (x%r + y) = x.
proof. by move=> rg; rewrite floorP /#. qed.

lemma round_fromint x : round x%r = x.
proof. by rewrite /round floor_add_lt1 /#. qed.

lemma round_id k x : -1%r/2%r <= x < 1%r/2%r => round (k%r + x) = k.
proof. by move=> ? @/round; rewrite -addrA floor_add_lt1 //#. qed.

lemma round_eq x y: round (x + y%r) = round x + y.
proof.
by rewrite /round -addrA [y%r+_]addrC addrA from_int_floor_addr.
qed.

(* -------------------------------------------------------------------- *)
lemma ge0_B : 0 <= B.
proof. smt(B_bound). qed.

hint exact : ge0_B.

(* -------------------------------------------------------------------- *)
hint simplify eq_fromint, lt_fromint, le_fromint.

(* -------------------------------------------------------------------- *)
lemma gt0_exp2 n : 0 < 2^n.
proof. by rewrite expr_gt0. qed.

hint exact : gt0_exp2.

lemma gt0_q : 0 < q.
proof. by solve. qed.

hint exact : gt0_q.

lemma ge0_q : 0 <= q.
proof. by smt(gt0_q). qed.

hint exact : ge0_q.

lemma nz_q : q <> 0.
proof. by rewrite expf_eq0. qed.

hint exact : nz_q.

(* -------------------------------------------------------------------- *)
(* 0 <= k < 2^B. *)
op ec' (k : int) = k * q %/ 2^B. 
op dc' (c : int) = round (c%r * (2^B)%r / q%r) %% 2^B.

lemma dvd_2XB_2XD : 2^B %| 2^D.
proof. by apply/dvdz_exp2l; smt(B_bound). qed.

hint exact : dvd_2XB_2XD.

lemma good_dc k e:
     0 <= k < (2^B)
  => (-q%r/(2^(B+1))%r) <= e%r < q%r/(2^(B+1))%r
  => dc' ((ec' k) + e) = k.
proof.
case=> [ge0_k ltk] [hge glt] @/dc' @/ec' @/q.
rewrite divMr // -fromintM mulrDl -mulrA divzK //.
rewrite fromintD mulrDl fromintM mulrK ?eq_fromint //.
rewrite round_id -1: pmod_small //. split.
- rewrite -/q ler_pdivl_mulr //= [_*q%r]mulrC mulrN.
  rewrite fromintM -ler_pdivr_mulr //= !mulNr.
  by rewrite -mulrA -invfM -fromintM -exprS.
- move=> _; rewrite ltr_pdivr_mulr //= -/q fromintM.
  rewrite -ltr_pdivl_mulr // -mulrA -invfM.
  by rewrite -fromintM -exprS.
qed.

end section.

clone FrodoPKE as FrodoPKE_ with
  op dc <- fun c => dc' (asint c),
  op ec <- fun k => inZq (ec' k),
  op max_noise <- q%/2^B,
  op under_noise_bound <- fun (e: Zq) (max_noise: int) => -(max_noise%r/2%r) <= (asint e)%r < max_noise%r/2%r,
  theory DM.ZR <- ZModpRing
  proof good_dc.

realize good_dc.
proof.
move => k e h0 h1.
rewrite fromint_div 1://= -mulrA -invfM -fromintM mulzC -exprS 1:// in h1.
rewrite addE inZqK modzDml modzE /dc'.
rewrite fromintD -mulrA mulrDl !mulrA.
rewrite -[(-_ %/ _ * q)%r * (2^B)%r]fromintM.
rewrite -mulNr -[_*q*_]mulrA [q*_]mulzC mulrA.
rewrite -[(_ * q)%r / _]fromint_div.
+ rewrite dvdz_mull dvdzz.
rewrite mulzK 1:// round_eq modzMDr -/(dc' _).
by rewrite good_dc.
qed.
