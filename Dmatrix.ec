require import AllCore Distr List.
require import Distrmatrix.
require import DList.
import StdOrder.IntOrder.
(*****) import DM.

export DM.

lemma max_eq x: max x x = x.
proof. done. qed.

lemma min_eq x: min x x = x.
proof. done. qed.

hint simplify (max_eq,min_eq).


lemma supp_dmatrix_tr m d r c: 0 <= r => 0 <= c =>
    m \in dmatrix d r c =>
    trmx m \in dmatrix d c r.
proof.
move => ? ? ^ ?.
rewrite !supp_dmatrix 1..4:/# => *.
rewrite size_tr => /#.
qed.

hint exact: supp_dmatrix_tr.
hint simplify supp_dmatrix_tr.

lemma dmatrix_tr1E (m: matrix) d r c: 0 <= r => 0 <= c =>
    size m = (r, c) =>
    mu1 (dmatrix d r c) m = mu1 (dmatrix d c r) (trmx m).
proof.
move => *.
rewrite {1}(dmatrix_cols d r c) // (dmatrix_rows d c r) //.
rewrite !dmapE /(\o) //=.
by smt(trmxK).
qed.

lemma trmx_cancel m : trmx (trmx m) = m.
proof. by rewrite trmxK. qed.

hint exact: trmx_cancel.
hint simplify trmx_cancel.

lemma catmr_empty a b m n d: 0 <= m => 0 <= n => a \in dmatrix d m n => b \in dmatrix d m 0 => (a || b) = a.
proof.
move => *.
rewrite /catmr.
have [#] ^ ? -> ^ ? -> := size_dmatrix d m n a _ _ _; 1..3: by trivial.
have [#] ^ ? -> ^ ? -> := size_dmatrix d m 0 b _ _ _; 1..3: by trivial.
rewrite eq_sym eq_matrixP.
split => [|i j [#] *].
+ rewrite size_offunm /#.
+ rewrite get_offunm 1:/# => //=.
  smt(getm0E ZR.addr0).
qed.

lemma dmatrix_dvector1E d (m: matrix) r c:
    0 <= r
    => 0 <= c
    => size m = (r + 1, c)
    => mu1 (dmatrix d (r + 1) c) m = mu1 (dmatrix d r c `*` dvector d c) (subm m 0 r 0 c, row m r).
proof.
move => ? ? [#] *.
rewrite dmatrix_tr1E 1:/# //.
rewrite dmatrixRSr1E //.
rewrite !dprod1E -submT.
rewrite dmatrix_tr1E //; 1: by rewrite size_tr rows_subm cols_subm /#.
qed.

lemma dlist_singleton1E d (x: 'a) :
    mu1 (dlist d 1) [x] = mu1 d x.
proof.
by rewrite (dlistS1E d x []) dlist0 // dunit1xx.
qed.

lemma subm_catmc m (r: int, r1: int ,r2:int, c1:int , c2: int):
    0 <= r1 => 0 <= r2 => 
    subm m r (r+r1) c1 c2 / subm m (r+r1) (r+r1+r2) c1 c2 =
    subm m r (r+r1+r2) c1 c2.
proof.
move => *.
rewrite eq_matrixP size_catmc size_subm rows_catmc cols_catmc !rows_subm !cols_subm => //= />.
split => [/#|i j *].
have ? : i < r1 + r2; 1: by rewrite /#.
have ? : j < c2 - c1; 1: by rewrite /#.
rewrite get_catmc rows_subm lez_maxr 1:/#.
case (i < r1) => *.
+ rewrite (getm0E (subm m (r+r1) _ _ _)) 1:/#.
  by rewrite !get_subm 1..4:/# ZR.addr0.
+ rewrite getm0E 1:/#.
  rewrite !get_subm 1..4:/# ZR.add0r => /#.
qed.

lemma subm_catmr m (r1: int, r2: int, c: int, c1: int, c2: int):
    0 <= c1 => 0 <= c2 =>
    (subm m r1 r2 c (c+c1) || subm m r1 r2 (c+c1) (c+c1+c2)) =
    subm m r1 r2 c (c+c1+c2).
proof.
move => *.
have -> : m = trmx (trmx m); 1: by trivial.
rewrite -!submT -catmcT.
congr.
by rewrite !submT subm_catmc.
qed.

lemma col_mul_eq m1 m2 i: m1 *^ col m2 i = col (m1 * m2) i.
proof.
rewrite eq_vectorP size_col size_mulmxv rows_mulmx /= => j [#] *.
by rewrite get_mulmxv get_mulmx.
qed.

lemma row_mul_eq m1 m2 i: row m1 i ^* m2 = row (m1 * m2) i.
proof.
rewrite eq_vectorP size_row size_mulvmx cols_mulmx /= => j [#] *.
by rewrite get_mulvmx get_mulmx.
qed.

lemma rcons_catmr (vs: vector list) (v: vector) r c:
    size vs = c =>
    size v = r =>
    0 <= c =>
    ofcols r (c + 1) (rcons vs v) = (ofcols r c vs || colmx v).
proof.
move => hvs *.
rewrite eq_matrixP size_catmr !rows_offunm !cols_offunm.
split => [/#| i j [#] *].
rewrite get_catmr get_offunm 1:/# /= nth_rcons hvs.
case (j < c) => *.
+ rewrite get_offunm 1:/#.
  rewrite getm0E => /=; 1: by rewrite cols_offunm => /#.
  by rewrite ZR.addr0.
+ have -> /=: j = c; 1: by rewrite /#.
  rewrite getm0E; 1: by rewrite rows_offunm cols_offunm /#.
  by rewrite cols_offunm lez_maxr 1:/# /= ZR.add0r.
qed.

lemma rcons_catmc (vs: vector list) (v: vector) r c:
    size vs = r =>
    size v = c =>
    0 <= r =>
    trmx (ofcols c (r+1) (rcons vs v)) = (trmx (ofcols c r vs) / rowmx v).
proof.
move => *.
by rewrite rcons_catmr.
qed.

lemma ofcols_colmx m r:
    rows m = r =>
    cols m = 1 =>
    ofcols r 1 [col m 0] = m.
proof.
move => <- h.
rewrite eq_matrixP /ofcols h => /> i j *.
have -> : j = 0; 1: by rewrite /#.
rewrite get_offunm /#.
qed.

lemma ofcols_rowmx m c:
    rows m = 1 =>
    cols m = c =>
    trmx (ofcols c 1 [row m 0]) = m.
proof.
move => h <-.
rewrite eq_matrixP /ofcols h => /> i j *.
have -> : i = 0; 1: by rewrite /#.
rewrite get_offunm /#.
qed.

lemma cons_catmr (vs: vector list) (v: vector) l:
    0 <= l =>
    ofcols l (size (v:: vs)) (v :: vs) = (ofcols l 1 [v] || ofcols l (size vs) vs).
proof.
move => *.
rewrite eq_matrixP size_catmr !rows_offunm !cols_offunm => />.
split => [| i j *].
+ rewrite !lez_maxr 1:addr_ge0 2,4:size_ge0 1..3:/#.
+ rewrite get_catmr get_offunm 1:/# /=.
  case (j = 0) => *.
  + rewrite get_offunm 1:/#.
    rewrite getm0E; 1: by rewrite rows_offunm cols_offunm => /#.
    rewrite ZR.addr0 /=. by subst j.
  + rewrite getm0E; 1: by rewrite rows_offunm cols_offunm => /#.
    rewrite ZR.add0r cols_offunm get_offunm => /#.
qed.

lemma ofcols_zerom r : ofcols r 0 [] = zerom r 0.
proof.
rewrite eq_matrixP => /> i j.
rewrite rows_offunm cols_offunm => /#.
qed.

lemma ofcols_zerom_tr r : trmx (ofcols r 0 []) = zerom 0 r.
proof.
by rewrite ofcols_zerom trmx_matrixc.
qed.

import StdBigop.Bigreal.BRM.
lemma dmatrixr01E d c m:
    0 <= c =>
    mu1 (dmatrix d 0 c) (subm m 0 0 0 c) = 1%r.
proof.
move => *.
have := (dmatrix1E d (subm m 0 0 0 c)).
rewrite rows_subm cols_subm /= !lez_maxr //.
by rewrite big_geq.
qed.

lemma drowmx1E d c (v: vector):
    0 <= c =>
    size v = c =>
    mu1 (dvector d c) v = mu1 (dmatrix d 1 c) (rowmx v).
proof.
move => *.
rewrite (dmatrix_dvector1E _ _ 0 _) // dprod1E rowK.
by rewrite dmatrixr01E.
qed.

lemma supp_drow d c m:
    0 <= c =>
    m \in dmatrix d 1 c => row m 0 \in dvector d c.
proof.
move => ?.
rewrite supp_dmatrix // supp_dvector => /#.
qed.

lemma supp_dmatrixr0 m d c: 0 <= c => m \in dmatrix d 0 c <=> m = zerom 0 c.
proof.
move => *.
rewrite supp_dmatrix 1, 2://.
split => [[#] *|-> /#].
+ rewrite eq_matrixP => /#.
qed.

lemma foo m (vs: vector list):
    m * ofcols (cols m) (size vs) vs = ofcols (rows m) (size vs) (map (fun v => m *^ v) vs).
proof.
elim vs.
+ rewrite /= !ofcols_zerom eq_matrixP size_mulmx cols_matrixc size_matrixc => /#.
+ move => v vs h.
  rewrite map_cons /= cons_catmr 1:cols_ge0.
  have -> : 1 + size vs = size ((m *^ v) :: map (fun v0 => m *^ v0) vs).
      by rewrite /= size_map.
  rewrite (cons_catmr _ _ (rows m)) 1:rows_ge0.
  rewrite catmrDr size_map -h.
  have -> //= : m * ofcols (cols m) 1 [v] = ofcols (rows m) 1 [m *^ v].
  + rewrite eq_matrixP size_mulmx !cols_offunm rows_offunm => /> i j.
    rewrite cols_offunm => *.
    have -> : j = 0; 1: by rewrite /#.
    rewrite get_offunm 1:/# /=.
    rewrite get_mulmx get_mulmxv.
    congr.

admit.
qed.

lemma dlist_dprod1E (d1: 'a distr) (d2: 'b distr) (xs: ('a*'b) list) n:
    0 <= n =>
    mu1 (dlist (d1 `*` d2) n) xs = mu1 (dlist d1 n `*` dlist d2 n) (unzip1 xs, unzip2 xs).
proof.
move => *.
rewrite dprod1E !dlist1E // !size_map //=.
case (n = size xs) => // *.
have -> : (fun (x: 'a * 'b) => mu1 (d1 `*` d2) x)
      = (fun (x: 'a * 'b) => mu1 d1 x.`1 * mu1 d2 x.`2);
  1: by smt(dprod1E).
rewrite big_split /big.
by rewrite !filter_map -!map_comp /preim /(\o) /=.
qed.

lemma dlist_dprodE (d1: 'a distr) (d2: 'b distr) n:
    0 <= n =>
    dlist (d1 `*` d2) n
  = dmap (dlist d1 n `*` dlist d2 n) (fun (abs: 'a list * 'b list) => zip abs.`1 abs.`2).
proof.
move => *.
rewrite eq_distr => abs'.
rewrite (in_dmap1E_can _ _ (fun (abs: ('a * 'b) list) => (unzip1 abs, unzip2 abs))) /=.
+ by rewrite zip_unzip.
+ move => ?.
  rewrite supp_dprod !supp_dlist // => [#] *.
  subst abs'.
  rewrite unzip1_zip 1:/# unzip2_zip 1:/# => /#.
by rewrite dlist_dprod1E.
qed.

lemma mulvmx_add_eq r b (vs: (vector * vector) list):
    0 <= r =>
    size vs = r =>
    all (fun (ac: vector * vector) => size ac.`1 = rows b) vs =>
    trmx (ofcols (rows b) r (unzip1 vs)) * b + trmx (ofcols (cols b) r (unzip2 vs))
  = trmx (ofcols (cols b) r (map (fun (ac: vector * vector) => ac.`1 ^* b + ac.`2) vs)).
proof.
move => *.
rewrite eq_matrixP size_addm size_mulmx size_tr rows_tr rows_offunm cols_offunm => /> i j.
rewrite rows_addm cols_addm rows_mulmx cols_mulmx !rows_tr cols_tr rows_offunm !cols_offunm /= => *.
rewrite get_addm get_mulmx trmxE /=.
rewrite !get_offunm 1,2:/# /=.
rewrite !(nth_map witness) 1,2:/# /=.
rewrite get_addv get_mulvmx.
rewrite col_ofcols 1:rows_ge0 // 2:size_map 1..2:/#.
+ by rewrite all_map.
by rewrite (nth_map witness) 1:/#.
qed.

lemma trmx_eq m1 m2: trmx m1 = trmx m2 <=> m1 = m2.
proof.
split => [h|-> //].
by rewrite -trmxK h trmxK.
qed.

lemma all_support_dprod d1 d2 xs:
    all (support (d1 `*` d2)) xs = (all (fun (x: 'a * 'b) => x.`1 \in d1) xs /\ all (fun (x: 'a * 'b) => x.`2 \in d2) xs).
proof.
rewrite -all_predI.
smt(supp_dprod).
qed.

lemma dmulvmx1E d r b m:
    0 <= r =>
    m \in dmap (dlist (dvector d (rows b)) r)
      (fun (va: vector list) =>
        trmx
          (ofcols (cols b) r
            (map (fun (a: vector) => a ^* b) va))
      ) =>
    mu1 (dmap (dlist (dvector d (rows b)) r)
      (fun (va: vector list) =>
        trmx
          (ofcols (cols b) r
            (map (fun (a: vector) => a ^* b) va))
      )) m
  = mu1 (dmap (dmatrix d r (rows b))
      (fun (a: matrix) => a * b)) m.
proof.
move => ?.
rewrite supp_dmap. case => va [#] /= *.
rewrite dmatrix_rows 1:rows_ge0 // dmap_comp.
rewrite !dmap1E /pred1 /(\o) /=.
congr.
rewrite fun_ext => va'.
admit.
qed.

lemma mulvmx_eq r b va:
    0 <= r =>
    trmx (ofcols (rows b) r va) * b = trmx (ofcols (cols b) r (map (fun a => a ^* b) va)).
proof.
move => *.
rewrite eq_matrixP size_mulmx size_tr rows_tr !cols_offunm rows_offunm => /> i j.
rewrite cols_offunm => *.
rewrite get_mulmx /=.
rewrite get_offunm 1:/# /=.
admit.
qed.

lemma ofcols_inj m n (v1 v2 : vector list) : 0 <= m => 0 <= n =>
     size v1 = m
  => size v2 = n
  => (forall x, x \in v1 => size x = n)
  => (forall x, x \in v2 => size x = n)
  => ofcols m n v1 = ofcols m n v2
  => v1 = v2.
proof. admitted.

lemma dmulvmx_add1E d r b m:    0 <= r =>
    m \in dmap (dlist (dvector d (rows b) `*` dvector d (cols b)) r)
      (fun (acs: (vector * vector) list) =>
        trmx
          (ofcols (cols b) r
            (map (fun (ac: vector * vector) => ac.`1 ^* b + ac.`2) acs))
      ) =>
    mu1 (dmap (dlist (dvector d (rows b) `*` dvector d (cols b)) r)
      (fun (acs: (vector * vector) list) =>
        trmx
          (ofcols (cols b) r
            (map (fun (ac: vector * vector) => ac.`1 ^* b + ac.`2) acs))
      )) m
  = mu1 (dmap (dmatrix d r (rows b) `*` dmatrix d r (cols b))
      (fun (ac: matrix * matrix) => ac.`1 * b + ac.`2)) m.
proof.
move => ?.
rewrite supp_dmap; case => acs' [#] /= h *.
rewrite !dmatrix_rows 1:rows_ge0 // 1:cols_ge0 //.
rewrite (dmap_dprod (dlist _ r)) dmap_comp /(\o) /=.
rewrite dlist_dprodE // dmap_comp /(\o) /=.
rewrite !dmap1E /pred1 /(\o) /=.
subst m.
move :h.
rewrite supp_dlist // all_support_dprod => [#] ? h *.
have h': all (fun (x: vector * vector) => size x.`1 = rows b) acs'.
+ move : h.
  have -> : (fun (x: vector * vector) => x.`1 \in dvector d (rows b)) = (fun (x : vector * vector) => size x.`1 = rows b /\ forall i, 0 <= i && i < rows b => x.`1.[i] \in d); 1: by smt(supp_dvector).
  rewrite all_predI => /#.

rewrite -{2}(mulvmx_add_eq _ _ _ _ _ h') //.
apply: mu_eq_support => /= -[v1 v2].
move/supp_dprod => /= [v1_supp v2_supp].
have sz_v1 := supp_dlist (dvector d (rows b)) r v1 //.
have sz_v2 := supp_dlist (dvector d (cols b)) r v2 //.
apply: eq_iff; split=> eq.
- rewrite -{2 5}[b]trmxK -2!trmxM -2!trmxD; congr; move: eq.
  rewrite -mulvmx_add_eq 1://.
  - by rewrite size_zip /#.
  - apply/allP => -[x y] /mem_zip[/= + _].
    case: sz_v1 => /(_ v1_supp) + _ - [? /allP +] x_v1.
    by move=> /(_ x x_v1); smt(supp_dvector).
print supp_dvector.
  search trmx ofcols.

  move/trmx_inj: eq.
move/(ofcols_inj (cols b) r ).

congr.
rewrite fun_ext; case => a c /=.
rewrite (mulvmx_add_eq r b acs') //.
admit.
qed.

lemma all_rcons['a] (p: 'a -> bool) (ys: 'a list) y:
    all p (rcons ys y) <=> all p ys /\ p y.
proof.
by rewrite -all_rev rev_rcons /= all_rev. 
qed.

abstract theory SampleL.
type in_t.
type out_t.

module List = {
  proc sample(d: in_t distr, n, f): out_t list = {
      var r;

      r <$ dlist d n;
      return map f r;
  }
}.

module Rcons = {
  proc sample(d: in_t distr, n, f): out_t list = {
    var r, rs, rsf, rs';
    rs <$ dlist d (n - 1);
    rsf <- map f rs;
    r <$ d;
    rs' <- rcons rsf (f r);
    return rs';
  }
}.

module LoopRcons = {
  proc sample(d, n, f) : out_t list = {
    var i : int;
    var r : in_t;
    var l : out_t list;
    
    i <- 0;
    l <- [];
    while (i < n){
      r <$ d;
      l <- rcons l (f r);
      i <- i + 1;
    }
    
    return l;
  }
}.

lemma tuple_eq ['a 'b] (xy: 'a * 'b) : xy = (xy.`1, xy.`2).
proof.
rewrite /#.
qed.

lemma dlistSr1E ['a] (d: 'a distr) xs x:
    mu1 (dlist d (size (rcons xs x))) (rcons xs x) =
    mu1 (dlist d (size xs)) xs * mu1 d x.
proof.
by rewrite !dlist1E 1,2:size_ge0 size_rcons /= big_rcons.
qed.

lemma size_behead ['a] (xs: 'a list):
   0 < size xs =>
   size (behead xs) = size xs - 1.
proof.
rewrite /#.
qed.

lemma all_behead ['a] (xs: 'a list) p:
    all p xs => all p (behead xs).
proof. rewrite /#. qed.

abbrev belast' ['a] (xs: 'a list) = rev (behead (rev xs)).

lemma size_belast' (xs: 'a list): 0 < size xs => size (belast' xs) = size xs - 1.
proof.
smt(size_rev).
qed.

lemma belast'_rcons xs (x: 'a):
   belast' (rcons xs x) = xs.
proof.
by rewrite rev_rcons /= revK.
qed.

lemma rcons_belast' (xs: 'a list):
    0 < size xs =>
    rcons (belast' xs) (last witness xs) = xs.
proof.
smt(revK rev_cons last_rcons).
qed.

lemma List_Rcons_eq:
    equiv[ List.sample ~ Rcons.sample : 0 < n{1} /\ ={d, n, f} ==> ={res} ].
proof.
bypr res{1} res{2} => //= &1 &2 l [#] *.
byequiv => //.
proc; inline *. swap{2} 2 1; wp. 
rndsem*{2} 0.
rnd (fun (r: in_t list) => (belast' r, last witness r))
    (fun (rsr: in_t list * in_t) => rcons rsr.`1 rsr.`2).
auto => />.
split => *.
+ rewrite rev_rcons behead_cons revK last_rcons => /#.
split => [rsr h|? rs h].
+ have ? : size rsr.`1 = n{1} - 1.
  + smt (supp_dlet supp_dmap size_rcons supp_dlist_size).
  have -> : n{1} = size (rcons rsr.`1 rsr.`2).
  + smt (supp_dlet supp_dmap size_rcons supp_dlist_size).
  rewrite -dprod_dlet tuple_eq /= dprod1E dlistSr1E /#.
split.
+ rewrite -dprod_dlet supp_dprod /=. 
  smt(supp_dlist rcons_belast' all_rcons size_belast' last_rcons).
+ smt(dprod_dlet rcons_belast' supp_dlist map_rcons rcons_belast').
qed.

lemma List_LoopRcons_eq:
    equiv[ List.sample ~ LoopRcons.sample : ={d, n, f} ==> ={res} ].
proof.
exists* n{1}; elim*.
elim /natind => [_n ?|_n].
+ proc*; inline *. rcondf{2} 6; auto; smt(weight_dlist0 supp_dlist0).
+ case (_n = 0) => [hn ? ?|? ? h].
  + proc;inline *. rcondt{2} 3; 1: by auto => /#.
    rcondf{2} 6; 1: by auto => /#.
    wp; rnd (head witness) (fun x => [x]); auto => /> *.
    rewrite hn /=. split => [*|? l hl].
    + by rewrite dlist_singleton1E. 
    + rewrite (supp_dlist _ 1 l) // in hl.
      case hl => hl; rewrite size_eq1 in hl; elim hl => x ->.
      by rewrite head_cons.
  + transitivity Rcons.sample
                 (0 < n{1} /\ ={d, n, f} ==> ={res})
                 (_n + 1 = n{1} /\ ={d, n, f} /\ 0 < n{1} ==> ={res}); 1..2: by rewrite /#.
    + exact List_Rcons_eq.
    + proc; splitwhile{2} 3: (i < n - 1).
      rcondt{2} 4; 1: by auto; while (i < n); auto => /#.
      rcondf{2} 7; 1: by auto; while (i < n); auto => /#.
      wp. rnd. 
      outline{1} [1-2] <@ List.sample.
      rewrite equiv[{1} 1 h]; inline; wp.
      while (={i,d,l,f} /\ n0{1} = n{2} - 1 /\ d0{1} = d{1} /\ f0{1} = f{1});
      auto => /#.
qed.    
end SampleL.

abstract theory SampleM.

clone import SampleL with
    type in_t <- vector,
    type out_t <- vector
    proof *.

module Matrix = {
  proc sample(d, r, c): matrix = {
    var m;
    m <$ dmatrix d r c;
    return m;
  }

  proc matrix_mul_add (m1, m2: matrix, m3): matrix = {
    return m1 * m2 + m3;
  }

  proc vector_mul_matrix_add (m1, m2, m3): matrix = {
    var i, v, vs;
    i <- 0;
    vs <- [];

    while (i < max (rows m1) (rows m3)) {
        v <- row m1 i ^* m2 + row m3 i;
        vs <- rcons vs v;
        i <- i + 1;
    }

    return trmx (ofcols (max (cols m2) (cols m3)) (max (rows m1) (rows m3)) vs);
  }
}.

module VectorRows = {
  var vs: vector list
  var l: int

  proc sample(d, r, c): matrix = {
    var m;
    l <- c;
    vs <@ SampleL.List.sample(dvector d c, r, idfun);
    m <- trmx (ofcols c r vs);

    return m;
  }
}.

module VectorRowsLoopRcons = {
  var vs: vector list
  var l: int

  proc sample(d, r, c): matrix = {
    var m;
    l <- c;

    vs <@ SampleL.LoopRcons.sample(dvector d c, r, idfun);
    m <- trmx (ofcols c r vs);

    return m;
  }
}.

(*
lemma Matrix_VectorRows_eq :
equiv[ Matrix.sample ~ VectorRows.sample :
    0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==>
      ={res} /\
        all (fun (v: vector) => size v = VectorRows.l{2}) VectorRows.vs{2}
].
proof.
proc. inline sample. sp.
rndsem*{2} 0.
rnd (fun m => (map (row m) (range 0 r{1}), m)) snd => />.
+ move => //= &1 &2 [#] * /#. 
+ auto => /> &2 *.
  split => [mvs h|*].
  + rewrite supp_dmap in h.
    case h => vs [#] h -> /=.
    have ? : size vs = r{2}; 1: by rewrite (supp_dlist_size _ _ _ _ h).
    apply (eq_from_nth witness).
    + rewrite size_map size_range /#.
    + move => i [#] *.
      rewrite (nth_map witness witness) 1:size_range 1:/#.
      rewrite (nth_iota _ _ _ witness) 1:/# /=.
      admit.
  split => [mvs h|? m *].
  + admit.
  split => *.
  + admit.
  + admit.
qed.

lemma VectorRows_VectorRowsLoopRcons_eq :
equiv [ VectorRows.sample ~ VectorRowsLoopRcons.sample :
    0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==>
      ={res} /\
        all (fun (v: vector) => size v = VectorRowsLoopRcons.l{2}) VectorRowsLoopRcons.vs{2}
].
proof.
proc. wp.
rewrite equiv[{1} 2 List_LoopRcons_eq].
inline sample; wp.
+ while (={d0, l, i, n}
  /\ d0{2} = dvector d{2} c{2}
  /\ VectorRowsLoopRcons.l{2} = c{2}
  /\ 0 <= c{2}
  /\ all (fun (v: vector) => size v = VectorRowsLoopRcons.l{2}) l{2}
); auto => /> &2 ? ? ? ?.
by rewrite all_rcons supp_dvector.
qed.

lemma Matrix_VectorRowsLoopRcons_eq:
equiv[ Matrix.sample ~ VectorRowsLoopRcons.sample:
    0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==>
      ={res} /\
        all (fun (v: vector) => size v = VectorRowsLoopRcons.l{2}) VectorRowsLoopRcons.vs{2}
].
proof.
transitivity VectorRows.sample
    (0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==>
      ={res} /\
        all (fun (v: vector) => size v = VectorRows.l{2}) VectorRows.vs{2}
    )
    (0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==>
      ={res} /\
        all (fun (v: vector) => size v = VectorRowsLoopRcons.l{2}) VectorRowsLoopRcons.vs{2}
    ) => //; 1: by rewrite /#.
+ exact  Matrix_VectorRows_eq.
+ exact VectorRows_VectorRowsLoopRcons_eq.
qed.

import StdOrder.IntOrder.
lemma matrix_mul_add_eq:
    equiv[ Matrix.matrix_mul_add ~ Matrix.vector_mul_matrix_add: ={m1, m2, m3} ==> ={res} ].
proof.
bypr res{1} res{2} => // &1 &2 m' [#] -> -> ->.
byequiv => //.
proc; inline *.
while{2} (
  ={m1, m2, m3} /\
  0 <= i{2} /\
  size vs{2} = i{2} /\
  i{2} <= max (rows m1{2}) (rows m3{2}) /\
  subm (m1{1} * m2{1} + m3{1}) 0 i{2} 0 (max (cols m2{1}) (cols m3{1})) = trmx (ofcols (max (cols m2{2}) (cols m3{2})) i{2} vs{2})
)
(max (rows m1{2}) (rows m3{2}) - i{2}).
+ auto => /> &r ? ? h ?.
  rewrite size_rcons => />.
  rewrite rcons_catmc 1,3://; 1: by rewrite size_addv size_mulvmx size_row.
  rewrite row_mul_eq -rowD rowmx_row_eq_subm cols_addm cols_mulmx -h.
  rewrite (subm_catmc _ 0 (size vs{r}) 1 _ _) /#.
+ auto => />.
  split => [|vs]; [split|split => [/#|*]]. 
  + by rewrite (ler_trans (rows m1{2}) _ _) 1:rows_ge0 1:maxrl.
  + rewrite eq_matrixP size_subm cols_offunm rows_offunm /= => ? ? [#] *.
    by rewrite !getm0E 1..2:/#.
  + rewrite -[m1{2}*_+_]subm_id rows_addm rows_mulmx cols_addm cols_mulmx.
    have <- /#: size vs = max (rows m1{2}) (rows m3{2}); 1: by rewrite /#.
qed.
*)
end SampleM.

abstract theory SampleLWE.

clone import SampleL with
    type in_t <- vector*vector,
    type out_t <- vector
    proof *.

module LWE_M = {
  proc sample(d, r, b): matrix = {
    var a, c, m;
    a <$ dmatrix d r (rows b);
    c <$ dmatrix d r (cols b);
    m <- a * b + c;
    return m;
  }
}.

module LWE_M_Loop = {
  var vs: vector list
  var l: int

  proc sample(d, r, b): matrix = {
    var i, v, a, c, m;

    l <- cols b;
    vs <- [];
    i <- 0;
    while (i < r) {
      a <$ dvector d (rows b);
      c <$ dvector d (cols b);

      v <- a ^* b + c;
      vs <- rcons vs v;

      i <- i + 1;
    }

    m <- trmx (ofcols (cols b) r vs);
    return m;
  }

  proc sample'(d, r, b): matrix = {
    var m;

    l <- cols b;
    vs <@ LoopRcons.sample(dvector d (rows b) `*` dvector d (cols b), r,
      fun (ac: vector * vector) => ac.`1 ^* b + ac.`2);

    m <- trmx (ofcols (cols b) r vs);
    return m;

  }
}.


lemma dmatrixr0_ll d c: 0 <= c => is_lossless (dmatrix d 0 c).
proof.
move => *.
by rewrite dmatrix_rows // dmap_ll /is_lossless weight_dlist0.
qed.

lemma LWE_M_Loop_eq:
    equiv[ LWE_M.sample ~ LWE_M_Loop.sample': 0 <= r{1} /\ ={d, r, b} ==> ={res} ].
proof.
proc. rewrite equiv[{2} 2 -List_LoopRcons_eq].
inline *.
rndsem*{2} 0.
rndsem*{1} 0.
rnd.
auto => /> &2 *.
split => [*|? m].
rewrite dmulvmx_add1E // dprod_dlet dmap_dlet /=.
+ congr; congr; rewrite fun_ext => a.
  have -> : (fun (b: matrix) => dunit (a, b)) = dunit \o (fun b => (a, b)); 1: by done.
  rewrite dlet_dunit dmap_comp => />.
+ rewrite supp_dlet; case => a; case.
  rewrite dmatrix_rows 1:rows_ge0 // supp_dmap; case => va; case => /= hva ?.
  rewrite supp_dmap; case => c; case.
  rewrite dmatrix_rows 1:cols_ge0 // supp_dmap; case => vc; case => /= hvc *.
  rewrite supp_dmap.
  exists (zip va vc) => /=.
  have hva' : size va = r{2}; 1: by apply (supp_dlist_size _ _ _ _ hva).
  have hvc' : size vc = r{2}; 1: by apply (supp_dlist_size _ _ _ _ hvc).
  have [#] har hac : size a = (r{2}, rows b{2}).
  + by smt(size_tr cols_offunm rows_offunm).
  have [#] hcr hcc : size c = (r{2}, cols b{2}).
  + by smt(size_tr cols_offunm rows_offunm).
  split.
  + rewrite supp_dlist // -(all_nthP _ _ witness) size_zip hva' hvc' => /> i ? hi.
    rewrite (nth_zip_cond witness) size_zip hva' hvc' hi supp_dprod => />.
    have /allP : all (support (dvector d{2} (rows b{2}))) va; 1: by smt(supp_dlist).
    have /allP : all (support (dvector d{2} (cols b{2}))) vc; 1: by smt(supp_dlist).
    smt(mem_nth).
  + subst m.
    rewrite eq_matrixP size_addm size_mulmx 1:/# size_tr cols_offunm rows_offunm => />.
    split => [/#|i j].
    rewrite rows_addm cols_addm rows_mulmx cols_mulmx har hcr hcc => //= ? hir *.
    rewrite get_offunm 1:/# /=.
    rewrite get_offunm 1:/# /=.
    rewrite (nth_map witness witness) 1:size_zip 1:/# nth_zip' // 1,2:/# /=.
    rewrite get_addv get_mulmx get_mulvmx.
    subst a c.
    rewrite trmxE get_offunm 1:/# /= col_ofcols 1:rows_ge0 //.
    rewrite supp_dlist // in hva.
    case hva.
    have -> : support (dvector d{2} (rows b{2})) = fun (v: vector) => size v = rows b{2} /\ forall i, 0 <= i && i < rows b{2} => v.[i] \in d{2}.
    + smt(supp_dvector).
    rewrite all_predI => /#.
qed.

lemma LWE_M_Loop_eq:
    equiv[ LWE_M.sample ~ LWE_M_Loop.sample: 0 <= r{1} /\ ={d, r, b} ==> ={res} ].
proof.
exists* r{1}; elim*.
elim /natind => [_r ?|_r].
+ proc; inline *; rcondf{2} 4; auto => [/# | /> *].
  smt(weight_dlist0 dmap_ll dlist_ll supp_dmatrixr0 rows_ge0 cols_ge0 mul0m lin_addm0 rows_matrixc cols_matrixc ofcols_zerom_tr).
+ case (_r = 0) => [*|? ? h].
  + proc;inline *; rcondt{2} 4; 1: by auto => /#.
    rcondf{2} 9; 1: by auto => /#.
    swap {2} 8 1; swap {2} 1 7; wp.
    do 2! rnd (fun m => row m 0) rowmx.
    auto => />.
    subst _r => /> &2.
    split => [*|*].
    + smt(drowmx1E size_dvector).
    + split => *.
      + smt(supp_drow).
      + split => *.
        + smt(rowmx_row supp_dmatrix).
        + split => *.
          + smt(drowmx1E size_dvector).
          + split => *.
            + smt(supp_drow).
            + split => *.
              + smt(rowmx_row supp_dmatrix).
              + rewrite row_mul_eq -rowD ofcols_rowmx //=.
                + smt(rows_addm rows_mulmx size_dmatrix).
                + smt(cols_addm cols_mulmx size_dmatrix).
admit.
qed.

end SampleM.
