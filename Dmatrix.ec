require import AllCore Distr List.
require import Distrmatrix.
require import DList.
import StdOrder.IntOrder.
(*****) import DM.

export DM.
(*clone import DynMatrix as Matrix.*)
(*export Matrix.*)

(*
op "_.[_<-_]" (m: matrix) (ij: int*int) (v: R): matrix =
   offunm (fun i j => if (i,j) = ij then v else m.[ij],rows m, cols m).
*)

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

lemma dmatrix_mul_eq d l m:
    0 <= l =>
    dmap (dmatrix d l (rows m)) (fun m1 => m1 * m) =
    dmap (dlist (dmap (dvector d (rows m)) (fun v => v ^* m)) l) (fun vs => trmx (ofcols (cols m) l vs)).
proof.
admit.
qed.

abstract theory SampleL.
type t.

module List = {
  proc sample(d, n): t list = {
      var r;

      r <$ dlist d n;
      return r;
  }
}.

module Rcons = {
  proc sample(d, n): t list = {
    var r, rs, rs';
    rs <$ dlist d (n - 1);
    r <$ d;
    rs' <- rcons rs r;
    return rs';
  }
}.

module LoopRcons = {
  proc sample(d, n) : t list = {
    var i : int;
    var r : t;
    var l : t list;
    
    i <- 0;
    l <- [];
    while (i < n){
      r <$ d;
      l <- rcons l r;
      i <- i + 1;
    }
    
    return l;
  }
}.

lemma List_Rcons_eq:
    equiv[ List.sample ~ Rcons.sample : 0 < n{1} /\ ={d, n} ==> ={res} ].
proof.
bypr res{1} res{2} => //= &1 &2 l *.
byequiv => //.
proc; inline *.
rndsem*{2} 0.
auto => //= />.
rewrite -(dmap_dprodE _ _ (fun (rsr: t list * t) => rcons rsr.`1 rsr.`2)).
rewrite !dlist_djoin 1..2:/# -!djoin_rcons -!nseqSr 1:/# => /#.
qed.

lemma List_LoopRcons_eq:
    equiv[ List.sample ~ LoopRcons.sample : ={d, n} ==> ={res} ].
proof.
exists* n{1}; elim*.
elim /natind => [_n ?|_n].
+ proc*; inline *. rcondf{2} 5; auto; smt(weight_dlist0 supp_dlist0).
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
                 (0 < n{1} /\ ={d, n} ==> ={res})
                 (_n + 1 = n{1} /\ ={d, n} /\ 0 < n{1} ==> ={res}); 1..2: by rewrite /#.
    + exact List_Rcons_eq.
    + proc; splitwhile{2} 3: (i < n - 1).
      rcondt{2} 4; 1: by auto; while (i < n); auto => /#.
      rcondf{2} 7; 1: auto. while (i < n); auto => /#.
      wp; rnd.
      outline {1} [1] rs <@ List.sample.
      rewrite equiv[{1} 1 h]; inline.
      by wp; while (={i,d,l} /\ n0{1} = n{2} - 1 /\ d0{1} = d{1}); auto => /#.
qed.    
end SampleL.

abstract theory SampleM.

clone import SampleL with
    type t <- vector
    proof *.

module Matrix = {
  proc sample(d, r, c): matrix = {
    var m;
    m <$ dmatrix d r c;
    return m;
  }

  proc sample'(d, r, b): matrix = {
    var a, c, m;
    a <$ dmatrix d r (rows b);
    c <$ dmatrix d r (cols b);
    m <- a * b + c;
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
  proc sample(d, r, c): matrix = {
    var vs, m;
    vs <@ SampleL.List.sample(dvector d c, r);
    m <- trmx (ofcols c r vs);

    return m;
  }
}.

module VectorRowsLoopRcons = {
  proc sample(d, r, c): matrix = {
    var vs, m;

    vs <@ SampleL.LoopRcons.sample(dvector d c, r);
    m <- trmx (ofcols c r vs);

    return m;
  }

  proc sample'(d, r, b): matrix = {
    var i, vs, v, a, c;

    i <- 0;
    vs <- [];
    while (i < r) {
      a <$ dvector d (rows b);
      c <$ dvector d (cols b);

      v <- a ^* b + c;
      vs <- rcons vs v;

      i <- i + 1;
    }

    return trmx (ofcols (cols b) r vs);
  }

  proc sample'aux(d, r, b): matrix = {
    var d', vs, m;
    d' <- dlet (dvector d (rows b)) (fun a => dmap (dvector d (cols b)) (fun c => a ^* b + c));
    vs <@ SampleL.LoopRcons.sample(d', r);
    m <- trmx (ofcols (cols b) r vs);
    return m;
  }
}.

lemma Matrix_VectorRows_eq :
    equiv[ Matrix.sample ~ VectorRows.sample : 0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==> ={res} ].

bypr (res{1}) (res{2}) => //= &1 &2 m [#] *.
byequiv => //.
proc; inline *.
rndsem*{2} 0.
auto => />.
by rewrite dmatrix_rows /#.
qed.

lemma VectorRows_VectorRowsLoopRcons_eq :
    equiv [ VectorRows.sample ~ VectorRowsLoopRcons.sample :
        0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==> ={res} ].
proof.
bypr res{1} res{2} => // &1 &2 m [#] ? ? <- <- <-.
byequiv => //.
proc; wp.
rewrite equiv[{1} 1 List_LoopRcons_eq].
call (_: true) => /=.
+ while (={d, l, i,  n}); auto => />.
+ skip => //=.
qed.

lemma Matrix_VectorRowsLoopRcons_eq:
    equiv[ Matrix.sample ~ VectorRowsLoopRcons.sample: 0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==> ={res} ].
proof.
transitivity VectorRows.sample
    (0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==> ={res})
    (0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==> ={res}) => //; 1: by rewrite /#.
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

end SampleM.
