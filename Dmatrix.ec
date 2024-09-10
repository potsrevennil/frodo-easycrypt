require import AllCore Distr List.
require import Distrmatrix.
require import DList.
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
type t.

clone import SampleL with
    type t <- vector
    proof *.

module Matrix = {
  proc sample(d, r, c): matrix = {
    var m;
    m <$ dmatrix d r c;
    return m;
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
}.

lemma Matrix_VectorRows_eq :
    equiv[ Matrix.sample ~ VectorRows.sample : 0 <= r{1} /\ 0 <= c{1} /\ ={d, r, c} ==> ={res} ].

bypr (res{1}) (res{2}) => //= &1 &2 m [#] *.
byequiv => //.
proc; inline *.
rndsem*{2} 0.
auto => //= />.
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

end SampleM.
