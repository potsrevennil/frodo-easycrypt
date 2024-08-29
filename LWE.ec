require import AllCore Distr List StdOrder.
require (****) DynMatrix.
(****) import IntOrder.

clone import DynMatrix as Matrix.

instance ring with R
  op rzero = ZR.zeror
  op rone  = ZR.oner
  op add   = ZR.( + )
  op opp   = ZR.([-])
  op mul   = ZR.( * )
  op expr  = ZR.exp
  op ofint = ZR.ofint

  proof oner_neq0 by apply ZR.oner_neq0
  proof addrA     by apply ZR.addrA
  proof addrC     by apply ZR.addrC
  proof addr0     by apply ZR.addr0
  proof addrN     by apply ZR.addrN
  proof mulr1     by apply ZR.mulr1
  proof mulrA     by apply ZR.mulrA
  proof mulrC     by apply ZR.mulrC
  proof mulrDl    by apply ZR.mulrDl
  proof expr0     by apply ZR.expr0
  proof ofint0    by apply ZR.ofint0
  proof ofint1    by apply ZR.ofint1
  proof exprS     by apply ZR.exprS
  proof ofintS    by apply ZR.ofintS
  proof ofintN    by apply ZR.ofintN.

op "_.[_<-_]" (m: matrix) (ij: int*int) (v: R): matrix =
   offunm (fun i j => if (i,j) = ij then v else m.[ij],rows m, cols m).
(*
op tolist (m: matrix): R list =
  let ys = range 0 (cols m) in
  let xs = range 0 (rows m) in
  let ms = concatMap (fun x => map (fun y => (x, y)) ys) xs in
  map (fun i => m.[i] ) ms.
*)

op n : { int | 0 < n } as gt0_n.
op nb : { int | 0 < nb } as gt0_nb.
op mb : { int | 0 < mb } as gt0_mb.

hint exact: gt0_n gt0_nb gt0_mb.

lemma ge0_n: 0 <= n.
proof. by apply ltrW. qed.

lemma ge0_mb: 0 <= mb.
proof. by apply ltrW. qed.

lemma ge0_nb: 0 <= nb.
proof. by apply ltrW. qed.

hint exact: ge0_n ge0_nb ge0_mb.

(* --------------------------------------------------------------------------- *)
(* Uniform distribution over R *)
op [lossless uniform full] duni_R : R distr.
hint exact: duni_R_ll duni_R_uni duni_R_fu.
hint simplify (duni_R_ll, duni_R_uni, duni_R_fu).

lemma duni_R_funi : is_funiform duni_R.
proof. by apply is_full_funiform. qed.

(* --------------------------------------------------------------------------- *)
(* Distribution over R (short values) *)

op [lossless] Chi  : R distr.
hint exact: Chi_ll.
hint simplify Chi_ll.

(* --------------------------------------------------------------------------- *)
(* Extension distribution to matrix *)

op duni_matrix = dmatrix duni_R.

hint exact: dmatrix_ll dmatrix_uni dvector_ll.
hint simplify (dmatrix_ll, dmatrix_uni, dvector_ll).

lemma duni_matrix_ll m n : is_lossless (duni_matrix m n).
proof. by trivial. qed.


lemma duni_matrix_fu m n A_:
     0 <= m => 0 <= n =>  A_ \in (duni_matrix m n) <=> size A_ = (m, n).
proof.
move => ge0m ge0n.
by apply /supp_dmatrix_full.
qed.

lemma duni_matrix_uni m n : is_uniform (duni_matrix m n).
proof. by trivial. qed.

op Chi_matrix = dmatrix Chi.

lemma Chi_matrix_ll m n : is_lossless (Chi_matrix m n).
proof. by trivial. qed.

hint simplify (duni_matrix_uni, duni_matrix_ll, Chi_matrix_ll).

module type Adv_T = {
   proc guess(A : matrix, uvw : matrix * matrix * matrix) : bool
}.

module LWE(Adv : Adv_T) = {

  proc main(b : bool) : bool = {
    var b', _A, s, e, u0, u1, s', e', v0, v1, _B, e'', w0, w1;

    _A <$ duni_matrix n n;
    s <$ Chi_matrix n nb;
    e <$ Chi_matrix n nb;
    u0 <- _A * s + e;
    u1 <$ duni_matrix n nb;

    s' <$ Chi_matrix mb n;
    e' <$ Chi_matrix mb n;
    v0 <- s' * _A + e';
    v1 <$ duni_matrix mb n;

    _B <$ duni_matrix n nb;
    e'' <$ Chi_matrix mb nb;
    w0 <- s' * _B + e'';
    w1 <$ duni_matrix mb nb;

    b' <@ Adv.guess(_A, if b then (u1,v1,w1) else (u0,v0,w0));
    return b';
   }

}.

(* --------------------------------------------------------------------------- *)
(* Version of LWE using a concrete hash function to derive the matrix          *)
(* --------------------------------------------------------------------------- *)
type seed.
op H : seed -> int -> int -> matrix.

(* --------------------------------------------------------------------------- *)
op [lossless] dseed : seed distr.

(* --------------------------------------------------------------------------- *)
(* LWE adversaries                                                             *)
(* --------------------------------------------------------------------------- *)
module type HAdv1_M = {
   proc guess(sd : seed, u : matrix) : bool
}.

module type HAdv1_V = {
   proc guess(sd : seed, u : vector) : bool
}.

(* LWE adversary *)
module LWE_H1(Adv : HAdv1_M) = {

  proc main(b : bool) : bool = {
    var seed, b', _A, s, e, u0, u1;

    seed <$ dseed;
    _A <- H seed n n;
    s <$ Chi_matrix n nb;
    e <$ Chi_matrix n nb;
    u0 <- _A * s + e;
    u1 <$ duni_matrix n nb;

    b' <@ Adv.guess(seed, if b then u1 else u0);
    return b';
   }

}.

module type HAdv2_T = {
   proc guess(sd : seed, _B : matrix, uv : matrix * matrix) : bool
}.

module LWE_H2(Adv : HAdv2_T) = {

  proc main(b : bool) : bool = {
    var seed, b', _A, s', e', u0, u1, _B, e'', v0, v1;

    seed <$ dseed;
    _B <$ duni_matrix n nb;
    s' <$ Chi_matrix mb n;
    e' <$ Chi_matrix mb n;
    e'' <$ Chi_matrix mb nb;

    _A <- H seed n n;
    u0 <- s' * _A + e';
    u1 <$ duni_matrix mb n;

    v0 <- s' * _B + e'';
    v1 <$ duni_matrix mb nb;

    b' <@ Adv.guess(seed, _B, if b then (u1, v1) else (u0, v0));
    return b';
   }

}.
