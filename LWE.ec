require import AllCore Distr List.
require (****) DynMatrix.

clone import DynMatrix as Matrix.

print DynMatrix.

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

(* --------------------------------------------------------------------------- *)
(* Uniform distribution over R *)
op [lossless uniform full] duni_R : R distr.

lemma duni_R_funi : is_funiform duni_R.
proof. apply is_full_funiform; [apply duni_R_fu | apply duni_R_uni]. qed.

(* --------------------------------------------------------------------------- *)
(* Distribution over R (short values) *)

op [lossless] Chi  : R distr.

(* --------------------------------------------------------------------------- *)
(* Extention distribution to matrix *) 

op duni_matrix = dmatrix duni_R.

lemma duni_matrix_ll m n : is_lossless (duni_matrix m n).
proof. apply/dmatrix_ll/duni_R_ll. qed.



lemma duni_matrix_fu m n A_: 
     0 <= m => 0 <= n =>  A_ \in (duni_matrix m n) <=> size A_ = (m, n).
proof. 
move => ge0m ge0n.
by apply /supp_dmatrix_full /duni_R_fu => //.
qed.

lemma duni_matrix_uni m n : is_uniform (duni_matrix m n).
proof. apply /dmatrix_uni/duni_R_uni. qed.

op Chi_matrix = dmatrix Chi.

lemma Chi_matrix_ll m n : is_lossless (Chi_matrix m n).
proof. apply/dmatrix_ll /Chi_ll. qed.

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
(* Version of LWE using a concrete hash function to derive the matrix         *)
(* --------------------------------------------------------------------------- *)
type seed.
op H : seed -> int -> int -> matrix.

(* --------------------------------------------------------------------------- *)
op [lossless] dseed : seed distr.

module type HAdv1_T = {
   proc guess(sd : seed, u : matrix) : bool
}.

module LWE_H1(Adv : HAdv1_T) = {

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
