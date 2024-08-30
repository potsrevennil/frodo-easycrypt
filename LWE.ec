require import AllCore Distr List StdOrder PROM.
require (****) DynMatrix.
(****) import IntOrder.
require (****) Hybrid.
require import SmtMap.

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
hint simplify (ge0_n,ge0_nb,ge0_mb).

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

(* LWE Matrix adversary *)
module LWE_M1(Adv: HAdv1_M) = {
  var sd: seed
  var _A: matrix

  proc main(b: bool) : bool = {
    var b', sc, ec, i, u0, u1, u0c, u1c, u0cs, u1cs;

    sd <$ dseed;
    _A <- H sd n n;

    u0cs <- [];
    u1cs <- [];
    i <- 0;
    while (i < nb) {
      sc <$ dvector Chi n;
      ec <$ dvector Chi n;

      u0c <- _A *^ sc + ec;
      u1c <$ dvector duni_R n;
      u0cs <- rcons u0cs u0c;
      u1cs <- rcons u1cs u1c;

      i <- i + 1;
    }

    u0 <- ofcols n nb u0cs;
    u1 <- ofcols n nb u1cs;

    b' <@ Adv.guess(sd, if b then u1 else u0);
    return b';
   }
}.

(* LWE Vector adversary *)
module LWE_V1(Adv: HAdv1_V) = {
  proc main(b: bool) : bool = {
    var sd, b', _A, sc, ec, u0, u1;

    sd <$ dseed;
    _A <- H sd n n;

    sc <$ dvector Chi n;
    ec <$ dvector Chi n;
    u0 <- _A *^ sc + ec;

    u1 <$ dvector duni_R n;

    b' <@ Adv.guess(sd, if b then u1 else u0);
    return b';
   }
}.

(* --------------------------------------------------------------------------- *)
(* Hybrid game model for LWE                                                   *)
(* --------------------------------------------------------------------------- *)
clone import Hybrid as Hybrid_H1 with
type input    <- unit,
type output   <- vector,
type inleaks  <- unit,
type outleaks <- seed,
type outputA  <- bool,
op q <- nb
proof q_ge0 by trivial
proof *.

module LWE_H1_Ob : Orclb = {
  var sd: seed
  var _A: matrix

  proc leaks(): seed = {
    sd <$ dseed;
    _A <- H sd n n;
    return sd;
  }

  proc orclL (): vector = {
    var si, ei;
    si <$ dvector Chi n;
    ei <$ dvector Chi n;
    return _A *^ si + ei;
  }

  proc orclR (): vector = {
    var v;
    v <$ dvector duni_R n;
    return v;
  }
}.

(* For linking LWE matrix adversary to LWE non-hybrid game adversary *)
module B(Adv : HAdv1_M) (Ob: Orclb) (O: Orcl) = {

  proc main(): bool = {
    var sd, b', i, u, c, cs;

    sd <@ Ob.leaks();

    cs <- [];
    i <- 0;
    while (i < nb) {
      c <@ O.orcl();
      cs <- rcons cs c;

      i <- i + 1;
    }

    u <- ofcols n nb cs;

    b' <@ Adv.guess(sd, u);
    return b';
  }

}.

(* LWE matrix computation *)
lemma LWE_M1_L (A<: HAdv1_M{-Count, -LWE_H1_Ob, -LWE_M1}) &m:
    Pr[LWE_M1(A).main(false) @ &m : res] = Pr[Ln(LWE_H1_Ob, B(A)).main() @ &m: res].
proof.
byequiv => //.
proc. inline *.
wp.
call (: LWE_M1.sd{1} = LWE_H1_Ob.sd{2} ) => //=.
wp.
while (u0cs{1} = cs{2} /\ i{1} = i{2} /\ LWE_M1._A{1} = LWE_H1_Ob._A{2}).
+ wp.
  rnd{1}. auto => //=.
+ by auto.
qed.

(* LWE matrix random sampling *)
lemma LWE_M1_R (A <: HAdv1_M{-Count, -LWE_H1_Ob, -LWE_M1}) &m:
    Pr[LWE_M1(A).main(true) @ &m : res] = Pr[Rn(LWE_H1_Ob, B(A)).main() @ &m: res].
proof.
byequiv => //.
proc. inline *.
wp.
call (: LWE_M1.sd{1} = LWE_H1_Ob.sd{2} ) => //=.
wp.
while (u1cs{1} = cs{2} /\ i{1} = i{2} /\ LWE_M1._A{1} = LWE_H1_Ob._A{2}).
+ wp.
  rnd. auto.
+ by auto.
qed.

(* --------------------------------------------------------------------------------*)
(* For linking LWE vector adversary to LWE Hybrid Game adversary using PROM theory *)
(* ------------------------------------------------------------------------------- *)
clone PROM.FullRO as LWE_V1_L with
  type in_t <- seed,
  type out_t <- vector,
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout <- fun (sd: seed) => dlet (dvector Chi n) (fun (s: vector) =>
    dmap (dvector Chi n) (fun (e: vector) => H sd n n *^ s + e))
  proof *.

clone PROM.FullRO as LWE_V1_R with
  type in_t <- seed,
  type out_t <- vector,
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout <- fun _ => dvector duni_R n
  proof *.

(* mock hybrid Ob oracle *)
module ObFake = {
  var sd: seed

  proc leaks(): seed = {
    return sd;
  }

  proc orclL (): vector = {
      var _A, si, ei;
      _A <- H sd n n;
      si <$ dvector Chi n;
      ei <$ dvector Chi n;
      return _A *^ si + ei;
  }

  proc orclR (): vector = {
      var v';
      v' <$ dvector duni_R n;
      return v';
  }
}.


(* mock hybrid game for vector adversary, so that we can link LWE vector adversary with LWE Hybrid Game adversary *)
module HAdv1_C(A : HAdv1_M) = {
  var v: vector

  module OFake = {
    proc orcl(): vector = {
      return v;
    }
  }

  proc guess(sd': seed, v': vector) : bool = {
    var b;
    v <- v';
    ObFake.sd <- sd';
    b <@ HybGame(B(A), ObFake, OFake).main();
    return b;
  }
}.

(* auxiliary game for linking vector adversary with hybrid mock and LWE Hybrid Game adversary utilizing PROM *)
module LWE_V1_AuxL (A: HAdv1_M) (O: LWE_V1_L.RO) = {
  module OFake = {
    proc orcl(): vector = {
      var v;
      v <@ O.get(ObFake.sd);
      return v;
    }
  }

  proc distinguish(): bool = {
    var b;
    ObFake.sd <$ dseed;
    O.sample(ObFake.sd);
    b <@ HybGame(B(A), ObFake, OFake).main();
    return b;
  }
}.

module LWE_V1_AuxR (A: HAdv1_M) (O: LWE_V1_R.RO) = {
  module OFake = {
    proc orcl(): vector = {
      var v;
      v <@ O.get(ObFake.sd);
      return v;
    }
  }

  proc distinguish(): bool = {
    var b;
    ObFake.sd <$ dseed;
    O.sample(ObFake.sd);
    b <@ HybGame(B(A), ObFake, OFake).main();
    return b;
  }
}.

lemma LWE_V1_L_Aux1 (A <: HAdv1_M{-LWE_V1_L.RO, -HAdv1_C}) &m:
    Pr[LWE_V1(HAdv1_C(A)).main(false) @ &m: res] = Pr[LWE_V1_L.MainD(LWE_V1_AuxL(A), LWE_V1_L.RO).distinguish() @ &m: res].
proof.
byequiv => //.
proc.
inline *.
wp.
call (: ={ObFake.sd}).
wp.
while (={i, cs, HybOrcl.l0, HybOrcl.l, ObFake.sd} /\ HAdv1_C.v{1} = r1{2} /\ LWE_V1_L.RO.m{2}.[ObFake.sd{2}] = Some r1{2}).
+ sp.
  + if => //=.
    auto.
  + if => //=.
    wp. auto => //=.
    move => &1 &2.
    case; case; case; case; case.
    move => ?; case.
    move => ?; case.
    move => ?; case.
    move => ? ?; case.
    move => ? ?; case.
    move => *.
    split.
    + by rewrite dlet_ll // => *; rewrite dmap_ll.
    + move => *.
      have ->: ObFake.sd{2} \in LWE_V1_L.RO.m{2}.
      + rewrite fmapP.
        by exists r1{2}.
      rewrite //= /#.
  + auto.
+ wp. rnd. wp. rnd{1}.
  rndsem*{1} 1.
  wp. rnd.
  auto => //= /> *.
  by rewrite get_setE /dom emptyE.
qed.

lemma LWE_V1_L_Aux2 (A <: HAdv1_M{-HAdv1_C, -LWE_H1_Ob, -LWE_V1_L.RO}) &m:
    Pr[LWE_V1_L.MainD(LWE_V1_AuxL(A), LWE_V1_L.LRO).distinguish() @ &m: res] = Pr[HybGame(B(A), LWE_H1_Ob, L(LWE_H1_Ob)).main() @ &m: res].
proof.
byequiv => //.
proc.
inline *; wp.
call (: ObFake.sd{1} = LWE_H1_Ob.sd{2}); wp.
while (={i, HybOrcl.l0, HybOrcl.l, cs} /\
  ObFake.sd{1} = LWE_H1_Ob.sd{2} /\
  LWE_H1_Ob._A{2} = H LWE_H1_Ob.sd{2} n n /\
  LWE_V1_L.RO.m{1}.[ObFake.sd{1}] = (HybOrcl.l0{1} < HybOrcl.l{1}) ? Some v{1} : None
).
+ sp.
  + if => //=.
    by auto => /#.
  + if => //=.
    wp 3 4.
    rndsem*{2} 1.
    auto => //= /> *.
    rewrite domE get_set_sameE => //= /#.
  + by auto => /#.
+ swap {2} [1..2] 2.
  auto => //= /> ? ? ? ?.
  by rewrite DInterval.supp_dinter emptyE => /#.
qed.

lemma LWE_V1_L (A <: HAdv1_M{-HAdv1_C, -LWE_H1_Ob, -LWE_V1_L.RO, -LWE_V1_L.FRO}) &m:
      Pr[LWE_V1(HAdv1_C(A)).main(false) @ &m: res] = Pr[HybGame(B(A),LWE_H1_Ob,L(LWE_H1_Ob)).main() @ &m: res].
proof.
rewrite (LWE_V1_L_Aux1 A _) -(LWE_V1_L_Aux2 A _).
byequiv (LWE_V1_L.FullEager.RO_LRO (LWE_V1_AuxL(A)) _) => // *.
by rewrite dlet_ll // => *; rewrite dmap_ll.
qed.

lemma LWE_V1_R_Aux1 (A <: HAdv1_M{-LWE_V1_R.RO, -HAdv1_C}) &m:
    Pr[LWE_V1(HAdv1_C(A)).main(true) @ &m: res] = Pr[LWE_V1_R.MainD(LWE_V1_AuxR(A), LWE_V1_R.RO).distinguish() @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (:true).
wp.
while (={i, cs, HybOrcl.l0, HybOrcl.l, ObFake.sd} /\ HAdv1_C.v{1} = r1{2} /\ LWE_V1_R.RO.m{2}.[ObFake.sd{2}] = Some r1{2}).
+ sp.
  + if => //=.
    by auto.
  + if => //=.
    by auto => //= /> /#.
  + by auto.
+ wp. rnd. wp. rnd. wp. rnd{1}. rnd{1}. wp. rnd. auto => //= /> *.
  by rewrite /dom emptyE //= get_set_sameE.
qed.

lemma LWE_V1_R_Aux2 (A <: HAdv1_M{-HAdv1_C, -LWE_H1_Ob, -LWE_V1_R.RO}) &m:
    Pr[LWE_V1_R.MainD(LWE_V1_AuxR(A), LWE_V1_R.LRO).distinguish() @ &m: res] = Pr[HybGame(B(A), LWE_H1_Ob, R(LWE_H1_Ob)).main() @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (:true); wp.
while (={i, HybOrcl.l0, HybOrcl.l, cs} /\
  ObFake.sd{1} = LWE_H1_Ob.sd{2} /\
  LWE_H1_Ob._A{2} = H LWE_H1_Ob.sd{2} n n /\
  LWE_V1_R.RO.m{1}.[ObFake.sd{1}] = (HybOrcl.l0{1} < HybOrcl.l{1}) ? Some v{1} : None
).
+ sp.
  + if => //=.
    by auto => /#.
  + if => //=.
    auto => //= /> *.
    rewrite get_set_sameE => //= /#.
  + by auto => /#. 
+ swap {2} [1..2] 2.
  auto => //= /> ? ? ? ?.
    by rewrite DInterval.supp_dinter emptyE => /#.
qed.

lemma LWE_V1_R (A <: HAdv1_M{-HAdv1_C, -LWE_H1_Ob, -LWE_V1_R.RO, -LWE_V1_R.FRO}) &m:
      Pr[LWE_V1(HAdv1_C(A)).main(true) @ &m: res] = Pr[HybGame(B(A),LWE_H1_Ob,R(LWE_H1_Ob)).main() @ &m: res].
proof.
rewrite (LWE_V1_R_Aux1 A _) -(LWE_V1_R_Aux2 A _).
byequiv (LWE_V1_R.FullEager.RO_LRO (LWE_V1_AuxR(A)) _) => // *.
qed.

lemma LWE_H1_Hybrid (A <: HAdv1_M{-Count, -LWE_H1_Ob, -LWE_M1, -HAdv1_C, -LWE_V1_L.RO, -LWE_V1_L.FRO, -LWE_V1_R.RO, -LWE_V1_R.FRO}) &m :
    islossless A.guess =>
    Pr[LWE_M1(A).main(false) @ &m : res] - Pr[LWE_M1(A).main(true) @ &m : res]
  = nb%r * (Pr[LWE_V1(HAdv1_C(A)).main(false) @ &m : res] - Pr[LWE_V1(HAdv1_C(A)).main(true) @ &m : res]).
proof.
move => A_ll.
rewrite (LWE_M1_L A) (LWE_M1_R A) (LWE_V1_L A) (LWE_V1_R A).
apply (Hybrid_restr LWE_H1_Ob (B(A)) _ _ _ _ _ &m (fun _ _ _ r => r)).
move => *.
proc; inline *.
wp. call (:true). wp.
while (i = Count.c /\ i <= nb).
+ auto. call(:true). auto => />. by rewrite ltzE.
+ auto => //=.
+ by islossless.
+ by islossless.
+ by islossless.
+ move => *.
  proc; call (:true); wp.
  while (i <= nb) (nb - i) => *;
  wp; call (:true);  auto => /#.
qed.

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
