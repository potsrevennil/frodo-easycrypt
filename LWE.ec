require import AllCore Distr List StdOrder PROM.
require (****) DynMatrix.
(****) import IntOrder.
require (****) Hybrid.
require import SmtMap.

require (****) Dmatrix.

clone import Dmatrix as Dmatrix_.

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

(* --------------------------------------------------------------------------- *)
(* Version of LWE using a concrete hash function to derive the matrix          *)
(* --------------------------------------------------------------------------- *)
type seed.

(* --------------------------------------------------------------------------- *)
op [lossless] dseed : seed distr.

module type Adv_M0 = {
   proc guess(sd: seed, m : matrix) : bool
}.

module type Adv_M = {
   proc guess(sd: seed, _B: matrix, m : matrix) : bool
}.

module type Adv_V = {
   proc guess(sd: seed, _B: matrix, v : vector) : bool
}.

theory LWE_Hybrid.

op G : seed -> int -> int -> matrix.

op k : { int | 0 <= k } as ge0_k.
op l : { int | 0 < l } as gt0_l.
op m: { int | 0 < m } as gt0_m.
op n : { int | 0 < n } as gt0_n.

hint exact: gt0_m gt0_n gt0_l ge0_k.
hint simplify (gt0_m, gt0_n, gt0_l, ge0_k).

module LWE_M(Adv: Adv_M) = {
  var sd: seed

  proc main(b : bool) : bool = {
    var b', s, e, u0, u1, _A, _B;

    sd <$ dseed;
    _A <- G sd m n;
    _B <$ duni_matrix m k;

    s <$ Chi_matrix l m;
    e <$ Chi_matrix l (n + k);
    u0 <- s * (_A || _B) + e;
    u1 <$ duni_matrix l (n + k);

    b' <@ Adv.guess(sd, _B, if b then u1 else u0);
    return b';
   }
}.

(* LWE Matrix adversary *)
module LWE_M_Loop(Adv: Adv_M) = {
  var sd: seed

  proc main(b : bool) : bool = {
    var b', i, sc, ec, u0, u1, u0c, u1c, u0cs, u1cs, _A, _B;

    sd <$ dseed;
    _A <- G sd m n;
    _B <$ duni_matrix m k;

    u0cs <- [];
    u1cs <- [];
    i <- 0;

    while (i < l) {
        sc <$ dvector Chi m;
        ec <$ dvector Chi (n + k);
        u0c <- sc ^* (_A || _B) + ec;
        u1c <$ dvector duni_R (n + k);

        u0cs <- rcons u0cs u0c;
        u1cs <- rcons u1cs u1c;

        i <- i + 1;
    }

    u0 <- trmx (ofcols (n + k) l u0cs);
    u1 <- trmx (ofcols (n + k) l u1cs);

    b' <@ Adv.guess(sd, _B, if b then u1 else u0);
    return b';
   }
}.

(* LWE Vector adversary *)
module LWE_V(Adv: Adv_V) = {
  var sd: seed

  proc main(b: bool) : bool = {
    var b', sc, ec, u0, u1, _A, _B;

    sd <$ dseed;
    _A <- G sd m n;
    _B <$ duni_matrix m k;

    sc <$ dvector Chi m;
    ec <$ dvector Chi (n + k);
    u0 <- sc ^* (_A || _B) + ec;
    u1 <$ dvector duni_R (n + k);

    b' <@ Adv.guess(sd, _B, if b then u1 else u0);
    return b';
   }
}.

lemma LWE_M_Eq (A <: Adv_M) b &m:
    Pr[LWE_M(A).main(b) @ &m: res] = Pr[LWE_M_Loop(A).main(b) @ &m: res].
proof.
admit.
qed.

(* --------------------------------------------------------------------------- *)
(* Hybrid game model for LWE                                                   *)
(* --------------------------------------------------------------------------- *)
clone import Hybrid as Hyb with
type input    <- unit,
type output   <- vector,
type inleaks  <- unit,
type outleaks <- seed*matrix,
type outputA  <- bool,
op q <- l
proof q_ge0 by trivial
proof *.

module type Adv_M_Orclb (Adv: Adv_M, Ob: Orclb, O: Orcl)= {
  proc main() : bool
}.

module LWE_Ob : Orclb = {
  var sd: seed
  var _B: matrix

  proc leaks(): seed*matrix = {
    sd <$ dseed;
    _B <$ duni_matrix m k;
    return (sd, _B);
  }

  proc orclL (): vector = {
    var sc, ec, v, _A;
    _A <- G sd m n;

    sc <$ dvector Chi m;
    ec <$ dvector Chi (n + k);
    v <- sc ^* (_A || _B) + ec;

    return v;
  }

  proc orclR (): vector = {
    var v;

    v <$ dvector duni_R (n + k);
    return v;
  }
}.

(* mock hybrid Ob oracle *)
module ObFake = {
  var sd: seed
  var _B: matrix

  proc leaks(): seed*matrix = {
    return (sd, _B);
  }

  proc orclL (): vector = {
      var sc, ec, v, _A;
      _A <- G sd m n;
      sc <$ dvector Chi m;
      ec <$ dvector Chi (n + k);
      v <- sc ^* (_A || _B) + ec;

      return v;
  }

  proc orclR (): vector = {
      var v';
      v' <$ dvector duni_R (n + k);
      return v';
  }
}.

(* For linking LWE matrix adversary to LWE non-hybrid game adversary *)
module B(Adv : Adv_M) (Ob: Orclb) (O: Orcl) = {
  var sd: seed

  proc main(): bool = {
    var b', i, u, c, cs, _A, _B;

    (sd, _B) <@ Ob.leaks();

    _A <- G sd m n;

    cs <- [];
    i <- 0;

    while (i < l) {
        c <@ O.orcl();
        cs <- rcons cs c;

        i <- i + 1;
    }

    u <- trmx (ofcols (n + k) l cs);

    b' <@ Adv.guess(sd, _B, u);
    return b';
  }
}.

(* LWE matrix computation *)
lemma LWE_M_L (A<: Adv_M{-Count, -B, -LWE_Ob, -LWE_M_Loop}) &m:
    Pr[LWE_M_Loop(A).main(false) @ &m : res] = Pr[Ln(LWE_Ob, B(A)).main() @ &m: res].
proof.
move => *.
byequiv => //=.
proc; inline *; wp.
call (: true) => //=; wp.
+ while (={i} /\ u0cs{1} = cs{2} /\
      LWE_M_Loop.sd{1} = LWE_Ob.sd{2} /\
      _B{1} = LWE_Ob._B{2} /\
      _A{1} = G LWE_M_Loop.sd{1} m n
  ).
  + wp. rnd{1}.
    by auto => /#.
  + by auto => /#.
qed.

(* LWE matrix random sampling *)
lemma LWE_M_R (A<: Adv_M{-Count, -B, -LWE_Ob, -LWE_M_Loop}) &m:
    Pr[LWE_M_Loop(A).main(true) @ &m : res] = Pr[Rn(LWE_Ob, B(A)).main() @ &m: res].
proof.
move => *.
byequiv => //.
proc; inline *; wp.
call (: true) => //=; wp.
+ while (={i} /\ u1cs{1} = cs{2} /\
      LWE_M_Loop.sd{1} = LWE_Ob.sd{2} /\
      _B{1} = LWE_Ob._B{2} /\
      _A{1} = G LWE_M_Loop.sd{1} m n
  ).
  + by auto => /#.
  + by auto => /#.
qed.

(* --------------------------------------------------------------------------------*)
(* For linking LWE vector adversary to LWE Hybrid Game adversary using PROM theory *)
(* ------------------------------------------------------------------------------- *)
clone PROM.FullRO as LWE_RO with
  type in_t <- seed * matrix * bool, (* (sd,_B,sample) *)
  type out_t <- vector,
  type d_in_t <- bool,
  type d_out_t <- bool,
  op dout <- fun (din: seed * matrix * bool) =>
    if din.`3
    then dvector duni_R (n + k)
    else dlet (dvector Chi m) (fun (s: vector) =>
            dmap (dvector Chi (n+k)) (fun (e: vector) => s ^* (G din.`1 m n || din.`2) + e))
  proof *.

(* mock hybrid game for vector adversary, so that we can link LWE vector adversary with LWE Hybrid Game adversary *)
module Hyb_Mock(Adv : AdvOrclb): Adv_V = {
  var v: vector

  module OFake = {
    proc orcl(): vector = {
      return v;
    }
  }

  proc guess(sd: seed, _B: matrix, v': vector) : bool = {
    var b;
    v <- v';
    ObFake.sd <- sd;
    ObFake._B <- _B;

    b <@ HybGame(Adv, ObFake, OFake).main();
    return b;
  }
}.

(* auxiliary game for linking vector adversary with hybrid mock and LWE Hybrid Game adversary utilizing PROM *)
module LWE_V_Aux (Adv: Adv_M) (O: LWE_RO.RO) = {
  var b: bool

  module OFake = {
    proc orcl(): vector = {
      var v;
      v <@ O.get(ObFake.sd, ObFake._B, b);
      return v;
    }
  }

  proc distinguish(b': bool): bool = {
    b <- b';
    ObFake.sd <$ dseed;
    ObFake._B <$ duni_matrix m k;
    O.sample(ObFake.sd, ObFake._B, b);
    b <@ HybGame(B(Adv), ObFake, OFake).main();
    return b;
  }
}.

lemma LWE_V_Aux (A <: Adv_M{-LWE_RO.RO, -Hyb_Mock, -LWE_V_Aux, -LWE_V}) b &m:
    Pr[LWE_V(Hyb_Mock(B(A))).main(b) @ &m: res] = Pr[LWE_RO.MainD(LWE_V_Aux(A), LWE_RO.RO).distinguish(b) @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (: ={ObFake.sd, ObFake._B}); wp.
while (={i, cs, HybOrcl.l0, HybOrcl.l, ObFake.sd, ObFake._B} /\
  Hyb_Mock.v{1} = r1{2} /\
  LWE_RO.RO.m{2}.[(ObFake.sd{2},ObFake._B{2},LWE_V_Aux.b{2})] = Some r1{2}
).
+ sp.
    + if => //=.
      auto.
    + if => //=.
      wp. auto => //= /> &2.
      case (LWE_V_Aux.b{2}).
      + rewrite //= domNE => /> /#.
      + rewrite //= domNE dlet_ll => /> *.
        + by rewrite dmap_ll.
        rewrite /#.
    + by auto.
+ wp. rnd. wp.
  case (b).
  + rnd; wp; rnd{1}; rnd{1}; auto => //= /> *.
    by rewrite /dom emptyE //= get_set_sameE.
  + rnd{1}. swap {1} 3 -1.
    rndsem*{1} 2.
    auto => //= /> *.
    by rewrite get_setE /dom emptyE.
qed.

lemma LWE_V_L_Aux (A <: Adv_M{-LWE_Ob, -LWE_RO.RO, -LWE_V_Aux}) &m:
    Pr[LWE_RO.MainD(LWE_V_Aux(A), LWE_RO.LRO).distinguish(false) @ &m: res] = Pr[HybGame(B(A), LWE_Ob, L(LWE_Ob)).main() @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (: ObFake.sd{1} = LWE_Ob.sd{2} /\ ObFake._B{1} = LWE_Ob._B{2}); wp.
while (={i, HybOrcl.l0, HybOrcl.l, cs} /\
  ObFake.sd{1} = LWE_Ob.sd{2} /\
  ObFake._B{1} = LWE_Ob._B{2} /\
  LWE_RO.RO.m{1}.[(ObFake.sd{1}, ObFake._B{1}, LWE_V_Aux.b{1})] = (HybOrcl.l0{1} < HybOrcl.l{1}) ? Some v0{1} : None /\
  !LWE_V_Aux.b{1}
).
+ sp.
  + if => //=.
    by auto => /#.
  + if => //=.
    wp 3 5.
    rndsem*{2} 1.
    auto => //= />.
    rewrite domE => *.
    rewrite get_set_sameE /#.
  + by auto => /#.
+ swap {2} [1..2] 2.
  auto => //= /> ? ? ? ? ? ?.
  by rewrite emptyE DInterval.supp_dinter /#.
qed.

lemma LWE_V_L (A <: Adv_M{-Hyb_Mock, -LWE_Ob, -LWE_RO.RO, -LWE_RO.FRO, -LWE_V, -LWE_V_Aux}) &m:
      Pr[LWE_V(Hyb_Mock(B(A))).main(false) @ &m: res] = Pr[HybGame(B(A),LWE_Ob,L(LWE_Ob)).main() @ &m: res].
proof.
rewrite (LWE_V_Aux A false _) -(LWE_V_L_Aux A _).
byequiv (LWE_RO.FullEager.RO_LRO (LWE_V_Aux(A)) _) => // x.
case (x.`3) => h //.
by rewrite dlet_ll // => *; rewrite dmap_ll.
qed.

lemma LWE_V_R_Aux (A <: Adv_M{-LWE_Ob, -LWE_RO.RO, -LWE_V_Aux}) &m:
    Pr[LWE_RO.MainD(LWE_V_Aux(A), LWE_RO.LRO).distinguish(true) @ &m: res] = Pr[HybGame(B(A), LWE_Ob, R(LWE_Ob)).main() @ &m: res].
proof.
byequiv => //.
proc; inline *; wp.
call (: ObFake.sd{1} = LWE_Ob.sd{2} /\ ObFake._B{1} = LWE_Ob._B{2}); wp.
while (={i, HybOrcl.l0, HybOrcl.l, cs} /\
  ObFake.sd{1} = LWE_Ob.sd{2} /\
  ObFake._B{1} = LWE_Ob._B{2} /\
  LWE_RO.RO.m{1}.[(ObFake.sd{1}, ObFake._B{1}, LWE_V_Aux.b{1})] = (HybOrcl.l0{1} < HybOrcl.l{1}) ? Some v0{1} : None /\
  LWE_V_Aux.b{1}
).
+ sp.
  + if => //=.
    by auto => /#.
  + if => //=.
    auto => //= /> *.
    rewrite get_set_sameE => //= /#.
  + by auto => /#.
+ swap {2} [1..2] 2.
  auto => //= /> ? ? ? ? ? ?.
    by rewrite DInterval.supp_dinter emptyE => /#.
qed.

lemma LWE_V_R (A <: Adv_M{-Hyb_Mock, -LWE_Ob, -LWE_RO.RO, -LWE_RO.FRO, -LWE_V, -LWE_V_Aux}) &m:
      Pr[LWE_V(Hyb_Mock(B(A))).main(true) @ &m: res] = Pr[HybGame(B(A),LWE_Ob,R(LWE_Ob)).main() @ &m: res].
proof.
rewrite (LWE_V_Aux A true _) -(LWE_V_R_Aux A _).
byequiv (LWE_RO.FullEager.RO_LRO (LWE_V_Aux(A)) _) => // x.
case (x.`3) => h //.
by rewrite dlet_ll // => *; rewrite dmap_ll.
qed.

lemma LWE_H_Hybrid (A <: Adv_M{-Count, -LWE_Ob, -LWE_M_Loop, -Hyb_Mock, -LWE_RO.RO, -LWE_RO.FRO, -LWE_V, -LWE_V_Aux}) &m :
    islossless A.guess =>
    Pr[LWE_M(A).main(false) @ &m : res] - Pr[LWE_M(A).main(true) @ &m : res]
  = l%r * (Pr[LWE_V(Hyb_Mock(B(A))).main(false) @ &m : res] - Pr[LWE_V(Hyb_Mock(B(A))).main(true) @ &m : res]).
proof.
move => A_ll.
rewrite !(LWE_M_Eq A).
rewrite (LWE_M_L A) (LWE_M_R A) (LWE_V_L A) (LWE_V_R A).
apply (Hybrid_restr LWE_Ob (B(A)) _ _ _ _ _ &m (fun _ _ _ r => r)).
move => *.
proc; inline *.
wp. call (:true). wp.
while (i = Count.c /\ i <= l).
+ auto. call(:true). auto => />. by rewrite ltzE.
+ auto => //=.
+ auto => //=.
+ by islossless.
+ by islossless.
+ by islossless.
+ move => *.
  proc; call (:true); wp.
  while (i <= l) (l - i) => *;
  wp; call (:true);  auto => /> /#.
qed.

end LWE_Hybrid.

(* --------------------- *)
(*  dyn matrix lemmas    *)
(* --------------------- *)

(* --------------- *)
(* LWE adversaries *)
(* --------------- *)
op H : seed -> int -> int -> matrix.
axiom H_mem: forall sd x y, H sd x y \in duni_matrix x y.

op n : { int | 0 < n } as gt0_n.
op nb : { int | 0 < nb } as gt0_nb.
op mb : { int | 0 < mb } as gt0_mb.

hint exact: gt0_n gt0_nb gt0_mb.
hint simplify (gt0_n, gt0_nb, gt0_mb).

(* LWE adversary *)
module LWE_H1(Adv : Adv_M0) = {
  proc main(b : bool) : bool = {
    var b', sd, _A, s, e, u0, u1, u;

    sd <$ dseed;
    _A <- H sd n n;
    s <$ Chi_matrix n nb;
    e <$ Chi_matrix n nb;
    u0 <- _A * s + e;
    u1 <$ duni_matrix n nb;
    u <- if b then u1 else u0;

    b' <@ Adv.guess(sd, u);
    return b';
   }
}.

section.
clone import LWE_Hybrid as LWE_Hyb1 with
  op G <- fun sd m n => trmx (H sd m n),
  op k <- 0,
  op l <- nb,
  op m <- n,
  op n <- n
  rename "G" as "H"
  rename "l" as "nb"
  proof * by done.

module Adv_M_T(Adv: Adv_M) = {
  proc guess(sd: seed, m0: matrix): bool = {
    var b, _B;
    _B <$ duni_matrix n 0;
    m0 <- trmx m0;
    b <@ Adv.guess(sd, _B, m0);
    return b;
  }
}.

lemma LWE_H1_Eq (A <: Adv_M{-LWE_M}) b &m:
    Pr[LWE_H1(Adv_M_T(A)).main(b) @ &m: res] = Pr[LWE_M(A).main(b) @ &m: res].
proof.
byequiv => //.
proc; inline *.
swap {1} 10 -7; swap {1} 8 1; wp.
call (:true) => /=; wp.
rnd trmx trmx.
wp.
rnd trmx trmx.
rnd trmx trmx.
auto => //= />.
move => sd ? _B ? *.
split => *.
+ rewrite /Chi_matrix.
  by apply (dfuni_matrix_tr1E _ _ nb n).
split => *.
+ by rewrite supp_dmatrix_tr.
split => *.
+ by rewrite supp_dmatrix_tr.
move => *; split => *.
+ rewrite /duni_matrix. by apply (dfuni_matrix_tr1E _ duni_R nb n).
split => *.
+ by rewrite supp_dmatrix_tr.
have -> := (catmr_empty (trmx (H sd n n)) _B n n duni_R _ _ _ _); 1..2, 4: by trivial. by rewrite supp_dmatrix_tr // H_mem.
case (b) => * //.
qed.


lemma LWE_H1_restr (A <: Adv_M{-Hyb.Count, -LWE_Ob, -LWE_M_Loop, -Hyb_Mock, -LWE_RO.RO, -LWE_RO.FRO, -LWE_V, -LWE_V_Aux, -LWE_M}) &m:
    islossless A.guess =>
    Pr[LWE_H1(Adv_M_T(A)).main(false) @ &m: res] - Pr[LWE_H1(Adv_M_T(A)).main(true) @ &m: res]
  = nb%r * (Pr[LWE_V(Hyb_Mock(B(A))).main(false) @ &m : res] - Pr[LWE_V(Hyb_Mock(B(A))).main(true) @ &m : res]).
proof.
rewrite !(LWE_H1_Eq A).
apply (LWE_H_Hybrid A).
qed.

end section.

section.

clone import LWE_Hybrid as LWE_Hyb2 with
  op G <- H,
  op k <- nb,
  op l <- mb,
  op m <- n,
  op n <- n
  rename "G" as "H"
  rename "l" as "mb"
  proof * by done.

module LWE_H2(Adv : Adv_M) = {
  proc main(b : bool) : bool = {
    var sd, b', _A, s', u0, u1, _B, e;

    sd <$ dseed;
    _B <$ duni_matrix n nb;
    s' <$ Chi_matrix mb n;
    e <$ Chi_matrix mb (n + nb);

    _A <- H sd n n;
    u0 <- s' * (_A || _B) + e;
    u1 <$ duni_matrix mb (n + nb);

    b' <@ Adv.guess(sd, _B, if b then u1 else u0);
    return b';
   }
}.

lemma LWE_H2_restr(A <: Adv_M{-Hyb.Count, -LWE_Ob, -LWE_M_Loop, -Hyb_Mock, -LWE_RO.RO, -LWE_RO.FRO, -LWE_V, -LWE_V_Aux, -LWE_M}) &m:
    islossless A.guess =>
    Pr[LWE_H2(A).main(false) @ &m: res] - Pr[LWE_H2(A).main(true) @ &m: res]
  = mb%r * (Pr[LWE_V(Hyb_Mock(B(A))).main(false) @ &m : res] - Pr[LWE_V(Hyb_Mock(B(A))).main(true) @ &m : res]).
proof.
have h : forall b, Pr[LWE_H2(A).main(b) @ &m: res] = Pr[LWE_M(A).main(b) @ &m: res].
+ move => b.
  byequiv => //.
  proc; inline *; wp.
  call (: true) => /=; wp.
  rnd. auto.
rewrite !h.
apply (LWE_H_Hybrid A).
qed.

end section.
