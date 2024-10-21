require import AllCore Distr List SmtMap Dexcepted PKE_ROM StdOrder.
require (**RndExcept **) LWE FLPRG DynMatrix.
(*****) import IntOrder.

clone import DynMatrix as DM.
clone import LWE as LWE_ with
  theory DM <- DM.

import LWE_.Dmatrix_.

lemma cancel_mb_nb_addm0 (m: matrix): size m = (mb, nb) => m = m + zerom mb nb.
proof.
    move => //= *.
    by rewrite lin_addm0 => /#.
qed.

lemma cancel_mb_nb_add0m (m: matrix): size m = (mb, nb) => m = zerom mb nb + m.
proof.
    move => //= *.
    by rewrite lin_add0m => /#.
qed.

lemma supp_cancel_mb_nb_addm0 m : forall d, m \in dmatrix d mb nb => m = m + zerom mb nb.
proof. move => d h. by apply /cancel_mb_nb_addm0 /(size_dmatrix _ _ _ _ h). qed.

lemma supp_cancel_mb_nb_add0m m : forall d, m \in dmatrix d mb nb => m = zerom mb nb + m.
proof. rewrite addmC. apply supp_cancel_mb_nb_addm0. qed. 

lemma supp_duni_cancel_mb_nb_addm0 m : m \in dmatrix duni_R mb nb => m = m + zerom mb nb.
proof. by apply supp_cancel_mb_nb_addm0. qed.

lemma supp_duni_cancel_mb_nb_add0m m : m \in dmatrix duni_R mb nb => m = zerom mb nb + m.
proof. by apply supp_cancel_mb_nb_add0m. qed.

hint exact: cancel_mb_nb_addm0 cancel_mb_nb_add0m supp_cancel_mb_nb_addm0 supp_cancel_mb_nb_add0m supp_duni_cancel_mb_nb_addm0 supp_duni_cancel_mb_nb_add0m.

(******************************************************************)
(*                pke definition                                  *)
(******************************************************************)
type plaintext.
type ciphertext.

type raw_ciphertext = matrix * matrix.

op m_encode : plaintext -> matrix.
op m_decode : matrix -> plaintext.

axiom m_encode_rows m : rows (m_encode m) = mb.
axiom m_encode_cols m : cols (m_encode m) = nb.

hint exact: m_encode_rows m_encode_cols.
hint simplify (m_encode_rows, m_encode_cols).

op c_encode : raw_ciphertext -> ciphertext.
op c_decode : ciphertext -> raw_ciphertext.

type pkey.
type skey.

type raw_pkey  = seed * matrix.
type raw_skey  = matrix.

op pk_encode : raw_pkey -> pkey.
op sk_encode : raw_skey -> skey.
op pk_decode : pkey -> raw_pkey.
op sk_decode : skey -> raw_skey.

axiom pk_encodeK : cancel pk_encode pk_decode.
axiom sk_encodeK : cancel sk_encode sk_decode.

(******************************************************************)
(*                The Hashed Encryption Scheme                     *)
(******************************************************************)

type randomness.

op [uniform full lossless]drand : randomness distr.

op prg_kg : randomness -> seed * matrix * matrix.
op prg_kg_ideal  =
     dlet dseed
       (fun (sd : seed) =>
          dlet (dmatrix Chi n nb) (fun (s : matrix) =>
               dmap (dmatrix Chi n nb) (fun (e : matrix) => (sd, s, e)))).

op prg_enc : randomness -> matrix * matrix * matrix.
op prg_enc_ideal =
     dlet (dmatrix Chi mb n)
       (fun (s' : matrix) =>
          dlet (dmatrix Chi mb n) (fun (e' : matrix) =>
               dmap (dmatrix Chi mb nb)  (fun (e'' : matrix) => (s', e', e'')))).

op kg(r : randomness) : pkey * skey =
   let (sd,s,e) = prg_kg r in
   let _B =  (H sd n n) * s + e in
       (pk_encode (sd,_B),sk_encode s).

op enc(rr : randomness, pk : pkey, m : plaintext) : ciphertext =
    let (sd,_B) = pk_decode pk in
    let (s',e',e'') = prg_enc rr in
    let _B' = s' * (H sd n n) + e' in
    let v = s' * _B + e'' in
        c_encode (_B',v + m_encode m).


op dec(sk : skey, c : ciphertext) : plaintext option =
    let (c1,c2) = c_decode c in
       Some (m_decode (c2 + -(c1 * sk_decode sk))).

(******************************************************************)
(*    The Security Games                                          *)
(******************************************************************)
clone import PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

module LWE_PKE_HASH : Scheme = {

  proc kg() : pkey * skey = {
     var r,pk,sk;
     r <$ drand;
     (pk,sk) <- kg r;
     return (pk,sk);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
     var rr,c;
     rr <$ drand;
     c <- enc rr pk m;
     return c;
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var mo;
    mo <- dec sk c;
    return mo;
  }
}.

module LWE_PKE_HASH_PROC : Scheme = {
  proc kg(): pkey * skey = {
    var sd,s,e,t;
    sd <$ dseed;
    s  <$ dmatrix Chi n nb;
    e  <$ dmatrix Chi n nb;
    t  <- (H sd n n) * s + e;
    return (pk_encode (sd,t),sk_encode s);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var sd, b,s',e',e'',b',v;
    (sd,b) <- pk_decode pk;
    s'  <$ dmatrix Chi mb n;
    e' <$ dmatrix Chi mb n;
    e'' <$ dmatrix Chi mb nb;
    b'  <- s' * (H sd n n) + e';
    v  <- s' * b + e'';
    return c_encode (b',v + m_encode m);
  }

  proc dec(sk : skey, c : ciphertext) : plaintext option = {
    var c1,c2;
    (c1,c2) <- c_decode c;
    return (Some (m_decode (c2 + -(c1 * sk_decode sk))));
  }
}.

clone import FLPRG as PRG_KG with
  type seed <- randomness,
  type output <- seed * matrix * matrix,
  op prg <- prg_kg,
  op dseed <- drand,
  op dout <- prg_kg_ideal
  proof *.

clone import FLPRG as PRG_ENC with
  type seed <- randomness,
  type output <- matrix * matrix * matrix,
  op prg <- prg_enc,
  op dseed <- drand,
  op dout <- prg_enc_ideal
  proof*.

module LWE_PKE_HASH_PRG : Scheme  = {
  var sd : seed
  var s  : matrix
  var e  : matrix
  var s'  : matrix
  var e' : matrix
  var e'' : matrix

  proc kg() : pkey * skey = {
     var t;
     t <-  (H sd n n) * s + e;
     return (pk_encode (sd,t),sk_encode s);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
     var sd,b,b',v;
     (sd,b) <- pk_decode pk;
     b' <- s' * (H sd n n) + e';
     v <- s' * b + e'';
     return c_encode (b',v + m_encode m);
  }

  include LWE_PKE_HASH [dec]
}.

module (D_KG(A : Adversary) : PRG_KG.Distinguisher)  = {
   proc distinguish(sd : seed, s : matrix, e : matrix) : bool = {
       var coins,b;
       LWE_PKE_HASH_PRG.sd <- sd;
       LWE_PKE_HASH_PRG.s <- s;
       LWE_PKE_HASH_PRG.e <- e;
       coins <$ drand;
       (LWE_PKE_HASH_PRG.s',LWE_PKE_HASH_PRG.e',LWE_PKE_HASH_PRG.e'') <- prg_enc coins;
       b <@ CPA(LWE_PKE_HASH_PRG,A).main();
       return b;
   }
}.

module (D_ENC(A : Adversary) : PRG_ENC.Distinguisher) = {
   proc distinguish(s' : matrix, e' : matrix, e'' : matrix) : bool = {
       var b;
       (LWE_PKE_HASH_PRG.sd,LWE_PKE_HASH_PRG.s,LWE_PKE_HASH_PRG.e) <$ prg_kg_ideal;
       LWE_PKE_HASH_PRG.s' <- s';
       LWE_PKE_HASH_PRG.e' <- e';
       LWE_PKE_HASH_PRG.e'' <- e'';
       b <@ CPA(LWE_PKE_HASH_PRG,A).main();
       return b;
   }
}.

module (DC_KG(A : CORR_ADV) : PRG_KG.Distinguisher)  = {
   proc distinguish(sd : seed, s : matrix, e : matrix) : bool = {
       var coins,b;
       LWE_PKE_HASH_PRG.sd <- sd;
       LWE_PKE_HASH_PRG.s <- s;
       LWE_PKE_HASH_PRG.e <- e;
       coins <$ drand;
       (LWE_PKE_HASH_PRG.s',LWE_PKE_HASH_PRG.e',LWE_PKE_HASH_PRG.e'') <- prg_enc coins;
       b <@ Correctness_Adv(LWE_PKE_HASH_PRG,A).main();
       return b;
   }
}.

module (DC_ENC(A : CORR_ADV) : PRG_ENC.Distinguisher) = {
   proc distinguish(s' : matrix, e' : matrix, e'' : matrix) : bool = {
       var b;
       (LWE_PKE_HASH_PRG.sd,LWE_PKE_HASH_PRG.s,LWE_PKE_HASH_PRG.e) <$ prg_kg_ideal;
       LWE_PKE_HASH_PRG.s' <- s';
       LWE_PKE_HASH_PRG.e' <- e';
       LWE_PKE_HASH_PRG.e'' <- e'';
       b <@ Correctness_Adv(LWE_PKE_HASH_PRG,A).main();
       return b;
   }
}.

section.
declare module A <: Adversary {-LWE_PKE_HASH_PRG}.

lemma cpa_proc &m :
  Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res] -
   Pr[CPA(LWE_PKE_HASH_PROC,A).main() @ &m : res] =
     Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ] -
        Pr [ PRG_KG.IND(PRG_KG.PRGi,D_KG(A)).main() @ &m : res ] +
     Pr [ PRG_ENC.IND(PRG_ENC.PRGr,D_ENC(A)).main() @ &m : res ] -
        Pr [ PRG_ENC.IND(PRG_ENC.PRGi, D_ENC(A)).main() @ &m : res ].
proof.
have -> : Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res]  =
  Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ].
  byequiv => //.
  proc.
  inline *.
  swap {1} 8 -4.
  by wp;call (: true);wp;rnd;call (_: true);auto => /> /#.

have -> : Pr[CPA(LWE_PKE_HASH_PROC, A).main() @ &m : res]   =
        Pr[PRG_ENC.IND(PRGi, D_ENC(A)).main() @ &m : res].
+ byequiv => //.
  proc. inline *. swap {1} [11..13] -7. swap {2} 3 -1.  swap {2} 6 -4. swap {2} 4 5.
seq 0 1: #pre; 1: by auto.
seq 3 1 : (#pre /\
    (sd,s,e){1} =
    (LWE_PKE_HASH_PRG.sd, LWE_PKE_HASH_PRG.s, LWE_PKE_HASH_PRG.e){2}). rndsem{1} 0. by auto.
seq 3 6 : (#pre /\
    (s',e',e''){1} =
    (LWE_PKE_HASH_PRG.s', LWE_PKE_HASH_PRG.e', LWE_PKE_HASH_PRG.e''){2}). rndsem{1} 0. by auto.

  wp. call(_: true). auto. call (_: true). by auto.

have -> : Pr[PRG_KG.IND(PRG_KG.PRGi, D_KG(A)).main() @ &m : res] =
          Pr[PRG_ENC.IND(PRG_ENC.PRGr, D_ENC(A)).main() @ &m : res].
            + byequiv => //. proc;inline *. sim. swap {2} 6 -5. by auto.
by ring.
qed.

end section.

(******************************************************************)
(*       Game Hopping Security                                    *)
(******************************************************************)


(* Hop 1 *)

module LWE_PKE_HASH1 = {
  proc kg() : pkey * skey = {
    var sd,s,b;
    sd <$ dseed;
    s  <$ dmatrix Chi n nb;
    b  <$ dmatrix duni_R n nb;
    return (pk_encode (sd,b), sk_encode s);
  }

  include LWE_PKE_HASH_PROC [-kg]

}.

module B1(A : Adversary) : Adv_M0 = {

  proc guess(sd, u : matrix) : bool = {
    var pk, m0, m1, c, b, b';
    pk <- pk_encode (sd,u);
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    c <@ LWE_PKE_HASH1.enc(pk, if b then m1 else m0);
    b' <@ A.guess(c);
    return b' = b;
  }
}.

section.

declare module A <: Adversary.

lemma hop1_left &m:
  Pr[CPA(LWE_PKE_HASH_PROC,A).main() @ &m : res] =
  Pr[LWE_H1(B1(A)).main(false) @ &m : res].
proof.
byequiv => //.
proc. inline *.
wp. sim. wp. rnd{2}. wp. by auto.
qed.

lemma hop1_right &m:
  Pr[LWE_H1(B1(A)).main(true) @ &m : res] =
  Pr[CPA(LWE_PKE_HASH1,A).main() @ &m : res].
proof.
byequiv => //.
proc;inline *.
wp. sim. wp. rnd. wp. rnd{1}. rnd. wp. rnd.
by auto.
qed.

end section.

(* Hop 2 *)

module LWE_PKE_HASH2 = {

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var _A,b', v;
    _A <- H (pk_decode pk).`1;
    b' <$ dmatrix duni_R mb n;
    v <$ dmatrix duni_R mb nb;
    return c_encode (b',v + m_encode m);  }

  include LWE_PKE_HASH1 [-enc]

}.


module B2(A : Adversary) : Adv_M = {

  proc guess(sd : seed, _B : matrix, b'v : matrix) : bool = {
    var pk, m0, m1, c, b, m, b';
    pk <- pk_encode (sd,_B);
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    m <- if b then m1 else m0;
    c <- c_encode((subm b'v 0 mb 0 n, subm b'v 0 mb n (n + nb) + m_encode m));
    b' <@ A.guess(c);
    return b' = b;
  }

}.

section.

declare module A <: Adversary.

lemma hop2_left &m:
  Pr[CPA(LWE_PKE_HASH1,A).main() @ &m : res] =
  Pr[LWE_H2(B2(A)).main(false) @ &m : res].
proof.
byequiv => //.
proc. inline *.
wp.
call (:true).
swap{1} 8 6; swap{1} [5..6] 7.
wp; rnd; call(:true). wp. rnd{2}. wp.
rndsem*{1} 7.
rnd (fun (e: matrix * matrix) => e.`1 || e.`2) (fun e => (subm e 0 mb 0 n, subm e 0 mb n (n + nb))).
rnd. wp. rnd. rnd{1}. rnd. auto => /> ? ? s hs _b h_b s' hs'.
split => [? h|? *].
+ rewrite -{1}subm_id.
  rewrite (subm_catmr _ _ _ 0 n nb) //.
  congr; move :h; by rewrite supp_dmatrix // 1:addr_ge0.
+ split => ?. 
  + rewrite supp_dmatrix 2:addz_ge0 // => [#] *.
    by rewrite -dprod_dlet dmatrix_catmr1E.
  + move => [e' e''].
    rewrite -dprod_dlet supp_dprod /=.
    rewrite !supp_dmatrix 6:addr_ge0 1..7:// => [#] he'r he'c ? he''r he''c ?.
    rewrite size_catmr rows_catmr he'r he'c he''r he''c => />.
    split => [i j|*].
    + rewrite cols_catmr get_catmr he'c he''c => *.
      case (j < n) => *.
      + by rewrite (getm0E _ i (j - n)) 1:/# ZR.addr0 => /#.
      + by rewrite (getm0E _ i j) 1:/# ZR.add0r => /#.
    + split => *.
      + smt(subm_catmrCl subm_catmrCr).
      + rewrite pk_encodeK /=.
        move :hs h_b hs'.
        rewrite !supp_dmatrix // => [#] ? ? ? [#] ? ? ? [#] ? ? ?.
        rewrite mulmx_catmrD 1:/# addm_catmr 1:cols_mulmx 1:/#.
        pose X := s' * _ + e'.
        pose Y := s' * _ + e''.
        have := subm_catmrCl X Y.
        have := subm_catmrCr X Y.
        rewrite !rows_addm !rows_mulmx !cols_addm !cols_mulmx => /#.
qed.

lemma hop2_right &m:
  Pr[LWE_H2(B2(A)).main(true) @ &m : res] =
  Pr[CPA(LWE_PKE_HASH2,A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *; wp.
call (:true).
swap {2} 7 -2. swap{2} [4..9] 2.
wp. rnd. call(:true).
wp.
rndsem*{2} 3.
rnd (fun m => (subm m 0 mb 0 n, subm m 0 mb n (n + nb))) (fun (m: matrix * matrix) => m.`1 || m.`2).
wp. swap{2} 2 1. do 2! rnd{1}. rnd{2}. auto => /> *.
have h : forall (b'0v: matrix * matrix), b'0v \in dlet (dmatrix duni_R mb n) (fun b'0 => dmap (dmatrix duni_R mb nb) (fun v => (b'0, v)))
  => size b'0v.`1 = (mb, n) /\ size b'0v.`2 = (mb, nb) /\
     subm (b'0v.`1 || b'0v.`2) 0 mb 0 n = b'0v.`1 /\ subm (b'0v.`1 || b'0v.`2) 0 mb n (n + nb) = b'0v.`2.
+ move => -[b'0 v]. rewrite -dprod_dlet supp_dprod !supp_dmatrix 1..4:// => />.
  smt(subm_catmrCl subm_catmrCr).
split => [? hb0v|*].
+ have /# := h _ hb0v.
split => [? hb0v|? ?].
+ have [#] * := h _ hb0v.
  rewrite -dprod_dlet dmatrix_catmr1E 1,2:// 1:size_catmr 1:/# => /#.
+ rewrite -dprod_dlet supp_dprod /=.
  rewrite !supp_dmatrix 2:addr_ge0 1..7:// !size_subm => [#].
  have -> /> hur huc hu: n+nb-n = nb; 1: by rewrite /#.
  split => *.
  + split => *; rewrite get_subm 1,2:/#.
    rewrite hu hur huc ltr_paddr 1:// 1:/# => />.
    rewrite hu hur huc [n+nb]addrC ltr_le_add 1:/# 1:// [0 <= _ + n]addr_ge0 => />.
  + by rewrite -{1}subm_id hur huc (subm_catmr _ _ _ 0 n nb). 
qed.
end section.

(* Final game analysis *)

section.

declare module A <: Adversary {-LWE_PKE_HASH_PRG,
  -LWE_Hyb1.Hyb.Count, -LWE_Hyb1.LWE_Ob, -LWE_Hyb1.LWE_M_Loop, -LWE_Hyb1.Hyb_Mock, -LWE_Hyb1.LWE_RO.RO, -LWE_Hyb1.LWE_RO.FRO, -LWE_Hyb1.LWE_V, -LWE_Hyb1.LWE_V_Aux, -LWE_Hyb1.LWE_M,
  -LWE_Hyb2.Hyb.Count, -LWE_Hyb2.LWE_Ob, -LWE_Hyb2.LWE_M_Loop, -LWE_Hyb2.Hyb_Mock, -LWE_Hyb2.LWE_RO.RO, -LWE_Hyb2.LWE_RO.FRO, -LWE_Hyb2.LWE_V, -LWE_Hyb2.LWE_V_Aux, -LWE_Hyb2.LWE_M
}.


local module Game2(A : Adversary) = {
  proc main() = {
    var sd, _B, m0, m1, m, _B', v, c, b, b';
    sd <$ dseed;
    _B <$ dmatrix duni_R n nb;
    (m0, m1) <@ A.choose(pk_encode (sd,_B));
    b <$ {0,1};
    m <- if b then m1 else m0;

    _B' <$ dmatrix duni_R mb n;
    v <$ dmatrix duni_R mb nb;
    c <- c_encode(_B', v);
    b' <@ A.guess(c);
    return b = b';
  }
}.

local lemma game2_equiv &m :
  Pr[CPA(LWE_PKE_HASH2,A).main() @ &m : res] =
  Pr[Game2(A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
call(_: true). wp.
rnd (fun z, z + m_encode m{2})
    (fun z, z - m_encode m{2}).
auto. call(_:true). auto. rnd{1}.
auto => /> *.
pose x := m_encode _.
split.
+ move => ?.
  by rewrite supp_dmatrix 1,2:// -addmA [_+x]addmC addmN.
move => *.
split.
+ move => vR ?.
  rewrite !mu1_uni; rewrite ?duni_matrix_uni.
  have ->: vR - x \in dmatrix duni_R mb nb.
  smt(duni_matrix_fu rows_addm rows_neg cols_addm cols_neg m_encode_rows m_encode_cols).
  by rewrite /#.
move => ? vL *.
split => *.
+ smt(duni_matrix_fu rows_addm rows_neg cols_addm cols_neg m_encode_rows m_encode_cols).
split => [|/#].
+ by rewrite -addmA addmN.
qed.

local lemma game2_prob &m :
  islossless A.guess => islossless A.choose =>
  Pr[Game2(A).main() @ &m : res] = 1%r / 2%r.
proof.
move => A_guess_ll A_choose_ll.
byphoare => //.
proc.
swap [4..5] 4;wp.
rnd  (fun bb => bb = b') => //=.
conseq (: _ ==> true).
+ by move=> />; apply DBool.dbool1E.
by islossless.
qed.

lemma main_theorem &m :
  islossless A.guess => islossless A.choose =>
  `| Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res] -  1%r / 2%r | <=
    nb%r * `| Pr[LWE_Hyb1.LWE_V(LWE_Hyb1.Hyb_Mock(LWE_Hyb1.B(Adv_M_T'(B1(A))))).main(false) @ &m : res]
            - Pr[LWE_Hyb1.LWE_V(LWE_Hyb1.Hyb_Mock(LWE_Hyb1.B(Adv_M_T'(B1(A))))).main(true) @ &m : res] | +
    mb%r * `| Pr[LWE_Hyb2.LWE_V(LWE_Hyb2.Hyb_Mock(LWE_Hyb2.B(B2(A)))).main(false) @ &m : res]
            - Pr[LWE_Hyb2.LWE_V(LWE_Hyb2.Hyb_Mock(LWE_Hyb2.B(B2(A)))).main(true) @ &m : res] | +
    `| Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ] -
        Pr [ PRG_KG.IND(PRG_KG.PRGi,D_KG(A)).main() @ &m : res ] | +
    `| Pr [ PRG_ENC.IND(PRG_ENC.PRGr,D_ENC(A)).main() @ &m : res ] -
        Pr [ PRG_ENC.IND(PRG_ENC.PRGi, D_ENC(A)).main() @ &m : res ] |.
proof.
move => A_guess_ll A_choose_ll.
have h0 := LWE_H1_restr (B1(A)) &m _; 1: by islossless.
have h1 := LWE_H2_restr (B2(A)) &m _; 1: by islossless.
rewrite -!RealOrder.normrZ.
+ by rewrite -[nb%r]RField.ofintR RealOrder.ler0n.
+ by rewrite -[mb%r]RField.ofintR RealOrder.ler0n.
rewrite -h0 -h1.
have := (cpa_proc A &m).
rewrite (hop1_left A &m).
rewrite (hop1_right A &m).
rewrite (hop2_left A &m).
rewrite (hop2_right A &m).
rewrite (game2_equiv &m).
rewrite (game2_prob &m _ _) //.
by smt().
qed.
end section.

(* NOTE:matrix dimension ? *)
op noise_exp (_A s s' e e' e'': matrix) m =
    let b = _A * s + e in
    let b' = s' * _A + e' in
    let v = s' * b + e'' in
    let (c1, c2) = c_decode (c_encode (b',v + m_encode m)) in
        c2 - c1 * s - m_encode m.

op noise_exp_val (s s' e e' e'': matrix) = s' * e + e'' - e'* s.

op max_noise : int.
op under_noise_bound : matrix -> int -> bool.

axiom good_c_decode c: c_decode (c_encode c) = c.
axiom good_m_decode m n :
  under_noise_bound n max_noise =>
  m_decode (m_encode m + n) = m.

hint simplify (good_c_decode).

module CorrectnessAdvNoise(A : CORR_ADV) = {
  proc main() = {
    var sd,s,s',e, e', e'', t, _A, m, nu, pk, sk;
    sd <$ dseed;
    s  <$ dmatrix Chi n nb;
    s'  <$ dmatrix Chi mb n;
    e  <$ dmatrix Chi n nb;
    e'  <$ dmatrix Chi mb n;
    e''  <$ dmatrix Chi mb nb;
    _A <- H sd n n;
    t  <- _A * s + e;

    (pk, sk) <- (pk_encode (sd,t), sk_encode s);
    m <@ A.find(pk, sk);
    nu <- noise_exp _A s s' e e' e'' m;

    return !under_noise_bound nu max_noise;
  }
}.

module CorrectnessBound = {
  proc main() = {
    var s, s', e, e', e'', nu;
    s  <$ dmatrix Chi n nb;
    s'  <$ dmatrix Chi mb n;
    e  <$ dmatrix Chi n nb;
    e'  <$ dmatrix Chi mb n;
    e''  <$ dmatrix Chi mb nb;
    nu <- noise_exp_val s s' e e' e'';
    return !under_noise_bound nu max_noise;
  }
}.


(* correctness *)
section.
declare module A <: CORR_ADV  {-LWE_PKE_HASH_PRG}.

lemma corr_proc &m :
    Pr[Correctness_Adv(LWE_PKE_HASH, A).main() @ &m: res] -
    Pr[Correctness_Adv(LWE_PKE_HASH_PROC, A).main() @ &m: res] =
    Pr[PRG_KG.IND(PRG_KG.PRGr,DC_KG(A)).main() @ &m: res] -
      Pr[PRG_KG.IND(PRG_KG.PRGi,DC_KG(A)).main() @ &m: res] +
    Pr[PRG_ENC.IND(PRG_ENC.PRGr,DC_ENC(A)).main() @ &m: res] -
      Pr[PRG_ENC.IND(PRG_ENC.PRGi, DC_ENC(A)).main() @ &m: res].
proof.
have -> : Pr[Correctness_Adv(LWE_PKE_HASH, A).main() @ &m: res] =
  Pr[PRG_KG.IND(PRG_KG.PRGr, DC_KG(A)).main() @ &m: res].
+ byequiv => //.
  proc; inline *.
  swap {1} 7 -5.
  wp; call (:true).
  by auto => /#.
have ->: Pr[PRG_KG.IND(PRG_KG.PRGi,DC_KG(A)).main() @ &m: res] =
  Pr[PRG_ENC.IND(PRG_ENC.PRGr,DC_ENC(A)).main() @ &m: res].
+ byequiv => //.
  proc; inline *.
  wp. swap {2} 6 -5.
  call(:true).
  by auto.
have ->: Pr[Correctness_Adv(LWE_PKE_HASH_PROC, A).main() @ &m: res] =
  Pr[PRG_ENC.IND(PRG_ENC.PRGi, DC_ENC(A)).main() @ &m: res].
+ byequiv => //.
  proc; inline *.
  swap {2} 6 -3. swap {2} [10..15] -6.
  wp. rndsem {1} 9. rnd. wp.
  call (: true).
  wp. rndsem {1} 0. rnd.
  by auto.

by ring.
qed.

lemma correctness_noise &m:
  Pr[ Correctness_Adv(LWE_PKE_HASH_PROC,A).main() @ &m : res]  <=
  Pr[ CorrectnessAdvNoise(A).main() @ &m : res].
proof.
byequiv => //.
proc. inline *.
swap {1} 10 -7; swap {1} [11..12] -6.
seq 9 10: (
  ={sd, s, s', e, e', e'', m} /\
  pk{1} = pk_encode (sd{1}, t{1}) /\
  sk{1} = sk_encode s{1} /\
  t{1} = H sd{1} n n * s{1} + e{1} /\
  _A{2} = H sd{2} n n /\
  s{1} \in dmatrix Chi n nb /\
  s'{1} \in dmatrix Chi mb n /\
  e'{1} \in dmatrix Chi mb n /\
  e''{1} \in dmatrix Chi mb nb /\
  e{1} \in dmatrix Chi n nb
).
+ call (_:true); auto => />.

auto => /> &2.
rewrite !supp_dmatrix // => ? ? ? ? ?.
rewrite pk_encodeK sk_encodeK.
rewrite /noise_exp /= [_+m_encode _]addmC -addmA.
pose x := _ * (H _ n n * _ + _) + _ - _.
apply Logic.contra.
rewrite [_+x-_]addmC addmA addNm m_encode_rows m_encode_cols.
rewrite -cancel_mb_nb_add0m.
+ rewrite /x mulmxDr mulmxDl oppmD.
  rewrite ?rows_addm ?rows_neg ?rows_mulmx ?cols_addm ?cols_neg ?cols_mulmx /=.
  rewrite /#.
by apply good_m_decode.
qed.

lemma matrix_cancel (x y z: matrix): x = y => x + z = y + z.
proof. done. qed.

lemma correctness_bound &m:
  islossless A.find =>
  Pr[ CorrectnessAdvNoise(A).main() @ &m : res] =
  Pr[ CorrectnessBound.main() @ &m : res].
proof.
move => *.
byequiv => //.
proc; inline *.
wp. call{1}(:true ==> true). wp. do 5! rnd. rnd{1}.
auto => // />.
move => sd hsd s hs s' hs' e he e' he' e'' he''.
move :hs hs' he he' he''.
rewrite !supp_dmatrix // => ? ? ? ? ? ?. 
apply /congr1; congr.
rewrite /noise_exp/noise_exp_val => /=.
rewrite -[(_ - _ - _)%Matrices]addmA -oppmD mulmxDl mulmxDr.
rewrite sub_eqm /= ?rows_addm ?rows_neg ?rows_mulmx ?cols_addm ?cols_neg ?cols_mulmx;
1..2: rewrite /#.

rewrite addmA.
apply matrix_cancel.
rewrite mulmxA.
pose x := s' * _ * s. rewrite -[x + _ + _]addmA.
pose y := s' * e + e''.
pose z := e' * s.
rewrite [y-z+_]addmC.
rewrite [_+(y-z)]addmA.
rewrite -[x+z+y]addmA.
rewrite [z+y]addmC.
rewrite -addmA -addmA addmN.
rewrite [_+(y+_)]addmA.
rewrite lin_addm0;
rewrite /x /y /z;
rewrite ?rows_addm ?rows_mulmx ?cols_addm ?cols_mulmx; rewrite /#.
qed.

lemma correctness_theorem &m :
  islossless A.find =>
  Pr[Correctness_Adv(LWE_PKE_HASH, A).main() @ &m: res] <=
  Pr[CorrectnessBound.main() @ &m : res] +
  (Pr[PRG_KG.IND(PRG_KG.PRGr,DC_KG(A)).main() @ &m: res] -
    Pr[PRG_KG.IND(PRG_KG.PRGi,DC_KG(A)).main() @ &m: res] +
  Pr[PRG_ENC.IND(PRG_ENC.PRGr,DC_ENC(A)).main() @ &m: res] -
    Pr[PRG_ENC.IND(PRG_ENC.PRGi, DC_ENC(A)).main() @ &m: res]).
proof.
move => *.
rewrite -correctness_bound // -corr_proc.
pose x := Pr[Correctness_Adv(LWE_PKE_HASH, A).main() @ &m : res].
rewrite RField.addrA [(_+x)%Real]RField.addrC -RField.addrA.
rewrite RealOrder.ler_addl RealOrder.subr_ge0.
exact correctness_noise.
qed.

end section.
