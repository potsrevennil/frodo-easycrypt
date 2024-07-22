require import AllCore Distr List SmtMap Dexcepted PKE_ROM StdOrder.
require (**RndExcept **) LWE FLPRG.
(*****) import IntOrder.

theory LWE_PKE_Hash.

clone import LWE as LWE_.
import Matrix.
import ZR.

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

type randomness.

op [uniform full lossless]drand : randomness distr.

op prg_kg : randomness -> seed * matrix * matrix.
op prg_kg_ideal  = 
     dlet dseed
       (fun (sd : seed) => 
          dlet (Chi_matrix n nb) (fun (s : matrix) => 
               dmap (Chi_matrix n nb) (fun (e : matrix) => (sd, s, e)))).

op prg_enc : randomness -> matrix * matrix * matrix.
op prg_enc_ideal = 
     dlet (Chi_matrix mb n)
       (fun (s' : matrix) => 
          dlet (Chi_matrix mb n) (fun (e' : matrix) => 
               dmap (Chi_matrix mb nb)  (fun (e'' : matrix) => (s', e', e'')))).

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
    s  <$ Chi_matrix n nb;
    e  <$ Chi_matrix n nb;
    t  <- (H sd n n) * s + e;
    return (pk_encode (sd,t),sk_encode s);
  }

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var sd, b,s',e',e'',b',v;
    (sd,b) <- pk_decode pk;
    s'  <$ Chi_matrix mb n;
    e' <$ Chi_matrix mb n;
    e'' <$ Chi_matrix mb nb;
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
    s  <$ Chi_matrix n nb;
    b  <$ duni_matrix n nb;
    return (pk_encode (sd,b), sk_encode s);
  }

  include LWE_PKE_HASH_PROC [-kg]

}.

module B1(A : Adversary) : HAdv1_T = {

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
wp. sim. wp. rnd{2}. wp. auto => /= />. rewrite duni_matrix_ll => //.
qed.

lemma hop1_right &m: 
  Pr[LWE_H1(B1(A)).main(true) @ &m : res] = 
  Pr[CPA(LWE_PKE_HASH1,A).main() @ &m : res].
proof.
byequiv => //.
proc;inline *. 
wp. sim. wp. rnd. wp. rnd{1}. rnd. wp. rnd.
auto => /= />. rewrite Chi_matrix_ll => //.
qed.

end section.

(* Hop 2 *)

module LWE_PKE_HASH2 = {

  proc enc(pk : pkey, m : plaintext) : ciphertext = {
    var _A,b', v;
    _A <- H (pk_decode pk).`1;
    b' <$ duni_matrix mb n;
    v <$ duni_matrix mb nb;
    return c_encode (b',v + m_encode m);  }

  include LWE_PKE_HASH1 [-enc]

}.


module B2(A : Adversary) : HAdv2_T = {
  
  proc guess(sd : seed, _B : matrix, b'v : matrix * matrix) : bool = {
    var pk, m0, m1, c, b, m, b';
    pk <- pk_encode (sd,_B);
    (m0, m1) <@ A.choose(pk);
    b <$ {0,1};
    m <- if b then m1 else m0;
    c <- c_encode((b'v.`1, b'v.`2 + m_encode m));
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
wp. swap {2} 11 -9. swap {2} 12 -8. swap {2} [14..16] -9.

seq 4 5 : (#pre /\ ={pk} /\ b0{1} = _B{2} /\ (pk_decode pk{2}).`1 = seed{2} /\ (pk_decode pk{2}).`2 = _B{2});
  1: by wp; rnd; rnd{1}; wp; rnd; auto; rewrite !Chi_matrix_ll => /> *; rewrite pk_encodeK => //.

  call (:true). wp. rnd{2}. wp. rnd{2}. do 2! wp. do 3! rnd. do 2! wp. rnd. call (:true). 
auto. rewrite! duni_matrix_ll => //.
qed.

lemma hop2_right &m: 
  Pr[LWE_H2(B2(A)).main(true) @ &m : res] = 
  Pr[CPA(LWE_PKE_HASH2,A).main() @ &m : res].
proof.
byequiv => //.
proc. inline *. 
swap {1} 11 -9. swap {1} 12 -8. swap{1} 8 -3. swap {1} [14..17] -9. swap {1} 16 -3. swap {1} 15 -2.

seq 5 4 : (#pre /\ ={pk} /\ _B{1} = b0{2} /\ (pk_decode pk{2}).`1 = sd{2} /\ (pk_decode pk{2}).`2 = b0{2}).
  by wp; rnd; rnd{2}; wp; rnd; auto => />; rewrite !Chi_matrix_ll => // *;rewrite pk_encodeK. 
wp. call (:true). wp. do 2! rnd. do 3! rnd{1}. wp. rnd. call (:true).
auto => />. rewrite !Chi_matrix_ll => //.
qed.

end section.

(* Final game analysis *)

section.

declare module A <: Adversary {-LWE_PKE_HASH_PRG}.

local module Game2(A : Adversary) = {
  proc main() = {
    var sd, _B, m0, m1, m, _B', v, c, b, b';
    sd <$ dseed;
    _B <$ duni_matrix n nb;
    (m0, m1) <@ A.choose(pk_encode (sd,_B));
    b <$ {0,1};
    m <- if b then m1 else m0;

    _B' <$ duni_matrix mb n;
    v <$ duni_matrix mb nb;
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
rnd. wp. rnd. call(_:true). wp. rnd. rnd{1}. rnd.
auto => /> *. rewrite Chi_matrix_ll => /> ? ? ? ? result_R bL *.
have h: forall (m: matrix), m \in duni_matrix mb nb => size m = (mb, nb).
   move => *. 
   apply (size_dmatrix duni_R mb nb) => //; 1..2: by smt (gt0_mb gt0_nb).
split. 
+ move => vR *.
  rewrite -addmA addNm m_encode_rows m_encode_cols eq_sym.
  smt (lin_addm0 gt0_mb gt0_nb).
move => ?;split.
move => vR0 ?. 
have : size ((vR0 - m_encode (if bL then result_R.`2 else result_R.`1))) = (mb,nb); last by 
  smt(duni_matrix_fu duni_matrix_uni mu1_uni gt0_mb gt0_nb).
by  smt(size_addm size_neg gt0_mb gt0_nb size_dmatrix m_encode_rows m_encode_cols).

move => ? vL ?;split. 
+ apply duni_matrix_fu;1,2:smt(gt0_mb gt0_nb).
  rewrite size_addm.
  + by rewrite m_encode_rows m_encode_cols;smt(size_dmatrix gt0_mb gt0_nb).
  by smt(size_dmatrix gt0_mb gt0_nb).

move => ?;split.
+ rewrite -addmA addmN m_encode_rows m_encode_cols.
  by smt(lin_addm0 gt0_mb gt0_nb).
by smt().
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
by islossless; smt(duni_matrix_ll Chi_matrix_ll). 
qed.

lemma main_theorem &m :
  islossless A.guess => islossless A.choose =>
  `| Pr[CPA(LWE_PKE_HASH,A).main() @ &m : res] -  1%r / 2%r | <=
    `| Pr[LWE_H1(B1(A)).main(false) @ &m : res] -
       Pr[LWE_H1(B1(A)).main(true) @ &m : res] | + 
    `| Pr[LWE_H2(B2(A)).main(false) @ &m : res] -
       Pr[LWE_H2(B2(A)).main(true) @ &m : res] | +
    `| Pr [ PRG_KG.IND(PRG_KG.PRGr,D_KG(A)).main() @ &m : res ] -
        Pr [ PRG_KG.IND(PRG_KG.PRGi,D_KG(A)).main() @ &m : res ] | +
    `| Pr [ PRG_ENC.IND(PRG_ENC.PRGr,D_ENC(A)).main() @ &m : res ] -
        Pr [ PRG_ENC.IND(PRG_ENC.PRGi, D_ENC(A)).main() @ &m : res ] |.
proof.
move => A_guess_ll A_choose_ll.
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

lemma eq_tuple_imply_fst (x z: 'a) (y w: 'b): (x, y) = (z, w) => (x, y).`1 = (z, w).`1.
proof. done. qed.

lemma eq_tuple_imply_snd (x z: 'a) (y w: 'b): (x, y) = (z, w) => (x, y).`2 = (z, w).`2.
proof. done. qed.


lemma dmatrix_rows m d r c: 0 < r => 0 < c => m \in dmatrix d r c => rows m = r. 
proof.
    move => *.
    rewrite -(fst_pair (rows m) (cols m)) -(fst_pair r c).
    apply /eq_tuple_imply_fst/(size_dmatrix d r c) => //;
    by apply ltrW.
qed.

lemma dmatrix_cols m d r c: 0 < r => 0 < c => m \in dmatrix d r c => cols m = c. 
proof.
    move => *.
    rewrite -(snd_pair (rows m) (cols m)) -(snd_pair r c).
    apply /eq_tuple_imply_snd/(size_dmatrix d r c) => //;
    by apply ltrW.
qed.

lemma chi_matrix_rows m r c: 0 < r => 0 < c => m \in Chi_matrix r c => rows m = r.
proof.
    rewrite /Chi_matrix => *; by apply (dmatrix_rows m Chi r c).
qed.

lemma chi_matrix_cols m r c: 0 < r => 0 < c => m \in Chi_matrix r c => cols m = c.
proof.
    rewrite /Chi_matrix => *; by apply (dmatrix_cols m Chi r c).
qed.

lemma chi_matrix_mb_n_rows m: m \in Chi_matrix mb n => rows m = mb.
proof. by apply /chi_matrix_rows. qed. 

lemma chi_matrix_mb_nb_rows m: m \in Chi_matrix mb nb => rows m = mb.
proof. by apply /chi_matrix_rows. qed. 

lemma chi_matrix_mb_nb_cols m: m \in Chi_matrix mb nb => cols m = nb.
proof. by apply /chi_matrix_cols. qed. 

lemma chi_matrix_n_nb_cols m: m \in Chi_matrix n nb => cols m = nb.
proof. by apply /chi_matrix_cols. qed. 

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

axiom sk_decode_cols sk: cols (sk_decode sk) = nb.

hint simplify (sk_decode_cols, good_c_decode).

module CorrectnessAdvNoise(A : CORR_ADV) = {
  proc main() = {
    var sd,s,s',e, e', e'', t, _A, m, nu, pk, sk;
    sd <$ dseed;
    s  <$ Chi_matrix n nb;
    s'  <$ Chi_matrix mb n;
    e  <$ Chi_matrix n nb;
    e'  <$ Chi_matrix mb n;
    e''  <$ Chi_matrix mb nb;
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
    s  <$ Chi_matrix n nb;
    s'  <$ Chi_matrix mb n;
    e  <$ Chi_matrix n nb;
    e'  <$ Chi_matrix mb n;
    e''  <$ Chi_matrix mb nb;
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
  pk_decode pk{1} = (sd{1}, t{1}) /\
  sk_decode sk{1} = s{1} /\
  t{1} = H sd{1} n n * s{1} + e{1} /\
  _A{2} = H sd{2} n n /\
  s'{1} \in Chi_matrix mb n /\
  e'{1} \in Chi_matrix mb n /\
  e''{1} \in Chi_matrix mb nb /\
  e{1} \in Chi_matrix n nb
).
+ call (_:true); auto => />. move => * />; split;
  [by apply /pk_encodeK|by apply /sk_encodeK].

auto => />.
move => &1 &2 ->.
move => /chi_matrix_mb_n_rows hrs';
move => /chi_matrix_mb_n_rows hre';
move => ^ /chi_matrix_mb_nb_rows hre'' /chi_matrix_mb_nb_cols hce'';
move => /chi_matrix_n_nb_cols hce.
rewrite /noise_exp /= [_+m_encode _]addmC -addmA. (* NOTE: ! why so slow ? *)
pose x := _ * (H _ n n * sk_decode _ + _) + _ - _.

apply Logic.contra; 
rewrite [_+x-_]addmC addmA addNm m_encode_rows m_encode_cols.

have -> :zerom mb nb + x = x.
+ rewrite /x mulmxDr mulmxDl oppmD.
  apply lin_add0m;
  rewrite ?rows_addm ?rows_neg ?rows_mulmx ?cols_addm ?cols_neg ?cols_mulmx;
  rewrite /#.
by apply good_m_decode.
qed.

lemma matrix_cacnel (x y z: matrix): x = y => x + z = y + z.
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
move => sd ?;
move => s /chi_matrix_n_nb_cols hcs;
move => s' /chi_matrix_mb_n_rows hrs';
move => e /chi_matrix_n_nb_cols hce;
move => e' /chi_matrix_mb_n_rows hre';
move => e'' ^ /chi_matrix_mb_nb_rows hre'' /chi_matrix_mb_nb_cols hce'' m.
apply /congr1; congr.
rewrite /noise_exp/noise_exp_val //=.
rewrite -[(_ - _ - _)%Matrices]addmA -oppmD mulmxDl mulmxDr.
rewrite sub_eqm /= ?rows_addm ?rows_neg ?rows_mulmx ?cols_addm ?cols_neg ?cols_mulmx;
1..2: rewrite /#.

rewrite addmA.
apply matrix_cacnel.
rewrite mulmxA.
pose x := s' * _ * s. rewrite -[x + _ + _]addmA.
pose y := s' * e + e''.
pose z := e' * s.
rewrite [y-z+_]addmC.
rewrite [_+(y-z)]addmA.
rewrite -[x+z+y]addmA.
rewrite [z+y]addmC.
rewrite -addmA -addmA addmN.
rewrite [_+(y+_)]addmA eq_sym.
apply lin_addm0;
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
