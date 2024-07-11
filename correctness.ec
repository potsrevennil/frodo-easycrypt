(* -------------------------------------------------------------------- *)
require import AllCore IntDiv Real StdOrder.
(*---*) import RField IntOrder RealOrder.

(* -------------------------------------------------------------------- *)
op round (x: real): int = floor (x + inv 2%r).

(* -------------------------------------------------------------------- *)
lemma floor_add_lt1 x y: 0%r <= y < 1%r => floor (x%r + y) = x.
proof. by move=> rg; rewrite floorP /#. qed.

lemma round_fromint x : round x%r = x.
proof. by rewrite /round floor_add_lt1 /#. qed.

lemma round_id k x : -1%r/2%r <= x < 1%r/2%r => round (k%r + x) = k.
proof. by move=> ? @/round; rewrite -addrA floor_add_lt1 //#. qed.

(* -------------------------------------------------------------------- *)
op D: {int | 0 <= D <= 16} as D_bound.
op B: {int | 0 <= B <= D} as B_bound.

(* -------------------------------------------------------------------- *)
hint exact : D_bound B_bound.

(* -------------------------------------------------------------------- *)
lemma ge0_B : 0 <= B.
proof. by case: B_bound. qed.

hint exact : ge0_B.

(* -------------------------------------------------------------------- *)
hint simplify eq_fromint, lt_fromint, le_fromint.

(* -------------------------------------------------------------------- *)
lemma gt0_exp2 n : 0 < 2^n.
proof. by rewrite expr_gt0. qed.

hint exact : gt0_exp2.

(* -------------------------------------------------------------------- *)
op q = 2^D.

lemma gt0_q : 0 < q.
proof. by solve. qed.

hint exact : gt0_q.

lemma nz_q : q <> 0.
proof. by rewrite expf_eq0. qed.

hint exact : nz_q.

(* -------------------------------------------------------------------- *)
(* 0 <= k < 2^B. *)
op ec (k : int) = k * q %/ 2^B. 
op dc (c : int) = round (c%r * (2^B)%r / q%r) %% 2^B.

lemma dvd_2XB_2XD : 2^B %| 2^D.
proof. by apply/dvdz_exp2l/B_bound. qed.

hint exact : dvd_2XB_2XD.

(* -------------------------------------------------------------------- *)
lemma decode_correctness k: 0 <= k < (2^B) => dc (ec k) = k.
proof.
move=> [# ge0_k ltk] @/dc @/ec @/q.
rewrite divMr // -fromintM -mulrA divzK // fromintM //.
rewrite mulrK; first by rewrite /= expf_eq0.
by rewrite round_fromint pmod_small.
qed.

(* -------------------------------------------------------------------- *)
lemma l2_18 k e:
     0 <= k < (2^B)
  => (-q%r/(2^(B+1))%r) <= e%r < q%r/(2^(B+1))%r
  => dc ((ec k) + e) = k.
proof.
case=> [ge0_k ltk] [hge glt] @/dc @/ec @/q.
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
