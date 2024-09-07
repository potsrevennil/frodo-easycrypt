require import AllCore Distr List.
require (****) DynMatrix.
(*****) import DList.

clone import DynMatrix as Matrix.
export Matrix.

op "_.[_<-_]" (m: matrix) (ij: int*int) (v: R): matrix =
   offunm (fun i j => if (i,j) = ij then v else m.[ij],rows m, cols m).

lemma eq_tuple_imply_fst (x z: 'a) (y w: 'b): (x, y) = (z, w) => (x, y).`1 = (z, w).`1.
proof. done. qed.

lemma eq_tuple_imply_snd (x z: 'a) (y w: 'b): (x, y) = (z, w) => (x, y).`2 = (z, w).`2.
proof. done. qed.

lemma eq_tuple_swap (x z: 'a) (y w: 'b): (x, y) = (z, w) <=> (y, x) = (w, z).
proof. done. qed.

lemma dmatrix_rows m d r c: 0 <= r => 0 <= c => m \in dmatrix d r c => rows m = r.
proof.
    move => *.
    rewrite -(fst_pair (rows m) (cols m)) -(fst_pair r c).
    by apply /eq_tuple_imply_fst/(size_dmatrix d r c) => /#.
qed.

lemma dmatrix_cols m d r c: 0 <= r => 0 <= c => m \in dmatrix d r c => cols m = c.
proof.
    move => *.
    rewrite -(snd_pair (rows m) (cols m)) -(snd_pair r c).
    by apply /eq_tuple_imply_snd/(size_dmatrix d r c) => /#.
qed.

lemma dmatrix_rows_tr m d r c: 0 <= r => 0 <= c => m \in dmatrix d r c => rows (trmx m) = c.
proof.
    move => *.
    rewrite rows_tr. by apply (dmatrix_cols m d r).
qed.

lemma dmatrix_cols_tr m d r c: 0 <= r => 0 <= c => m \in dmatrix d r c => cols (trmx m) = r.
proof.
    move => *.
    rewrite cols_tr. by apply (dmatrix_rows m d r c).
qed.

lemma cancel_addm0 m d r c: 0 <= r => 0 <= c => m \in dmatrix d r c => m = m + zerom r c.
proof.
    move => *.
    rewrite lin_addm0 => //; rewrite eq_sym.
    + by apply (dmatrix_rows m d r c).
    + by apply (dmatrix_cols m d r c).
qed.

lemma cancel_add0m m d r c: 0 <= r => 0 <= c => m \in dmatrix d r c => m = zerom r c + m.
proof.
   move => *.
   rewrite addmC.
   by apply (cancel_addm0 m d r c).
qed.

lemma supp_dmatrix_tr m d r c: 0 <= r => 0 <= c =>
    m \in dmatrix d r c =>
    trmx m \in dmatrix d c r.
proof.
move => ? ? ^ ?.
rewrite !supp_dmatrix 1..4:/#.
move => [#] ? ? h.
rewrite size_tr.
split.
+ rewrite eq_tuple_swap (size_dmatrix d r c) => /#.
+ move => i j [#]. rewrite rows_tr cols_tr trmxE => *.
  apply (h j i) => /#.
qed.

hint exact: supp_dmatrix_tr.
hint simplify supp_dmatrix_tr.

lemma dmatrix_tr1E (m: matrix) d r c: 0 <= r => 0 <= c =>
    size m = (r, c) =>
    mu1 (dmatrix d r c) m = mu1 (dmatrix d c r) (trmx m).
proof.
move => ? ? [#] hr hc *.
have hrt: rows (trmx m) = c; 1: by rewrite rows_tr .
have hct: cols (trmx m) = r; 1: by rewrite cols_tr.
rewrite -{1}hr -{1}hc -hrt -hct.
rewrite !dmatrix1E hr hc hrt hct.
rewrite /big !filter_predT.
pose r' := range 0 r.
pose c' := range 0 c.
rewrite -!foldr_comp //=.
have ->: (fun (i : int) => foldr Real.( * ) 1%r (map (fun (j : int) => mu1 d m.[i, j]) c'))
       = (fun (i : int) => foldr (Real.( * ) \o fun (j : int) => mu1 d m.[i, j]) 1%r c').
+ by rewrite fun_ext => *; rewrite foldr_comp.
have ->: (fun (i : int) => foldr Real.( * ) 1%r (map (fun (j : int) => mu1 d m.[j, i]) r'))
       = (fun (i : int) => foldr (Real.( * ) \o fun (j : int) => mu1 d m.[j, i]) 1%r r').
+ by rewrite fun_ext => *; rewrite foldr_comp.

elim r' => //=.
+ rewrite /(\o).
  by elim c'.
+ move => x xs h.
  rewrite {1}/(\o) h.
  rewrite /(\o).
  pose f x0 := foldr (fun (x1 : int) => ( * ) (mu1 d m.[x1, x0])) 1%r xs.
  have -> : (fun x0 => Real.( * ) (foldr (fun (x1 : int) => Real.( * ) (mu1 d m.[x1, x0])) 1%r xs))
       = (fun x0 => Real.( * ) (f x0)); 1: by trivial.
  have -> : (fun x0 => Real.( * ) (mu1 d m.[x, x0] * foldr (fun x1 => Real.( * ) (mu1 d m.[x1, x0])) 1%r xs))
       = (fun x0 => Real.( * ) (mu1 d m.[x, x0] * f x0)); 1: by trivial.
  clear h; elim c' => //.
  move => y ys //=.
  pose t0 := foldr (fun (x0 : int) => ( * ) (mu1 d m.[x, x0])) 1%r ys.
  pose t1 := foldr (fun (x0 : int) => ( * ) (f x0)) 1%r ys.
  pose t2 := foldr (fun (x0 : int) => ( * ) (mu1 d m.[x, x0] * f x0)) 1%r ys.

  by rewrite RField.mulrA -[_*t0*_]RField.mulrA [t0*f y]RField.mulrC RField.mulrA -[_ * t0 * t1]RField.mulrA /#.
qed.

lemma trmx_cancel m : trmx (trmx m) = m.
proof. by rewrite trmxK. qed.

hint exact: trmx_cancel.
hint simplify trmx_cancel.

lemma catmr_empty a b m n d: 0 <= m => 0 <= n => a \in dmatrix d m n => b \in dmatrix d m 0 => (a || b) = a.
proof.
move => *.
rewrite /catmr.
have h0 := dmatrix_rows a d m n _ _ _; 1..3: by trivial.
have h1 := dmatrix_cols a d m n _ _ _; 1..3: by trivial.
rewrite h0 h1.
rewrite (dmatrix_rows b d m 0) //.
rewrite (dmatrix_cols b d m 0) //.
rewrite eq_sym eq_matrixP.
split.
+ rewrite //= h0 h1 => /#.
+ move => i j h.
  rewrite get_offunm => //=.
  + rewrite /#.
  + have -> : b.[i, j - n] = ZR.zeror.
    + by apply getm0E => /#.
  by rewrite ZR.addr0.
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
