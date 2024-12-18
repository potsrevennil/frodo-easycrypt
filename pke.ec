require import AllCore Int Real List IntDiv.
require import ZModP.
require BitWord.
require import Array.
require import Keccak1600_Spec.
require import BitEncoding.
(*---*) import BS2Int.
(*---*) import BitChunking.
require (*--*) FrodoPKE_correctness.
require (*--*) Distrmatrix.

clone import FrodoPKE_correctness as FrodoPKE_correctness_ with
    op N: int = 640,
    op Nb: int = 8,
    op Mb: int = 8,
    op D: int = 15,
    op q: int = 32768,
    op B: int = 2,
    op lenSE: int = 128
    proof gt0_N by trivial
    proof gt0_Nb by trivial
    proof gt0_Mb by trivial
    proof D_bound by trivial
    proof B_bound by trivial
    proof ge0_lenSE by trivial.

import FrodoPKE_correctness_.FrodoPKE_.
import DM.
import Dmatrix_.
import Distrmatrix_.
import Zq.

op "_.[_<-_]" (m: matrix) (ij: int*int) (v: Zq): matrix.

from Jasmin require import JWord.
from Jasmin require import JArray.

op toW8 (w: FrodoPKE_correctness_.W8.sT): JWord.W8.t = JWord.W8.bits2w (FrodoPKE_correctness_.W8.val w).

(*
op tolist (m: t): R list =
  let ys = range 0 (cols m) in
  let xs = range 0 (rows m) in
  let ms = flatten (map (fun x => map (fun y => (x, y)) ys) xs) in
  map (fun i => m.[i] ) ms.
  *)

op CDF_table: int array = mkarray [
   4643; 13363; 20579; 25843;
   29227; 31145; 32103; 32525;
   32689; 32745; 32762; 32766;
   32767
].

module Sample = {
  proc sample(r: bool list): Zq = {
    var i, e, t;
    e <- 0;
    i <- 0;
    t <- bs2int (behead r);

    while (i < size CDF_table) {
      if (CDF_table.[i] < t) {
        e <- e + 1;
      }
      i <- i + 1;
    }

    e <- (-1)^(b2i (head false r)) * e;
    return inZq e;
  }

  proc matrix(r: W16.t list, n1: int, n2: int): matrix = {
      var i, j, x;
      var m: matrix;
      i <- 0;
      j <- 0;
      while (i < n1) {
        while (j < n2) {
          x <@ sample(W16.w2bits (r.[i * n2 + j]));
          m.[(i,j)] <- x;
          n2 <- n2 + 1;
        }
        n1 <- n1 + 1;
      }

      return m;
  }
}.

module Encoding = {
(*
  proc pack(c: matrix, n1: int, n2: int): bool list = {
    var i, j, l, cd;
    var b: bool array;
    i <- 0;

    while (i < n1) {
      j <- 0;

      while (j < n2) {
        cd <- mkarray (take D (int2bs 16 (asint c.[(i,j)])));

        l <- 0;
        while (l < D) {
          b.[(i*n2+j)*D+l] <- cd.[D-1-l];

          l <- l + 1;
        }

        j <- j + 1;
      }
      i <- i + 1;
    }

    return ofarray b;
  }

  proc unpack(bs: bool list, n1: int, n2: int):  M.t = {
    var i, j, l, ac;
    var arrb: bool array;
    var c: M.t;

    arrb <- mkarray bs;

    i <- 0;
    while (i < n1) {
      j <- 0;

      while (j < n2) {
        l <- 0;
        ac <- 0;

        while (l < D) {
          ac <- ac + (b2i arrb.[(i*n2+j)*D+l]) * 2^(D-1-l);
          l <- l + 1;
        }
        c.[(i, j)] <- inZq ac;

        j <- j + 1;
      }
      i <- i + 1;
    }

    return c;
  }
  *)

  proc encode(bk: bool array): matrix = {
    var i, j, l;
    var k;
    var mk: matrix;

    i <- 0;
    while (i < Nb) {
      j <- 0;
      while (j < Nb) {
        l <- 0;
        while (l < B) {
          k <- k + (b2i bk.[(i*Nb+j)*B + l]) * 2^l;
          l <- l + 1;
        }

        mk.[(i, j)] <- inZq (k * q %/ (2^B));

        j <- j + 1;
      }
      i <- i + 1;
    }

    return mk;
  }

  proc decode(mk: matrix): bool array = {
    var i, j, l;
    var k;
    var bk: bool array;

    i <- 0;
    while (i < Nb) {
      j <- 0;

      while (j < Nb) {
        k <- mkarray (int2bs B (floor ((asint mk.[(i,j)] * 2^B)%r / q%r + 1%r/2%r) %% 2^B));

        l <- 0;
        while (l < B) {
          bk.[(i * Nb + j)*B + l] <- k.[l];
          l <- l + 1;
        }

        j <- j + 1;
      }
      i <- i + 1;
    }

    return bk;
  }
}.


op w128toW8l bs = map W8.bits2w (chunk W8.size (W128.w2bits bs)).
op w8ltoW16l (bs: W8.t list) = map W16.bits2w (chunk W16.size (flatten (map W8.w2bits bs))).
op tobytes bs = map W8.bits2w (chunk W8.size bs).

op N: int = FrodoPKE_correctness_.N.

module GenA = {
  proc init(seedA: bool list): matrix = {
    var i, j;
    var seed: W8.t list;
    var c: W16.t list;
    var a: matrix;

    i <- 0;
    while (i < N) {
      seed <- tobytes (int2bs 16 i ++ seedA);
      c <- w8ltoW16l (SHAKE128 seed (2*N));

      j <- 0;
      while (j < N) {
        a.[(i,j)] <- inZq (W16.to_uint (nth witness c j));
        j <- j+1;
      }

      i <- i+1;
    }

    return a;
  }
}.

type pkey = matrix * matrix. 
type skey = matrix.

type ciphertext = matrix * matrix. 
type plaintext = bool list.

(* A prf-based concrete frodo pke spec: replace the input seedA by matrix A, output of GenA(seedA) *)
module PKE = {
  proc kg_derand(coins: matrix * bool list) : pkey * skey = {
    var ma, mb, me, mst: matrix; (* a: (n, n), b, e: (n, nb), st: (nb, n) *)
    var seedSE: bool list;
    var r: W16.t list;
    var b: bool list;

    ma <- coins.`1;
    seedSE <- coins.`2;

    r <- w8ltoW16l (SHAKE128 ((toW8 mask5f) :: tobytes seedSE) (4*N*Nb));
    mst <@ Sample.matrix(take (N*Nb) r, Nb, N);
    me <@ Sample.matrix(drop (N*Nb) r, N, Nb);

    mb <- ma * (trmx mst) + me;

    return ((ma, mb), mst);
  }

  proc enc_derand(pt: plaintext, pk: pkey, coins: bool list): ciphertext = {
    var ma, mb, ms', me', me'', mb', mu, mv, mc: matrix;
    var r: W16.t list;

    (ma, mb) <- pk;

    r <- w8ltoW16l (SHAKE128 (toW8 mask96 :: tobytes coins) (4*N*Nb + 2*Nb*Nb));
    ms' <@ Sample.matrix(take (N*Nb) r, Nb, N);
    me' <@ Sample.matrix(take (N*Nb) (drop (N*Nb) r), Nb, N);
    me'' <@ Sample.matrix(drop (2*N*Nb) r, Nb, Nb);

    mb' <- ms' * ma + me';

    mu <@ Encoding.encode(mkarray pt);
    mv <- ms' * mb + me'';
    mc <- mv + mu;

    return (mb', mc);
  }

  proc dec(ct: ciphertext, sk: skey): plaintext = {
    var c1, c2;
    var mb', mc, m: matrix; (* c1: (nb, n), c2: (nb, nb) *)
    var u;

    (c1, c2) <- ct;
    m <- c2 - c1 * (trmx sk);

    u <@ Encoding.decode(m);

    return ofarray u;
  }
}.
end PKE.

