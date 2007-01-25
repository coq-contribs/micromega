(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Import ZArith.
Require Import Micromegatac.


Lemma minus_one_is_not_positive : -1 >= 0 -> False.
Proof.
  micromega.
Qed.

Lemma add_tauto : 0 >= 0 -> -1 >= 0 -> False.
Proof.
  micromega.
Qed.

Lemma add_tauto_change_order : -1 >= 0 -> 0 >= 0 -> False.
Proof.
  micromega.
Qed.

Lemma x_cannot_have_different_values : (forall x (P:Prop), x = 1 -> P-> x= 0 -> False).
  intros.
  micromega.
Qed.

Lemma x_plus_y_and_y_0_impl_x_pos : forall x y, x + y = 0 -> y = 0 -> x >= 0.
  intros.
  micromega.
Qed.

Lemma products_by_constants : (forall x y, 3 *x = 0 -> y= 5 -> 3 * x + y  >= 5 -  x * 3).
  intros x y.
  micromega.
Qed.


Lemma transitivity : forall k k',   0 < k' -> k' < k -> k' >= 0.
Proof.
  intros.
  micromega.
Qed.

Lemma assumption : (forall x:Z, (x*x)=0 -> x*x = 0).
Proof.
  intros;micromega.
Qed.


Lemma conjonction_in_goal :   ( forall x y, 0 <= x -> y <= 0 -> 0 <= x - 1 ->  0 <= x /\ x - 1 < x).
Proof.
  intros.
  micromega.
Qed.

Lemma unknown_operator :   ( forall x y, x / y = x / y).
Proof.
  intros.
  micromega.
Qed.

Lemma many_vars : forall a b c d e f, a + b + c + d + e + f > 0 -> a < 0 -> b < 0 -> c < 0 -> d < 0 -> e < 0 -> f < 0 -> False.
Proof.
  intros.
  micromega.
Qed.

Lemma power0 : forall x, x^0 = 1.
Proof.
  intros.
  micromega.
Qed.

Lemma power1 : forall x, x^1 = x.
Proof.
  intros.
  try omega.
  try ring.
  (* Yeap, I can do it! *)
  micromega.
Qed.

Lemma power2 : forall x, x^2 = x*x.
Proof.
  intros.
  micromega.
Qed.

Lemma plus_minus : forall x y, x + y = 0 -> x -y = 0 -> x = 0 /\ y = 0.
Proof.
  intros ; micromega.
Qed.

Lemma binomial : forall x y, (x+y)^2 = x^2 + 2*x*y + y^2.
Proof.
  intros.
  micromega.
Qed.

Lemma prod_pos_pos : forall x y, x >=0 -> y >= 0 -> x * y >= 0.
Proof.
  intros.
  micromega.
Qed.

Lemma one_one_prod_one : forall x y, 1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
  intros ; micromega.
Qed.

Lemma square_pos : forall x, x^2 >= 0.
Proof.
  intros.
  micromegah x.
Qed.

Lemma triang_ineq : forall x y, x >= 0 -> y >= 0 -> (x+y)^2 >= x^2 + y^2.
Proof.
  intros.
  micromega.
Qed.


(* I can't solve these goals -- yet *)

Lemma there_is_a_rational_solution : (forall x , 2*x = 1  -> False).
  intro.
  try micromega.
  intros;omega.
Qed.


