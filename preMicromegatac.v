(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Import ZArith.
Require Export Micromega.

(* Treatment of equality is missing... *)
Ltac psimpl_arith :=
  let __H := fresh in
    match goal with
      | |- ( ?X > ?Y)  \/ ?R  => destruct (Z_gt_le_dec X Y) as [__H | __H] ; [left ; exact __H | right]
      | |- ( ?X < ?Y)  \/ ?R  => destruct (Z_lt_le_dec X Y) as [__H | __H] ; [left ; exact __H | right]
      | |- ( ?X >= ?Y) \/ ?R  => destruct (Z_ge_lt_dec X Y) as [__H | __H] ; [left ; exact __H | right]
      | |- ( ?X <= ?Y) \/ ?R  => destruct (Z_lt_le_dec Y X) as [__H | __H] ; [right | left ; exact __H]
      | |- (@eq Z ?X ?Y) \/ ?R => destruct (Z_eq_dec X Y)  as [__H | __H] ; [left ; exact __H | right]
      | |- ~ (@eq Z ?X ?Y) \/ ?R => destruct (Z_eq_dec X Y)  as [__H | __H] ; [right | left ; exact __H]
      | H: ~ (?X > ?Y) |- _  => generalize  (Znot_gt_le X Y H) ; clear H ; intro H      
      | H: ~ (?X < ?Y) |- _  => generalize  (Znot_lt_ge X Y H) ; clear H ; intro H
      | H: ~ (?X <= ?Y) |- _ => generalize  (Znot_le_gt X Y H) ; clear H ; intro H
      | H: ~ (?X >= ?Y) |- _ => generalize  (Znot_ge_lt X Y H) ; clear H ; intro H
      | H: ?E -> False  |- _ => change  (~ E) in H
      | |- (@eq Z ?X ?Y)  => destruct (Z_eq_dec X Y)  as [__H | __H] ; [exact __H | apply False_ind]
      | |- ~ ?X => red ; intro
      | |- ( ?X > ?Y)  => destruct (Z_gt_le_dec X Y) as [__H | __H] ; [exact __H | apply False_ind]
      | |- ( ?X < ?Y)  => destruct (Z_lt_le_dec X Y) as [__H | __H] ; [exact __H | apply False_ind]
      | |- ( ?X >= ?Y) => destruct (Z_ge_lt_dec X Y) as [__H | __H] ; [exact __H | apply False_ind]
      | |- ( ?X <= ?Y) => destruct (Z_lt_le_dec Y X) as [__H | __H] ; [apply False_ind | exact __H]
(* also eliminate conjunctions... *)
    end.

Lemma relax_gt : forall x y, x > y -> x >= y + 1.
Proof.
  intros;omega.
Qed.

Lemma relax_lt : forall x y, x < y -> x + 1 <= y.
Proof.
  intros;omega.
Qed.

Lemma relax_neq : forall x y, ~ x = y -> x > y \/ x < y.
Proof.
  intros;omega.
Qed.


Ltac zrelax :=
  repeat psimpl_arith ;
  repeat
    (match goal with
       | H : (?X > ?Y) |- _ => generalize (relax_gt _ _ H); intro ; clear H
       | H : (?X < ?Y) |- _ => generalize (relax_lt _ _ H); intro ; clear H
       | H : ~ (@eq Z ?X ?Y) |- _ => destruct (relax_neq _ _ H); clear H 
     end).
(* I would not like to clear Hs*)


Tactic Notation "micromega"  := micromegaw -1 ; vm_compute ; reflexivity.
Tactic Notation "micromega" constr(d) := micromegad d; vm_compute ; reflexivity.

Ltac sos := sosw ; vm_compute ; reflexivity.

Ltac omicron :=  omicronw ; vm_compute ; reflexivity.

(* Intuition might undo simplifications *)

Tactic Notation "micmac" constr(d) := repeat psimpl_arith ; (intuition auto)  ; micromegad d; vm_compute ; reflexivity.

Tactic Notation "micmac" := repeat psimpl_arith ; (intuition auto) ; 
  let x := (constr : (Zneg xH)) in micromegad x  ; vm_compute ; reflexivity.


  









