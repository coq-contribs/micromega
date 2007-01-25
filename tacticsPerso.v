(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Lemma  apply_fun : forall (A B:Type) (f: A -> B), forall x y, x = y -> f x = f y.
Proof.
  congruence.
Qed.

Ltac apply_fun f H H1:= generalize (apply_fun _ _ f _ _ H) ; intro H1.

Require Import List.

Ltac local_change x :=
  match goal with
    | |- ?F ?X => change (F x)
  end.

Ltac gen_abs x :=
  match goal with
    | |- ?F ?X => change (let x := X in F x) ; intro  x; generalize x;clear x
  end.


Ltac dup x := generalize x; intro.
Ltac add_eq expr val := set (temp := expr) ; generalize (refl_equal temp) ; unfold temp at 1 ; generalize temp ; intro val ; clear temp.

Require Import Bool.

 Ltac flatten_bool :=
     repeat match goal with
              [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
              |  [ id : _ || _ = true |- _ ] =>  destruct (orb_prop _ _ id); clear id
            end.



