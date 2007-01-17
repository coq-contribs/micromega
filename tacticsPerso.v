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

Ltac CaseEq a := generalize (refl_equal a); pattern a at -1 in |- *; case a.
Ltac gen_clear x := generalize x ; clear x.
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


