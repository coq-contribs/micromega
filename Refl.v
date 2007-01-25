(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Import tacticsPerso.
Require Import List.
Require Import Util.

(* Refl of '->' '/\' : basic properties *)

Fixpoint make_impl (A:Type) (eval : A -> Prop) (l : list A) (goal : Prop) {struct l} : Prop :=
  match l with
    | nil => goal
    | cons e l => (eval e) -> (make_impl A eval l goal)
  end.

Fixpoint make_conj (A:Type) (eval : A -> Prop) (l : list A) {struct l} : Prop :=
  match l with
    | nil => True
    | cons e nil => (eval e)
    | cons e l2 => ((eval e) /\ (make_conj A eval l2))
  end.

Fixpoint make_dis (A:Type) (eval : A -> Prop) (l:list A) {struct l} : Prop :=
  match l with
    | nil => False
    | cons e nil => eval e
    | cons e l2  => (eval e) \/ (make_dis A eval l2)
  end.

Lemma make_conj_impl : forall  A eval l (g:Prop), (make_conj A eval l -> g) <-> make_impl A eval l g.
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct l.
  simpl.
  tauto.
  generalize  (IHl g).
  tauto.
Qed.

Lemma make_conj_impl1 : (forall  A eval l (g:Prop), (make_conj A eval l -> g) -> make_impl A eval l g). 
Proof.
  exact (fun A eval l g => let (x,y) := make_conj_impl A eval l g  in x).
Qed.

Lemma make_conj_impl2 : forall  A eval l (g:Prop), make_impl A eval l g -> (make_conj A eval l -> g).
Proof.
  exact (fun A eval l g => let (x,y) := make_conj_impl A eval l g  in y).
Qed.

Lemma make_conj_in : forall  A eval l, make_conj  A eval l ->  (forall p, In p l -> eval  p).
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct l.
  simpl in H0.
  destruct H0.
  subst ; auto.
  tauto.
  destruct H.
  destruct H0.
  subst;auto.
  apply IHl ; auto.
Qed.

Lemma make_conj_in' : forall  (A:Type) (eval:A->Prop) l, (forall p, In p l -> eval p) -> make_conj  A eval l.
Proof.
  induction l;simpl;intros.
  auto.
  generalize (H _ (or_introl _ (refl_equal a))).
  destruct l ; try tauto.
  intros ; split.
  auto.
  apply IHl.
  intros.
  apply H.
  right; auto.
Qed.


Lemma make_conj_app : forall  A eval  l1 l2, make_conj A eval l1 -> make_conj A eval l2 -> make_conj A eval (l1++ l2).
Proof.
  induction l1.
  simpl.
  auto.
  simpl.
  destruct l1.
  simpl.
  destruct l2.
  tauto.
  tauto.
  intro.
  case_eq ((a0::l1)++ l2).
  intros ; discriminate.
  intros.
  inversion H;subst.
  split;try tauto.
  change (a1::(l1++l2)) with ((a1:: l1)++ l2).
  apply IHl1.
  tauto.
  auto.
Qed.

Lemma make_dis_app : forall  A eval  l1 l2, make_dis A eval l1 \/ make_dis A eval l2 -> make_dis A eval (l1++ l2).
Proof.
  induction l1.
  simpl.
  tauto.
  intros.
  simpl.
  case_eq (l1++l2).
  simpl in H.
  intros.
  destruct l1.
  destruct H.
  auto.
  destruct l2.
  simpl in H;tauto.
  discriminate.
  discriminate.
  intros.
  assert (eval a \/ (make_dis A eval l1 \/ make_dis A eval l2)).
  destruct H ; auto.
  simpl in H.
  destruct l1 ; tauto.
  destruct H1.
  tauto.
  right.
  rewrite <- H0.
  apply IHl1 ; auto.
Qed.
  
  

Lemma make_conj_app' : forall  A eval l1 l2, make_conj A eval (l1 ++ l2) -> make_conj A eval l1 /\ make_conj A eval l2.
Proof.
  induction l1.
  simpl.
  tauto.
  simpl.
  destruct l1.
  simpl.
  destruct l2; simpl.
  tauto.
  destruct l2.
  tauto.
  tauto.
  intro.
  case_eq ((a0::l1)++l2).
  intros ; discriminate.
  intros.
  inversion H;subst.
  change ((a1:: l1)++l2) with ((a1:: l1)++ l2) in H0.
  destruct H0.
  generalize (IHl1 _ H1).
  tauto.
Qed.

Lemma make_dis_app' : forall  A eval l1 l2, make_dis A eval (l1 ++ l2) -> make_dis A eval l1 \/ make_dis A eval l2.
Proof.
  induction l1.
  simpl.
  tauto.
  intros.
  simpl in H.
  revert H.
  case_eq (l1 ++ l2).
  simpl.
  destruct l1.
  tauto.
  intros ; discriminate.
  intros.
  rewrite <- H in H0.
  destruct H0.
  simpl.
  destruct l1; tauto.
  generalize (IHl1 _ H0).
  simpl.
  destruct l1 ; tauto.
Qed.


  

Lemma demorgan_1 : forall A eval, (forall x, eval x \/ ~ eval x) -> forall l, ~ make_dis A eval l -> (make_conj A (fun x => ~ eval x) l).
Proof.
  induction l.
  simpl.
  auto.
  simpl.
  destruct l.
  destruct (H a);tauto.
  intros.
  assert (~ eval a /\ ~ make_dis A eval (a0 :: l)).
  destruct (H a) ; tauto.
  tauto.
Qed.

Lemma demorgan_2 : forall A eval, forall l,  (make_conj A (fun x => ~ eval x) l)  ->  ~ make_dis A eval l.
Proof.
  induction l.
  simpl.
  auto.
  simpl.
  destruct l.
  auto.
  intros.
  destruct H.
  tauto.
Qed.



