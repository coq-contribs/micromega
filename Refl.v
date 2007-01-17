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

Module Type S.

  (* 'Term' is a syntactic representation of a certain kind of propositions. *)
  Variable Term : Set.

  Variable Env : Type.

  Variable eval : Env -> Term -> Prop.

  Variable Term' : Set.

  Variable eval' : Env -> Term' -> Prop.

  Variable normalise : Term -> list Term'.

  Variable negate : Term' -> Term'.

  Hypothesis normalise_sound : forall env t t', In t' (normalise t) -> eval env t ->  eval' env t'.
  Hypothesis normalise_complete : forall env t, (forall t', In t' (normalise t) -> eval' env t')  ->  eval env t.

  Hypothesis no_middle : forall env d, (eval' env d) \/ ~ (eval' env d).
  Hypothesis negate_sound : forall d env, ~ (eval' env d) -> eval' env (negate d).
  Hypothesis negate_complete : forall d env, eval' env (negate d) -> ~ eval' env d.

End S.


Module R.

  Fixpoint make_impl (A:Set) (eval : A -> Prop) (l : list A) (goal : Prop) {struct l} : Prop :=
    match l with
      | nil => goal
      | cons e l => (eval e) -> (make_impl A eval l goal)
    end.


  (* Tail recursive...*)
  Fixpoint make_impl'(A:Set) (eval : A -> Prop) (l : list A) (g:Prop) {struct l} : Prop :=
    match l with
      | nil => g
      | cons e l => make_impl' A eval l (eval e -> g)
    end.

  Fixpoint make_conj (A:Set) (eval : A -> Prop) (l : list A) {struct l} : Prop :=
    match l with
      | nil => True
      | cons e nil => (eval e)
      | cons e l2 => ((eval e) /\ (make_conj A eval l2))
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

  Lemma make_conj_in' : forall  (A:Set) (eval:A->Prop) l, (forall p, In p l -> eval p) -> make_conj  A eval l.
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
    CaseEq ((a0::l1)++ l2).
    intros ; discriminate.
    intros.
    inversion H;subst.
    split;try tauto.
    change (a1::(l1++l2)) with ((a1:: l1)++ l2).
    apply IHl1.
    tauto.
    auto.
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
    CaseEq ((a0::l1)++l2).
    intros ; discriminate.
    intros.
    inversion H;subst.
    change ((a1:: l1)++l2) with ((a1:: l1)++ l2) in H0.
    destruct H0.
    generalize (IHl1 _ H1).
    tauto.
  Qed.

End R.



Module ReflD (S:S).
  Import S.
  Import R.

  Lemma lift_negate : forall env d l, 
    make_impl Term' (eval' env) ((negate d)::l) False ->  
    make_impl Term' (eval' env) l (eval' env d).
  Proof.
    intros.
    apply make_conj_impl1.
    intros.
    generalize (make_conj_impl2 _ _ _ _  H).
    clear H.
    intros.
    simpl in H.
    destruct  (no_middle env d).
    auto.
    generalize (negate_sound d env H1).
    intros.
    destruct l.
    tauto.
    tauto.
  Qed.

  Definition normalise_list (l:list Term) : list Term' :=
    ListS.concatMap _ _ (normalise) l.

  
  Lemma normalise_list_cons : forall e l, normalise_list (e::l) = (normalise_list l)++(normalise e).
  Proof.
    unfold normalise_list.
    intros.
    rewrite ListS.concatMap_cons.
    reflexivity.
  Qed.

  Lemma eval_make_conj : forall env a, eval env a -> make_conj Term' (eval' env) (normalise a).
  Proof.
    intros.
    apply make_conj_in'.
    intros.
    eapply normalise_sound;eauto.
  Qed.


  Lemma make_conj_eval : forall env a, make_conj Term' (eval' env) (normalise a) ->  eval env a.
  Proof.
    intros.
    apply normalise_complete.
    intros.
    eapply make_conj_in;eauto.
  Qed.

  Lemma conj_normalise : forall env d, make_conj Term (eval env) d -> make_conj Term' (eval' env) (normalise_list d).
  Proof.
    induction d.
    simpl.
    auto.
    rewrite normalise_list_cons.
    intros.
    apply make_conj_app.
    simpl in H.
    destruct d.
    simpl.
    auto.
    destruct H.
    tauto.
    simpl in H.
    assert (eval env a).
    destruct d ; tauto.
    apply eval_make_conj;auto.
  Qed.    

  Lemma conj_normalise' : forall env d, make_conj Term' (eval' env) (normalise_list d) -> make_conj Term (eval env) d.
  Proof.
    induction d.
    auto.
    rewrite normalise_list_cons.
    simpl.
    intros.
    destruct (make_conj_app' _ _ _ _ H).
    clear H.
    assert (eval env a).
    apply make_conj_eval;auto.
    destruct d ; auto.
  Qed.

  Module Type CheckerS.

    Variable Witness : Set.
    Variable checker : Witness -> list Term' -> bool.
    
    Hypothesis checker_sound : forall t, (exists w, checker w t = true) -> forall env, make_impl _ (eval' env)  t False.
  End CheckerS.

  Module CheckerMaker(C : CheckerS).
    Module Checker := C.
    Import Checker.
    
    Definition checkerT (w : Witness) (l:list Term) : bool :=
      checker w (normalise_list l).

    Lemma checkerT_sound : forall t, (exists w, checkerT w t = true) -> forall env, make_impl _ (eval env)  t False.
    Proof.
      intros.
      apply make_conj_impl1.
      intro.
      generalize (conj_normalise _ _ H0).
      apply make_conj_impl2.
      destruct H  as [w H].
      unfold checkerT in H.
      apply checker_sound.
      exists w ; auto.
    Qed.

  (* This is a fold2 - could be made tail-recursive*)
  Fixpoint order_checker  (t1 : list Term')  (wits:list Witness)  (t2 : list Term') {struct wits}: bool :=
    match t2 with
      | nil => true
      | t'::rt2 => 
	match wits with
	  | nil => false
	  | w::rwits => match checker w ((negate t')::t1) with
			  | true => order_checker  t1 rwits rt2
			  | false => false
			end
	end
    end.


  Lemma order_checker_sound : forall t1 t2,
    (exists wits,order_checker  t1 wits  t2 = true) -> 
    forall env, make_impl _ (eval' env) t1 (make_conj _ (eval' env) t2).
  Proof.
    intros t1 t2 H.
    destruct H as [wits H].
    gen_clear H.
    gen_clear t2.
    induction wits.
    (* BC *)
    simpl.
    destruct t2.
    simpl.
    intros.
    apply make_conj_impl1.
    auto.
    congruence.
    (* IC *)
    simpl.
    destruct t2.
    (* t2 = nil *)
    intros.
    simpl.
    apply make_conj_impl1;auto.
    (* t2 <> nil *)
    CaseEq (checker  a (negate t :: t1)); try (intros;discriminate).
    intros.
    assert (make_impl Term' (eval' env) t1 (eval' env t)).
    apply lift_negate.
    apply checker_sound.
    exists a ; auto.
    simpl.
    destruct t2.
    auto.
    (**)
    apply make_conj_impl1.
    intro.
    split.
    gen_clear H2.
    apply make_conj_impl2.
    auto.
    gen_clear H2.
    apply make_conj_impl2.
    apply IHwits.
    auto.
  Qed.

  Definition order_checkerT  (t1 : list Term)   (wits:list Witness)  (t2 : list Term) : bool :=
    order_checker (normalise_list t1) wits (normalise_list t2).


  Lemma order_checkerT_sound : forall t1 t2,
    (exists wits, order_checkerT  t1 wits  t2 = true) -> 
    forall env, make_impl _ (eval env) t1 (make_conj _ (eval env) t2).
  Proof.
    intros.
    apply make_conj_impl1.
    intro.
    apply conj_normalise'.
    generalize (conj_normalise _ _ H0).
    apply make_conj_impl2.
    unfold order_checkerT in H.
    eapply order_checker_sound;eauto.
  Qed.
End CheckerMaker.

End ReflD.

