(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Import Refl.
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

  Variable negate : Term -> list Term'.

  Hypothesis no_middle_eval' : forall env d, (eval' env d) \/ ~ (eval' env d).

  Hypothesis normalise_sound : forall env t, eval env t -> make_conj Term' (eval' env) (normalise t).
  Hypothesis normalise_complete : forall env t, make_conj Term' (eval' env) (normalise t) -> eval env t.

  Hypothesis negate_sound : forall env t, eval env t -> make_conj Term' (fun x => ~ (eval' env x)) (negate t).
  Hypothesis negate_complete : forall env t, make_conj Term' (fun x => ~ (eval' env x)) (negate t) -> eval env t.


  Variable Witness : Set.
  Variable checker : Witness -> list Term' -> bool.
  
  Hypothesis checker_sound : forall t, (exists w, checker w t = true) -> forall env, make_impl _ (eval' env)  t False.

End S.





Module Make (S:S).
  Import S.

  (* On normalising a list... *)

  Definition normalise_list (l:list Term) : list Term' :=
    ListS.concatMap _ _ (normalise) l.
  
  Lemma normalise_list_cons : forall e l, normalise_list (e::l) = (normalise_list l)++(normalise e).
  Proof.
    unfold normalise_list.
    intros.
    rewrite ListS.concatMap_cons.
    reflexivity.
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
    apply normalise_sound;auto.
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
    apply normalise_complete;auto.
    destruct d ; auto.
  Qed.

  (* On the negation of a list... *)

  Definition negate_list (l:list Term) : list Term' :=
    ListS.concatMap _ _ (negate) l.
  
  Lemma negate_list_cons : forall e l, negate_list (e::l) = (negate_list l)++(negate e).
  Proof.
    unfold negate_list.
    intros.
    rewrite ListS.concatMap_cons.
    reflexivity.
  Qed.
  Require Import tacticsPerso.


  Lemma make_dis_negate_list : forall env t2, ~ make_dis Term' (eval' env) (negate_list t2) -> 
    make_conj Term  (eval env)  t2.
  Proof.
    induction t2.
    simpl.
    tauto.
    simpl.
    destruct t2.
    rewrite negate_list_cons.
    simpl.
    intros.
    generalize (demorgan_1 _ _ (no_middle_eval' env) _ H).
    intro.
    apply negate_complete;auto.
    intros.
    rewrite negate_list_cons in H.
    generalize (demorgan_1 _ _ (no_middle_eval' env) _ H).
    intro.
    clear H.
    destruct (make_conj_app' Term' _ _ _  H0).
    split ; auto.
    apply negate_complete;auto.
    apply IHt2.
    apply demorgan_2;auto.
  Qed.

    
    

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

  (* This is a fold2 - could be made tail-recursive
     t2 is already a negation of the original pb
     *)
  Fixpoint pre_order_checker  (t1 : list Term')  (wits:list Witness)  (t2 : list Term') {struct wits}: bool :=
    match t2 with
      | nil => true
      | t'::rt2 => 
	match wits with
	  | nil => false
	  | w::rwits => match checker w ( t'::t1) with
			  | true => pre_order_checker  t1 rwits rt2
			  | false => false
			end
	end
    end.

  Definition order_checkerT  (t1 : list Term)   (wits:list Witness)  (t2 : list Term) : bool :=
    pre_order_checker (normalise_list t1) wits (negate_list t2).


  Lemma order_checkerT_sound : forall t1 t2,
    (exists wits, order_checkerT  t1 wits  t2 = true) -> 
    forall env, make_impl _ (eval env) t1 (make_conj _ (eval env) t2).
  Proof.
    intros.
    apply make_conj_impl1.
    intro.
    destruct H as [wits  H].
    unfold order_checkerT in H.
    apply make_dis_negate_list.
    red ; intro.
    generalize (conj_normalise _ _ H0).
    intros.
    clear H0.
    revert H H1 H2.
    generalize (normalise_list t1).
    generalize (negate_list t2).
    (* Here we go *)
    induction wits.
    simpl.
    destruct l.
    simpl.
    auto.
    intros ; discriminate.
    (**)
    simpl.
    destruct l.
    simpl.
    auto.
    intro.
    case_eq (checker a (t::l0)).
    intros.
    generalize (checker_sound (t::l0) (ex_intro _ a H) env).
    intro.
    simpl in H1.
    destruct l.
    apply (make_conj_impl2  _ _ _ _ H3).
    simpl.
    destruct l0.
    auto.
    tauto.
    destruct H1.
    apply (make_conj_impl2  _ _ _ _ H3).
    simpl.
    destruct l0 ; tauto.
    apply (IHwits _ _ H0 H1);auto.
    intros ; discriminate.
  Qed.
    

End Make.