(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Import ZArith.
Require Import List.
Require Import tacticsPerso.
Require Import Bool.

(* Basic arithmetics results *)

Module ZArithE.
  Open Scope Z_scope.
  Lemma pos_times_pos_is_pos : forall x y, x >= 0 -> y >= 0 -> x * y >= 0.
  Proof.
    intros.
    assert (0 <= x * y).
    apply Zmult_le_0_compat;omega.
    omega.
  Qed.
  
  Lemma neq_or : forall x y, x <> y -> x > y \/ y > x.
  Proof.
    intros ; omega.
  Qed.

End ZArithE.

  
Module ListS.

  Fixpoint fold_left (A B:Type) (f:B -> A -> B)  (acc:B) (l:list A) {struct l}: B := 
    match l with 
      | nil => acc
      | e::l => fold_left _ _ f (f acc e) l
    end.
  
  Fixpoint fold_right (A B:Type) (f:A->B->B) (l:list A) (acc:B) {struct l} :B :=
    match l with 
      | nil => acc
      | e::l => f e (fold_right _ _ f l acc )
    end.


  Definition forallb (A:Type) (f:A -> bool) (l:list A)  : bool :=
    fold_left _ _ (fun acc  e => andb acc (f e) ) true l.

  Lemma forallb_spec : forall (A:Type) (l:list A) (pred: A -> bool), ListS.forallb A pred l = true -> forall x, In x l -> pred x = true.
  Proof.
    unfold forallb.
    intros  A l.
    pattern true at 1.
    gen_abs b.
    induction l.
    simpl.
    tauto.
    intros.
    simpl in H.
    simpl in H0.
    destruct H0.
    subst.
    destruct (pred x).
    reflexivity.
    replace (b&& false) with false in H.
    assert (fold_left A bool (fun (acc : bool) (e : A) => acc && pred e) false l = false).
    clear H IHl.
    induction l.
    reflexivity.
    simpl.
    auto.
    congruence.
    destruct b ; reflexivity.
    eapply IHl ; eauto.
  Qed.

  (*Fixpoint fold_left2 (A B Acc:Set) (f: Acc -> A -> B -> Acc) (acc:Acc) (l1:list A) (l2:list B) {struct l1} :Acc*)


  Fixpoint find (A:Set) (select: A -> bool) (l: list A) {struct l}: option A :=
    match l with
      | nil => None
      | cons e l => if select e then Some e else find  _ select l
  end.

  Definition mem (A:Set) (eq: A -> A -> bool) (x:A) (l : list A) : bool :=
    match find A (fun e => eq e x) l with
      | None => false
      | Some _ => true
    end.


  Definition concatMap (A B :Set) (f: A -> list B) (l :list A) : list B :=
      ListS.fold_left _ _ (fun acc e => f e ++ acc) nil l.

  Lemma concatMap_cons : forall A B f e l, concatMap A B f (e::l) = (concatMap A B f l) ++ (f e).
  Proof.
    unfold concatMap.
    simpl.
    intros.
    rewrite <- app_nil_end.
    pattern (f e) at 1.
    local_change (nil++(f e)).
    generalize (@nil B).
    induction l.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite <- IHl.
    rewrite app_ass.
    reflexivity.
  Qed.

  Lemma concatMapIn : forall A B f l , forall c, In c l -> forall e, In e (f c) -> In e (concatMap A B f l). 
  Proof.
    induction l.
    simpl.
    tauto.
    rewrite concatMap_cons.
    intros.
    simpl in H.
    destruct H.
    subst.
    apply in_or_app.
    tauto.
    apply in_or_app.
    left ; eapply IHl; eauto.
  Qed.
    


  Lemma concatMapIn' : forall A B f l , forall e, In e (concatMap A B f l) -> exists c, In c l /\ In e (f c).
  Proof.
    induction l.
    simpl.
    tauto.
    intros.
    rewrite concatMap_cons in H.
    destruct (in_app_or _  _ _ H).      
    destruct (IHl _ H0).
    exists x.
    simpl.
    tauto.
    exists a.
    simpl ; tauto.
  Qed.


  Lemma map_app : forall (A B:Set) (f:A->B) l1 l2, map f (l1++l2) = (map f l1) ++ (map f l2).
  Proof.
    induction l1.
    reflexivity.
    simpl.
    intros.
    rewrite IHl1.
    reflexivity.
  Qed.

  Open Scope Z_scope.

  Fixpoint length_z (A:Set) (l:list A) {struct l} : Z :=
    match l with
      | nil => 0
      | e::l => 1+(length_z A l)
    end.

  (* Borrowed from 8.1beta *)

  Fixpoint skipn (A:Set) (n:nat)(l:list A) { struct n } : list A := 
    match n with 
      | O => l 
      | S n => match l with 
		 | nil => nil 
		 | a::l => skipn A n l
	       end
    end.

  Lemma skipn_simpl : forall A n l,
    skipn A n l  = 
    match n with
      | O => l 
      | S n => match l with 
		 | nil => nil 
		 | a::l => skipn A n l
	       end
    end.
  Proof.
    destruct n; reflexivity.
  Qed.
		     

  Lemma skipn_nil : forall A n, skipn A n nil = nil.
  Proof.
    destruct n; reflexivity.
  Qed.

  Lemma skipn_succ : forall A n l, skipn A n l = nil -> skipn A (S n) l = nil.
  Proof.
    induction n.
    intros.
    destruct l.
    reflexivity.
    simpl in H.
    discriminate.
    intros.
    destruct l.
    reflexivity.
    simpl in H.
    rewrite skipn_simpl.
    apply IHn.
    auto.
  Qed.


 Lemma skipn_add : forall A  n' n l, skipn A n (skipn A n' l) = skipn A (n+n') l.
 Proof.
   induction n'.
   simpl.
   intros.
   replace (n+0)%nat with n.
   reflexivity.
   omega.
   simpl.
   destruct l.
   rewrite skipn_nil.
   rewrite skipn_nil.
   reflexivity.
   rewrite IHn'.
   replace (n + S n')%nat with (S (n+n')).
   reflexivity.
   omega.
 Qed.

 Lemma skipn_cons : forall A n e e' l l', skipn A n (e::l) = e'::l' -> skipn A n l = l'.
 Proof.
   induction n.
   simpl.
   congruence.
   simpl.
   intros.
   destruct l.
   rewrite skipn_nil in H ; discriminate.
   eapply IHn;eauto.
 Qed.
   



 Lemma skipn_in : forall A n e l, In e (skipn A n l) -> In e l.
 Proof.
   induction n.
   tauto.
   simpl.
   destruct l.
   auto.
   intros.
   right.
   apply IHn;auto.
 Qed.

 Lemma In_map : forall A B (f:A->B) e l, In e (map f l) -> exists e', In e' l /\ e = f e'.
 Proof.
   induction l.
   exact (fun H => False_ind _ H).
   simpl.
   intro H ; destruct H.
   exists a ; split ; [left ; reflexivity | symmetry ;auto].
   destruct (IHl H) as [e' [H1 H2]].
   exists e'; split ; [right ; exact H1 |exact H2].
 Qed.
 

End ListS.