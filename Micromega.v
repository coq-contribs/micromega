(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
(* Prelude *)
Require Import ZArith.
Require Import List.
Require Import tacticsPerso.
Require Import Util.
Require Import Refl.
Open Scope Z_scope.
Require Export ROmega. 
Import ZArithE.

Definition is_strict_neg (z:Z) : bool :=
  match z with
    | Zneg n => true
    | _ => false
  end.

Lemma is_strict_neg_ok : forall z , is_strict_neg z = true -> z < 0.
Proof.
  destruct z ; simpl; compute;congruence.
Qed.

Definition is_neg (z:Z) : bool :=
  match z with
    | Zneg n => true
    | Z0     => true
    | _ => false
  end.

Lemma is_neg_ok : forall z , is_neg z = true -> z <= 0.
Proof.
  destruct z ; simpl; compute;congruence.
Qed.

Require Import LegacyRing.
Require Import Ring_theory.
Require Import Ring_normalize.
Require Import Quote.
(*
I could use the new ring implementation.
Is-it really faster ?
The variables are stored in a list, a binary tree (as used by LegacyRing) 
would be more efficient especially if there are a lot of variables.
Require Import Ring_polynom.
Print PExpr.
Print PEeval.
*)


Module Polynomial.

  Definition Var := index.
  Definition EEnv := varmap Z.
  Definition Expr := polynomial Z.
  
  Definition interp_p := @interp_p Z Zplus Zmult Z0 Zopp.
  
  Definition power_pos (e:Expr) (n:positive) : Expr :=
    iter_pos n Expr (fun x => Pmult e x) (Pconst 1).
  
  Definition power (e:Expr) (z:Z) : Expr :=
    match z with
      | Z0 => Pconst 1
      | Zpos p => power_pos e p
      | Zneg _ => Pconst 0
    end.
  
  Inductive Op : Set :=
  | OpNEq
  | OpEq
  | OpLe
  | OpGe
  | OpGt
  | OpLt.
  
  Definition eval_op (o:Op) : Z -> Z -> Prop :=
    match o with
      | OpNEq => fun x y => ~ @eq Z x y
      | OpEq => @eq Z
      | OpLe => Zle
      | OpGe => Zge
      | OpGt => Zgt
      | OpLt => Zlt
    end.
  
  
  Record Cstr : Set := {
    lhs : Expr;
    op : Op;
    rhs : Expr
  }.
  
  
  Definition Term := Cstr.
  
  Definition Env := EEnv.
  
  Definition eval (env:Env) (t:Term) : Prop :=
    let (lhs,op,rhs) := t in
      (eval_op op) (interp_p env lhs) (interp_p env rhs).
  
  Inductive redOp : Set :=
  | Equal (*=0*)
  | Strict (*>0*)
  | NonStrict (*>=0*).

  Definition Term' := (Expr * option redOp)%type.
  
  Definition eval_redop (o:redOp) : Z -> Z -> Prop :=
    match o with 
      | Equal     => @eq Z
      | Strict => Zgt
      | NonStrict => Zge
    end.
  
  Definition eval' (env:Env) (t:Term') : Prop :=
    let (e,op) := t in
      match op with 
        | None => interp_p env e <> 0
        | Some op => eval_redop op (interp_p env e) 0
      end.

  Definition Minus (e1 e2 : Expr) : Expr :=
    Pplus e1 (Popp e2).

(* These versions work for Z, Q, Z... *)
(*  Definition normalise (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
        | OpEq => (Minus lhs  rhs , Equal)::nil
	| OpLe => (Minus rhs lhs,NonStrict) :: nil
	| OpGe => (Minus lhs rhs,NonStrict) :: nil
	| OpGt => (Minus lhs rhs,Strict)::nil
	| OpLt => (Minus rhs lhs,Strict)::nil
      end.


  Definition negate (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
  (* e = e'  == (e >= e' /\ e' >= e) ==  ( ~ e < e' /\ ~ e' < e) *)
        | OpEq => (Minus rhs lhs , Strict)::(Minus lhs rhs, Strict)::nil
  (* e <= e' == ~ e > e' *)
	| OpLe => (Minus lhs rhs, Strict) :: nil
	| OpGe => (Minus rhs lhs, Strict) :: nil
	| OpGt => (Minus rhs lhs, NonStrict)::nil
	| OpLt => (Minus lhs rhs, NonStrict)::nil
      end.
*)
(* For Z, it might be better to relax... *)
(*  Definition normalise (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
        | OpEq => (Minus lhs  rhs , Equal)::nil
	| OpLe => (Minus rhs lhs,NonStrict) :: nil
	| OpGe => (Minus lhs rhs,NonStrict) :: nil
	| OpGt => (Minus lhs (Pplus rhs (Pconst 1)),NonStrict)::nil
	| OpLt => (Minus rhs (Pplus lhs (Pconst 1)),NonStrict)::nil
      end.

  Definition negate (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
  (* e = e'  == (e >= e' /\ e' >= e) ==  ( ~ e < e' /\ ~ e' < e) *)
        | OpEq => (Minus rhs (Pplus lhs (Pconst 1)), NonStrict)::(Minus lhs (Pplus rhs (Pconst 1)), NonStrict)::nil
  (* e <= e' == ~ e > e' *)
	| OpLe => (Minus lhs (Pplus rhs (Pconst 1)), NonStrict) :: nil
	| OpGe => (Minus rhs (Pplus lhs (Pconst 1)), NonStrict) :: nil
	| OpGt => (Minus rhs lhs, NonStrict)::nil
	| OpLt => (Minus lhs rhs, NonStrict)::nil
      end.
*)

(** Third option : join of previous  **)
(*  Definition normalise (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
        | OpEq => (Minus lhs  rhs , Equal)::nil
	| OpLe => (Minus rhs lhs,NonStrict) :: nil
	| OpGe => (Minus lhs rhs,NonStrict) :: nil
	| OpGt => (Minus lhs (Pplus rhs (Pconst 1)),NonStrict)::(Minus lhs rhs, Strict) ::nil
	| OpLt => (Minus rhs (Pplus lhs (Pconst 1)),NonStrict)::(Minus rhs lhs, Strict) ::nil
      end.

  Definition negate (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
  (* e = e'  == (e >= e' /\ e' >= e) ==  ( ~ e < e' /\ ~ e' < e) *)
        | OpEq => (Minus rhs (Pplus lhs (Pconst 1)), NonStrict)::(Minus lhs (Pplus rhs (Pconst 1)), NonStrict)::nil
  (* e <= e' == ~ e > e' *)
	| OpLe => (Minus lhs (Pplus rhs (Pconst 1)), NonStrict) :: nil
	| OpGe => (Minus rhs (Pplus lhs (Pconst 1)), NonStrict) :: nil
	| OpGt => (Minus rhs lhs, NonStrict)::nil
	| OpLt => (Minus lhs rhs, NonStrict)::nil
      end.
*)

  Definition normalise (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
        | OpEq => (Minus lhs  rhs , Some Equal)::nil
        | OpNEq => (Minus lhs  rhs , None)::nil
	| OpLe => (Minus rhs lhs,Some NonStrict) :: nil
	| OpGe => (Minus lhs rhs,Some NonStrict) :: nil
	| OpGt => (Minus lhs rhs, Some Strict) ::nil
	| OpLt => (Minus rhs lhs, Some Strict) ::nil
      end.

  Definition negate (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
        | OpNEq => (Minus rhs  lhs, Some Equal)::nil
        | OpEq => (Minus rhs  lhs, None)::nil
  (* e <= e' == ~ e > e' *)
	| OpLe => (Minus lhs rhs, Some Strict) :: nil
	| OpGe => (Minus rhs  lhs, Some Strict) :: nil
	| OpGt => (Minus rhs lhs, Some NonStrict)::nil
	| OpLt => (Minus lhs rhs, Some NonStrict)::nil
      end.

  Lemma no_middle_eval' : forall env d, (eval' env d) \/ ~ (eval' env d).
  Proof.
    unfold eval'.
    destruct d.
    destruct o.
    destruct r ; simpl ; try omega.
    omega.
  Qed.

  Lemma normalise_sound : forall env t, eval env t -> make_conj Term' (eval' env) (normalise t).
  Proof.
    destruct t ; simpl.
    destruct op0 ; simpl; try omega.
  Qed.

  Lemma normalise_complete : forall env t, make_conj Term' (eval' env) (normalise t) -> eval env t.
  Proof.
    destruct t ; simpl ; destruct op0;simpl ; omega.
  Qed.

  Lemma negate_sound : forall env t, eval env t -> make_conj Term' (fun x => ~ (eval' env x)) (negate t).
  Proof.
    destruct t as [t' o] ; simpl ; destruct o ; simpl ; omega.
  Qed.

  Lemma negate_complete : forall env t, make_conj Term' (fun x => ~ (eval' env x)) (negate t) -> eval env t.
  Proof.
    destruct t as [t' o] ; simpl ; destruct o ; simpl ; omega.
  Qed.

  Definition redOpMult (o o':redOp) : redOp :=
    match o  with
      | Equal      => Equal
      | NonStrict => NonStrict
      | Strict  =>  o'
    end.

  Definition redOpAdd (o o':redOp) : redOp :=
    match o  with
      | Equal        => o'
      | NonStrict => match o' with
                       | Strict => Strict                         
                       |   _    => NonStrict
                     end
      | Strict    => Strict
  end.


  Lemma redOpMult_sound : forall o o' e e',
    eval_redop o e 0 -> eval_redop o' e' 0 -> eval_redop (redOpMult o o') (e * e') 0.
  Proof.
    unfold eval_redop ;  destruct o;simpl;intros.
    subst ; reflexivity.
    destruct o'.
    rewrite Zmult_comm ;subst;reflexivity.
    apply Zmult_gt_0_compat;auto.
    apply pos_times_pos_is_pos ; romega.
    destruct o'; apply pos_times_pos_is_pos ; romega.
  Qed.

  Lemma redOpAdd_sound : forall o o' e e',
    eval_redop o e 0 -> eval_redop o' e' 0 -> eval_redop (redOpAdd o o') (e + e') 0.
  Proof.
    unfold eval_redop ;  destruct o; destruct o'; simpl;intros; try romega.
  Qed.


  Inductive Monoid (l:list Term') : Expr -> Prop :=
  | M_One : Monoid l (Pconst 1)
  | M_In : forall p, In (p,None) l -> Monoid l p
  | M_Mult : forall e1 e2, Monoid l e1 -> Monoid l e2 -> Monoid l (Pmult e1 e2).


  Inductive Cone (l: list (Term')): Expr -> redOp -> Prop :=
  | InC : forall p op, In (p,Some op) l -> Cone l p op
  | IsIdeal : forall p, Cone l p Equal -> forall p', Cone l (Pmult p p') Equal
  | IsSquare : forall p, Cone l (Pmult p p) NonStrict
  | IsMonoid : forall p, Monoid l p -> Cone l (Pmult p p) Strict
  | IsMult : forall p op q oq, Cone l p op -> Cone l q oq -> Cone l (Pmult p q) (redOpMult op oq)
  | IsAdd : forall p op q oq, Cone l p op -> Cone l q oq -> Cone l (Pplus p q) (redOpAdd op oq)
  | IsPos : forall c, c > 0 -> Cone l (Pconst c) Strict
  | IsZ   : Cone l (Pconst 0) Equal.


  Lemma Monoid_mono : forall l p q , Monoid l q -> Monoid (p::l) q.
  Proof.
    intros ; induction H.
    apply M_One ; auto.
    apply M_In; auto.
    right;auto.
    apply M_Mult ; auto.
  Qed.

  Lemma Cone_mono : forall l p q oq, Cone l q oq -> Cone (p::l) q oq.
  Proof.
    intros.
    induction H.
    apply InC.
    right;auto.
    apply IsIdeal;auto.
    apply IsSquare.
    apply IsMonoid;apply Monoid_mono;auto.
    apply IsMult ; auto.
    apply IsAdd ; auto.
    apply IsPos;auto.
    apply IsZ.
  Qed.


  Lemma Monoid_diff : forall l env, (forall p, In p l -> eval' env p) -> 
    forall q, Monoid l q -> eval' env (q,None).
  Proof.
    intros.
    induction H0.
    simpl.
    congruence.
    apply H ; auto.
    simpl in * .
    red ; intro.
    generalize (Zmult_integral _ _ H0).
    tauto.
  Qed.
  
  Lemma Cone_positive : 
    forall l env, (forall p, In p l -> eval' env p) -> 
      forall q oq, Cone l q oq-> eval' env (q,Some oq).
  Proof.
    intros.
    induction H0.
    apply H ;auto.
    simpl in * |- * .
    rewrite IHCone;reflexivity.
    simpl.
    apply sqr_pos.
    generalize (Monoid_diff _ _ H _ H0).
    simpl.
    generalize (interp_p env p).
    intros.
    destruct (neq_or _ _ H1).
    apply Zmult_gt_0_compat;auto.
    replace (z*z) with (-z*-z).
    assert ( (-z)* (-z) > 0).
    apply Zmult_gt_0_compat;romega.
    auto.
    ring.
    simpl.
    apply redOpMult_sound;auto.
    simpl.
    apply redOpAdd_sound;auto.
    simpl.
    auto.
    simpl.
    reflexivity.
  Qed.

  (* A syntactic characterisation of elements of a Cone - S_In : nat -> index into a map?*)
  Definition MonoidMember : Set := list nat.

  Inductive ConeMember : Set :=
  | S_In : nat -> ConeMember
  | S_Ideal : Expr -> ConeMember -> ConeMember
  | S_Square : Expr -> ConeMember
  | S_Monoid : MonoidMember -> ConeMember
  | S_Mult : ConeMember -> ConeMember -> ConeMember
  | S_Add : ConeMember -> ConeMember -> ConeMember
  (* Because I am working over Z *)
  | S_Pos : positive -> ConeMember
  | S_Z : ConeMember.
  
  Definition mult (t t' : Expr * redOp) : Expr * redOp :=
    let (te,o) := t in
      let (te',o') := t' in
        (Pmult te te', redOpMult o o').
  
  Definition plus (t t' : Expr*redOp) : Expr * redOp :=
    let (te,o) := t in
      let (te',o') := t' in
        (Pplus te te', redOpAdd o o').
  
  Definition multo (e:Expr) (t:Expr * redOp) : Expr * redOp :=
    let (te,o) := t in
      match o with
        | Equal => (Pmult te e,Equal)
        | _    => t
      end.

  (* Could be a fold_left *)
  Fixpoint eval_monoid (l: list Term') (idxs : MonoidMember) {struct idxs} : Expr :=
    match idxs with
      | nil => Pconst 1
      | n :: rst => Pmult (match nth n l (Pconst 1, None) with
                      | (x,None) => x
                      |  _       => Pconst 1
                    end)  (eval_monoid l rst)
    end.

  Lemma eval_monoid_monoid : forall l m, Monoid l (eval_monoid l m).
  Proof.
    induction m.
    simpl.
    constructor.
    simpl.
    apply M_Mult;auto.
    destruct (nth_in_or_default a l (Pconst 1,None)).
    destruct (nth a l (Pconst 1, None)).    
    destruct o.
    constructor.
    apply M_In;auto.
    rewrite e.
    apply M_One.
  Qed.


  Fixpoint eval_cone  (l: list Term') (p: ConeMember) {struct p} : Expr * redOp :=
    match p with
      | S_In n => match nth n l (Pconst 1,Some Strict) with
                    | (x, None) => (Pconst 1, Strict)
                    | (x, Some o) => (x,o)
                  end
      | S_Ideal e c => multo e (eval_cone l c)
      | S_Square p => (Pmult p p, NonStrict)
      | S_Monoid m => let p := eval_monoid l m in (Pmult p p, Strict)
      | S_Mult p q => 
        mult (eval_cone l p) (eval_cone l q)
      | S_Add p q => plus (eval_cone l p) (eval_cone l q)
      | S_Pos p => (Pconst (Zpos p),Strict)
      | S_Z => (Pconst Z0, Equal)
    end.

  Lemma eval_cone_cone : forall p s, let (t,o) := eval_cone p s in Cone p t o.
  Proof.
    intros.
    induction s;simpl.
    destruct (nth_in_or_default n p (Pconst 1,Some Strict)).
    destruct (nth n p (Pconst 1, Some Strict)).
    destruct o.
    apply InC;auto.
    apply IsPos;romega.
    destruct (nth n p (Pconst 1, Some Strict)).
    inversion e.
    apply IsPos;auto.
    compute ; congruence.
    (**)
    destruct (eval_cone p s).
    unfold multo.
    destruct r; auto.
    apply IsIdeal;auto.
    apply IsSquare.
    apply IsMonoid.
    apply eval_monoid_monoid.
    destruct (eval_cone p s1).
    destruct (eval_cone p s2).
    unfold mult.
    apply IsMult;auto.
    destruct (eval_cone p s1).
    destruct (eval_cone p s2).
    unfold plus.
    apply IsAdd;auto.
    apply IsPos.
    compute; congruence.
    apply IsZ.
  Qed.
  

  Definition witness (t:list Term') (e:Expr) := 
    exists o, Cone t e o /\ forall env, not (eval_redop  o  (interp_p env e) 0).

  Lemma prove_unfeasible : forall t e, witness t e -> forall env,make_impl Term' (eval' env) t False.
  Proof.
    intros.
    destruct H as [o [wit H]].  
    apply make_conj_impl1.
    intro.
    generalize (make_conj_in _ _ _  H0).
    intros.
    unfold eval' in H1.
    generalize (Cone_positive _ _ H1 _ o wit).
    generalize (H env).
    simpl.
    tauto.
  Qed.

  Require Import ZArith_base.
  
  Definition checker_neg (t : Expr * redOp) : bool :=
    let (poly,op) := t in
    match 
      @polynomial_simplify Z Zplus Zmult 1 Z0 Zopp Zeq_bool poly
      with
      | Nil_monom => match op with
                       | Strict    => true
                       |   _       => false
                     end
      | Cons_monom x Nil_var (Nil_monom) => match op with
                                              | Equal      => is_strict_neg x
                                              | NonStrict => is_strict_neg x
                                              | Strict    => is_neg x
                                            end
      | _ => false
    end.
    

  Lemma checker_neg_sound : forall p o, checker_neg (p,o) = true -> forall env, ~ eval_redop  o (interp_p env p) 0.
  Proof.
    intros.
    rewrite <- (polynomial_simplify_ok Z Zplus Zmult 1 0 Zopp Zeq_bool env).
    unfold checker_neg in H.
    destruct (polynomial_simplify Zplus Zmult 1 0 Zopp Zeq_bool p).
    destruct o.
    discriminate.
    simpl.
    omega.
    discriminate.
    destruct v; try discriminate.
    destruct c; try discriminate.
    destruct o ; simpl.
    generalize (is_strict_neg_ok _ H).
    romega.
    generalize (is_neg_ok _ H).
    romega.
    generalize (is_strict_neg_ok _ H).
    romega.
    discriminate.
    Require Import LegacyZArithRing.
    apply ZTheory.
  Qed.

  Definition Witness := ConeMember.

  Definition checker : Witness -> list Term' -> bool :=
    fun wit l => checker_neg   (eval_cone l wit).

  Lemma checker_sound : forall t, (exists w, checker w t = true) -> forall env, make_impl _ (eval' env)  t False.
  Proof.
    intros.
    destruct H as [w H].
    case_eq (eval_cone t w).
    intros.
    apply (prove_unfeasible t e).
    unfold witness.
    exists r.
    split.
    generalize (eval_cone_cone t w).
    destruct (eval_cone t w).
    inversion H0 ; auto.
    unfold checker in H.
    intros.
    apply checker_neg_sound;auto.
    rewrite H0 in H.
    auto.
  Qed.

End Polynomial.

(* Generalised checkers comme for free *)

Require CheckerMaker.

Module Checkers := CheckerMaker.Make(Polynomial).

(** Used by the tactics == unproved **)
Import Polynomial.
Fixpoint simpl_expr (e:Expr) : Expr :=
  match e with
    | Pmult y z => let y' := simpl_expr y in let z' := simpl_expr z in
      match y' , z' with
        | Pconst 1 , z' => z'
        |     _     , _   => Pmult y' z'
      end
    | Pplus x  y => Pplus (simpl_expr x) (simpl_expr y)
    |   _    => e
  end.


Definition simpl_cone (e:ConeMember) : ConeMember :=
  match e with
    | S_Square t => match simpl_expr t with
                      | Pconst (Zpos x) => S_Pos (BinPos.Pmult x x)
                      | Pconst ZO   => S_Z
                      |       x     => S_Square x
                    end
    | S_Mult t1 t2 => 
      match t1 , t2 with
        | S_Z      , x        => S_Z
        |    x     , S_Z      => S_Z
        | S_Pos xH ,   x      => x
        |     x    , S_Pos xH => x
        | S_Pos p1 , S_Pos p2 => S_Pos (BinPos.Pmult p1 p2)
        | S_Pos p1 , S_Mult (S_Pos p2)  x => S_Mult (S_Pos (BinPos.Pmult p1 p2)) x
        | S_Pos p1 , S_Mult x (S_Pos p2)  => S_Mult (S_Pos (BinPos.Pmult p1 p2)) x
        | S_Mult (S_Pos p2)  x  , S_Pos p1   => S_Mult (S_Pos (BinPos.Pmult p1 p2)) x
        | S_Mult x (S_Pos p2)   , S_Pos p1   => S_Mult (S_Pos (BinPos.Pmult p1 p2)) x
        | S_Pos x   , S_Add y z   => S_Add (S_Mult (S_Pos x) y) (S_Mult (S_Pos x) z)
        |     _     , _   => e
      end
    | S_Add t1 t2 => 
      match t1 ,  t2 with
        | S_Z     , x => x
        |   x     , S_Z => x
        |   x     , y   => S_Add x y
      end
    |   _     => e
  end.


(** To ease bindings from ml code **)
Definition varmap := Quote.varmap.
Definition make_impl := Refl.make_impl.
Definition make_conj := Refl.make_conj.
Definition varmap_type := varmap Z.
Definition coneMember := ConeMember.

Definition eval := eval.
Definition empty_checkerT_sound := Checkers.checkerT_sound.
Definition order_checkerT_sound := Checkers.order_checkerT_sound.

Definition prod_pos_nat := prod positive nat.

Definition power := power.



Extraction "micromega.ml"  List.map simpl_cone Checkers. 

  