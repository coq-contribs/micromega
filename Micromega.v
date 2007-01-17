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

Lemma pos_times_pos_is_pos : forall x y, x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
  intros.
  assert (0 <= x * y).
  apply Zmult_le_0_compat;omega.
  omega.
Qed.

Lemma power_2 : forall x, Zpower_nat x 2 = x * x.
Proof.
  intro.
  unfold Zpower_nat.
  simpl.
  ring.
Qed.
  
Definition is_neg (z:Z) : bool :=
  match z with
    | Zneg n => true
    | _ => false
  end.

Lemma is_neg_ok : forall z , is_neg z = true -> z < 0.
Proof.
  destruct z ; simpl; compute;congruence.
Qed.



(* Polynomial expressions *)
(* 
  Require Import Ring_theory.
  Require Import Ring_normalize.
  I do not use the polynomial defined in ring
  1) They live in Type. For coq 8.0pl3, this is not very handy
  2) The sectioning mechanism makes the assumption of a varmap.
*)
Module M.

  Require Import LegacyZArithRing.
  Require Import LegacyRing_theory.
  Require Import Quote.
  Require Import Ring_normalize.

  Definition Var := index.
  Definition EEnv := varmap Z.

  Definition get_env (e:EEnv) (i:Var) :Z  := @varmap_find Z Z0 i e.

  
  Inductive Expr : Set :=
    | V : Var -> Expr
    | C : Z -> Expr
    | Mult : Expr -> Expr -> Expr
    | Add  : Expr -> Expr -> Expr
    | Minus : Expr -> Expr -> Expr
    | UMinus : Expr -> Expr
    | Power : Expr -> Z -> Expr.
  
  Fixpoint eval_expr  (env: EEnv) (p:Expr) {struct p}: Z :=
    match p with
      | V v => get_env env v
      | C c => c
      | Mult p q => (eval_expr env p) * (eval_expr env q)
      | Add p q => (eval_expr env p) + (eval_expr env q)
      | Minus p q => (eval_expr env p) - (eval_expr env q)
      | UMinus p => - (eval_expr env p)
      | Power p n => Zpower (eval_expr env p) n
    end.
  
  Fixpoint power_nat (p:polynomial Z) (n:nat) {struct n} : polynomial Z:=
    match n with
      | O => Pconst 1
      | S n => Pmult p (power_nat p n)
    end.
  

  Fixpoint iter_pos (n:positive) (A:Type) (f:A -> A) (x:A) {struct n} : A :=
    match n with
      | xH => f x
      | xO n' => iter_pos n' A f (iter_pos n' A f x)
      | xI n' => f (iter_pos n' A f (iter_pos n' A f x))
    end.

  Fixpoint iter_nat (n:nat) (A:Type) (f:A -> A) (x:A) {struct n} : A :=
    match n with
      | O => x
      | S n' => f (iter_nat n' A f x)
    end.


  Theorem iter_nat_plus :
    forall (n m:nat) (A:Type) (f:A -> A) (x:A),
      iter_nat (n + m) A f x = iter_nat n A f (iter_nat m A f x).
  Proof. 
    simple induction n;
      [ simpl in |- *; auto with arith
	| intros; simpl in |- *; apply f_equal with (f:= f); apply H ]. 
  Qed.



  Theorem iter_nat_of_P :
    forall (p:positive) (A:Type) (f:A -> A) (x:A),
      iter_pos p A f x = iter_nat (nat_of_P p) A f x.
  Proof. 
    intro n; induction n as [p H| p H| ];
      [ intros; simpl in |- *; rewrite (H A f x);
    rewrite (H A f (iter_nat (nat_of_P p) A f x)); 
      rewrite (ZL6 p); symmetry in |- *; apply f_equal with (f:= f);
	apply iter_nat_plus
	| intros; unfold nat_of_P in |- *; simpl in |- *; rewrite (H A f x);
	  rewrite (H A f (iter_nat (nat_of_P p) A f x)); 
	    rewrite (ZL6 p); symmetry in |- *; apply iter_nat_plus
	| simpl in |- *; auto with arith ].
  Qed.

  Definition power_pos (pol:polynomial Z) (p:positive)  : polynomial Z:=
    iter_pos p (polynomial Z) (Pmult pol)  (Pconst 1).

  Definition power (pol:polynomial Z) (z:Z) : polynomial Z:=
    match z with
      | Zpos p => power_pos pol p
      | Z0 => Pconst 1
      | Zneg _ => Pconst 0
    end.
    

  Fixpoint to_polynomial (p:Expr) :polynomial Z:=
    match p with 
      | V v => Pvar _ v
      | C c => Pconst c
      | Mult p1 p2 => Pmult (to_polynomial p1) (to_polynomial p2)
      | Add p1 p2 => Pplus (to_polynomial p1) (to_polynomial p2)
      | Minus p1 p2 => Pplus (to_polynomial p1) (Popp (to_polynomial p2))
      | UMinus p => Popp (to_polynomial p)
      | Power p n => power (to_polynomial p) n
    end.

  Definition interp_p := @interp_p Z Zplus Zmult Z0 Zopp.

  Lemma interp_p_simpl : forall (p:polynomial Z) (v:varmap Z), interp_p v  p =
    match p with
      | Pconst c => c
      | Pvar i => varmap_find Z0 i v
      | Pplus p1 p2 => Zplus (interp_p v p1) (interp_p  v p2)
      | Pmult p1 p2 => Zmult (interp_p  v p1) (interp_p  v p2)
      | Popp p1 => Zopp (interp_p  v p1)
    end.
  Proof.
    destruct p ; reflexivity.
  Qed.


  Lemma polynomial_expr : forall v p, eval_expr v p = interp_p v  (to_polynomial p).
  Proof.
    induction p; simpl; try reflexivity ; try (rewrite IHp1 ; rewrite IHp2 ; reflexivity).
    rewrite IHp ; reflexivity.
    rewrite IHp.
    destruct z ; simpl; try reflexivity.
    unfold power_pos.
    rewrite iter_nat_of_P.
    rewrite Zpower_pos_nat.
    generalize (lt_O_nat_of_P p0).
    induction (nat_of_P p0).
    intros ; apply False_ind;omega.
    intros.
    destruct n.
    reflexivity.
    simpl in IHn.
    simpl.
    rewrite <- IHn.
    reflexivity.
    omega.
  Qed.
  

  Inductive Op : Set :=
    | OpEq
    | OpLe
    | OpGe
    | OpGt
    | OpLt.
  
  Definition eval_op (o:Op) : Z -> Z -> Prop :=
    match o with
      | OpEq => (fun x y => x = y)
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
  
  Module Polynomial.
    
    Definition Term := Cstr.
    
    Definition Env := EEnv.
    
    Definition eval (env:Env) (t:Term) : Prop :=
      let (lhs,op,rhs) := t in
	(eval_op op) (eval_expr env lhs) (eval_expr env rhs).
    
    Definition Term' := Expr.
    
    Definition eval' (e:Env) (t:Term')  :Prop :=
      eval_expr e t >= 0.
    
    Definition normalise (p:Term) : list Term' :=
      let (lhs,op,rhs) := p in
	match op with
	  | OpEq => (Minus lhs rhs) :: (Minus rhs lhs) :: nil
	  | OpLe => (Minus rhs lhs) :: nil
	  | OpGe => (Minus lhs rhs) :: nil
	  | OpGt => (Minus lhs (Add rhs (C 1)))::nil
	  | OpLt => (Minus rhs (Add lhs (C 1)))::nil
	end.
    
    Lemma normalise_sound : forall env t t', In t' (normalise t) -> eval env t ->  eval' env t'.
    Proof.
      destruct t.
      simpl.
      unfold eval'.
      destruct op0;simpl; intros e H H1; repeat (destruct H); simpl; omega.
    Qed.

    Lemma normalise_complete : forall env t, (forall t', In t' (normalise t) -> eval' env t')  ->  eval env t.
    Proof.
      destruct t.
      unfold eval'.
      simpl.
      destruct op0; simpl; intros.
      generalize (H _ (or_introl _ (refl_equal (Minus lhs0 rhs0)))).
      generalize (H _ (or_intror _ (or_introl _ (refl_equal (Minus rhs0 lhs0))))).
      simpl;omega.
      intros.
      generalize (H _ (or_introl _ (refl_equal (Minus rhs0 lhs0)))).  
      simpl;omega.
      generalize (H _ (or_introl _ (refl_equal (Minus lhs0 rhs0)))).  
      simpl;omega.
      generalize (H _ (or_introl _ (refl_equal (Minus lhs0 (Add rhs0 (C 1)))))).
      simpl;omega.
      generalize (H _ (or_introl _ (refl_equal (Minus rhs0 (Add lhs0 (C 1)))))).
      simpl;omega.
    Qed.

    Definition negate (t:Term') : Term' := Minus (UMinus t) (C 1).

    Lemma no_middle : forall env d, (eval' env d) \/ ~ (eval' env d).
    Proof.
      intros.
      unfold eval'.
      omega.
    Qed.

    Lemma negate_sound : forall d env, ~ (eval' env d) -> eval' env (negate d).
    Proof.
      unfold eval'.
      unfold negate.
      simpl.
      intros ; omega.
    Qed.

    Lemma negate_complete : forall d env, eval' env (negate d) -> ~ eval' env d.
    Proof.
      unfold eval'.
      unfold negate.
      simpl.
      intros ; omega.
    Qed.
    
  End Polynomial.
  
  Import Polynomial.
  
  (* The Cone of a list (finite set) of polynomials
    NB : For efficiency, this should be a map...
   *)
  
  Inductive Cone (l: list Expr):Expr -> Prop :=
    | InC : forall p , In p l -> Cone l p
    | IsSquare : forall p, Cone l (Power p 2)
    | IsMult : forall p q, Cone l p -> Cone l q -> Cone l (Mult p q)
    | IsAdd : forall p q, Cone l p -> Cone l q -> Cone l (Add p q)
    | IsPos : forall c, c >= 0 -> Cone l (C c).
  

  Lemma Cone_mono : forall l p q, Cone l q -> Cone (p::l) q.
  Proof.
    intros.
    induction H.
    apply InC.
    right;auto.
    apply IsSquare.
    apply IsMult ; auto.
    apply IsAdd ; auto.
    apply IsPos;auto.
  Qed.
  
  
  
  Lemma Cone_positive : 
    forall l env, (forall p, In p l -> eval_expr env p >= 0) -> 
      forall q , Cone l q -> eval_expr env q >= 0.
  Proof.
    intros.
    induction H0.
    apply H ;auto.
    simpl.
    unfold Zpower_pos.
    simpl.
    legacy ring (eval_expr env p * (eval_expr env p * 1)).
    apply sqr_pos.
    simpl.
    apply pos_times_pos_is_pos;auto.
    simpl.
    omega.
    auto.
  Qed.

  Import R.  


  (* A syntactic characterisation of elements of a Cone - S_In : nat -> index into a map?*)
  Inductive ConeMember : Set :=
    | S_In : nat -> ConeMember
    | S_Square : Expr -> ConeMember
    | S_Mult : ConeMember -> ConeMember -> ConeMember
    | S_Add : ConeMember -> ConeMember -> ConeMember
	(* Because I am working over Z *)
    | S_Pos : positive -> ConeMember
    | S_Z : ConeMember.
  
  Fixpoint eval_cone  (l: list Expr) (p: ConeMember) {struct p} : Expr :=
    match p with
      | S_In n => nth n l (C 1)
      | S_Square p => Power p 2
      | S_Mult p q => Mult (eval_cone l p) (eval_cone l q)
      | S_Add p q => Add (eval_cone l p) (eval_cone l q)
      | S_Pos p => C (Zpos p)
      | S_Z => C Z0
    end.

  Lemma eval_cone_cone : forall p s, Cone p (eval_cone  p s).
  Proof.
    intros.
    induction s;simpl.
    destruct (nth_in_or_default n p (C 1)).
    apply InC;auto.
    rewrite e.
    apply IsPos;auto.
    compute ; congruence.
    apply IsSquare.
    apply IsMult;auto.
    apply IsAdd;auto.
    apply IsPos.
    compute; congruence.
    apply IsPos.
    compute ; congruence.
  Qed.
  

  (* An optimized version which is sufficient for linear certificates *)
  Fixpoint eval_lin_aux (l:list Expr) (cert: list (positive * nat)) (res:Expr)   {struct cert} : Expr :=
    match cert with
      | nil => res
      | (p,n)::rest => match ListS.skipn Expr n l with
			 | nil => res (* bad index *)
			 | expr::l => eval_lin_aux  l rest (Add (Mult (C (Zpos p)) expr) res)
		       end
    end.

  Definition eval_lin (l:list Expr) (cert: list (positive * nat))  : Expr := eval_lin_aux l cert (C (Z0)).


  Lemma eval_lin_cone : forall p  cert, Cone p (eval_lin p cert).
  Proof.
    unfold eval_lin.
    intros.
    assert (Cone p (C 0))%Z.
    apply IsPos.
    omega.
    gen_clear H.
    pattern p at 3.
    local_change (ListS.skipn Expr O p).
    cbv beta.
    generalize (C 0).
    generalize 0%nat.
    (* Starting induction *)
    induction cert.
    simpl.
    auto.
    intros.
    simpl.
    destruct a as [p0 n0].
    rewrite ListS.skipn_add.
    CaseEq (ListS.skipn Expr (n0+n) p).
    auto.
    intros.
    replace l with (ListS.skipn Expr (S(n0 + n)) p).
    apply (IHcert (S (n0+n)) ((Add (Mult (C (Zpos p0)) e0) e))).
    apply IsAdd.
    apply IsMult.
    apply IsPos.
    compute.
    discriminate.
    apply InC.
    apply (ListS.skipn_in Expr (n0+n)).
    rewrite H0.
    left ; reflexivity.
    auto.
    rewrite ListS.skipn_simpl.
    destruct p.
    rewrite ListS.skipn_nil in H0.
    discriminate.
    eapply ListS.skipn_cons; eauto.
  Qed.
  

  Definition witness (t:list Expr) (e:Expr) := Cone t e /\ forall env, eval_expr env e < 0.

  Lemma prove_unfeasible : forall t e, witness t e -> forall env,make_impl Term' (eval' env) t False.
  Proof.
    intros.
    destruct H as [wit H].  
    apply make_conj_impl1.
    intro.
    generalize (make_conj_in _ _ _  H0).
    intros.
    unfold eval' in H1.
    generalize (Cone_positive _ _ H1 _ wit).
    generalize (H env).
    omega.
  Qed.


  Module ReflPoly := ReflD(Polynomial).
  Import ReflPoly.
  

  Definition checker_neg (poly:polynomial Z) : bool :=
    match 
      @polynomial_simplify Z Zplus Zmult 1 Z0 Zopp Zeq poly
      with
      |Cons_monom x Nil_var (Nil_monom) => is_neg x
      |  _  => false
    end.
    

  Lemma checker_neg_sound : forall p, checker_neg p = true -> forall env, interp_p env p < 0.
  Proof.
    intros.
    rewrite <- (polynomial_simplify_ok Z Zplus Zmult 1 0 Zopp Zeq env).
    unfold checker_neg in H.
    destruct (polynomial_simplify Zplus Zmult 1 0 Zopp Zeq p).
    discriminate.
    destruct v; try discriminate.
    destruct c; try discriminate.
    generalize (is_neg_ok _ H).
    simpl.
    auto.
    discriminate.
    apply ZTheory.
  Qed.

  Module Checker.
    
    Definition Witness := ConeMember.

    Definition checker : Witness -> list Term' -> bool :=
      fun wit l => checker_neg (to_polynomial  (eval_cone l wit)).

    Lemma checker_sound : forall t, (exists w, checker w t = true) -> forall env, make_impl _ (eval' env)  t False.
    Proof.
      intros.
      destruct H as [w H].
      apply (prove_unfeasible t (eval_cone t w)). 
      unfold witness.
      split.
      apply eval_cone_cone.
      unfold checker in H.
      intros.
      rewrite polynomial_expr.
      apply checker_neg_sound;auto.
    Qed.

  End Checker.

  (* Generalised checkers comme for free *)

  Module Checkers := ReflPoly.CheckerMaker(Checker).

  Module CheckerLin.
    
    Definition Witness := list (positive *nat).

    Definition checker : Witness -> list Term' -> bool :=
      fun wit l => checker_neg (to_polynomial  (eval_lin l wit)).

    Lemma checker_sound : forall t, (exists w, checker w t = true) -> forall env, make_impl _ (eval' env)  t False.
    Proof.
      intros.
      destruct H as [w H].
      apply (prove_unfeasible t (eval_lin t w)). 
      unfold witness.
      split.
      apply eval_lin_cone.
      unfold checker in H.
      intros.
      rewrite polynomial_expr.
      apply checker_neg_sound;auto.
    Qed.

  End CheckerLin.

  Module CheckersLin := ReflPoly.CheckerMaker(CheckerLin).

End M.  


  (** To ease bindings from ml code **)
Definition varmap := Quote.varmap.
Definition make_impl := Refl.R.make_impl.
Definition make_conj := Refl.R.make_conj.
Definition varmap_type := varmap Z.
Definition coneMember := M.ConeMember.

Definition eval := M.Polynomial.eval.
Definition empty_checkerT_sound := M.Checkers.checkerT_sound.
Definition order_checkerT_sound := M.Checkers.order_checkerT_sound.

Definition prod_pos_nat := prod positive nat.

Definition lin_empty_checkerT_sound := M.CheckersLin.checkerT_sound.
Definition linorder_checkerT_sound := M.CheckersLin.order_checkerT_sound.




Extraction "micromega.ml"  List.map M. 

  