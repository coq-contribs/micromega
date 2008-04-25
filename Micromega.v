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

(*Require Import LegacyRing.
Require Import Ring_theory.
Require Import LRing_normalise.
Require Import Quote.
**)
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

  Definition Var := positive.
  Require VarMap.
  Definition EEnv := VarMap.t Z.
  Require Export NRing.
  Definition Expr := PExpr Z.

  Fixpoint interp_p (l:EEnv) (pe: Expr) {struct pe} : Z :=
   match pe with
   | PEc c =>  c
   | PEX j => VarMap.find  0 j l
   | PEadd pe1 pe2 => (interp_p l pe1) + (interp_p l pe2)
   | PEsub pe1 pe2 => (interp_p l pe1) - (interp_p l pe2)
   | PEmul pe1 pe2 => (interp_p l pe1) * (interp_p l pe2)
   | PEopp pe1 => - (interp_p l pe1)
   | PEpow pe1 n => Zpower (interp_p l pe1) (Z_of_N n)
   end.

  Lemma interp_PEeval : forall env pe, interp_p env pe = @PEeval Z Z0 Zplus Zmult Zminus Zopp Z (fun x => x) Z Z_of_N Zpower (None,env) pe.
  Proof.
    induction pe ; simpl ; intros.
    reflexivity.
    reflexivity.
    rewrite <- IHpe1 ; rewrite <- IHpe2 ; reflexivity.
    rewrite <- IHpe1 ; rewrite <- IHpe2 ; reflexivity.
    rewrite <- IHpe1 ; rewrite <- IHpe2 ; reflexivity.
    rewrite <- IHpe ; reflexivity.
    rewrite <- IHpe ; reflexivity.
  Qed.

(*  
  Definition power_pos (e:Expr) (n:positive) : Expr :=
    iter_pos n Expr (fun x => Pmult e x) (Pconst 1).
  
  Definition power (e:Expr) (z:Z) : Expr :=
    match z with
      | Z0 => Pconst 1
      | Zpos p => power_pos e p
      | Zneg _ => Pconst 0
    end.
*)

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

(*  Definition Minus (e1 e2 : Expr) : Expr :=
    Pplus e1 (Popp e2). *)

  (* Over Z, there are several ways exist to normalise and negate *)

(*
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
*)

   Definition normalise (t:Term) : list Term' :=
      let (lhs,o,rhs) := t in
        match o with
          | OpEq => (PEsub lhs  rhs , Some Equal)::nil
          | OpNEq => (PEsub lhs  rhs , None)::nil
	         | OpLe => (PEsub rhs lhs,Some NonStrict) :: nil
	         | OpGe => (PEsub lhs rhs,Some NonStrict) :: nil
	         | OpGt => (PEsub lhs rhs , Some Strict) :: nil
	         | OpLt => (PEsub rhs lhs , Some Strict) :: nil
        end.

  Definition negate (t:Term) : list Term' :=
    let (lhs,o,rhs) := t in
      match o with
    | OpNEq => (PEsub rhs  lhs, Some Equal)::nil
    | OpEq => (PEsub rhs  lhs, None)::nil
  (* e <= e' == ~ e > e' *)
	   | OpLe => (PEsub lhs rhs, Some Strict) :: nil
	   | OpGe => (PEsub rhs  lhs, Some Strict) :: nil
	   | OpGt => (PEsub rhs lhs, Some NonStrict)::nil
	   | OpLt => (PEsub lhs rhs, Some NonStrict)::nil
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
  | M_One : Monoid l (PEc 1)
  | M_In : forall p, In (p,None) l -> Monoid l p
  | M_Mult : forall e1 e2, Monoid l e1 -> Monoid l e2 -> Monoid l (PEmul e1 e2).


  Inductive Cone (l: list (Term')): Expr -> redOp -> Prop :=
  | InC : forall p op, In (p,Some op) l -> Cone l p op
  | IsIdeal : forall p, Cone l p Equal -> forall p', Cone l (PEmul p p') Equal
  | IsSquare : forall p, Cone l (PEmul p p) NonStrict
  | IsMonoid : forall p, Monoid l p -> Cone l (PEmul p p) Strict
  | IsMult : forall p op q oq, Cone l p op -> Cone l q oq -> Cone l (PEmul p q) (redOpMult op oq)
  | IsAdd : forall p op q oq, Cone l p op -> Cone l q oq -> Cone l (PEadd p q) (redOpAdd op oq)
  | IsPos : forall c, c > 0 -> Cone l (PEc c) Strict
  | IsZ   : Cone l (PEc 0) Equal.


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
    generalize (@Monoid_diff _ _ H _ H0).
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
        (PEmul te te', redOpMult o o').
  
  Definition plus (t t' : Expr*redOp) : Expr * redOp :=
    let (te,o) := t in
      let (te',o') := t' in
        (PEadd te te', redOpAdd o o').
  
  Definition multo (e:Expr) (t:Expr * redOp) : Expr * redOp :=
    let (te,o) := t in
      match o with
        | Equal => (PEmul te e,Equal)
        | _    => t
      end.

  (* Could be a fold_left *)
  Fixpoint eval_monoid (l: list Term') (idxs : MonoidMember) {struct idxs} : Expr :=
    match idxs with
      | nil => PEc 1
      | n :: rst => PEmul (match nth n l (PEc 1, None) with
                      | (x,None) => x
                      |  _       => PEc 1
                    end)  (eval_monoid l rst)
    end.

  Lemma eval_monoid_monoid : forall l m, Monoid l (eval_monoid l m).
  Proof.
    induction m.
    simpl.
    constructor.
    simpl.
    apply M_Mult;auto.
    destruct (nth_in_or_default a l (PEc 1,None)).
    destruct (nth a l (PEc 1, None)).    
    destruct o.
    constructor.
    apply M_In;auto.
    rewrite e.
    apply M_One.
  Qed.


  Fixpoint eval_cone  (l: list Term') (p: ConeMember) {struct p} : Expr * redOp :=
    match p with
      | S_In n => match nth n l (PEc 1,Some Strict) with
                    | (x, None) => (PEc 1, Strict)
                    | (x, Some o) => (x,o)
                  end
      | S_Ideal e c => multo e (eval_cone l c)
      | S_Square p => (PEmul p p, NonStrict)
      | S_Monoid m => let p := eval_monoid l m in (PEmul p p, Strict)
      | S_Mult p q => 
        mult (eval_cone l p) (eval_cone l q)
      | S_Add p q => plus (eval_cone l p) (eval_cone l q)
      | S_Pos p => (PEc (Zpos p),Strict)
      | S_Z => (PEc Z0, Equal)
    end.

  Lemma eval_cone_cone : forall p s, let (t,o) := eval_cone p s in Cone p t o.
  Proof.
    intros.
    induction s;simpl.
    destruct (nth_in_or_default n p (PEc 1,Some Strict)).
    destruct (nth n p (PEc 1, Some Strict)).
    destruct o.
    apply InC;auto.
    apply IsPos;romega.
    destruct (nth n p (PEc 1, Some Strict)).
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
    (*unfold eval' in H1.*)
    generalize (@Cone_positive _ _ H1  _ o wit).
    generalize (H env).
    simpl.
    tauto.
  Qed.

  Require Import ZArith_base.

  (*Definition polynomial_simplify :=       @polynomial_simplify Z Zplus Zmult 1 Z0 Zopp  Zeq*)

  Definition polynomial_simplify := @norm_aux Z Z0 1 Zplus Zmult Zminus Zopp (fun x y => proj1_sig (Z_eq_bool x y)).
  Definition polynomial_simplify_ok := @norm_aux_spec Z Z0 1 Zplus Zmult Zminus Zopp (@eq Z).


  Definition checker_neg (t : Expr * redOp) : bool :=
    let (poly,op) := t in
    match 
      polynomial_simplify  poly
      with
      | Pc x => match op with
                  | Equal      => is_strict_neg x
                  | NonStrict => is_strict_neg x
                  | Strict    => is_neg x
                end
      | _ => false
    end.

  
  Require InitialRing.
  Require Ring_theory.

  Lemma Zsemi_ring : semi_ring_theory Z0 (Zpos xH) Zplus Zmult (@eq Z).
  Proof.
    constructor; intros ; try omega.
    rewrite Zmult_comm ; reflexivity.
    rewrite Zmult_assoc ; reflexivity.
    rewrite Zmult_plus_distr_l ; reflexivity.
  Qed.

  Lemma Zalmost_ring : almost_ring_theory Z0 (Zpos xH) Zplus Zmult Zminus Zopp (@eq Z).
  Proof.
    destruct Zsemi_ring.
    constructor ; auto.
    intros.
    rewrite <- Zopp_mult_distr_l ; reflexivity.
    intros ; omega.
  Qed.

  Lemma ZNpower : forall r n, r ^ Z_of_N n = pow_N 1 Zmult r n.
  Proof.
    destruct n.
    reflexivity.
    simpl.
    unfold Zpower_pos.
    replace (pow_pos Zmult r p) with (1 * (pow_pos Zmult r p)) by ring.
    generalize 1.
    induction p; simpl ; intros ; repeat rewrite IHp ; ring.
  Qed.
    
    


  Lemma checker_neg_sound : forall p o, checker_neg (p,o) = true -> forall env, ~ eval_redop  o (interp_p env p) 0.
  Proof.
    intros.
    unfold interp_p.
    rewrite interp_PEeval.
    rewrite (@norm_aux_spec Z Z0 1 Zplus Zmult Zminus Zopp (@eq Z) 
      InitialRing.Zsth InitialRing.Zeqe Zalmost_ring 
      Z Z0 (Zpos xH) Zplus Zmult Zminus Zopp (fun x y => proj1_sig (Z_eq_bool x y)) (fun x => x)).
    unfold checker_neg in H.
    change ((norm_aux 0 1 Zplus Zmult Zminus Zopp (fun x y => proj1_sig (Z_eq_bool x y)) p))
      with (polynomial_simplify p).
    destruct (polynomial_simplify p).
    simpl.
    destruct o ;simpl ; intros.
    generalize (is_strict_neg_ok _ H).
    romega.
    generalize (is_neg_ok _ H).
    romega.
    generalize (is_strict_neg_ok _ H).
    romega.
    discriminate.
    discriminate.
    constructor; intros ; try reflexivity.
    generalize H0; unfold Z_eq_bool; destruct (Z_eq_dec x y). 
      trivial. 
      simpl; intros; discriminate.

    constructor.
    apply ZNpower.
  Qed.


  Definition Witness := ConeMember.

  Definition checker : Witness -> list Term' -> bool :=
    fun wit l => checker_neg   (eval_cone l wit).

  Lemma checker_sound : forall t  w, checker w t = true -> forall env, make_impl _ (eval' env)  t False.
  Proof.
    intros.
    case_eq (eval_cone t w).
    intros.
    apply (@prove_unfeasible t e).
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
    | PEmul y z => let y' := simpl_expr y in let z' := simpl_expr z in
      match y' , z' with
        | PEc 1 , z' => z'
        |     _     , _   => PEmul y' z'
      end
    | PEadd x  y => PEadd (simpl_expr x) (simpl_expr y)
    |   _    => e
  end.


Definition simpl_cone (e:ConeMember) : ConeMember :=
  match e with
    | S_Square t => match simpl_expr t with
                      | PEc (Zpos x) => S_Pos (BinPos.Pmult x x)
                      | PEc ZO   => S_Z
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


Fixpoint map_cone (f: nat -> nat) (e:ConeMember) : ConeMember :=
  match e with
    | S_In n         => S_In (f n)
    | S_Ideal e cm   => S_Ideal e (map_cone f cm)
    | S_Square _     => e
    | S_Monoid l     => S_Monoid (List.map f l)
    | S_Mult cm1 cm2 => S_Mult (map_cone f cm1) (map_cone f cm2)
    | S_Add cm1 cm2  => S_Add (map_cone f cm1) (map_cone f cm2)
    |  _             => e
  end.

Fixpoint indexes (e:ConeMember) : list nat :=
  match e with
    | S_In n         => n::nil
    | S_Ideal e cm   => indexes cm
    | S_Square e     => nil
    | S_Monoid l     => l
    | S_Mult cm1 cm2 => (indexes cm1)++ (indexes cm2)
    | S_Add cm1 cm2  => (indexes cm1)++ (indexes cm2)
    |  _             => nil
  end.
  
(** To ease bindings from ml code **)
(*Definition varmap := Quote.varmap.*)
Definition make_impl := Refl.make_impl.
Definition make_conj := Refl.make_conj.

Require VarMap.

(*Definition varmap_type := VarMap.t Z. *)
Definition env := EEnv.
Definition node := @VarMap.Node Z.
Definition empty := @VarMap.Empty Z.
Definition leaf := @VarMap.Leaf Z.

Definition coneMember := ConeMember.

Definition eval := eval.
Definition empty_checkerT_sound := Checkers.checkerT_sound.
Definition order_checkerT_sound := Checkers.order_checkerT_sound.

Definition prod_pos_nat := prod positive nat.

Definition n_of_Z (z:Z) : N :=
  match z with
    | Z0 => N0
    | Zpos p => Npos p
    | Zneg p => N0
  end.
  

(*Definition power := power.*)


Extraction "micromega.ml"  List.map simpl_cone map_cone indexes  n_of_Z Checkers. 

  