(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
(* From Q to Z
   micromega can prove these lemma!
*)
Require Import ZArith.
Require Import Zdiv.
Require Import preMicromegatac.
Open Scope Z_scope.

Definition ceiling (a b:Z) : Z :=
  let (q,r) := Zdiv_eucl a b in
    match r with
      | Z0 => q
      | _  => q + 1
    end.

Lemma narrow_interval_lower_bound : forall a b x, a > 0 -> a * x  >= b -> x >= ceiling b a.
Proof.
  unfold ceiling.
  intros.
  generalize (Z_div_mod b a H).
  destruct (Zdiv_eucl b a).
  intros.
  destruct H1.
  destruct H2.
  destruct (Ztrichotomy z0 0) as [ HH1 | [HH2 | HH3]]; destruct z0; zrelax ; try micmac 2.
  discriminate.
Qed.

Lemma narrow_interval_upper_bound : forall a b x, a > 0 -> a * x  <= b -> x <= Zdiv b a.
Proof.
  unfold Zdiv.
  intros.
  generalize (Z_div_mod b a H).
  destruct (Zdiv_eucl b a).
  intros.
  destruct H1.
  destruct H2.
  zrelax ;micmac 2.
Qed.

Lemma test : forall x, 2 * x >= 1 -> 2 * x <= 1 -> False.
Proof.
  intros.
  assert (2 > 0).
  micmac.
  generalize (narrow_interval_lower_bound _ _ _ H1 H).
  generalize (narrow_interval_upper_bound _ _ _ H1 H0).
  set (upper := 1 / 2).
  compute in upper.
  set (lower := ceiling 1  2).
  compute in lower.
  unfold upper.
  unfold lower.
  omicron.
Qed.

(* In this case, a certificate is made of a pair of inequations, in 1 variable,
   that do not have an integer solution.
   => modify the fourier elimination
   *)
Require Import QArith.
Import Polynomial.
Require Import Ring_normalize.

Record Witness : Set := {
  var : polynomial Z; (* this is a variable or a monomial *)
  ub  : Q * ConeMember;
  lb  : Q * ConeMember
}.

Import ZArith.


(* n/d <= x  -> d*x - n >= 0 *)
Definition makeLb (v:Expr) (q:Q) : Term :=
  let (n,d) := q in Build_Cstr  (Pmult (Pconst (Zpos d)) (v)) OpGe (Pconst  n).

(* x <= n/d  -> d * x <= d  *)
Definition makeUb (v:Expr) (q:Q) : Term :=
  let (n,d) := q in
    Build_Cstr  (Pmult (Pconst (Zpos d)) v)  OpLe (Pconst  n).

Require Import List.

Definition qceiling (q:Q) : Z :=
  let (n,d) := q in ceiling n (Zpos d).

Definition qfloor (q:Q) : Z :=
  let (n,d) := q in Zdiv n (Zpos d).

Require Import Bool.

Definition zchecker (w:Witness) (l:list Term) : bool :=
  let (v,ub,lb) := w in
    let (qub,pr1) := ub in
      let (qlb,pr2) := lb in
        (* the bounds are provable *)
        andb (Checkers.order_checkerT l (cons pr2 (cons pr1 nil)) (cons (makeUb v qub) (cons (makeLb v qlb) nil)))
        (* and the Z interval is empty *)
         (if Z_gt_dec  (qceiling qlb) (qfloor qub) then true else false).

Require Import tacticsPerso.

Lemma zChecker_sound : forall t, (exists w, zchecker w t = true) -> forall env, make_impl _ (eval env)  t False.
Proof.
  intros.
  destruct H as [w H].
  unfold zchecker in H.
  destruct w.
  destruct ub0 ; destruct lb0.
  flatten_bool.
  apply Refl.make_conj_impl1.
  intro.
  generalize (Checkers.order_checkerT_sound t (makeUb var0 q :: makeLb var0 q0 :: nil) (@ex_intro _ _ (c0::c::nil) H0) env).
  intros.
  generalize (Refl.make_conj_impl2 _ _ _ _ H2 H).
  simpl.
  clear H H2 H0.
  intros.
  destruct (Z_gt_dec (qceiling q0) (qfloor q)).
  unfold qceiling,qfloor in z.
  destruct q0 ; destruct q.
  destruct H.
  set (v := (Polynomial.interp_p env var0)%Z).
  assert ( (Zpos Qden0) * v <= Qnum0)%Z.
  exact H.
  assert ((Zpos Qden) * v >= Qnum)%Z.
  exact H0.
  clear H H0.
  assert (Zpos Qden > 0)%Z.
  compute ; reflexivity.
  generalize (narrow_interval_lower_bound _ _ _ H H3). 
  intros.
  assert (Zpos Qden0 > 0)%Z.
  compute ; reflexivity.
  generalize (narrow_interval_upper_bound _ _ _ H4 H2).
  intros.
  omicron.
  discriminate.
Qed.

