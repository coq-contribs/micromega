Require Import  ZMicromega.
Require Import QMicromega.
Require Import  RMicromega.
Require Import QArith.
Require Export Ring_normalize.
Require Import ZArith.
Require Import Reals.
Require Export RingMicromega.
Require Import VarMap.
Require Tauto.

Tactic Notation "micromega"  := micromegap (Zneg xH)  ; 
  intros __wit __varmap __ff ; change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
    apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity.

Tactic Notation "micromega" constr(d) := micromegap d; 
  intros __wit __varmap __ff ; change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
    apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity.


Ltac omicron :=  omicronp ; intros __wit __varmap __ff ; change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
  apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity.

Ltac qomicron :=  qomicronp ; intros __wit __varmap __ff ; change (Tauto.eval_f (Qeval_formula (@find Q 0%Q __varmap)) __ff) ; 
  apply (QTautoChecker_sound __ff __wit); vm_compute ; reflexivity.

Ltac romicron :=  romicronp ; intros __wit __varmap __ff ; change (Tauto.eval_f (Reval_formula (@find R 0%R __varmap)) __ff) ; 
  apply (RTautoChecker_sound __ff __wit); vm_compute ; reflexivity.

Ltac rmicromega :=  rmicromegap ; intros __wit __varmap __ff ; change (Tauto.eval_f (Reval_formula (@find R 0%R __varmap)) __ff) ; 
  apply (RTautoChecker_sound __ff __wit); vm_compute ; reflexivity. 


Ltac zomicron :=  zomicronp ; intros __wit __varmap __ff ; change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
  apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity.

Ltac sos := sosp ; intros __wit __varmap __ff ; change (Tauto.eval_f (Zeval_formula (@find Z Z0 __varmap)) __ff) ; 
  apply (ZTautoChecker_sound __ff __wit); vm_compute ; reflexivity.



