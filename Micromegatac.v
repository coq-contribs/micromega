(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Fr�d�ric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Export Micromega.
Require Export preMicromegatac.
Require Import Zpol.
Require Import QArith.
 Export Polynomial.
Require Export Ring_normalize.

Ltac zomicron   := zomicronw ; vm_compute ; reflexivity.
    
Ltac omicmac := repeat psimpl_arith ; (omicron ||  (zrelax ; omicron) || zomicron || (zrelax ; zomicron)).




