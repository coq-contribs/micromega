Require Import ZMicromega.
Require Import QMicromega.
Require Import VarMap.
Require Import RingMicromega.
Require Import NArith.

Extraction "micromega.ml"  List.map simpl_cone map_cone indexes  n_of_Z Nnat.N_of_nat ZTautoChecker QTautoChecker find.