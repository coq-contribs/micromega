(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
open Quote
open Ring

TACTIC EXTEND Micromega1
   [ "MicromegaH" constr_list(l) ] -> [ Coq_micromega.micromega l ]
END




