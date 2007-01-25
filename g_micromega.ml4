(********************************************************************)
(*                                                                  *)
(* Micromega:A reflexive tactics  using the Positivstellensatz      *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
open Quote
open Ring
open Utils


TACTIC EXTEND Micromega1
  [ "micromegaw"  integer(i) ] -> [ Coq_micromega.micromega  i]
END

TACTIC EXTEND Micromega2
  [ "micromegad"  constr(i) ] -> [ Coq_micromega.micromega
				     (try 
				       (CoqToCaml.z (Coq_micromega.M.parse_z i))
				      with _ -> -1)   ]
END

TACTIC EXTEND Micromega3
  [ "omicronw"  ] -> [ Coq_micromega.omicron]
END

TACTIC EXTEND Micromega4
  [ "sosw"   ] -> [ Coq_micromega.sos ]
END

TACTIC EXTEND Micromega5
  [ "zomicronw"   ] -> [ Coq_micromega.zomicron ]
END


