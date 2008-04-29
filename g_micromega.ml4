(** Header **)open Quote
open Ring
open Utils


TACTIC EXTEND Micromega
[ "micromegap"  constr_list(i) ] -> [ Coq_micromega.micromega
				      (try 
					(CoqToCaml.z (Coq_micromega.M.parse_z (List.hd i)))
				       with _ -> -1)   ]
 END

 TACTIC EXTEND Sos
 [ "sosp" ] -> [ Coq_micromega.sos]
  END


  TACTIC EXTEND Omicron
  [ "omicronp"  ] -> [ Coq_micromega.omicron]
   END

  TACTIC EXTEND QOmicron
  [ "qomicronp"  ] -> [ Coq_micromega.qomicron]
   END


   TACTIC EXTEND ZOmicron
   [ "zomicronp"  ] -> [ Coq_micromega.zomicron]
    END

   TACTIC EXTEND ROmicron
   [ "romicronp"  ] -> [ Coq_micromega.romicron]
    END

   TACTIC EXTEND RMicromega
   [ "rmicromegap" constr_list(i) ] -> [ Coq_micromega.rmicromega
 					 (try 
					(CoqToCaml.z (Coq_micromega.M.parse_z (List.hd i)))
				       with _ -> -1)]
    END

