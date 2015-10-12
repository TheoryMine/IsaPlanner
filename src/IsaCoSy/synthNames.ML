(* How names of various things are represented in IsaCoSy *)

structure SynthNames = struct 

  (* Names for constants: We store ConstInfo in tables and sets of these names *)
  structure ConstantName : SSTR_NAME = SStrName;
  
  (* Names of positions where arguments can occur. (integers) *)
  structure ArgName : INT_NAME = IntName;
  
  (* Names of constraints *)             
  structure ConstraintName : SSTR_INT_NAME = SStrIntName;
   
  (* Names of holes (ie. meta-variables) in a synthesis attempt *)
  structure HoleName : SSTR_INT_NAME = SStrIntName;

end;
