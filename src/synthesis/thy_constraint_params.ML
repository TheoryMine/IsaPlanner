(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      thy_synth_params.ML
    Author:     Moa Johansson, University of Edinburgh
                moa.johansson@ed.ac.uk                
           and  Lucas Dixon, University of Edinburgh
                               
*)
(* -------------------------------------------------------------------------*)
(*  synthesis parameterisation from a theory. (terms for constraints, and constants) *)
(* -------------------------------------------------------------------------*)

structure ThyConstraintParams  = 
struct
local open ConstraintParams; in (* Constant and constraint Information *)

  (* -------------------------------------------------------- *)
  (* Get constants of a theory from inductivly defined function
     and from datatype constructors.                          *)
  (* -------------------------------------------------------- *)
  
  (* IMPROVE: seems like a hacky way to get the simp theorems, is there a better way? *)
  fun termrws_of_const_simps ctxt n = 
      map termrw_of_thm
          ((Proof_Context.get_thms ctxt (n^".simps")) handle ERROR s => []);
  
  (* Theory.context -> (String.string * Term.typ) list  *)      
  (* Get the constants of a given context *)
  fun consts_of_ctxt ctxt = 
      let
        val thy = Proof_Context.theory_of ctxt
        val consts = Sign.consts_of thy
        val constlist = (#constants (Consts.dest consts))
        val thynm = Context.theory_name thy (* Name_Space.path_of (Sign.naming_of thy) *)
      in
        (* Does not work for constants with names that are inherited from elsewhere. *)
        constlist 
          |> (map_filter (fn (constnm, (ty,_)) => 
                           if (String.isPrefix thynm constnm) then SOME (constnm, ty)
                           else NONE))
      end;
  
  (* Get the user defined datatypes of a theory *)
  (* Context.theory -> (String.string * DatatypeAux.datatype_info) list *)
  (* IMPROVE: looks like a hacky way to select datatypes in a theory, 
     no principled way to do this? *)
  (* FIXME: can datatypes be declared in a ctxt? do we need to treat ctxt properly? *)
  fun datatypes_of_ctxt ctxt = 
      let
        val thy = Proof_Context.theory_of ctxt
        val datatype_infotab = Symtab.dest (BNF_LFP_Compat.get_all thy [])
        val thynm = Context.theory_name thy(*NameSpace.path_of (Sign.naming_of thy)*)
      in
        filter (fn (datatypnm,_) => String.isPrefix thynm datatypnm) 
               datatype_infotab
      end;  
  
  (* for working with Datatypes *)
  (* get datatype info from theory *)
  exception not_a_datatype_exp of string;
  fun get_dinfo_in_thy thy datatype_name = 
      (case (Symtab.lookup (BNF_LFP_Compat.get_all thy []) datatype_name) 
       of NONE => raise not_a_datatype_exp datatype_name
        | SOME dinfo => dinfo);
  fun get_dinfo_in_ctxt ctxt datatype_name = 
      get_dinfo_in_thy (Proof_Context.theory_of ctxt) datatype_name;

  (* get the rewrites from a datatype (injectivity and distinctness) *)
  local 
    val hol_sym_thm = @{thm "HOL.sym"};
    val hol_iffd1_thm = @{thm "HOL.iffD1"};
    val hol_eq_False_thm = @{thm "HOL.eq_False"};
    val hol_eq_False_thm_sym = Seq.hd (rtac hol_eq_False_thm 1 hol_sym_thm);
  in
    fun termrws_of_datatype' dinfo = 
        let (* Change a distinctness theorem from eg. "Suc ?m ~= 0" to 
               "(Suc ?m3 = 0) = False" 
               This need some pre-processing, as comes like 0 ~= suc ?N, 
               our program would expect (0 = suc ?N) = false *)
          fun modify_distinct dist_thm = dist_thm RS (hol_eq_False_thm_sym RS hol_iffd1_thm);
        in map termrw_of_thm 
               ((#inject dinfo) (* e.g. (Suc x = Suc y) = (x = y) *)
                @ map modify_distinct (#distinct dinfo)) (* e.g. (0 = suc ?N) = false  *)
        end;
  end;
  (* get directly from theory *)
  fun termrws_of_datatype ctxt nm = termrws_of_datatype' (get_dinfo_in_ctxt ctxt nm);

  (* *)
  fun varify_typ ty = 
    Trm.map_typ_tfrees 
      (fn ((nm,sort), typ) => Trm.mk_tvar(Trm.var_of_free_name nm, sort)) ty

  (* Get the constructor names paired with its type from the datatype info,
     along with injectivity and distinctness theorems. *)
  fun consts_of_datatype' dinfo =
      let (* descr is a list for some reason, seems to only have one thing in it
          for most (all?) of my datatypes; maybe for mutual recurisve datatypes? *)
        val descr = (#descr dinfo);
        
      in (* make list of all constructor symbols and their type *)
        (maps (fn (_,(nm,typargs, constructors)) => 
                let 
                  val my_typargs =  
                      map (varify_typ o Old_Datatype_Aux.typ_of_dtyp descr) typargs
                  val resulttyp = Type(nm, my_typargs)
                in map (fn (constr_nm, dtyps) => 
                              let 
                                val argtyps = map (varify_typ o 
                                                   Old_Datatype_Aux.typ_of_dtyp descr) dtyps
                              in (constr_nm, argtyps ---> resulttyp) end)    
                          constructors
                end)
            descr)
      end;
  fun consts_of_datatype ctxt nm = consts_of_datatype' (get_dinfo_in_ctxt ctxt nm)

  (* Get the constructor names paired with its type from the datatype info,
     along with injectivity and distinctness theorems. *)
  fun get_datatype_consts_and_termrws ctxt nm = 
      let val dinfo = get_dinfo_in_ctxt ctxt nm
      in (consts_of_datatype' dinfo, termrws_of_datatype' dinfo) end;

  (* add a datatype, given its name: add all its constructors and it's special equations *)
  fun add_datatype ctxt dn = 
      let val (consts,rws) = get_datatype_consts_and_termrws ctxt dn
      in add_termrws ctxt rws o add_consts consts end;
  val add_datatypes = fold o add_datatype; 

  fun add_datatype' ctxt (Type(dn,_)) = add_datatype ctxt dn
    | add_datatype' ctxt _ = raise ERROR "add_datatype': not a Type type";  
  val add_datatypes' = fold o add_datatype'; 

  (* Name and type of equality, plus library theorems to generate
         basic constraints from *)
  val consts_for_eq = [Term.dest_Const (Thm.term_of @{cpat "HOL.eq :: ?'a => ?'a => bool"})];
  val termrws_for_eq = map termrw_of_thm
      [@{thm "IsaPHOLUtils.IsaP_reflexive"}, @{thm "IsaPHOLUtils.IsaP_eq_commute"}]

  (* too add equality to a ConstraintParams *)
  fun add_eq ctxt = add_termrws ctxt termrws_for_eq o add_cconsts consts_for_eq;

  (* *)
  fun all_consts_of_ctxt ctxt = 
      let val consts = consts_of_ctxt ctxt;
          val datatype_nms = map fst (datatypes_of_ctxt ctxt)
      in consts @ (maps (consts_of_datatype ctxt) datatype_nms) end;
  
  (* Dummy constant information without constraints *)
  fun just_consts_of_ctxt ctxt = 
      empty |> add_consts (all_consts_of_ctxt ctxt);

end;
end;
