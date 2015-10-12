(* *)

signature CONSTRAINT_PARAMS = 
sig
  type T (* type of parameterisation for synthesis *)

  (* *)
  val empty : Proof.context -> T

  exception not_such_const_exp of string; 

  (* stuff stored in param info *)
  val get_termrws : T -> (Term.term * Term.term) list
  val get_commute_trms : T -> (string * Term.term) list
  val get_consts : T -> Term.typ Symtab.table (* consts for synthesis *)
  val get_cconsts : T -> Term.typ Symtab.table (* all consts; used by constraints *)

  (* add function symbols that can be used to do synthesis *)
  val add_const : string * Term.typ -> T -> T
  val add_consts : (string * Term.typ) list -> T -> T
  val add_const_of_string_name : Proof.context -> string -> T -> T
  val add_consts_of_string_names : Proof.context -> string list -> T -> T

  (* add function symbols only for constraints *)
  val add_cconst : string * Term.typ -> T -> T
  val add_cconsts : (string * Term.typ) list -> T -> T
  val add_cconst_of_string_name : Proof.context -> string -> T -> T
  val add_cconsts_of_string_names : Proof.context -> string list -> T -> T

  (* *)
  val add_const_term_as_cconst : Proof.context -> Term.term -> T -> T
  val add_cconsts_in_term : Proof.context -> Term.term -> T -> T

  (* making equality term pairs. *)
  val termrw_of_term : Term.term -> (Term.term * Term.term) option
  val termrw_of_thm : Thm.thm -> (Term.term * Term.term) option

  (* internal: adds term pair as rw constraint only, 
     will probably raise exception if constants are missing *)
  val add_termrw' : Proof.context -> Term.term * Term.term -> T -> T

  (* add a pair of terms, including all their constants *)
  val add_termrw : Proof.context -> Term.term * Term.term -> T -> T
  val add_termrws : Proof.context -> (Term.term * Term.term) list -> T -> T

  (* THINK: maybe parameterise these info functor? On Terms? *)
  (* raises exception if term if badly formed, if not an equality, adds as "thm => True" *)
  val add_term : Proof.context -> Term.term -> T -> T 
  val add_terms : Proof.context -> Term.term list -> T -> T 
  
  (* Add terms that needn't be equations to constr_trms, to gen constraints forbidding
     instances of the whole term. *)       
  val add_arb_term : Proof.context -> Term.term -> T -> T
  val add_arb_terms : Proof.context -> Term.term list -> T -> T

  (* Add a given commutativity term *)                                                           
  val add_commute_terms : (string * Term.term) list -> T -> T

  (* Check if the function is associative and commutative, if so also commute defs.*)
  val add_ac_properties_of_const : Proof.context -> (string * Term.typ) -> 
                                   Thm.thm list -> T -> (Proof.context * T)
 
  (* if not an equality, adds as "thm => True" *)
  val add_thm : Proof.context -> Thm.thm -> T -> T
  val add_thms : Proof.context -> Thm.thm list -> T -> T

  (* Build constraints that forbids nesting of the same function over a given limit *)
  val add_nesting_constrs : Proof.context -> int option -> T -> T

  (* Add HOL equality to the set of constants *)
  val add_eq : Proof.context -> T -> T                                                            
 
  (* Adding datatype constructors and constraints on these *)
  val add_datatype : Proof.context -> Term.typ -> T -> T
  val add_datatypes  : Proof.context -> Term.typ list -> T -> T
 
  (* pretty printing *)
  val pretty : Proof.context -> T -> Pretty.T
  val print : Proof.context -> T -> unit

end;


structure ConstraintParams = 
struct
  
  (* Internal parameter representation *)
  datatype T = 
    Params of 
    { (* term equations from which to make more constraints *)
      termrws : (Term.term * Term.term) list,
      (* other terms we want to generate constraints from (non equational) *)
      constr_trms : Term.term list,
      (* Commutativity terms *)
      commute_trms : (string * Term.term) list,
      (* symbols we know about/can use in synthesis *)
      consts : Term.typ Symtab.table,
      (* constraint only consts, superset of consts *)
      cconsts : Term.typ Symtab.table,
      (* A function for sorting the constants, according to desired LPO precedence *)
      sort_lpo_precf : (string * Term.typ) list -> (string * Term.typ) list
    };

(* Functions for ordering constants, to be used by LPO *)
fun arg_order ((_,t1), (_,t2)) = 
            let val (argtyps1,_) = Term.strip_type t1
                val (argtyps2,_) = Term.strip_type t2
            in int_ord (List.length argtyps1, List.length argtyps2) end
          | arg_order _ = raise ERROR "Trying to compare non-Consts.";

(* Very simple ordering of constants. Simply order constants according 
   to number of arguments, in a list, with all datatypes assumed smaller than 
   all function defs. *)
  fun arg_const_order ctxt synth_consts = 
      let 
        val (dtyp_consts, fun_consts) = 
            List.partition (Refute.is_IDT_constructor (Proof_Context.theory_of ctxt))
                  synth_consts   
      in 
        (Library.sort arg_order dtyp_consts) @ 
        (Library.sort arg_order fun_consts)
      end;

 (* This function returns a list sorted by LPO precedence, with datatype
  constructors are assumed smaller than function symbols. *)
  fun sort_def_order ctxt consts (*constants as (string * typ) *) =
      let 
       val (datatype_consts, funconsts) = 
            List.partition (Refute.is_IDT_constructor (Proof_Context.theory_of ctxt)) consts;
       val sorted_dtyps = Library.sort arg_order datatype_consts;
        (* Get the rhs of equations defining each function of interest *)
        val fun_defs = map (fn (cnm, ty) => 
                    let 
                      val def_rules = 
                          List.foldl (fn ((spec,(_,rules)), rs) =>
                                         case spec of Spec_Rules.Equational => (rules@rs)
                                                    | _ => rs)
                           [] (Spec_Rules.retrieve ctxt (Const(cnm, ty)))
                      val rule_rhsides = 
                         map (fn def_rule => def_rule |> Thm.concl_of
                                                      |> Zipper.mktop
                                                      |> Subst.move_to_rhs_of_eq
                                                      |> Zipper.trm) def_rules
                    in ((cnm,ty), rule_rhsides) end)
                funconsts
        fun fundef_order (((f1,ty1), rhss1), ((f2,ty2), rhss2)) =
            if 
              (* Does f2 occur in def of f1 *)
              exists (fn rhs1 => Term.exists_Const 
                                   (fn (cnm,ty) => 
                                       Trm.eq (Const(cnm,ty), Const(f2,ty2))) rhs1) 
                     rhss1
             then 
              (* Does f1 also occur in def of f2 *)
              if exists (fn rhs2 =>
                            Term.exists_Const 
                              (fn (cnm,ty) => 
                                  Trm.eq (Const(cnm,ty), Const(f1,ty1))) rhs2) 
                        rhss2
              then EQUAL (* Functions defined by mutual recursion.*)
              else GREATER (* f1 is greater than f2, as f1 is defined in terms of f2 *)
            else 
              (* Is f2 defined in terms of f1 *)
              if exists (fn rhs2 =>
                            Term.exists_Const 
                              (fn (cnm,ty) =>Trm.eq (Const(cnm,ty), Const(f1,ty1))) rhs2) 
                        rhss2
              then LESS (* f1 is less than f2, as f2 is def in terms of f1 *)
              else EQUAL; (* neither defined in terms of the other *) 
      in
        sorted_dtyps @ (map fst (Library.sort fundef_order fun_defs))
      end;

  (* Default order-function is based on which funs are defined in terms of each other,
     with datatype consts smaller than fun. consts.*)    
  fun empty ctxt = Params { termrws = [], constr_trms = [], commute_trms = [],
                            consts = Symtab.empty, cconsts = Symtab.empty,
                            sort_lpo_precf = sort_def_order ctxt};

  (* boilerplate stuff *)
  fun get_termrws (Params rep) = #termrws rep;
  fun get_constr_trms (Params rep) = #constr_trms rep;
  fun get_commute_trms (Params rep) = #commute_trms rep;
  fun get_consts (Params rep) = #consts rep;
  fun get_cconsts (Params rep) = #cconsts rep;
  fun get_sort_lpo_precf (Params rep) = #sort_lpo_precf rep;
  fun update_termrws f (Params rep) = 
      Params { termrws = f(#termrws rep), constr_trms = #constr_trms rep, 
               commute_trms = #commute_trms rep, consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_constr_trms f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = f (#constr_trms rep), 
               commute_trms = #commute_trms rep, consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_commute_trms f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep, 
               commute_trms = f (#commute_trms rep), consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_consts f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep, 
               commute_trms = #commute_trms rep, consts = f(#consts rep), cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_cconsts f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep,
               commute_trms = #commute_trms rep, consts = #consts rep, cconsts = f(#cconsts rep),
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_sort_lpo_precf f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep,
               commute_trms = #commute_trms rep, consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = f(#sort_lpo_precf rep)};
  val set_termrws = update_termrws o K;
  val set_constr_trms = update_constr_trms o K;
  val set_commute_trms = update_commute_trms o K;
  val set_consts = update_consts o K;
  val set_cconsts = update_cconsts o K;
  val set_sort_lpo_precf = update_sort_lpo_precf o K;
  
  (* pretty printing *)
  fun pretty_termrw ctxt (t1,t2) = 
      Pretty.block [Trm.pretty ctxt t1, Pretty.str " => ", Trm.pretty ctxt t2];

  fun pretty ctxt p = 
      Pretty.block [Pretty.str "SynthParams {", 
        Pretty.indent 2 (Pretty.chunks
         [Pretty.block [Pretty.str "termrws: ", Pretty.list "{" "}"
            (map (pretty_termrw ctxt) (get_termrws p))],
          Pretty.block [Pretty.str "constr_trms: ", Pretty.list "{" "}"
            (map (Trm.pretty ctxt) (get_constr_trms p))],
          Pretty.block [Pretty.str "commute_trms: ", Pretty.list "{" "}"
            (map ((Trm.pretty ctxt) o snd) (get_commute_trms p))],
          Pretty.block [Pretty.str "consts: ", Pretty.list "{" "}"
            (map (fn (s,ty) => Trm.pretty ctxt (Const(s,ty))) (Symtab.dest (get_consts p)))],
          Pretty.block [Pretty.str "cconsts: ", Pretty.list "{" "}"
            (map (fn (s,ty) => Trm.pretty ctxt (Const(s,ty))) (Symtab.dest (get_cconsts p)))]
         ]), 
        Pretty.str "}"];
  val print = Pretty.writeln oo pretty;

  (* additing constants that can be used during synthesis *)
  val add_cconst = update_cconsts o Symtab.update;
  val add_cconsts = fold add_cconst;

  exception not_such_const_exp of string; 
  fun add_cconst_of_string_name ctxt s p = 
      (case Symtab.lookup (get_cconsts p) s of NONE => 
         ((add_cconst (s,Sign.the_const_type (Proof_Context.theory_of ctxt) s) p)
          handle Term.TYPE _ => raise not_such_const_exp s)
       | SOME _ => p);
  val add_cconsts_of_string_names = fold o add_cconst_of_string_name;

  (* *)
  fun add_const_term_as_cconst ctxt (Const (s,ty)) p = 
      add_cconst_of_string_name ctxt s p
    | add_const_term_as_cconst _ _ _ = raise ERROR "not a 'Const(...)' term ";
      
  fun add_cconsts_in_term ctxt t =
      fold (add_cconst_of_string_name ctxt) (Trm.constnames_of t);

  (* adding rewrite rule we might want to make constraints from *)
  fun add_termrw' ctxt (t1,t2) p = 
      p |> update_termrws (curry List.:: (t1,t2));

  (* adding rewrite rule we might want to make constraints from *)
 fun add_termrw ctxt (t1,t2) p = 
      p |> add_cconsts_in_term ctxt t1
        |> add_termrw' ctxt (t1,t2);
  val add_termrws = fold o add_termrw;

  (* Add an arbitrary (non-rw rule) term that we don't want to make instances of *)
  fun add_arb_term ctxt t p = p |> add_cconsts_in_term ctxt t
                                |> update_constr_trms (curry List.:: t)   
  val add_arb_terms  = fold o add_arb_term;

  (* Make pair of terms for lhs and rhs of an equation. NONE if t isn't an equation *)
  fun termrw_of_term t = 
      let 
        val z = Zipper.mktop t
        val lhs_t = (Subst.move_to_lhs_of_eq z) |> Zipper.trm
        val rhs_t = (Subst.move_to_rhs_of_eq z) |> Zipper.trm
      in SOME (lhs_t,rhs_t)
      end handle Eq_LData_HOL.bad_term_exp _ => NONE;

  (* assumes don't care about conditions of theorem: if it's a conditional eq, it's treated simply
     as an equation.  *)
  fun termrw_of_thm thm = termrw_of_term (Thm.concl_of thm);

  (* add a term or theorem. If it's an equation, the lhs will become a constraint term
     if eq is a valid rw rule. For non-equations, add the whole thing as a constraint term.*)
  fun add_term ctxt t p = 
       case (termrw_of_term t) of 
            SOME (lhs,rhs) => add_termrw ctxt (lhs,rhs) p
          | NONE => add_arb_term ctxt t p;
  val add_terms = fold o add_term;
  fun add_thm ctxt thm p = 
      case (termrw_of_thm thm) of
          SOME (lhs,rhs) => add_termrw ctxt (lhs,rhs) p
        | NONE => add_arb_term ctxt (Thm.concl_of thm) p;
  val add_thms = fold o add_thm;

  fun add_commute_trm (const_nm, commute_trm) params =
       update_commute_trms (curry List.:: (const_nm,commute_trm)) params;
  fun add_commute_terms commutes params = fold add_commute_trm commutes params;

  fun add_commute_thm (const_nm, commute_thm) params = 
      add_commute_trm (const_nm, Thm.concl_of commute_thm) params;

(* Add both to params and output. *)
  fun add_ac_properties_of_const ctxt (const_nm,ty) def_thms p =
      let
        val (assoc_opt, commute_opt) = ConstraintParamSchemes.synth_ac_thrms 
                                         ctxt (const_nm,ty) def_thms

        fun opt_add_assoc ctxt params NONE = (ctxt, params)
          | opt_add_assoc ctxt params (SOME assoc_thm) = 
            (SynthOutput.add_thms [assoc_thm] ctxt,
             add_thm ctxt (snd assoc_thm) params);

        fun opt_add_commute ctxt params NONE = (ctxt,params)
          | opt_add_commute ctxt params (SOME (commute_thm, commuted_defs)) =
            (SynthOutput.add_thms (commute_thm::commuted_defs) ctxt,
             params |> add_commute_trm (const_nm, (Thm.concl_of o snd) commute_thm)
                    |> add_thms ctxt (map snd commuted_defs));

        val (ctxt2, params2) = opt_add_assoc ctxt p assoc_opt;
        val (ctxt3, params3) = opt_add_commute ctxt2 params2 commute_opt
      in
       (ctxt3, params3)
      end;

 (* Build constraint terms that prevents a function to nest more than a given number of times with
    itself *)
  fun add_nesting_constrs ctxt nesting_opt p = 
      case nesting_opt of 
        NONE => p 
      | SOME max_nesting => 
        let 
          fun mk_n_new_var_nms n name_set =
              fold_map (fn i =>fn varnms => 
                         StrIntName.NSet.add_new ("x",i) varnms)
                         (Library.upto (1,n)) name_set;

          fun nest_at_i (i, args) varnms 0 f = 
              let
                val (nw_vars,_) =  mk_n_new_var_nms (length args) varnms
              in Term.list_comb (f, Library.map2 (fn vnm=>fn(_,argty)=> Var(vnm,argty))
                                    nw_vars args) end
            | nest_at_i (i,args) varnms n f = 
              let
                val (vs,varnms') = mk_n_new_var_nms ((length args) -1) varnms
                val (nw_args,_) = fold_map (fn (arg_ind,argtyp) => fn vars => 
                                        if arg_ind = i 
                                        then (nest_at_i (i,args) varnms' (n-1) f, vars)
                                        else (Var(hd vars,argtyp), tl vars))
                                        args vs 
                in
                  Term.list_comb (f, nw_args)  
                end;

          fun build_constr_t (cnm,ty) = 
              let    
                val (argtyps, restyp) = Term.strip_type ty
                val indexed_args = map_index I argtyps
                val arginds_of_restyp = map_filter 
                    (fn (i,argtyp)=> if (argtyp=restyp) then SOME i else NONE) indexed_args
               in 
                 map (fn i => nest_at_i (i,indexed_args) (StrIntName.NSet.empty) max_nesting (Const(cnm,ty)))
                      arginds_of_restyp
               end;
        in
          add_arb_terms ctxt
                        (maps build_constr_t (Symtab.dest (get_consts p)))
                        p
        end; 

  (* adding consts which can be used for synthesis *)
  fun add_const c = update_consts (Symtab.update c) o (add_cconst c);
  val add_consts = fold add_const;
  (* *)
  fun add_const_of_string_name ctxt s p = 
      (case Symtab.lookup (get_cconsts p) s of NONE => 
         ((add_const (s,Sign.the_const_type (Proof_Context.theory_of ctxt) s) p)
          handle Term.TYPE _ => raise not_such_const_exp s)
       | SOME x => add_const (s,x) p);

  val add_consts_of_string_names = fold o add_const_of_string_name;



(* ------ Add common constants to the constraint params ------*)

 (* Name and type of equality, plus library theorems to generate basic constraints from *)
  val HOL_eq_const = [Term.dest_Const (Thm.term_of @{cpat "HOL.eq :: ?'a => ?'a => bool"})];
  val reflexiveTrue = @{lemma "(x = x) = True" by simp};
  val eq_commute = @{lemma "(x = y) = (y = x)" by auto};

  val termrws_for_eq = map_filter termrw_of_thm [reflexiveTrue];

  (* Add HOL equality to a ConstraintParam *)
  fun add_eq ctxt = add_termrws ctxt termrws_for_eq o add_cconsts HOL_eq_const o add_commute_thm ("HOL.eq",eq_commute);


(* ------ Adding datatypes: their constructors and constraints on these ------*)

  (* get the rewrites from a datatype (injectivity and distinctness) *)
  local 
    val hol_sym_thm = @{thm "HOL.sym"};
    val hol_iffd1_thm = @{thm "HOL.iffD1"};
    val hol_eq_False_thm = @{thm "HOL.eq_False"};
    val hol_eq_False_thm_sym = Seq.hd (rtac hol_eq_False_thm 1 hol_sym_thm);
  in
    fun termrws_of_datatype dinfo = 
        let (* Change a distinctness theorem from eg. "Suc ?m ~= 0" to 
               "(Suc ?m3 = 0) = False" 
               This need some pre-processing, as comes like 0 ~= suc ?N, 
               IsaCoSy would expect (0 = suc ?N) = false *)
          fun modify_distinct dist_thm = dist_thm RS (hol_eq_False_thm_sym RS hol_iffd1_thm);
        in map_filter termrw_of_thm 
               ((#inject dinfo) (* e.g. (Suc x = Suc y) = (x = y) *)
                @ map modify_distinct (#distinct dinfo)) (* e.g. (0 = suc ?N) = false  *)
        end;
  end;

 (* Get the constructor names paired with its type from the datatype info,
     along with injectivity and distinctness theorems. *)
  fun consts_of_datatype dinfo =
      let (* descr is a list for some reason, seems to only have one thing in it
          for most (all?) of my datatypes; maybe for mutual recurisve datatypes? *)
        val descr = (#descr dinfo);

        fun varify_typ ty = 
            Trm.map_typ_tfrees 
              (fn ((nm,sort), typ) => Trm.mk_tvar(Trm.var_of_free_name nm, sort)) ty
        
      in (* make list of all constructor symbols and their type *)
        (maps (fn (_,(nm,typargs, constructors)) => 
                let 
                  val my_typargs =  
                      map (varify_typ o Datatype_Aux.typ_of_dtyp descr) typargs
                  val resulttyp = Type(nm, my_typargs)
                in map (fn (constr_nm, dtyps) => 
                              let 
                                val argtyps = map (varify_typ o 
                                                   Datatype_Aux.typ_of_dtyp descr) dtyps
                              in (constr_nm, argtyps ---> resulttyp) end)    
                          constructors
                end)
            descr)
      end;

 exception not_a_datatype_exp of string;
  fun get_dinfo_in_thy thy datatype_name = 
      (case (Datatype_Data.get_info thy datatype_name) 
       of NONE => raise not_a_datatype_exp datatype_name
        | SOME dinfo => dinfo);
  fun get_dinfo_in_ctxt ctxt datatype_name = 
      get_dinfo_in_thy (Proof_Context.theory_of ctxt) datatype_name;


(* Get the constructor names paired with its type from the datatype info,
     along with injectivity and distinctness theorems. *)
  fun get_datatype_consts_and_termrws ctxt nm = 
      let val dinfo = get_dinfo_in_ctxt ctxt nm
      in (consts_of_datatype dinfo, termrws_of_datatype dinfo) end;

 (* add a datatype, given its name: add all its constructors and it's special equations *)
  fun add_datatype_aux ctxt dn = 
      let val (consts,rws) = get_datatype_consts_and_termrws ctxt dn
      in add_termrws ctxt rws o add_consts consts end;

fun add_datatype ctxt (Type(dn,_)) = add_datatype_aux ctxt dn
    | add_datatype ctxt _ = raise ERROR "add_datatype': not a Type type";  

val add_datatypes = fold o add_datatype; 

end;

local structure CheckConstraintParams : CONSTRAINT_PARAMS = ConstraintParams; in val _ = (); end;
