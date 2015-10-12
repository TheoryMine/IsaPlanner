(* *)

signature CONSTRAINT_PARAMS = 
sig
  type T (* type of parameterisation for synthesis *)

  (* *)
  val empty : T

  exception not_such_const_exp of string; 

  (* stuff stored in param info *)
  val get_termrws : T -> (Term.term * Term.term) list
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

  (* making quality term pairs, if not eq, then makes equality "t = True" *)
  val termrw_of_term : Term.term -> Term.term * Term.term
  val termrw_of_thm : Thm.thm -> Term.term * Term.term

  (* internal: adds term pair as rw constraint only, 
     will probably raise exception if constants are missing *)
  val add_termrw' : Proof.context -> Term.term * Term.term -> T -> T

  (* add a pair of terms, including all their constants *)
  val add_termrw : Proof.context -> Term.term * Term.term -> T -> T
  val add_termrws : Proof.context -> (Term.term * Term.term) list -> T -> T

  (* THINK: maybe parameterise these info functor? *)
  (* raises exception if term if badly formed, if not an equality, adds as "thm => True" *)
  val add_term : Proof.context -> Term.term -> T -> T 
  val add_terms : Proof.context -> Term.term list -> T -> T 
  
  (* Add terms that needn't be equations to constr_trms, to gen constraints forbidding
     instances of the whole term. *)       
  val add_arb_term : Proof.context -> Term.term -> T -> T
  val add_arb_terms : Proof.context -> Term.term list -> T -> T

  val add_ac_properties_of_const : Proof.context -> (string * Term.typ) -> 
                                   Thm.thm list -> T -> (Proof.context * T)
  val add_ac_properties_of_consts : Proof.context -> ((string * Term.typ) * Thm.thm list) list -> 
                                                      T -> (Proof.context * T)
 
  (* if not an equality, adds as "thm => True" *)
  val add_thm : Proof.context -> Thm.thm -> T -> T
  val add_thms : Proof.context -> Thm.thm list -> T -> T

  (* Build constraints that forbids nesting of the same (unary) function over a given limit *)
  val add_nesting_constrs : Proof.context -> int option -> T -> T

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
      (* symbols we know about/can use in synthesis *)
      consts : Term.typ Symtab.table,
      (* constraint only consts, superset of consts *)
      cconsts : Term.typ Symtab.table,
      (* LPO precedence for constants *)
      (* lpo_precf : (string * Term.typ) -> int *)
      (* A function for sorting the constants, according to desired LPO precedence *)
      sort_lpo_precf : (string * Term.typ) list -> (string * Term.typ) list
    };

(* Very simple default ordering of constants. Simply order constants according 
   to number of arguments, in a list *)
  fun arg_const_order synth_consts = 
      let 
        fun arg_order ((_,t1), (_,t2)) = 
            let val (argtyps1,_) = Term.strip_type t1
                val (argtyps2,_) = Term.strip_type t2
            in int_ord (List.length argtyps1, List.length argtyps2) end
          | arg_order _ = raise ERROR "Trying to compare non-Consts.";
      in 
        Library.sort arg_order synth_consts
      end;

      
  val empty = Params { termrws = [], constr_trms = [], 
                       consts = Symtab.empty, cconsts = Symtab.empty,
                       sort_lpo_precf =  arg_const_order};

  (* boilerplate stuff *)
  fun get_termrws (Params rep) = #termrws rep;
  fun get_constr_trms (Params rep) = #constr_trms rep;
  fun get_consts (Params rep) = #consts rep;
  fun get_cconsts (Params rep) = #cconsts rep;
  fun get_sort_lpo_precf (Params rep) = #sort_lpo_precf rep;
  fun update_termrws f (Params rep) = 
      Params { termrws = f(#termrws rep), constr_trms = #constr_trms rep, 
               consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_constr_trms f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = f (#constr_trms rep), 
               consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_consts f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep, 
               consts = f(#consts rep), cconsts = #cconsts rep,
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_cconsts f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep,
               consts = #consts rep, cconsts = f(#cconsts rep),
             sort_lpo_precf = #sort_lpo_precf rep};
  fun update_sort_lpo_precf f (Params rep) = 
      Params { termrws = #termrws rep, constr_trms = #constr_trms rep,
               consts = #consts rep, cconsts = #cconsts rep,
             sort_lpo_precf = f(#sort_lpo_precf rep)};
  val set_termrws = update_termrws o K;
  val set_constr_trms = update_constr_trms o K;
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
      let (* val thy = Proof_Context.theory_of ctxt;
            val ct1 = Thm.cterm_of thy t1;  Don't do these: we want to sometimes use fake constants
          val ct2 = Thm.cterm_of thy t2;  *** checks terms are well-formed *)
      in p |> update_termrws (curry List.:: (t1,t2)) end;

  (* adding rewrite rule we might want to make constraints from *)
  fun add_termrw ctxt (t1,t2) p = 
      p |> add_cconsts_in_term ctxt t1
        |> add_termrw' ctxt (t1,t2);
  val add_termrws = fold o add_termrw;

  (* Add an arbitrary term that we don't want to make instances of *)
  fun add_arb_term ctxt t p = p |> add_cconsts_in_term ctxt t
                                |> update_constr_trms (curry List.:: t)   
  val add_arb_terms  = fold o add_arb_term;

  (* Make pair of terms for lhs and rhs of an equation. If it's not an equation, the 
     conclusion it turned into the equation "t = True" *)
    (* FIXME : What if t isn't a boolean? We'll make a badly formed term *)
  fun termrw_of_term t = 
      let 
        val z = Zipper.mktop t
        val lhs_t = (Subst.move_to_lhs_of_eq z) |> Zipper.trm
        val rhs_t = (Subst.move_to_rhs_of_eq z) |> Zipper.trm
      in (lhs_t,rhs_t)
      end handle Eq_LData_HOL.bad_term_exp _ => (Res.try_dest_Trueprop t, 
                                                 Const ("HOL.True", Type ("HOL.bool", [])));

  (* assumes don't care about conditions of theorem: if it's a conditional eq, it's treated simply
     as an equation. If it's not an equation, the conclusion it turned into the equation 
     "concl = True" *)
  (* FIXME: treat as a one directional rewrite: conclusion => assumptions ? *)
  fun termrw_of_thm thm = termrw_of_term (Thm.concl_of thm);
  
  (* add a term or theorem (as an equation ?)*)
  fun add_term ctxt t p = add_termrw ctxt (termrw_of_term t) p;
  val add_terms = fold o add_term;
  fun add_thm ctxt thm p = add_termrw ctxt (termrw_of_thm thm) p;
  val add_thms = fold o add_thm;

(* Add both to params and output? *)
  fun add_ac_properties_of_const ctxt (const_nm,ty) def_thms p =
      let
        val ac_thrms = ConstraintParamSchemes.synth_ac_thrms 
                         ctxt (const_nm,ty) def_thms
        val nw_ctxt = 
            SynthOutput.add_thms (map (fn (prf,thm) => 
                                          ("AC-preprocessing: "^prf,thm)) 
                                      ac_thrms) ctxt
      in
        (nw_ctxt, add_thms nw_ctxt (map snd ac_thrms) p)
      end;

  fun add_ac_properties_of_consts ctxt consts p =
      List.foldl (fn (((const_nm,ty), def_thms), (context,params)) => 
                     add_ac_properties_of_const context (const_nm,ty) def_thms params) 
                (ctxt,p) consts;

 (* Currently only nesting limitations on unary and binary functions. *) 
  fun add_nesting_constrs ctxt nesting_opt p = 
      case nesting_opt of 
        NONE => p 
      | SOME max_nesting => 
        let 
          fun nest1 0 f t = t
            | nest1 n f t = nest1 (n-1) f (f$t);
 
          fun nest2_l (ienv,ty) 0 f t = t
            | nest2_l(ienv,ty) n f t = 
              let 
                val (v,ienv') = InstEnv.new_uninst_var (("x",1),ty) ienv
              in nest2_l (ienv',ty) (n-1) f (f$t$Var(v,ty)) end;

          fun nest2_r (ienv,ty) 0 f t = t
            | nest2_r (ienv,ty) n f t = 
              let 
                val (v,ienv') = InstEnv.new_uninst_var (("x",1),ty) ienv
              in nest2_r (ienv',ty) (n-1) f (f$Var(v,ty)$t) end;  

          fun build_constr_t (cnm,ty) = 
              let 
                val ienv = InstEnv.init ctxt
              in
              case (Term.strip_type ty) of 
                 (*Type of unary function that can nest itself *)
                ([ty1], ty2) =>  
                if ty1=ty2 then 
                   let 
                    val (init_var,ienv1) = InstEnv.new_uninst_var (("x",0),ty1) ienv
                   in
                     [nest1 (max_nesting+1) (Const(cnm,ty)) (Var(init_var,ty1))]
                   end
                else []
              (*Type of binary function that can nest itself *)  
              | ([argty1,argty2], res_typ) => 
                if argty1=argty2 andalso argty1=res_typ then
                  let 
                    val (init_var,ienv1) = InstEnv.new_uninst_var (("x",0),argty1) ienv
                  in
                  [nest2_l (ienv1,argty1) (max_nesting+1)
                           (Const(cnm,ty)) (Var(init_var,argty1)),
                   nest2_r (ienv1, argty1) (max_nesting+1)
                           (Const(cnm,ty)) (Var(init_var,argty1))]
                  end
                else []
              | _ => [] 
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



end;

local structure CheckConstraintParams : CONSTRAINT_PARAMS = ConstraintParams; in val _ = (); end;
