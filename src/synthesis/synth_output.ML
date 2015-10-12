(* synthesis/synth_output.ML                                *)
(* Author: Moa Johansson                                    *)

(* Structure for recording what IsaCoSy should output.      *)
(* Records theorems and conjectures found (so far) during   *)
(* synthesis.                                               *)

signature SYNTH_OUTPUT =
sig
  type T
  structure Ctxt : PROOF_DATA where type T = T
  val empty : T
  val get_conjs : T -> term list
  val get_thm_net : T -> (string (* proof description *)
                       * Thm.thm) (* proved theorem *)
                       Net.net
  val get_thms : T -> (string * Thm.thm) list
  val get_all : T -> term list (* DBG: Everything synthesised. *)
  (* Total number of synthesised terms considered *)
  val get_tot_synthterms : T -> int 
  (* Number of synthesise terms for a give size, specified by IntName *)                                  
  val get_tot_for_size : T -> IntName.name -> int
  val get_tot_synthterms_tab : T -> int IntNTab.T

  val add_sterms : Term.term list -> Proof.context -> Proof.context
  val add_conjs : Term.term list -> Proof.context -> Proof.context
  val add_thms : (string * Thm.thm) list -> Proof.context -> Proof.context
  val add_thms_no_subsumption : (string * Thm.thm) list -> Proof.context -> Proof.context

  (* Add to size given by 'IntName' *)
  val add_to_tot : IntName.name -> int -> Proof.context -> Proof.context

  val set_conjs : Term.term list -> Proof.context -> Proof.context
end;


structure DB_SynthOutput =
struct
  datatype T = SynthOutput of {
      conjs : Term.term list,
      thms : (string (* proof description *)
              * Thm.thm) (* proved theorem *)
               Net.net,
      tot_synthterms_tab : int IntNTab.T,
      all : Term.term list
  };
  val empty = SynthOutput{conjs = [], thms = Net.empty, 
                          tot_synthterms_tab = IntNTab.empty, all =[]};
  fun get_conjs (SynthOutput rep) = #conjs rep;
  fun get_thm_net (SynthOutput rep) = #thms rep;
  fun get_thms rep = Net.content (get_thm_net rep);
  fun get_all (SynthOutput rep) = #all rep;
  fun get_tot_synthterms_tab (SynthOutput rep) =  #tot_synthterms_tab rep;
  fun get_tot_synthterms rep = IntNTab.fold (fn (size, num_trms) => fn tot => tot + num_trms)  
                                            (get_tot_synthterms_tab rep) 0;
  fun get_tot_for_size rep size = IntNTab.get (get_tot_synthterms_tab rep) size;

  fun update_conjs f (SynthOutput rep) = 
      SynthOutput{conjs = f (#conjs rep), thms = #thms rep, 
                  tot_synthterms_tab = #tot_synthterms_tab rep, all= #all rep};
  fun update_sterms f (SynthOutput rep) = 
      SynthOutput{conjs =  (#conjs rep), thms = #thms rep, 
                  tot_synthterms_tab = #tot_synthterms_tab rep, all=f(#all rep)};     

  fun update_thms f (SynthOutput rep) = 
      SynthOutput{conjs = #conjs rep, thms = f (#thms rep), 
                 tot_synthterms_tab = #tot_synthterms_tab rep, all= #all rep};
  fun update_tot_synthterms f (SynthOutput rep) = 
      SynthOutput{conjs = #conjs rep, thms = #thms rep, tot_synthterms_tab = f (#tot_synthterms_tab rep), all= #all rep};
  structure Ctxt = Proof_Data(type T = T fun init thy = empty)
  
  fun add_conjs nw_conjs ctxt =
      Ctxt.map (update_conjs (fn old_conjs => nw_conjs @ old_conjs)) ctxt;
  fun set_conjs conjs ctxt = 
      Ctxt.put (update_conjs (fn _ => conjs) (Ctxt.get ctxt)) ctxt;
  fun add_sterms nw_terms ctxt =
      Ctxt.map (update_sterms (fn old_terms => nw_terms @ old_terms)) ctxt;
  fun add_to_tot size num_synthterms ctxt = 
      Ctxt.put (update_tot_synthterms (IntNTab.ins (size, num_synthterms)) 
                                      (Ctxt.get ctxt)) ctxt;                                    
 

fun add_thm_no_sub ctxt (prf,thm) net =
    let
        val tin = Thm.concl_of thm
        fun varify_typ ty = 
            Trm.map_typ_tfrees 
              (fn ((nm,sort), typ) => Trm.mk_tvar(Trm.var_of_free_name nm, sort)) ty         
        fun varify_thm thm = thm |> Thm.concl_of
                                 |> Envir.beta_eta_contract 
                                 |> Trm.change_frees_to_fresh_vars
                                 |> Trm.map_trm_types varify_typ     
        (* Variant of input theorem-term with variables *)
        val t_varified = varify_thm thm
        fun freevars_alpha_conv ((_,thm1),(_,thm2)) = 
            uncurry Trm.trm_name_eq (varify_thm thm1, varify_thm thm2);
    in
      Net.insert_term freevars_alpha_conv (t_varified, (prf,thm)) net
    end;

fun add_thms_to_net_no_sub ctxt net thms = fold (add_thm_no_sub ctxt) thms net
fun add_thms_no_subsumption nw_thms ctxt = 
      Ctxt.map (update_thms (fn old_thm_net => add_thms_to_net_no_sub ctxt old_thm_net nw_thms)) ctxt;

(*If the thm is not subsumed, add to the net. Also remove anything subsumed by
  the new theorem from the net. If the theorem is subsumed, its not added
  to the SynthOutput. *)
  fun add_thm ctxt (prf,thm) net =  
      let
        val tin = Thm.concl_of thm
        fun varify_typ ty = 
            Trm.map_typ_tfrees 
              (fn ((nm,sort), typ) => Trm.mk_tvar(Trm.var_of_free_name nm, sort)) ty         
        fun varify_thm thm = thm |> Thm.concl_of
                                 |> Envir.beta_eta_contract 
                                 |> Trm.change_frees_to_fresh_vars
                                 |> Trm.map_trm_types varify_typ     
        (* Variant of input theorem-term with variables *)
        val t_varified = varify_thm thm
        (* Fix the vars, when we match against net-terms.*)
        val t_fixed = Trm.change_vars_to_fresh_frees tin;
        (* Potential terms to subsume or be sumbsumed by *)
        val net_thms = Net.unify_term net tin
        fun freevars_alpha_conv ((_,thm1),(_,thm2)) = 
            uncurry Trm.trm_name_eq (varify_thm thm1, varify_thm thm2);
        (* Update the net, check if new term is subsumed, or does subsume
           something in the net*)
        fun update_subsumption_net (p,net_thm) (subsumed, net) =
            let 
              val net_t = varify_thm net_thm
            in
              if subsumed then 
                (subsumed, net) (* It's already subsumed by something in net.*)
              else  
                case (MyUnify.match [(net_t, t_fixed)]) (InstEnv.init ctxt) of
                  SOME _ => (true, net)
                | NONE => (* Need to check if tin subsumes the net_term. *)
                  (case (MyUnify.match [(t_varified, Trm.change_vars_to_fresh_frees net_t)]
                                       (InstEnv.init ctxt)) of
                     SOME _ => (false, Net.delete_term freevars_alpha_conv (net_t,(p,net_thm)) net)
                   | NONE => (false, net)
                  )
            end; 

        val (subsumed, net2) = fold update_subsumption_net net_thms (false, net);     
      in
        if (not subsumed) 
        then Net.insert_term freevars_alpha_conv (t_varified, (prf,thm)) net2
        else net2
      end;

  fun add_thms_to_net ctxt net thms = fold (add_thm ctxt) thms net

  fun add_thms nw_thms ctxt = 
      Ctxt.map (update_thms (fn old_thm_net => add_thms_to_net ctxt old_thm_net nw_thms)) ctxt;

 

end; (* *)

structure SynthOutput : SYNTH_OUTPUT = DB_SynthOutput
