(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:
    The Reasoning state
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature RSTATE = 
sig 

  type T (* type of a reasoning state *)
  type rtechn = T -> T Seq.seq

(*   type rtechn

  val fn_of_rtechn : rtechn -> (T -> T Seq.seq)
  val name_of_rtechn : rtechn -> string
  val mk_rtechn : (string * (T -> T Seq.seq)) -> rtechn
*)
  (* consrtuctors - see pplan... *)
  val init : Proof.context -> T
  val init_from_thy : Context.theory -> T
  val init_from_pp : PPlan.T -> T

  val unfold : T -> T Seq.seq                
  val sol_setf : T -> T                  

  val set_rtechn : rtechn option -> T -> T
  val set_cinfo : CInfo.T -> T -> T
  val set_lcinfo : LCInfo.T -> T -> T
  val set_prev :  T option -> T -> T
  val set_pplan : PPlan.T -> T -> T
  val set_ctxt : Proof.context -> T -> T

  val set_curnames : PPlan.gname list (* result names: forwards proof *)
                      * PPlan.gname list (* goal names: backwards proof *)
                      -> T -> T 
  val set_goalnames : PPlan.gname list -> T -> T 
  val set_resultnames : PPlan.gname list -> T -> T 

  val add_curnames : PPlan.gname list * PPlan.gname list -> T -> T
  val add_goalnames : PPlan.gname list -> T -> T
  val add_resultnames : PPlan.gname list -> T -> T

  val get_rtechn : T -> rtechn option
  val get_cinfo : T -> CInfo.T
  val get_lcinfo : T -> LCInfo.T
  val get_prev : T -> T option
  val get_pplan : T -> PPlan.T
  val get_curnames : T -> PPlan.gname list * PPlan.gname list
  val get_goalnames : T -> PPlan.gname list
  val get_resultnames : T -> PPlan.gname list
  val get_ctxt : T -> Proof.context

  (* set a search stack operation *)
  val set_searchops : T MSearch.searchopT list -> T -> T
  val add_searchop : T MSearch.searchopT -> T -> T
  val get_searchops : T -> T MSearch.searchopT list
  val pop_searchop : T -> (T * T MSearch.searchopT) option
  val search : T MSearch.T -> T -> T Seq.seq
  val tracedsearch : ((T MSearch.T * T) option -> (T MSearch.T * T) option) 
                     -> T MSearch.T -> T -> T Seq.seq
  val delayed_search : T MSearch.T -> T -> T Seq.seq

  (* updating parts of the reasoning state *)
  val update_pplan : (PPlan.T -> PPlan.T) -> T -> T
  val update_lcinfo : (LCInfo.T -> LCInfo.T) -> T -> T
  val update_rtechn : (rtechn option -> rtechn option) -> T -> T
  val update_curnames : (PPlan.gname list * PPlan.gname list 
                         -> PPlan.gname list * PPlan.gname list )
                         -> T -> T
  val update_resultnames : (PPlan.gname list -> PPlan.gname list) -> T -> T
  val update_goalnames : (PPlan.gname list -> PPlan.gname list) -> T -> T
  val update_ctxt : (Proof.context -> Proof.context) -> T -> T
  val update_cinfo : (CInfo.T -> CInfo.T) -> T -> T

  (* Pass on local cinfo, by deafuat (push) to goalnames. *)
  (* val push_lcinfo : PPlan.gname -> T -> T *)
  val give_lcinfo : PPlan.gname -> PPlan.gname list -> T -> T

  (* Set dealyoptions for search *)
  val get_delayop : T -> (T, Term.term) MSearch.delayopT option
  val delay_rst :  Term.term -> T -> T
  val reset_delayopt : T -> T
  val resume_others : Term.term -> T -> T 
  val eval_delayopts : T -> (T * (T, Term.term) MSearch.delayopT) option
                          
  (* Unique ID's for Reasoning states - for internal use/debugging *)
  val get_id : T -> int (* unique id for each state, assuming use of unfold *)
  val new_id : T -> T (* force a new id *)

  val pretty : T -> Pretty.T
  val print : T -> unit

end; (* signature *)



structure DB_RState
(* : RSTATE *) 
= struct

  datatype T = 
    RState of { rtechn    : (T -> T Seq.seq) option, (* rtechn option *)
                linfo     : LCInfo.T,
                pplan     : PPlan.T,
                prev      : T option,
                id        : int,
                curnames  : PPlan.gname list * PPlan.gname list,
                searchop  : T MSearch.searchopT list,
                delayop   : ((T, Term.term) MSearch.delayopT) option}
  (* and rtechn = RTechn of (string * (T -> T Seq.seq));
  fun fn_of_rtechn (RTechn (s,f)) = f;
  fun name_of_rtechn (RTechn (s,f)) = s;
  val mk_rtechn = RTechn; *)

  type rtechn = T -> T Seq.seq;

  val global_id = Synchronized.var "IsaPlanner.global_id" 0;
  fun inc_g_id () = 
      Synchronized.change_result global_id (fn global_id => (global_id,global_id + 1)); 

  fun update_rtechn f (RState rep) = 
      RState{ rtechn = f (#rtechn rep), prev = #prev rep, linfo = #linfo rep, 
              pplan = #pplan rep, id= #id rep, curnames = #curnames rep, searchop = #searchop rep, 
              delayop = #delayop rep};
  fun update_prev f (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = f (#prev rep), linfo = #linfo rep, 
              pplan = #pplan rep, id= #id rep, curnames = #curnames rep, searchop = #searchop rep, delayop= #delayop rep};
  fun update_pplan f (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = #prev rep, linfo = #linfo rep, 
              pplan = f (#pplan rep), id= #id rep, 
              curnames = #curnames rep, searchop = #searchop rep, delayop= #delayop rep};

  val update_ctxt = update_pplan o PPlan.update_context;
  val update_cinfo = update_ctxt o CInfo.Ctxt.map;

  fun update_lcinfo f (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = #prev rep, linfo = f (#linfo rep), 
              pplan = #pplan rep, id= #id rep, curnames = #curnames rep, searchop = #searchop rep, 
              delayop= #delayop rep};
  fun update_searchop f (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = #prev rep, linfo = #linfo rep, 
              pplan = #pplan rep, id= #id rep, 
              curnames = #curnames rep, searchop = f (#searchop rep), delayop= #delayop rep};
  fun new_id (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = #prev rep, linfo = #linfo rep, 
              pplan = #pplan rep, id=inc_g_id(), curnames = #curnames rep, 
              searchop = #searchop rep, delayop= #delayop rep};
  fun update_curnames f (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = #prev rep, linfo = #linfo rep, 
              pplan = #pplan rep, id= #id rep, curnames = f (#curnames rep), 
              searchop = #searchop rep, delayop= #delayop rep};
  fun update_delayop f (RState rep) = 
      RState{ rtechn = #rtechn rep, prev = #prev rep, linfo = #linfo rep, 
              pplan = #pplan rep, id= #id rep, curnames = #curnames rep, 
              searchop = #searchop rep, delayop= f (#delayop rep)};

  fun update_goalnames f = update_curnames (fn (rs,gs) => (rs,f gs));    
  fun update_resultnames f = update_curnames (fn (rs,gs) => (f rs,gs));    

  val set_rtechn = update_rtechn o K;
  val set_lcinfo = update_lcinfo o K;
  val set_prev = update_prev o K;
  val set_pplan = update_pplan o K;
  val set_searchops = update_searchop o K;
  val set_delayop = update_delayop o K;
  val set_curnames = update_curnames o K;    
  fun set_goalnames gs = update_curnames (fn (rs,_) => (rs,gs));    
  fun set_resultnames rs = update_curnames (fn (_,gs) => (rs,gs));    

  val set_ctxt = update_ctxt o K;
  val set_cinfo = update_cinfo o K;

  fun get_rtechn (RState rep) = #rtechn rep;
  fun get_lcinfo (RState rep) = #linfo rep;
  fun get_prev (RState rep) = #prev rep;
  fun get_pplan (RState rep) = #pplan rep;
  fun get_id (RState rep) = #id rep;
  fun get_curnames (RState rep) = #curnames rep;
  val get_goalnames = snd o get_curnames;
  val get_resultnames = fst o get_curnames;
  fun get_searchops (RState rep) = #searchop rep;
  fun get_delayop (RState rep) = #delayop rep;

  val get_ctxt = PPlan.get_context o get_pplan;
  val get_cinfo = CInfo.Ctxt.get o get_ctxt;

  fun add_curnames (rs2,gs2) = 
      update_curnames (fn (rs,gs) => (rs2 @ rs, gs2 @ gs));
  fun add_goalnames gs = add_curnames ([],gs);
  fun add_resultnames rs = add_curnames (rs,[]);

  (* for search ops *)
  val add_searchop = update_searchop o (fn h => fn t => h::t);
  val drop_searchop = update_searchop tl;
  fun pop_searchop rst = 
      case get_searchops rst of [] => NONE 
        | (h::t) => SOME (set_searchops t rst, h);

 (* For delay options *)
 exception DelayException of string;

 fun delay_rst t rst = update_delayop (fn _ => SOME (MSearch.delay t)) rst;
 val reset_delayopt  = update_delayop (fn _ => NONE);

 fun to_resume t rsts = 
     let
       fun to_resume_aux t (ts,fs) []  = (ts,fs)
         | to_resume_aux t (ts,fs) (rst::rsts)  = 
           (case (get_delayop rst) of
             SOME(MSearch.delay t') => if (t = t') then 
                                         to_resume_aux t ((reset_delayopt rst)::ts,fs) rsts
                                       else to_resume_aux t (ts,(rst::fs)) rsts
           | _ => raise DelayException "Trying to resume a state that isn't delayed." )
              (*This shouldn't happen, should only be called on lists of delayed states *)
     in
       to_resume_aux t ([],[]) rsts
     end;

 fun resume_others t rst=  
                  let val defrost_fun = to_resume t in
                    update_delayop (fn _ => SOME (MSearch.resume(defrost_fun))) rst
                  end;

  (* Evaluate and update a state's delay-options in delayed search. *)    
   fun eval_delayopts rst = 
       case (get_delayop rst) of 
         NONE => NONE
       | SOME (MSearch.delay t) => SOME(rst, MSearch.delay t)
       | SOME (MSearch.resume defrost_fun) => SOME(reset_delayopt rst, MSearch.resume defrost_fun)

  (* unfold a reasoning state to get the continuation states 
     Maintains unique ID's for each new state *)
  fun unfold (st as (RState rep)) = 
      case (#rtechn rep) of 
        SOME r => Seq.map new_id (r st)
(*         SOME (RTechn (s,r)) => Seq.map new_id (r st) *)
      | NONE => Seq.empty;

  fun sol_setf st  = 
      if Basics.is_some (get_rtechn st) then st 
      else add_searchop MSearch.endstrategy st;

  (* Run a stacked search *)
  fun search topsstrat rst = 
      MSearch.search pop_searchop
                     (Seq.map sol_setf o unfold)
                     topsstrat rst;

  fun tracedsearch tracef topsstrat rst = 
      MSearch.traced_search tracef pop_searchop
                     (Seq.map sol_setf o unfold)
                     topsstrat rst;

 fun delayed_search topsstrat rst = 
      MSearch.delayed_search eval_delayopts pop_searchop
                     (Seq.map sol_setf o unfold)
                     topsstrat rst;

 (* pass on local cinfo *)
 fun give_lcinfo fromgoal togoals rst = 
     fold 
       (fn togoal => update_cinfo (LCInfo.give (get_lcinfo rst) fromgoal togoal))
       togoals rst;

 (* pass on local cinfo to result names and goalnames *)
(* fun push_lcinfo fromgoal rst = 
     (give_lcinfo fromgoal (fst (get_curnames rst)) o
      give_lcinfo fromgoal (snd (get_curnames rst))) rst;*)


  (* initialisation of a new rstate *)
  fun init ctxt = 
      RState {rtechn = NONE, 
              linfo = LCInfo.empty, 
              prev = NONE, 
              pplan = PPlan.init ctxt, 
              id = inc_g_id (),
              curnames = ([],[]),
              searchop = [],
              delayop = NONE};

  fun init_from_thy thry = init (Proof_Context.init_global thry);

  fun init_from_pp pp = 
      (init (PPlan.get_context pp))
        |> set_pplan pp;
  
  (* pretty printing by just printing the proof plan *)
  val pretty = PPlan.pretty o get_pplan;
  val print = PPlan.print o get_pplan;

end; (* functor *)


structure RState : RSTATE = DB_RState;

(* structure RState = RStateFUN( structure PPlan = PPlan ); *)

(* install pretty printer: print out the proof plan *)
(*install_pp (make_pp ["RState", "T"] (Pretty.pprint o RState.pretty));*)
