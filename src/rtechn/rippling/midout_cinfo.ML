(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      cinfo/rippling/midout_cinfo.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    15 Mar 2003
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Contextual-information for performing rippling. The main purpose
    of this is to manage multiple skeletons, and tie together the
    database of wave rules to the process of rippling. Furthermore, we
    manage the overall ripppling process and provide information on
    matching rules.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature MIDOUT_RIPPLE_CINFO = 
sig
  structure BasicCInfo : BASIC_RIPPLE_CINFO

    type MidOutInfo;
    structure MidOutI : LOCAL_INFO_ITEM where type T = MidOutInfo;

    val get : PPlan.gname ->  RState.T -> MidOutInfo
 
    val init : ((PPlan.gname * Term.term) * 
                         BasicCInfo.RippleSkel.T option) list
                      ->  PPlan.gname -> RState.T 
                      -> RState.T Seq.seq
    val update_midout :
        PPlan.gname  (* old gname *)
        * MidOutInfo (* old cinfo *) ->
        PPlan.gname -> (* new gname *)
        RState.T -> RState.T Seq.seq

    val update_midout_from_goal :
        PPlan.gname ->  PPlan.gname
         -> RState.T -> RState.T Seq.seq   

    val proj_of : PPlan.gname -> RState.T -> RState.T Seq.seq                      
end;


(* Contextual information for Rippling *)
functor MidOutRippleCInfoFUN (BasicCInfo : BASIC_RIPPLE_CINFO)
: MIDOUT_RIPPLE_CINFO
= struct

structure BasicCInfo : BASIC_RIPPLE_CINFO = BasicCInfo;
local 
  open BasicCInfo;
in

(* Idea: If each middle-out info has an ienv, we can get projections just by looking up inev,
   and don't actually have to do projections again *)
datatype MidOutInfo = MCInfo of 
           {trace : PPlan.gname list,
            projections : InstEnv.T list, (* The instantiations for these projections *)
            init_skels : ((PPlan.gname * Term.term) (* skeleton name and term *)
                          * RippleSkel.T option) (* anntotations etc for a skel *)
                          list};

fun get_trace (MCInfo mi) = (#trace mi);
fun get_projections (MCInfo mi) = (#projections mi);
fun get_init_skels (MCInfo mi) = (#init_skels mi);
fun pretty_trace mi = map PPlan.pretty_gname (get_trace mi);


  (* contextual info sturcture *)
(* Information associated with goals in reasoning states during rippling *)
structure MidOutI = 
  LocalInfoFUN( 
    struct
      type T = MidOutInfo;
      val name = "Middle-out: " ^ BasicCInfo.RippleSkel.name;
      val copy = I; (* copy is just Id as no refs *)
      val pretty = fn d : T => fn rst => Pretty.list "[" "]" (pretty_trace d)
    end
  );
 
fun get goal rst = MidOutI.get rst goal;

(* Get the projection of this goal *)
fun proj_of goal rst = 
    let
      val proj_envs = get_projections (get goal rst)
    in
      RTechnEnv.givename (RstName.str ("Exploring projections on goal: "^goal))
                         (fn rst' => 
                             (map (fn env => 
                                   (RState.set_pplan 
                                      (Prf.inst_prf env (RState.get_pplan rst'))
                                      (RState.set_rtechn NONE rst')))
                                  proj_envs)
                               |> Seq.of_list)
                       rst
    end;
    

  (* lists with one of each list of list of lists *)
  fun one_of_each [] = []
    | one_of_each [[]] = []
    | one_of_each [(h::t)] = [h] :: (one_of_each [t])
    | one_of_each ([] :: xs) = []
    | one_of_each ((h :: t) :: xs) = 
      (map (fn z => h :: z) (one_of_each xs)) 
      @ (one_of_each (t :: xs));

(* Update functions for doing rippling with middle-out rewriting,
i.e. in the presence of meta-variables that might stand
for extra term structure. Here, we copute the measure based
on the optimistic assumption that the meta-variables will just
be projections. A term is measure decreasign if its projection
has a better measure than the last normal ripple *)
fun update_midout_i (oldrelgraph,oldskels) projection rst = 
     let 
       val pplan = RState.get_pplan rst
       val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) oldrelgraph;

       (* FIXME: If we're doing middle-out rippling it shouldn't
                 be nessecary to include the regular wave-rules,
                 in fact doing so can cause nasty nasty ho-unification
                 mosters to appear. *)
        val arules2 = [] (* lookup_arules pplan newgname *)
                  
        (* FIXME: proj should also return ienv, so we don't have so
           many projections to check in the rest of the trace. *)
        (*val projections = Seq.list_of (LemmaSpec.proj_trms_pplan 
                                         pplan newgname) *)
     in 
        (select_valid_skels oldskels)
        (* filter: keep only if not worse than treshold. *)
        |> (Library.map_filter 
              (fn s => case (*RippleSkel.mk_midout_next ectxt projections s *)(* only singleton list if grouped mes *)
                    RippleSkel.mk_better_next ectxt projection s
                        of [] => NONE
                         | (l as _::_ ) => 
                           SOME (map (fn e =>
                                         (RippleSkel.get_named_skel_term e,
                                          SOME e)) l)
           ))
        (* |> print_count_list "update_midout_i: each skeletons embeddings" *)
        |> one_of_each
        (* |> print_count_list "one_of_each: " *)
        |> map (fn skls2 => mk_rcinfo arules2 oldrelgraph skls2)
        (* filter out cases where nothing embeds *)
        |> List.filter is_valid_ripple_state_i
    end; 


(* Note: this will be slow and crappy if we don't use a grouped
measure *) 

(* 'pre_midout_skels' is the skeletons & measures used to
calculate the possible measures for the first middle-out step *)
fun update_midout (oldgname, (* prev goal *)
                   MCInfo{trace=trace, projections=ps, init_skels=init_skels}) 
                  goal rst0 = 
      let 
         val nw_trace = trace@[goal]  

         val proj_ienvs = 
             fold (fn g => fn ienvs => 
                              maps (fn ienv =>
                                       (LemmaSpec.proj_ienv_pplan 
                                          ienv (RState.get_pplan rst0) g)
                                         |> Seq.list_of)
                                   ienvs)
                  nw_trace [RstPP.get_ienv rst0]
             
         val rst = MidOutI.put (goal, MCInfo{trace=nw_trace,
                                             projections= proj_ienvs,
                                             init_skels=init_skels})
                               rst0
                               
         (* a (goal * term list) list, the term list is the possible projections of one goal *)
        (* val inst_trace_trms = 
             map (fn goal =>
                     map (fn ienv => 
                             InstEnv.inst_trm ienv 
                                              (Prf.get_ndname_ctrm 
                                                 (RState.get_pplan rst) goal))
                         proj_ienvs
                         |> pair goal)
                 nw_trace
         *)
         
         (* Check the trace for a particular instantiation *)
         fun update_midout_aux ienv (rst, init_skels) = 
            let 
              val inst_trace =  
                  map (fn goal => (InstEnv.inst_trm ienv 
                                                    (Prf.get_ndname_ctrm 
                                                       (RState.get_pplan rst) goal))
                                    |> pair goal) 
                      nw_trace
            in 
              fold (fn (g, proj_g) => fn allskels => 
                      maps (fn (rst, skels) => 
                               (update_midout_i (get_relgraph rst oldgname, skels) 
                                                proj_g rst)
                                 |> map (fn rcinfo => I.put (g, rcinfo) rst)
                                 |> map (fn rst' => (rst', all_skels_of rst' g)))
                           allskels)
                   inst_trace [(rst, init_skels)]
            end
      in
        case 
          (Library.get_first (fn ienv => 
                                 case (update_midout_aux ienv (rst, init_skels))
                                  of [] => NONE
                                   | (h::t) => SOME (Seq.of_list (map fst (h::t)))) 
                     proj_ienvs)
         of
          NONE => Seq.empty
        | SOME nw_rsts => nw_rsts 
       (* (fold update_midout_aux inst_trace_trms [(rst, init_skels)]) *)
       (* (fold update_midout_aux proj_ienvs [(rst, init_skels)])
          |> map fst
          |> Seq.of_list *) 
      end;

fun update_midout_from_goal oldg newg rst = 
    update_midout (oldg,get oldg rst) newg rst;

fun init init_skels goal rst =
    let 
      val projections = Seq.list_of (LemmaSpec.proj_ienv_pplan 
                                       (RstPP.get_ienv rst) (RState.get_pplan rst) goal)
      val proj_trms = map (fn ienv => InstEnv.inst_trm ienv (Prf.get_ndname_ctrm 
                                                               (RState.get_pplan rst) goal))
                          projections
       val rst' = MidOutI.put (goal, MCInfo{trace=[goal],
                                            projections= projections,
                                            init_skels=init_skels})
                              rst
    in 
      case
        (Library.get_first (fn proj_trm => 
                               case (update_midout_i (ParamRGraph.empty, init_skels) 
                                                     proj_trm rst') of
                                 [] => NONE | (h::t) => SOME (h::t))
                        proj_trms)
       of
          NONE => Seq.empty
        | SOME rcinfos => (map (fn rcinfo => I.put (goal, rcinfo) rst') rcinfos)
                          |> Seq.of_list
      (* (update_midout_i (ParamRGraph.empty, init_skels) proj_trms rst')
         |> map (fn rcinfo => I.put (goal, rcinfo) rst')
         |> Seq.of_list
       *)
    end;

end; (* local *)
end; (* struct *)
