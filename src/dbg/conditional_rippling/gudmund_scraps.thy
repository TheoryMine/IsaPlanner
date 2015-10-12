

lemmas lstep = st_def Domain_def Connected_def rngrestr_def forwardcomp_def

ML {* 


  val assume_rtechn =
 			DTac.mk_from_isa_tac_local
        (K (Pretty.str ("by assumption")),
         (assume_tac 1));


local open BasicRipple; open RTechnEnv; in

val my_simp_only =       
			DTac.mk_from_isa_tac_local
        (K (Pretty.str ("simp with givens")), 
         (Simplifier.simp_tac (Simplifier.addsimps (@{simpset},[@{thm st_def}, @{thm Domain_def}, @{thm Connected_def},@{thm rngrestr_def},@{thm forwardcomp_def}])) 1));

fun dmy_simp_only g rst = 
		apply_dtac_to_g my_simp_only g rst;

val stepcase_by_ripplingN = 
    RstName.str "My applicable rules explorer";

(* this wrapping work -- but not really sure why!! *)
(* \<dots> but get an exception -- maybe something the simplifier does?? *)

fun has_app_rules goal rst =
   not (List.null (RippleCInfo.lookup_arules (RState.get_pplan rst) goal))


fun rsteps_on_goal goal = 
          (fn rst => (RippleCInfo.lookup_arules (RState.get_pplan rst) goal)
            |> Seq.of_list 
				    |> Seq.maps (fn dtac => ((apply_dtac_to_g dtac goal)
                    thenr (map_then rsteps_on_goal)) rst)
    (* always give option to GIVE UP A GOAL *)
            |> Seq.cons (rst |> end_rst (RstName.str ("end explr on goal: " 
                                               ^ goal)) 
    (* THIS WAS REQUIRED FOR CONT. -- not sure why !!! *)
                              |> RState.set_goalnames [goal] )
      
); 

fun explore_rtechn goal =
		(refine stepcase_by_ripplingN
            (rsteps_on_goal goal)
       (* THIS ONE DOES ALWAYS PRINT OUT GOALS -- strange\<dots> *)
       thenr (map_then DTacRTechn.simp_noasm)
       thenr (map_then dmy_simp_only)) : RTechn.T ;

end; 

*}


(* THIS WORKS 
ML {*

val myrst = 
  PrintMode.setmp []
  (fn () => PPInterface.ipp @{theory} (explore_rtechn "g") ("g","Callers = dom (call ; st |> Connected) ==> s \<notin> dom call \<Longrightarrow> Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)")) ();
*}
;

*)


(* USE OF RIPPLING -- make sure functions are measure decreasing *)


ML {*
val _ = writeln "test";
*}

(* RIPPLING DOESN'T WORK DIRECTLY *)
(* strange: should at least apply notdomoverun'' and notdomoverun' *)


ML {* print_depth 1;
@{term "Callers = dom (call ; st |> Connected) 
==> s \<notin> dom call 
\<Longrightarrow> Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)"} *}


ML {* 
val skels = PPlan.get_varified_lasm_nctrms (RState.get_pplan rst0) goalname;

local open RippleCInfo 
  val rst = rst0;
  val goal = goalname;
  val relgraph = ParamRGraph.empty;
  (* lists with one of each list of list of lists *)
  fun one_of_each [] = []
    | one_of_each [[]] = []
    | one_of_each [(h::t)] = [h] :: (one_of_each [t])
    | one_of_each ([] :: xs) = []
    | one_of_each ((h :: t) :: xs) = 
      (map (fn z => h :: z) (one_of_each xs)) 
      @ (one_of_each (t :: xs));
in 
     val pplan = RState.get_pplan rst
      val goalterm = Prf.get_ndname_ctrm pplan goal 
      val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) relgraph;
     val skellists = one_of_each
	  (* Produce lists of states for each skeleton and combine them *)
          (map (fn (n,t) =>
		               case RippleSkel.init {ectxt=ectxt, skelterm=t, 
                                         skelname=n, target=goalterm} 
		 (* skeleton does not currently embedd *)
		                of [] => [((n,t), NONE)] 
		                 | (l as _::_) => map (fn e => ((n,t), SOME e)) l) skels)
end;

val [rst1] = Seq.list_of (RippleCInfo.start skels ParamRGraph.empty goalname rst0);

*}
