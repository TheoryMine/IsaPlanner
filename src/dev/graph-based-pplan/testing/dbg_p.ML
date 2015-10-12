open G;

(* prepare G.res_thm and G.apply_unify_trm *)
val th = (thm "exI");
val nid = "g";
val (flexygoalnames,inp) = I.get();

val thry = #thy rep;
val nd = get_nd p nid;
 
val (p as G.Proof rep) = (close_open_goal nid inp);
val meth = (Nd.MethThm th);
val localflexes = (map (fn nid => (nid, Logic.dest_equals (goal_trm p nid))) 
               flexygoalnames);
val trm = (Thm.prop_of th);

      val initvars = (#vars rep);
      val thry = #thy rep;

      val (t,vars2) = externalise_trm initvars trm;

Pretty.writeln (PData.Trm.Var.NTab.pretty (PData.Trm.Var.pretty_typ thry) (snd vars2));

      val ct = Trm.concl_of t;
      val ats = Trm.prems_of t;

Pretty.writeln (Trm.pretty thry (Goal.trm_of (Nd.get_goal nd)));
Pretty.writeln (Trm.pretty thry ct);

      val useq = Trm.unify' thry vars2 localflexes
                            (nid,(Goal.trm_of (Nd.get_goal nd), ct));

length (Seq.list_of useq);
val ((insts,flexes),modifiedvars) = Seq.hd useq;

            val ((prf_ienv, tgt_ienv), vars) = 
                prep_envs_of_inst initvars modifiedvars insts; 

G.InstEnv.print thry prf_ienv;
G.InstEnv.print thry tgt_ienv;
Pretty.writeln (PData.Trm.Var.NTab.pretty (PData.Trm.Var.pretty_typ thry) (snd vars));

            val (newflexes,updatedflexes) =
                List.partition (fn (n,_) => Goal.NTab.ord (n,nid) = EQUAL) 
                               flexes; 
            val newflexts =
                map (InstEnv.inst_trm tgt_ienv o Logic.mk_equals o snd)
                    newflexes;
            val updatedflexnts =
                map (apsnd (InstEnv.inst_trm tgt_ienv o Logic.mk_equals))
                    updatedflexes;
            val updatedflexgs = map fst updatedflexnts;

            val newsubgts = (map (InstEnv.inst_trm tgt_ienv) ats);

            val ((newflexgs,subgs), p2) = 
                p |> inst_proof prf_ienv (* effects old flex goals - is there any issue with dependency managemant of var names? probably ok.... *)
                  |> set_vars vars
                  |> update_goals_trms updatedflexnts
                  (* |> close_open_goal nid  *)
                  |> ((add_resolved_subgoals nd nid newflexts)
                        -- (add_resolved_subgoals nd nid newsubgts))


