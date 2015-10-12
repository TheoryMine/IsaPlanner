 use_thy "examples/N";
val thry = theory "N";
val rippling = RippleLemCalc.induct_ripple_lemcalc;
 val myrst = PPInterface.ipp thry (rippling "g") ("g","a + b = b + (a::N)");

(* trace to step case of lemma *)
val goal = "lem_k";
val dtacs = RippleCInfo.applicable_dtacs_of myrst goal;
val [dtac] = dtacs; 
val rst2s = Seq.list_of (RTechnEnv.apply_dtac_to_g dtac goal myrst);
val [rst2] = rst2s;
val oldgoal = goal;
val newgoal = "lem_m";

(* returns [] when should return a valid measure *)
(* val rst3s = Seq.list_of (RippleCInfo.update_from_goal oldgoal newgoal rst2); *)

(* for entering RippleCInfo.update *)
val all_old_skels = RippleCInfo.all_skels_of rst2 oldgoal; 
val oldskels = all_old_skels;
val oldgname= oldgoal;
val newgname = newgoal;
val rst = rst2;

(* inside: RippleCInfo.update *)
val pplan = RState.get_pplan rst;
val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
val oldrelgraph = RippleCInfo.get_relgraph rst oldgname;
val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) 
                             oldrelgraph;

(* getting inside RippleSkel... *)
val [s] = RippleCInfo.select_valid_skels oldskels;
val nexts = RippleSkel.mk_better_next ectxt newgoalterm s;

val (skel_name,skel_trm) = RippleSkel.get_named_skel_term s;
val oldms = RippleSkel.get_measures s;
val [oldm] = oldms;
val oldms = RippleSkel.get_measure_col s;

RippleMeasure.print oldm;

val target_trm = newgoalterm;
val es = Seq.list_of (Embed.embed ectxt skel_trm target_trm);

val m2col = RippleMeasure.better_next_measures oldms es;
RippleMeasure.Col.is_empty m2col;
val m2col = RippleMeasure.all_next_measures oldms es;
val m2s = RippleMeasure.Col.list_of m2col;
val [m2] = m2s;

RippleMeasure.print m2;

RippleMeasure.ord (m2,oldm);

next_measures oldst ectxt skelterm newtrm
