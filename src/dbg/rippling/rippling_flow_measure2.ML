 use_thy "examples/N";
val thry = theory "N";
val rippling = RippleLemCalc.induct_ripple_lemcalc;
val myrst = PPInterface.ipp thry (rippling "g") ("g","n * p + q * p = (n + q) * (p :: N)");

(* trace to step case of lemma *)
val goal = "s";
val dtacs = RippleCInfo.applicable_dtacs_of myrst goal;
val [dtac1,dtac2] = dtacs; 
val rst2s = Seq.list_of (RTechnEnv.apply_dtac_to_g dtac2 goal myrst);
val [rst2] = rst2s;
val oldgoal = goal;
val newgoal = "t";

(*** returns [] when should return a valid measure ***)
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

(*** returns []; should return valid ripple state ***)
(* val nexts = RippleSkel.mk_next ectxt newgoalterm s; *)

val (skel_name,skel_trm) = RippleSkel.named_skel_term_of s;
val oldms = RippleSkel.measures_of s;
val [oldm] = oldms;
FlowMeasure.print oldm;

val target_trm = newgoalterm;
val e2s = Seq.list_of (Embed.embed ectxt skel_trm target_trm);
val [e] = e2s;

val oldst = s;

val [m2] = RippleMeasure.next_measure oldm e;
FlowMeasure.print m2;
RippleMeasure.ord (oldm,m2);

next_measures oldst ectxt skelterm newtrm
