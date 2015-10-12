use "ROOT.ML";
(*use_thy "benchmarks/BestF_L";*)


use "rtechn/conj/conjecturedb_lib.ML";
use "rtechn/conj/conjdb_cinfo.ML";
use "rtechn/conj/conj_stack_cinfo.ML";
use "rtechn/rippling/ripple_bf_techn.ML"; 
structure Ripple_BF = RippleBFRTechnFUN
                        (structure RippleRTechn = RippleRTechn_dsum);

structure RippleCalc = RippleLemCalcFUN(structure BasicRipple = RippleCaseSplit);
structure Ripple = RippleLemSpecFUN(structure RippleLemCalc = RippleCalc
            structure MidOutRCInfo = MidOutCInfo_g_dsum);
Trm.drop_var_args_flag := false;
use_thy "benchmarks/Casesplit";
val thy = theory "Casesplit";
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then Ripple.induct_and_ripple);



val bestfs = (MSearch.bestfs(Ripple_BF.compare_rsts));
val bf_ripple = PPInterface.ipp_s bestfs (Ripple_BF.induct_and_ripple
              Ripple_BF.basic_bf_steps);
use "ROOT.ML";
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then 
                              RippleCaseSplit.induct_and_ripple);
use_thy "benchmarks/Casesplit";
Trm.drop_var_args_flag := false;

val (t, ppl, rz, gz) = the ((ripple ("a","x mem (t@l) = (x mem t | x mem l)"); NONE) handle Res.my_ex x => SOME x);

PolyML.exception_trace (fn () => ripple ("", "x mem (t@l) = (x mem t | x mem l)"));
ripple ("a", "x mem l@[x]");
ripple ("a","x mem (ins(x,l))");
ripple ("a","x mem l --> x mem (l@t)");
ripple ("a","x mem t --> x mem (l@t)");
ripple  ("a","x mem (ins(x,l)) = True");
ripple ("a","~(x=y) --> (x mem (ins_set(y,l)) = x mem l)");

(* can't solve *)
ripple  ("a","x=y --> (x mem (ins_set(y,l)) = True)");
ripple  ("a","x mem (ins_set(x,l)) = True)");

(* Simp fails on one case *)
ripple  ("a","~(x=y) --> (x mem (ins(y,l)) = x mem l)");


(*bf-more inefficent as not simplifies non-ripple step*)
bf_ripple ("", "x mem (t@l) = (x mem t | x mem l)");
bf_ripple ("", "x mem l@[x]");
bf_ripple ("","x mem (ins(x,l))"); (* works!*)
bf_ripple ("","x mem l --> x mem (l@t)");
bf_ripple ("","x mem t --> x mem (l@t)");
bf_ripple  ("","x mem (ins(x,l)) = True");
bf_ripple ("","~(x=y) --> (x mem (ins_set(y,l)) = x mem l)");


bf_ripple  ("","x=y ==> (x mem (ins_set(y,l)) = True)");
(*works with bf*)
bf_ripple  ("","x mem (ins_set(x,l)) = True");



use_thy "benchmarks/Casesplit";
val rst = it;
val old_skels = RippleCInfo.all_skels_of rst "e";


Seq.list_of (SplitterRTechn.split_if_rtechn "e" rst );
val rst2 = hd it;
PPInterface.print_rst rst2;
Seq.list_of (Seq.maps (fn rst1 => RippleCInfo.update_all old_skels (RState.set_rtechn NONE rst1)) (Seq.single rst2));
val rst3 = hd it;
PPInterface.print_rst rst3;
 val t = Sign.read_term (the_context()) "l :: 'a List";
val ty = Term.type_of t
val ty_str = case ty of
                     Type(ty_str, _) => ty_str
                   | TFree(s,_)  => error ("Free type: " ^ s)
                   | TVar((s,i),_) => error ("Free variable: " ^ s);

val dtypestab = DatatypePackage.get_datatypes thry;
val dt = case Symtab.lookup dtypestab ty_str
                of SOME dt => dt
                 | NONE => error ("Not a Datatype: " ^ ty_str);

val rw_list = (#case_rewrites dt);
val split_thm = thm (ty_str^".split");

fun casesplit_thm_of_type thry typ =
    let
      val dtypestab = DatatypePackage.get_datatypes thry;
      val ty_str = case ty of 
                     Type(ty_str, _) => ty_str
                   | TFree(s,_)  => raise error 
                                            ("Free type: " ^ s)   
                   | TVar((s,i),_) => raise error 
                                            ("Free variable: " ^ s)

      val dt = case Symtab.lookup dtypestab ty_str
                of SOME dt => dt
                 | NONE => error ("Not a Datatype: " ^ ty_str)

    in
      []
    end;

ripple ("a","case l of [] => True | (h#t) => False");


(* Mysteriously don't apply < rule *)
val rst = ripple ("a", "(a + b) < a + (suc b)");
val old_skels = RippleCInfo.all_skels_of rst "n";
val ms = RippleCInfo.measures_of rst "n"; (* All seem to be 4 *)
RippleCInfo.print_applicable_rules rst "n"; (* This incude desired < rule *)

val [d1,d2,d3,d4] =  RippleCInfo.applicable_dtacs_of rst "n";
val [rst2] = Seq.list_of ( RTechnEnv.apply_dtac_to_g d2 "n" rst); (* This gives what we're after *)

Seq.list_of (RippleCInfo.update_from_goal "n" "o" rst2); (* Empty *)
val [rst3] = Seq.list_of (RippleCInfo.update_all_from_goal "n" "o" rst2);
val ms2 = RippleCInfo.measures_of rst3 "o"; (* empty *)

val newgoalterm = Prf.get_ndname_ctrm (RState.get_pplan rst2) "o";
val [skel] = RippleCInfo.select_valid_skels old_skels;

(* Both empty, no embedding ??? *)
 RippleCInfo.RippleSkel.mk_next newgoalterm skel;
 RippleCInfo.RippleSkel.mk_all_next newgoalterm skel;
val (nm, st) = RippleCInfo.RippleSkel.named_skel_term_of skel;

(* Both empty - no embedding!!! *)
 Seq.list_of (EmbeddingLib.embed st newgoalterm);
 Seq.list_of (EmbeddingLib.embed newgoalterm st);
