(* Structure for storing the output of a particular run of
 synthesis. Records the theorems, conjectures, and statistics relevant
 to synthesis in the current theory/context. *)



signature SYNTH_CONTEXT =
sig

  type T (* data that lives in theory/context *)
  type stats

  val synth_stats_of : T -> stats
  val result_thms_of : T -> (string * Thm.thm) list
  val conjs_of : T -> Term.term list

  val reset_stats : T -> T
  val update_result_thms : ((string * Thm.thm list) -> (string * Thm.thm list)) -> T -> T 

  structure Thy : sig
    val synth_stats_of : theory -> stats
    val result_thms_of : theory -> (string * Thm.thm) list
    val conjs_of : theory -> Term.term list
  end;

  structure Ctxt : sig
    val synth_stats_of : Proof.context -> stats
    val result_thms_of : Proof.context -> (string * Thm.thm) list
    val conjs_of : Proof.context -> Term.term list
  end;

end;


structure SynthContext =
struct

(* TODO: Decide what to go in stats. *)
type stats = string;
fun merge_stats s1 s2 = s1 ^ s2;


datatype T = SynthResData of {
         stats : stats,
         result_thms : (string * Thm.thm) list,
         conjs : Term.term list};
val empty = SynthResData{stats = "",
                         result_thms = [],
                         conjs = []};

fun merge (SynthResData rep) (SynthResData rep2) = 
    SynthResData{
    stats = merge_stats (#stats rep) (#stats rep2),
    result_thms = (#result_thms rep) @ (#result_thms rep2),
    conjs = (#conjs rep) @ (#conjs rep2)
    };


fun synth_stats_of (SynthResData rep) = (#stats rep);
fun result_thms_of (SynthResData rep) = (#result_thms rep);
fun conjs_of (SynthResData rep) = (#conjs rep);

fun reset_stats (SynthResData rep) =
     SynthResData{stats = "", result_thms = #result_thms rep , conjs = #conjs rep};

fun update_stats f (SynthResData rep ) =
     SynthResData{stats = f (#stats rep), result_thms = #result_thms rep , conjs = #conjs rep};
fun update_result_thms f (SynthResData rep) =
    SynthResData{stats = #stats rep, result_thms = f (#result_thms rep), conjs = #conjs rep};
fun update_conjs f (SynthResData rep) =
    SynthResData{stats = #stats rep, result_thms = #result_thms rep, conjs = f (#conjs rep)};

fun pretty_stats stats = Pretty.chunks[Pretty.str "Stats:", Pretty.str stats];

fun pretty_thms ctxt thrms = Pretty.chunks 
                          ((Pretty.str "Theorems:") ::
                          (map (fn (prf, thm) => 
                                   Pretty.block[Pretty.str prf, 
                                                Trm.pretty ctxt (Thm.concl_of thm)]) thrms));
fun pretty_conjs ctxt conjs = Pretty.chunks ((Pretty.str "Conjectures: ")::(map (Trm.pretty ctxt) conjs));

fun pretty ctxt (SynthResData rep) = 
    Pretty.chunks[pretty_stats (#stats rep),
                  pretty_thms ctxt (#result_thms rep),
                  pretty_conjs ctxt (#conjs rep)];
    
structure ThyData = Theory_Data
  (
    type T = T
    val empty = empty
    val extend = I
    fun merge (t1, t2) = merge (t1, t2)
  );
val of_ctxt = ThyData.get o ProofContext.theory_of;
val of_thy = ThyData.get;



structure Ctxt =
struct
    val synth_stats_of = synth_stats_of o of_ctxt;
    val result_thms_of = result_thms_of o of_ctxt;
    val conjs_of = conjs_of o of_ctxt;
end;

structure Thy =
struct
    val synth_stats_of = synth_stats_of o of_thy ;
    val result_thms_of = result_thms_of o of_thy; 
    val conjs_of = conjs_of o of_thy;
end;

end;
