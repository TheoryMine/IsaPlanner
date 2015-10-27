theory IsaPtest
imports IsaP
begin

section "Sets"

definition 
  disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where
 "disjoint A B \<equiv> A \<inter> B = {}"

declare disjoint_def[wrule]

primrec
  disjoint_with_lists :: "'a set \<Rightarrow> ('a set) list \<Rightarrow> bool"
where
    "disjoint_with_lists S [] = True"
  | "disjoint_with_lists S (x#xs) = (disjoint S x \<and> disjoint_with_lists S xs)"

thm disjoint_with_lists.simps

declare disjoint_with_lists.simps[wrule]

primrec
  disjoint_lists :: "('a set) list \<Rightarrow> bool"
where
    "disjoint_lists [] = True"
  | "disjoint_lists (x#xs) = (disjoint_with_lists x xs \<and> disjoint_lists xs)"

declare disjoint_lists.simps[wrule]

definition 
  partition :: "'a set \<Rightarrow> ('a set) list \<Rightarrow> bool" 
where 
  "partition S SS \<equiv> foldl (\<lambda> res el. {el} \<union> res) {} SS = {}
                    \<and> disjoint_lists SS"

declare partition.simps [wrule]
section "Relations"

definition product :: "('a set \<times> 'b set) \<Rightarrow> ('a \<times> 'b) set"
where "product R \<equiv> {r. \<exists> x y. r = (x,y) \<and> x \<in> (fst R) \<and> y \<in> (snd R)}"

abbreviation relation (infix "\<leftrightarrow>" 51)
where "A \<leftrightarrow> B \<equiv> Pow (product (A,B))"

abbreviation dom 
where "dom r \<equiv> Domain r"

abbreviation rng 
where "rng r \<equiv> Range r"

definition totalrel (infix "<<->" 51)
where "A <<-> B \<equiv> {r. r \<in> A \<leftrightarrow> B \<and> dom r = A}"

definition surjrel (infixl "<->>" 51)
where "A <->> B \<equiv> {r. r \<in> A \<leftrightarrow> B \<and> rng r = B}"

definition totalsurjrel (infixl "<<->>" 51)
where "A <<->> B \<equiv> (A <<-> B) \<inter> (A <->> B)"

definition 
  forwardcomp :: "('a * 'b) set \<Rightarrow> ('b * 'c) set \<Rightarrow> ('a * 'c) set" (infixl ";" 40)
where "p ; q \<equiv> {(x,y). \<exists> z. (x,z) \<in> p \<and> (z,y) \<in> q}"

(* definition forwardcomp (infixl ";" 40) *)
(*"('a set \<times> 'b set) set \<Rightarrow> ('b set \<times> 'c set) set \<Rightarrow> ('a set \<times> 'c set) set" *)
(* where "p;q \<equiv> {r. \<exists> x y z. r = (x,z) \<and> (x,y) \<in> p \<and> (y,z) \<in> q}" *)

definition identrel :: "'a set \<Rightarrow> ('a \<times> 'a) set"
where "identrel S \<equiv> {r. \<exists> i. r = (i,i) \<and> i \<in> S}"

definition domrestr (infix "<|" 35)
where "A <| R \<equiv> {r. r \<in> R \<and> fst r \<in> A}"

definition domsub (infix "<<|" 35)
where "A <<| R \<equiv> {r. r \<in> R \<and> fst r \<notin> A}"

definition rngrestr (infix "|>" 35)
where "R |> A \<equiv> {r. r \<in> R \<and> snd r \<in> A}" 

definition rngsub (infix "|>>" 35)
where "A |>> R \<equiv> {r. r \<in> R \<and> snd r \<notin> A}"

abbreviation inverse ("_~")
where "inverse \<equiv> converse"
 
abbreviation image
where "image \<equiv> Image"

definition override (infix "<+" 35)
where "R1 <+ R2 \<equiv> R2 \<union> (domsub (dom R2) R1)"

section "Functions"

thm converse_def

definition pfun_abrial 
where "pfun_abrial S T \<equiv> {f. f \<in> S \<leftrightarrow> T \<and> ((inverse f);f) = identrel (rng f)}"



definition pfun (infix "+>" 51)
(* should maybe be? *)
(* where "S +> T \<equiv> {f. f \<in> S \<leftrightarrow> T \<and> (\<forall>x \<in> (S \<inter> dom f). \<exists>!y. (x,y) \<in> f)}" *)
(* or maybe more type checking is required ??? *)
where "S +> T \<equiv> {f. f \<in> S \<leftrightarrow> T \<and> (\<forall>x \<in> dom f. \<exists>!y. (x,y) \<in> f)}"

definition tfun (infix "\<rightarrow>" 51)
where "S \<rightarrow> T \<equiv> {f. f \<in> S +> T \<and> dom f = S}"

definition pinj (infix ">+>" 51)
where "S >+> T \<equiv> {f. f \<in> S +> T \<and> (inverse f) \<in> T +> S}"

definition tinj  (infix ">\<rightarrow>" 51)
where "S >\<rightarrow> T \<equiv> {f. f \<in> S \<rightarrow> T \<and> (inverse f) \<in> T +> S}"

definition psurj (infix "+\<guillemotright>" 51)
where "S +\<guillemotright> T \<equiv> {f. f \<in> S +> T \<and> rng f = T}"

definition tsurj (infix "-\<guillemotright>" 51)
where "S -\<guillemotright> T \<equiv> {f. f \<in> S \<rightarrow> T \<and> rng f = T}"

definition bij (infix ">-\<guillemotright>" 51)
where "S >-\<guillemotright> T \<equiv> {f. f \<in> S >\<rightarrow> T \<and> f \<in> S -\<guillemotright> T}"

definition fapp (infixl "$" 51)
where "f $ x \<equiv> THE y. (x,y) \<in> f"

(* should this be the case??? *)
lemma "f $ x = y \<Longrightarrow> (x,y) \<in> f"
  apply (unfold fapp_def)
  apply auto
  sorry

(* should this hold?? *)
lemma 
  assumes h1: "f $ x = y"
  shows "x \<in> dom f"
proof -
  from h1 have "(THE y. (x,y) \<in> f) = y" by (unfold fapp_def)
  thm the_equality
oops

(* should this hold?? *)
lemma "f $ x = y \<Longrightarrow> y \<in> rng f"
  sorry

(* i.e. what does f$x actually mean *)

lemma fapp_unique: "\<lbrakk>x \<in> dom f; f \<in> A +> B; (x,y) \<in> f\<rbrakk> \<Longrightarrow> f $ x = y"
  apply (unfold fapp_def)
  apply (unfold pfun_def)
  apply (rule the_equality)
  apply auto
  done

lemma tfunpfun: "A \<rightarrow> B \<subseteq> A +> B"
  apply (unfold pfun_def tfun_def)
  apply auto
  done


lemma tfun_pfun_subset: "F \<rightarrow> G \<subseteq> F +> G"
  apply (unfold pfun_def tfun_def)
  apply auto
  done


lemma "\<lbrakk>x \<in> dom f;(f \<in> A \<rightarrow> B);(x,y) \<in> f\<rbrakk> \<Longrightarrow> f $ x = y"
  apply (rule fapp_unique)
  prefer 2
  apply (rule set_mp[OF tfun_pfun_subset])
  apply simp_all
  done

lemma tfun_is_pfun: 
  assumes H: "f \<in> F \<rightarrow> G"
  shows "f \<in> F +> G"
proof -
  have g1: "F \<rightarrow> G \<subseteq> F +> G" by (rule tfun_pfun_subset) 
  with H show ?thesis by auto
qed

lemma pfun_diff_eq: "(\<forall>x\<in> dom f. \<exists>!y. (x, y) \<in> f) = ((f~ ; f) = identrel (rng f))"
  apply (unfold converse_def identrel_def)
  apply (unfold Range_def converse_def Domain_def)
  apply (unfold forwardcomp_def)
  apply auto
  done

lemma pfun_eq_pfunabrial: "S +> T = pfun_abrial S T"
  apply (unfold pfun_def pfun_abrial_def)
  apply (subst pfun_diff_eq)
  apply (rule refl)
  done

section "Subtype"

definition subtype :: "('a set) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a set"
where "subtype t restr \<equiv> {x. x \<in> t \<and> restr x}"

lemma subtype_true: "\<forall> r. subtype T r \<subseteq> T"
  apply (rule allI)
  apply (unfold subtype_def)
  apply auto
  done

typedef Digit = "{n::nat. n \<le> 9}"
  by auto

thm Digit_def
thm Rep_Digit
thm Abs_Digit_inverse
thm Rep_Digit_inverse

types Digitlist = "Digit list"

fun
  sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
    "sublist [] ys = True"
  | "sublist xs [] = False"
  | "sublist (x#xs) ys = (if x = hd ys then True else sublist xs (tl ys))"

datatype Status = seize | dialing | unobtainable | connecting | ringing | speech | engaged | suspended

definition
  Connected
where
  "Connected \<equiv> {ringing,speech,suspended}"
  
definition
  Established
where
  "Established \<equiv> Connected \<union> {connecting,engaged}"

consts
  Subs :: "Digitlist set"

definition
  Valid
where
  "Valid \<equiv> {v. \<exists> s. sublist v s}"

definition
  SubRec :: "(Status * Digitlist) set"
where
  "SubRec \<equiv> {(seize,[])} \<union> 
            {r. \<exists> n. r = (dialing,n)  \<and> n \<in> (Valid - Subs) - {[]}} \<union>
            {r. \<exists> (n::Digitlist). r = (unobtainable,n)  \<and> n \<notin> Valid} \<union>
            {r. \<exists> s n. r = (s,n) \<and> s \<in> Established  \<and> n \<in> Subs}"

definition
  st  ::  "((Status * Digitlist) * Status) set"
where
  "st \<equiv> {x. \<exists> a b. x = ((a,b),a)}"

definition
  num  ::  "((Status * Digitlist) * Digitlist) set"
where
  "num \<equiv> {x. \<exists> a b. x = ((a,b),b)}"

lemma "(x,y) \<in> SubRec"
apply (cases x)
apply (unfold SubRec_def)
apply auto
oops

(* Types as definitions -- UNIV + typechecking *)

abbreviation 
  Nats :: "nat set"
where
  "Nats \<equiv> UNIV"

abbreviation
  Digits :: "Digit set"
where
  "Digits \<equiv> UNIV"

(* locale removed for simplicity *)

consts 
  Free :: "Digitlist set"
  Callers :: "Digitlist set"
  Unavailable :: "Digitlist set"
  call :: "(Digitlist * (Status * Digitlist)) set"
  connected :: "(Digitlist * Digitlist) set"


axioms
 inv1: "partition Subs [Free,Unavailable,dom call, rng connected]"
 inv2: "Callers =  dom ((call ; st) |> Connected)"
 inv3: "connected = (Callers  <| (call ; num))"
 tinvcall: "call \<in> Subs +> SubRec"
 tinvcon: "connected \<in> Subs >+> Subs"

lemma "x \<in> Free \<Longrightarrow> x \<notin> dom call"
  using inv1
  apply (unfold partition_def)
  apply auto
  done

lemma rngresunion [wrule]: "((A \<union> B) |> C) = (A |> C) \<union> (B |> C)"
  apply (unfold rngrestr_def)
  apply auto
  done

lemma notdomcomp: "x \<notin> dom F \<Longrightarrow> x \<notin> dom (F ; G)"
  apply (unfold forwardcomp_def)
  apply (unfold Domain_def)
  apply auto
  done

(*
declare notdomcomp[wrule]
*) 

lemma notdomoverun [wrule]: "x \<notin> dom F \<Longrightarrow> (F <+ {(x,y)}) = F \<union> {(x,y)}"
  apply (unfold Domain_def)
  apply (unfold override_def)
  apply (unfold domsub_def Domain_def)
  apply auto
  done

(*
 declare notdomoverun [wrule]
*)

lemma compuniondist: "((a \<union> b) ; c) = (a ; c) \<union> (b ; c)"
  apply (unfold forwardcomp_def)
  apply auto
  done

declare compuniondist[wrule]


(*
declare notdomoverun[subst compuniondist, wrule]
*)

(* wave rule we would like to be able to speculate *)
lemma notdomoverun' [wrule]: "x \<notin> dom F \<Longrightarrow> ((F <+ {(x,y)});G) = ((F;G) \<union> ({(x,y)};G))"
  apply (subst compuniondist[symmetric])
  apply (subst notdomoverun)
  apply simp_all
  done

lemma notdomoverun'' [wrule]: "x \<notin> dom F \<Longrightarrow> (((F <+ {(x,y)});G) |> H) = (((F;G) |> H) \<union> (({(x,y)};G) |> H))"
  apply (subst rngresunion[symmetric])
  apply (subst compuniondist[symmetric])
  apply (subst notdomoverun)
  apply simp_all
  done

ML{*
  val thry = @{theory}

  structure BasicRipple = FlowRippler.RTechn.Basic;
  val rippling = BasicRipple.ripple_stepcase
*}

(* THIS SHOULD WORK -- at least notdomoverun should work *)

(* can this be discovered? *)
lemma emptyunion [wrule]: "(B = {}) ==> (A = A \<union> B)"
  by auto

declare Relation.Domain_Un_eq [wrule]

lemma
  assumes h: "s \<notin> dom call"
  shows "Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)"
  using h apply (subst notdomoverun'') (* conditional *) 
  apply assumption
 apply (subst Relation.Domain_Un_eq) 
  apply (subst inv2[symmetric])
  apply (simp add: st_def Domain_def Connected_def rngrestr_def forwardcomp_def)
  done


lemma
  assumes h: "s \<notin> dom call"
  shows "Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)"
  using h apply (subst notdomoverun) (* conditional *) 
   apply assumption  (* prove condition -- by assumption *) 
  apply (subst compuniondist) 
  apply (subst rngresunion)
  apply (subst Relation.Domain_Un_eq) 
  apply (subst inv2[symmetric]) (* weak fert *)
(* hmm: A = A \<union> B ==> A = A /\ B = {} ??? *)
  apply (rule emptyunion)
  apply (simp add: st_def Domain_def Connected_def rngrestr_def forwardcomp_def)
  done

(* TODO:

RIPPLING:
   - get proof through by explore_rtech
   - change flow/measure to replace this by rippling
     - for example, this can be achieved by a new critic
       fired when rippling fails
   - see if rewrite rules (lemmas) can be discovered somehow
   - try on other examples

STRATEGY:
    - see if a more specific (but sufficiently general) strategy can be written which applies to other goals
    - see if it applies to "similar POs"
    - see if a direct proof/tactic reuse does not hold
*)

ML {* Print_Mode.print_mode := [] *}

ML{*

val myrst = 
  Print_Mode.setmp []
  (fn () => PPInterface.ipp_of_terms @{theory} (RTechnEnv.map_then BasicRipple.ripple_stepcase) 
    [@{term "Callers = dom (call ; st |> Connected) 
      ==> s \<notin> dom call 
      ==> Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)"}]) ();
PPInterface.print_rst myrst;
*}
ML {* print_depth 10; *}

-- "What are the applicable rules"
ML {* 
val rst1 = myrst;
val gname = "g1";
val arules = Seq.list_of (BasicRipple.RippleCInfo.applicable_dtacseq_of rst1 gname);
length arules;
val [r1,r2,r3] =  arules;
*}

-- "Apply a rule"
ML {* 
val [rst2] = Seq.list_of (RTechnEnv.apply_dtac_to_g r2 gname rst1);
val l = RState.get_goalnames rst2;
val gname2 = "g1c";
PPInterface.print_rst rst2;
*}

ML {* exists *}

ML {* 
BasicRipple.make_ripple_goal_cinfos gname 
*}

ML {*
val [rst2] = Seq.list_of (RippleCInfo.update gname gname2 rst2);
val oldskels = RippleCInfo.all_skels_of rst2 gname2;
PPInterface.print_rst rst2;
RippleCInfo.print rst2 gname;
RippleCInfo.print rst2 gname2;
*}

ML {*
  val l = Seq.list_of (BasicRipple.do_dtac_ripple_step r2 gname rst1);
*}

ML {* 
val [rst2] = Seq.list_of (BasicRipple.rsteps_on_goal gname rst1);
PPInterface.print_rst myrst;
*}

ML {*

val [rst2] = Seq.list_of (RTechnEnv.apply_dtac_to_g r2 gname rst1);
val gname2 = "g1c"
val [rst2] = Seq.list_of (RippleCInfo.update gname gname2 rst2);
PPInterface.print_rst rst2;
*}


ML {*
val rst0 = PPInterface.init_rst @{theory}
  ["Callers = dom (call ; st |> Connected) ==> s \<notin> dom call \<Longrightarrow> Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)"]
;
*}

-- ""

ML {*
  val [goalname] = RState.get_goalnames rst0;
  val initrtechn = BasicRipple.startr_on_goal goalname;

  val [rst1] = Seq.list_of (initrtechn rst0);

  val oldskels = RippleCInfo.all_skels_of rst1 goalname;
  PPInterface.print_rst rst1;
*}

-- ""

ML {*
val arules = BasicRipple.RippleCInfo.applicable_dtacseq_of rst1 goalname;

(* 2 rules -- but none are selected -- does this mean that Flow is checked later?? *)
length (Seq.list_of arules);

val [r1,r2,r3] =  (Seq.list_of arules);

val [rst1_1] = Seq.list_of (RTechnEnv.apply_dtac_to_g r1 goalname rst1);
val [rst1_2] = Seq.list_of (RTechnEnv.apply_dtac_to_g r2 goalname rst1);

PPInterface.print_rst rst1_1;
PPInterface.print_rst rst1_2;

*}

ML {*
PPInterface.print_rst rst1_1;
PPInterface.print_rst rst1_2;
PPInterface.print_rst rst1;

val [cgoalname, sgoalname] = RState.get_goalnames rst1_1;

val [] = Seq.list_of (RippleCInfo.update goalname sgoalname rst1_1);
val [rst1_1b] = Seq.list_of (RippleCInfo.update_unrestricted goalname sgoalname rst1_1);
RippleCInfo.print rst1_1b sgoalname;
PPInterface.print_rst rst1_1b;
*}

ML {*
val [rst1_2b] = Seq.list_of (RippleCInfo.update goalname sgoalname rst1_2);
PPInterface.print_rst rst1_2b;
RippleCInfo.print rst1_2b goalname;
RippleCInfo.print rst1_2b sgoalname;
*}


ML {* 

(* both new states are blocked  -- should only really be the case for the first of them*)
(* val bl1 = RippleCInfo.blocked_chk rst1 sgoalname [rst1_1];
val bl2 = RippleCInfo.blocked_chk rst1 goalname [rst1_2];
*)

val ihn = "g1a";
val IH = RstPP.goal_concl rst1_1b ihn;
val gt = RstPP.goal_concl rst1_1b sgoalname;

TermDbg.writeterm IH;
writeln "\n-------\n";
TermDbg.writeterm gt;

*}


ML {* 
RippleCInfo.print rst1_1b sgoalname;
*}


ML {* 

val ectxt = Embed.Ectxt.init (RstPP.get_ienv rst1_1b) ParamRGraph.empty;
val [e1] = Seq.list_of (Embed.embed ectxt IH gt);

Embed.print e1;

*}



ML {* PPInterface.print_rst rst1_1; *}

ML {* 

val rst = rst1_1;
val oldgname = goalname;
val oldskels = RippleCInfo.all_skels_of rst oldgname;
val newgname = sgoalname;

local open RippleCInfo;
in
     val pplan = RState.get_pplan rst
			val arules2 = lookup_arules pplan newgname
     	val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
      val oldrelgraph = get_relgraph rst oldgname 
      val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) oldrelgraph;

      (* Create embedding for this skeleton if it
         has any in the current target. *)
      fun does_embed (n,t) target =
		      (case RippleSkel.init {ectxt=ectxt, skelterm=t,
                                 skelname=n,target=target} of 
               (* If this skeleton does not embedd at the moment *)
                 [] => [((n,t), NONE)] 
		         | (l as _::_) => map (fn e => ((n,t), SOME e)) l);
end
*}

ML {* length oldskels; 
  oldskels *}

ML {* length oldskels; 
  oldskels *}

ML {* 

map (RippleCInfo.RippleSkel.print @{context}) oldskels *}


ML {* 
PPInterface.print_rst rst;

val l = oldskels
        |> (map (fn ((n,t), skel) => 
										case skel 
							  (* No previous embedding, check if embedds in new target *)
										 of NONE => does_embed (n,t) newgoalterm
							  (* The skeleton did embed previously, get new skels *)				 
											| SOME skeleton => 
                        case RippleSkel.mk_all_next ectxt newgoalterm skeleton 
												 of [] => [((n,t), NONE)]        
													| (l as _::_) => 
														map (fn e => (RippleSkel.get_named_skel_term e,	
																					SOME e)) l ))
|> one_of_each;

*}

(* to change flow 
   - all are blocked
   - but valid rules
   - rewrite term/skeleton size is unchanged, i.e. wave front does not move
   - not blocked after rewrite
   - then change flow to allow this (but cannot back-flow or circle-flow?)

*)

ML {*

(* F(A) rewrites to G(A) *)

*)

*}



ML {*
local open BasicRipple; open RTechnEnv; in

val rst0 = PPInterface.init_rst thry ("g",
  "Callers = SetDefsIsaP.dom (call ; st |> Connected) ==> s \<notin> dom call \<Longrightarrow> Callers = dom (((call <+ {(s,(seize,[]))}) ; st) |> Connected)");
val goal = "g";
val arules = Seq.of_list (RippleCInfo.lookup_arules (RState.get_pplan rst0) goal); 
val rst1seq = Seq.maps (fn dtac => do_dtac_ripple_step dtac goal rst0) arules;

(* val rst1seq = Seq.maps (fn dtac => apply_dtac_to_g dtac goal rst0) arules; *)

val l = length (Seq.list_of rst1seq);
val _ = map PPInterface.print_rst (Seq.list_of rst1seq);
val [rst1,rst2] = (Seq.list_of rst1seq);

val arules = BasicRipple.RippleCInfo.applicable_dtacseq_of rst1 "g";

end;

*}
;





end