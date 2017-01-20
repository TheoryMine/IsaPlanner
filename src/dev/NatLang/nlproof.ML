(* Natural Language Proof *)
signature NL_PROOF =
sig

  type id_mnlp = int list
  type text_mnlp = Pretty.T
  type ttree
  
  type nl_proof_node 
  type nl_proof_tree 
  
  (* initialise a NLProofTree from a reasoning state *)
  val nlproof_tree_mk :
                   Prf.T
                   -> ttree
                   -> nl_proof_tree
  val nlproof_init : RState.T -> string -> nl_proof_tree list
  
  val uncurried_string_of_named_goal : Prf.T -> string -> string
  val vars_from_name : Proof.context -> string -> string list
  
  val nl_proof_tree_dummy : string -> nl_proof_tree
  
  val parse_tree : HTraceCInfo.tree -> HTraceCInfo.tree
  (* print and prettify *)
  val pretty_fix_nl : Proof.context -> string * typ -> Pretty.T
  val term_to_FO_string : term -> string
  
  val pretty_nlp : Proof.context -> string -> nl_proof_tree list -> Pretty.T
  val print : Proof.context -> string -> nl_proof_tree list -> unit
  
  val flatten_lemmas : string -> HTraceCInfo.tree -> ttree list
  val mk_latex_document : string -> string -> string -> Pretty.T -> Pretty.T
  
end;

use "$ISAPLANNER_DIRECTORY/src/dev/NatLang/pretty_latexification.ML";

structure NLProof : NL_PROOF =
struct

local open HTraceCInfo; open DB_APrf; open Prf; in

type id_mnlp = int list (* Is this the best way to identify nodes in the proof tree? *)
type text_mnlp = Pretty.T
  
datatype nl_proof_node = 
  NLProofNode of {proof    : Prf.T,
                  top_goal : string,
                  node_id  : int list, 
                  name     : string, 
                  text     : Pretty.T,
                  deps     : string list}
    
datatype nl_proof_tree = NLProofTree of (nl_proof_node * nl_proof_tree list)
  
fun nl_proof_tree_dummy txt = 
  NLProofTree (NLProofNode 
                 {proof    = Prf.init @{context},
                  top_goal = "dummy top goal",
                  node_id  = [], 
                  name     = "dummy name", 
                  text     = Pretty.str txt,
                  deps     = []}, []);

(* Tree and TTree functions *)

fun parse_tree (Tree ((k,rst),ch)) =
let 
  val xx = String.concat (map (fn x => x ^ " ") (RState.get_goalnames rst))
  val new_rst = DescripCInfo.prepend_str_rst xx rst
  val _ = writeln (DescripCInfo.string_of_rst new_rst)
in
  Tree ((k,new_rst), map parse_tree ch)
end
     

type D = {top_goal  : string,
          fname     : string,
          goals     : string list,
          node_id   : int list, 
          rstate    : RState.T}

datatype ttree = TTree of (D * ttree list)

fun set_top_goal g (TTree (D,ch)) = 
  TTree ({top_goal = g,
          fname = #fname D,
          goals = #goals D,
          node_id = #node_id D, 
          rstate = #rstate D}, ch)

fun set_goals gs (TTree (D,ch)) = 
  TTree ({top_goal = #top_goal D,
          fname = #fname D,
          goals = gs,
          node_id = #node_id D, 
          rstate = #rstate D}, ch)
  
fun set_node_id id (TTree (D,ch)) = 
  TTree ({top_goal = #top_goal D,
          fname = #fname D,
          goals = #goals D,
          node_id = id, 
          rstate = #rstate D}, ch)

fun set_rstate rst (TTree (D,ch)) = 
  TTree ({top_goal = #top_goal D,
          fname = #fname D,
          goals = #goals D,
          node_id = #node_id D, 
          rstate = rst}, ch)

fun list_until _ [] = []
  | list_until P (h::t) =
  if P (h::t) then [h] else h :: list_until P t
  
fun find_lem_name_in_string s =
let
  val L = String.explode s
  fun frec (h1::h2::h3::h4::h5::t) = 
      if String.implode [h1,h2,h3,h4,h5] = "lem_{" then
        h1::h2::h3::h4::h5 :: list_until (fn l => str (hd l) = "}") t
      else frec (h2::h3::h4::h5::t)
    | frec _ = []
in
  String.implode (frec L)
end

fun find_induction_var_in_rstname s =
  (nth (space_explode " " s) 2)

fun find_and_kill_lemmas (TTree (D,ch)) = 
let 
  val ch' = 
    if String.isSubstring RstName.lemcalc_str (DescripCInfo.string_of_rst (#rstate D)) 
    then tl ch
    else map find_and_kill_lemmas ch
in TTree (D,ch')
end

(* returns a list of lemmas (the order is as they appear in the flattened tree, 
   which is the reverse of how they should appear in the readable proof) *)
fun prune_lemmas (TTree (D,ch)) = 
let
  val rst = #rstate D
  val xlems = List.concat (map prune_lemmas ch)
in
  if String.isSubstring RstName.lemcalc_str (DescripCInfo.string_of_rst rst)
  then 
    let 
      val (TTree (D',ch')) = hd ch
      val (TTree (D'',_)) = hd ch'
      val tt = TTree (D'',map find_and_kill_lemmas (tl ch'))
                |> set_node_id (#node_id D')
      val _ = if null ch orelse length ch > 2
              then raise ERROR ("Oh, no!"^(Int.toString (length ch))) 
              else ()
    in tt :: xlems 
    end
  else xlems
end

fun filter_ends [] =  []
  | filter_ends ((Tree ((k,rst),ch))::t) = 
  if String.isSubstring "End" (DescripCInfo.string_of_rst rst) 
     orelse String.isSubstring "Solved!" (DescripCInfo.string_of_rst rst)
  then filter_ends t 
  else (Tree ((k,rst),ch))::(filter_ends t)

(* removes some redundancy in the trace tree, adds name of top goal 
   (calling a lema updates the top goal) and ID *)
(* TODO: current goals should be correct*)
fun restructure_tree fnm t = 
  restructure_tree_rec fnm "g1" [] 0 t
  
and restructure_tree_rec fnm tg id i (Tree ((_,rst),ch)) = 
  if null ch then 
      TTree ({top_goal = tg, fname = fnm, node_id = i::id, goals = RState.get_goalnames rst, rstate = rst}, [])
  else
    let 
      val rch = rev (filter_ends ch)
      val (Tree ((_,rst'),ch')) = hd rch
      val id_upd = i::id
      
      val _ = if null ch' then () else raise ERROR "WHAT?"
      val ngs = RState.get_goalnames rst'
      val D = {top_goal = tg, fname = fnm, node_id = id_upd, goals = ngs, rstate = rst'}
      
      val xtg = if String.isSubstring RstName.induct_ripple_lemcalc_str (DescripCInfo.string_of_rst rst')
                then (writeln"oi!";find_lem_name_in_string (DescripCInfo.string_of_rst rst'))
                else tg
    in 
        TTree (D, map_numbering 0 (restructure_tree_rec fnm xtg id_upd) (tl rch))
    end

fun flatten_lemmas fnm T =
  let val (TTree (D,ch)) = restructure_tree fnm T
  in (TTree (D, map find_and_kill_lemmas ch)) :: prune_lemmas (TTree (D,ch))
  end

  
fun rstate_of_ttree (TTree (D,_)) = #rstate D
fun hand_goals_down full_prf (TTree (D,ch)) =
let
  val rst = #rstate D
  val xch = 
    if String.isSubstring RstName.induction_on_str (DescripCInfo.string_of_rst rst) 
    then 
      let val x1 = get_ndname_lasms full_prf (hd (#goals D))
          val x2 = get_ndname_lasms full_prf (hd (tl (#goals D)))
          val Gs = if length x1 < length x2 
                   (* This IF distinguishes between the step case and base case
                      by checking which one has more assumptions. Step has IH, so 
                      it should be larger. *)
                   then [(hd (#goals D)),(hd (tl (#goals D)))] 
                   else [(hd (tl (#goals D))),(hd (#goals D))]
      in ([set_goals [hd Gs] (hd ch), set_goals [hd (tl Gs)] (hd (tl ch))])
      end
    else ch
in
  TTree (D, map (hand_goals_down full_prf) xch)
end

fun mk_ttrees full_prf fnm T =
   map (hand_goals_down full_prf) (flatten_lemmas fnm T)

(* convert type name from T_xy to T_{xy} *) 
fun fix_typ_name t = 
  if t = "nat" orelse t = "Nat.nat" then "\\mathbb{N}"
  else if  t = "bool" orelse t = "HOL.bool" then "\\mathbb{B}"
  else if String.isPrefix "'" t then 
    fix_typ_name (String.implode (tl (String.explode t)))
  else if length (space_explode "_" t) > 1 then 
    String.concat
     ([hd (space_explode "_" t), "_{"] @ (tl (space_explode "_" t)) @ ["}"])
  else t

(* convert variables like bool1 to b_1 *) 
fun fix_vars_name v = 
  if String.isPrefix "nat" v then 
    let val x = if v = "nat" then "0" else (String.extract (v,3,NONE)) 
    in "n_{"^x^"}" 
    end
  else if String.isPrefix "bool" v then 
    let val x = (if v = "bool" then "0" else (String.extract (v,4,NONE)))
    in "b_{"^x^"}" 
    end
  else if String.isPrefix "?" v then 
    fix_vars_name (String.implode (tl (String.explode v)))
  else if String.size v > 1 then 
    let val (h::t) = map str (String.explode (hd (space_explode "." v)))
    in String.concat ([h, "_{\\mbox{\\tiny "] @ t @ ["}}"])
    end
  else v
    
fun fix_const_name c =
  case space_explode "_" c of 
     "f" :: ft => "f_{"^int_to_greek (int_of_string (String.concat ft))^"}"
   | "C" :: ft => "C_{"^int_to_abc (int_of_string (String.concat ft))^"}"
   | _ => c
   
   (*
fun fix_vars_in_term (t:term) = 
  case t of 
    (t1 $ t2) => (fix_vars_in_term t1) $ (fix_vars_in_term t2)
  | (Free (n,tt)) => (Free (fix_vars_name n,tt))
  | (Var ((n,i),tt)) => (Var ((fix_vars_name n,i),tt))
  | t => t

fun fix_consts_in_term (t:term) = 
  case t of 
    (t1 $ t2) => (fix_consts_in_term t1) $ (fix_consts_in_term t2)
  | (Const (c,tt)) => (Const (fix_const_name c,tt))
  | t => t
  *)
  
fun fix_vars_and_consts_in_term (t:term) = 
  case t of 
    (t1 $ t2) => (fix_vars_and_consts_in_term t1) $ (fix_vars_and_consts_in_term t2)
  | (Free (n,tt)) => (Free (fix_vars_name n,tt))
  | (Var ((n,i),tt)) => (Var ((fix_vars_name n,i),tt))
  | (Const (c,tt)) => (Const (fix_const_name c,tt))
  | t => t

(* Convert a term to its first-order string representation, including changing variables like booln to b_{n} 
   Removes abstraction! *)
fun term_to_FO_string (t:term) = 
  let
    val (h,args) = Term.strip_comb t;
    val sargs = map (term_to_FO_string) args;
  in 
    case t of 
    (Const ("HOL.Not",_)) $ (Const ("HOL.eq",_) $ t1 $ t2) => 
      if term_to_FO_string t1 < term_to_FO_string t2 then 
        term_to_FO_string t1 ^ " \\neq " ^ term_to_FO_string t2
      else 
        term_to_FO_string t2 ^ " \\neq " ^ term_to_FO_string t1
        (*
    | (Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_)) $ ((Const ("Nat.Suc",_)) $ ((Const ("Nat.Suc",_)) $ ((Const ("Nat.Suc",_)) $ t))))))) => "("^term_to_FO_string t ^ " + 6)"
    | (Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_)) $ ((Const ("Nat.Suc",_)) $ ((Const ("Nat.Suc",_)) $ t)))))) => "("^term_to_FO_string t ^ " + 5)"
    | (Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_)) $ ((Const ("Nat.Suc",_)) $ t))))) => "("^term_to_FO_string t ^ " + 4)"
    | (Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_) $ ((Const ("Nat.Suc",_)) $ t)))) => "("^term_to_FO_string t ^ " + 3)"
    | (Const ("Nat.Suc",_) $ (Const ("Nat.Suc",_) $ t)) => "("^term_to_FO_string t ^ " + 2)"
    | (Const ("Nat.Suc",_)) $ t => "("^term_to_FO_string t ^ " + 1)"
    *)
    | _ => 
      if null args then 
        (case h of 
           (Const (n,_)) => if Long_Name.base_name n = "zero" then "0" 
                             else Long_Name.base_name n
         | (Free (n,_)) => n |> fix_vars_name
         | (Var (n,_)) => Term.string_of_vname n
         | (Bound _) => "what?"
         | _ => raise ERROR "Imposible to reach a term"
        )
      else
        (case (h,sargs) of 
           (Const ("HOL.eq",_), [s1,s2]) => s1 ^ " = " ^ s2
         | (Const ("eq",_), [s1,s2]) => s1 ^ " = " ^ s2
         | (Const ("Set.member",_), [s1,s2]) => s1 ^ " \\in " ^ s2
         | (Const ("Nat.Suc",_), [s]) => "{\\tt{Suc}}("^s^")"
         | (Const ("HOL.Trueprop",_), [s]) => s
         | (Const ("HOL.Not",_), [s]) => "\<not>" ^ s
         | (Const (c,_), _) => (let val cc = List.last (space_explode "." c) in
           if "f" = hd (space_explode "_" cc) orelse "C" = hd (space_explode "_" cc) then 
             (fix_const_name cc)
                  ^ (if null sargs then "" else "(" ^ (commas sargs) ^ ")")
           else 
             (term_to_FO_string h) 
                  ^ (if null sargs then "" else "(" ^ (commas sargs) ^ ")") end)
         | _ => (term_to_FO_string h) 
                  ^ (if null sargs then "" else "(" ^ (commas sargs) ^ ")")
        )
  end;

  
fun term_to_FO_string_align_eqs (t:term) = 
  let
    val (h,args) = Term.strip_comb t;
    val sargs = map (term_to_FO_string) args;
  in 
    if null args then 
      (case h of 
         (Const (n,_)) => if Long_Name.base_name n = "zero" then "0" 
                           else Long_Name.base_name n
       | (Free (n,_)) => n |> fix_vars_name
       | (Var (n,_)) => Term.string_of_vname n
       | (Bound _) => "what?"
       | _ => raise ERROR "Imposible to reach a term"
      )
    else
      (case (h,sargs) of 
         (Const ("HOL.eq",_), [s1,s2]) => s1 ^ " &= " ^ s2
       | (Const ("eq",_), [s1,s2]) => s1 ^ " &= " ^ s2
       | (Const ("Set.member",_), [s1,s2]) => s1 ^ " &\\in " ^ s2
       | (Const ("HOL.Trueprop",_), [s]) => s
       | (Const ("HOL.Not",_), [s]) => "\<not>" ^ s
       | (Const (c,_), _) => 
         if "f" = hd (space_explode "_" c) orelse "C" = hd (space_explode "_" c) then 
           (fix_const_name c)
                ^ (if null sargs then "" else "(" ^ (commas sargs) ^ ")")
         else 
           (term_to_FO_string h) 
                ^ (if null sargs then "" else "(" ^ (commas sargs) ^ ")")
       | _ => (term_to_FO_string h) 
                ^ (if null sargs then "" else "(" ^ (commas sargs) ^ ")")
      )
  end;
  
(* methods *)
fun mname0 (Meth (optmeth,_)) = optmeth
  | mname0 AsmMeth = MOpen

fun methkind_string MOpen = "open"
  | methkind_string (MClosed (MKindRes g, _)) = ("from_result: " ^ g)
  | methkind_string (MClosed (MKindSubst g, _)) = ("from_result: " ^ g)
  | methkind_string (MClosed (MKindPrf (mname,prf), _)) = mname
  | methkind_string (MClosed (MKindThm th, _)) = "from theorem: " ^ (Thm.get_name_hint th)
  | methkind_string (MClosed (MKindTac (th,(tac,p)), _)) =
    String.concat [ "from tactic: ", Pretty.string_of p]

fun ref_aux_result mname = 
  if String.isPrefix "subst " mname 
     orelse String.isPrefix "subst_w_thm: " mname 
     orelse String.isPrefix "rule " mname 
     orelse String.isPrefix "from_result: " mname
  then commas (tl (space_explode " " mname))
  else ""

fun ref_aux_thms mname = 
  if String.isPrefix "subst_w_thm: " mname 
  then 
    tl (space_explode " " mname)
  else []


fun deps_of_mth m = 
  ref_aux_thms (methkind_string (mname0 m))
  
fun resulting_gnames_from_meth MOpen = []
  | resulting_gnames_from_meth (MClosed (_, sg)) = sg
  
fun string_of_meth_and_result meth = 
  (ref_aux_result (methkind_string (mname0 meth)), resulting_gnames_from_meth (mname0 meth))
  
  
fun get_goal_and_meth full_prf (TTree (D,_)) =
let 
  val mth = map (get_ndname_meth full_prf) (#goals D)
  val gs =  (#goals D)
  val _ = if length mth > 1 orelse length gs > 1 then raise ERROR "more than one goal during rippling" else ()
in 
  if null mth orelse null gs
  then NONE
  else SOME (hd gs, hd mth)
end

fun get_goals_and_meths_rippling full_prf (TTree (D,ch)) =
  case get_goal_and_meth full_prf (TTree (D,ch)) of 
    NONE => List.concat (map (get_goals_and_meths_rippling full_prf) ch)
  | SOME X => X :: List.concat (map (get_goals_and_meths_rippling full_prf) ch)
    
fun reference_the_method mth = 
  let 
    fun last_two [] = []
      | last_two [h] = [h]
      | last_two [h1,h2] = [h1,".",h2]
      | last_two (_::t) = last_two t
    val s = fst (string_of_meth_and_result mth)
    val x = String.concat (last_two (space_explode "." s))
    val rf = if String.isSubstring "lem_" s 
             then "\\mbox{\\color{gray}{by Lemma \\ref{" ^ find_lem_name_in_string s ^ "}}}" 
             else if s = "" then "\\mbox{\\color{gray}{trivial}}"
             else "\\mbox{\\color{gray}{by (\\ref{" ^ x ^ "})}}" 
  in rf
  end

fun string_results_from_method mth = snd (string_of_meth_and_result mth)

fun print_meths_and_results _ [] = []
  | print_meths_and_results full_prf ((g,mth)::t) = 
let 
  val trm = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g
in
  writeln ("Goal name: " ^ g)
  :: writeln ("Term: " ^ (term_to_FO_string trm))
  :: writeln ( "Method: " ^ reference_the_method mth )
  :: writeln ("Results: [" ^ commas (string_results_from_method mth) ^ "]")
  :: writeln ("------ ")
  :: print_meths_and_results full_prf t
end


fun pair_from_eq_term t =
  let 
    val (h,args) = Term.strip_comb t;
  in 
    case (h,args) of 
      (Const ("op =",_), [s1,s2]) => (s1,s2)
    | (Const ("HOL.eq",_), [s1,s2]) => (s1,s2)
    | (Const ("eq",_), [s1,s2]) => (s1,s2)
    | _ => raise TERM ("Term is not equality! ",[t])
   end

fun Uchain_from_gs_rec full_prf ((g1,m1)::(g2,m2)::t) = 
  let
    val t1 = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g1
    val t2 = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g2
    val (a1,b1) = pair_from_eq_term t1
    val (a2,_) = pair_from_eq_term t2
  in
    if a1 = a2 
    then (Uchain_from_gs_rec full_prf ((g2,m2)::t)) @ [(b1,m1)] 
    else (a2,m1) :: Uchain_from_gs_rec full_prf ((g2,m2)::t)
  end
| Uchain_from_gs_rec full_prf [(g,m)] =
  let 
    val t = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g
    val (a,b) = pair_from_eq_term t 
  in (if a = b then [] else [(b,m)])
  end
| Uchain_from_gs_rec _ [] = []
  
and map_eq_align_tabs [] = []
  | map_eq_align_tabs [(x,m)] =
    [String.concat ["&= ", ( term_to_FO_string) x, 
                    " &", reference_the_method m]]
  | map_eq_align_tabs ((x,m)::t) =
    String.concat ["&= ", ( term_to_FO_string) x, 
                   " &", reference_the_method m, "\\\\"]::map_eq_align_tabs t

and Uchain_from_gL _ [] = []
  | Uchain_from_gL full_prf ((g,m)::L) =
  let 
    val t = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g
    val (a,_) = pair_from_eq_term t
    val xL = Uchain_from_gs_rec full_prf ((g,m)::L)
  in 
    term_to_FO_string a :: map_eq_align_tabs xL
  end

fun make_Uchain_align full_prf tL =
  Pretty.chunks 
    (latex_env "align*" "" (map Pretty.str (Uchain_from_gL full_prf tL)))

fun make_Uchain_align_ref g full_prf tL =
  Pretty.chunks (
    [Pretty.str "\\begin{align*}"]
    @ (map Pretty.str (Uchain_from_gL full_prf tL))
    @ [Pretty.str ("\\numberthis \\label{"^g^"}")]
    @ [Pretty.str "\\end{align*}"])
     

fun break_into_chainable_lists full_prf L =
  let
    fun frec ((g1,m1)::T1) [] = frec T1 [[(g1,m1)]]
      | frec [] T = T
      | frec _ ([]::_) = raise ERROR "impossible use of break_into_chainable_lists!"
      | frec ((g1,m1)::T1) (((g2,m2)::T2)::T) = 
    let 
      val t1 = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g1
      val t2 = (HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g2
      val (a1,b1) = pair_from_eq_term t1
      val (a2,b2) = pair_from_eq_term t2
    in  
      if not (a1 = a2) andalso not (b1 = b2) 
      then frec T1 ([(g1,m1)]::((g2,Meth (MClosed (MKindSubst g1, []),Goaln.NSet.empty))::T2)::T)
      else frec T1 (((g1,m1)::(g2,m2)::T2)::T)
    end
  in
    (map rev (frec L []))
  end
  
fun make_Uchains full_prf L = 
  map (make_Uchain_align full_prf) (break_into_chainable_lists full_prf L)
  
fun make_and_display_Uchains full_prf L = 
let 
  fun frec [] = []
    | frec [h] = 
       [Pretty.str "Ultimately, we can show IG$_{\\thesection}$ as follows:",
       make_Uchain_align full_prf h]
    | frec (((g,m)::L)::t) =
       [Pretty.str "Moreover, we have the following:",
       make_Uchain_align_ref g full_prf ((g,m)::L)] @ frec t
in
  case break_into_chainable_lists full_prf L of 
    [] => [Pretty.str "This is trivial"]
  | ([]::_) => raise ERROR "impossible output from break_into_chainable_lists in make_and_display_Uchains!"
  | [((g,m)::L)] => 
      [Pretty.str "We show this with the following chain of equalities: ", 
       make_Uchain_align full_prf ((g,m)::L)]
  | ((g,m)::L)::T => 
      [Pretty.str "First, notice that the following is true: ", (*\\begin{align*}\\label{U1}", 
       Pretty.str ((term_to_FO_string o HOLogic.dest_Trueprop o (get_ndname_ctrm full_prf)) g), 
       Pretty.str "\\end{align*}",
       Pretty.str "as follows: ",*)
       make_Uchain_align_ref g full_prf ((g,m)::L)] 
      @ frec T
end
    
fun remove_schematic x = String.explode x |> filter (not o (equal "?") o str) |> String.implode

fun pretty_thmL_from_fname ctxt fname =
let
  val ft = fname^".simps"
  val tL = ft |> Proof_Context.get_thms ctxt
                 |> map (remove_schematic 
                         o term_to_FO_string_align_eqs
                         o HOLogic.dest_Trueprop 
                         o Thm.full_prop_of ) (* pretty_thm *)
  val l = length tL
  fun ap i t = t ^ " \\label{" ^ ft ^ "_" ^ string_of_int i ^ "}" 
               ^ (if i = l then "" else "\\\\")
  val xL = map Pretty.str (map_numbering 1 ap tL)
in
  latex_env "align" "" xL
end
    
fun uncurried_string_of_named_goal prf = 
  term_to_FO_string o HOLogic.dest_Trueprop o (get_ndname_ctrm prf)

fun pretty_tfix_nl thry (n,srt) =  
  let val t = Pretty.string_of (Trm.pretty_sort thry srt)
  in
    (Pretty.block 
      [if String.isPrefix "type" t then Pretty.str "set" else Pretty.str t, 
       Pretty.str " ", 
       TFree.pretty_name n]
    )
  end;

fun pretty_fix_nl thry (n,typ) = (* includes naturals, booleans and lists *)
  let 
    val k = fix_typ_name (Old_Datatype_Aux.name_of_typ typ) 
    val t = if k = "" then Pretty.string_of (Trm.pretty_typ thry typ) else k
  in
     Pretty.block 
      [Pretty.str "\\forall\\hspace{1pt} ", 
       Free.pretty_name (fix_vars_name n), 
       Pretty.str " ",
       if String.isPrefix "nat" t orelse String.isPrefix "Nat.nat" t then 
         Pretty.str "\\in \\mathbb{N}"
       else if String.isPrefix "bool" t orelse String.isPrefix "HOL.bool" t then 
         Pretty.str "\\in \\mathbb{B}"
       else if length (space_explode "." t) > 1 then 
         Pretty.str (String.concat ("\\in "::(tl (space_explode "." t))))
       else 
         let val explodes = (space_explode " " t)
         in 
           if length explodes > 1 andalso String.isPrefix "list" (hd (tl explodes)) then 
             Pretty.str ((hd explodes)^" - list")
           else Pretty.str ("\\in " ^ t )
         end
      ]
  end;
 

fun pretty_fix_nl_english thry (n,typ) = (* includes naturals, booleans and lists *)
  let 
    val k = fix_typ_name (Old_Datatype_Aux.name_of_typ typ)
    val t = if k = "" then Pretty.string_of (Trm.pretty_typ thry typ) else k
  in
     Pretty.block 
      [Pretty.str "$", 
       Free.pretty_name (fix_vars_name n), (*
       if "nat" = t orelse "Nat.nat" = t then 
         Pretty.str "$ natural number"
       else if "bool" = t orelse "HOL.bool" = t then 
         Pretty.str "$ boolean"
       else *)
         let val spex = space_explode " " t 
             val dotex = space_explode "." t 
             val tt = if length dotex > 1 then List.last dotex else t
         in 
           if length spex > 1 then 
             Pretty.str ((String.concat (tl spex)) ^ " with elements of" ^ (hd spex)) 
           else Pretty.str (" \\in " ^ tt ^ "$")
         end
      ]
  end;

(* with types/sorts *)
fun prettyL_fixes_nl context ptab = 
    let
      val tvsL = rev (Trm.TypParams.get_plist (Cx.get_typps_of_ptab ptab))
      val vsL = rev (Trm.TrmParams.get_plist (Cx.get_trmps_of_ptab ptab))
      val fix_typesPL = 
          if null tvsL then [] else 
          [Pretty.block (pretty_dots (map (pretty_tfix_nl context) tvsL))]
      val fixPL = 
          if null vsL then [] else 
          [Pretty.block (pretty_dots (map (pretty_fix_nl context) vsL))]
    in if null fix_typesPL andalso null fixPL then []
       else if null fix_typesPL orelse null fixPL then 
              [pretty_sep_block " " (fix_typesPL @ fixPL)]
       else [pretty_sep_block " \\mbox{and} " (fix_typesPL @ fixPL)]
    end;

fun prettyL_fixes_nl_english caps context ptab = 
    let
      val tvsL = rev (Trm.TypParams.get_plist (Cx.get_typps_of_ptab ptab))
      val vsL = rev (Trm.TrmParams.get_plist (Cx.get_trmps_of_ptab ptab))
      val fix_typesPL = 
          if null tvsL then [] else 
          [Pretty.block
             [Pretty.str ((if caps then "F" else "f")^"or every "), 
              Pretty.block (pretty_commas_and (map (pretty_tfix_nl context) tvsL))]]
      val fixPL = 
          if null vsL then [] else 
          [Pretty.block 
             [Pretty.str ((if caps then "F" else "f")^"or every "), 
              Pretty.block (pretty_commas_and (map (pretty_fix_nl_english context) vsL))]]
    in if null fix_typesPL andalso null fixPL then []
       else if null fix_typesPL orelse null fixPL then 
              [pretty_sep_block " " (fix_typesPL @ fixPL)]
       else [pretty_sep_block " \\mbox{and} " (fix_typesPL @ fixPL)]
    end;
    
fun pretty_type_nl typ = 
let
    val t = fix_typ_name (Old_Datatype_Aux.name_of_typ typ)
    val dotex = space_explode "." t 
in 
  Pretty.str (if length dotex > 1 then String.concat (tl dotex) else t)
end
    
fun pretty_var_in_set (n,typ) = (* includes naturals, booleans and lists *)
  let 
    val tt = pretty_type_nl typ
  in
     Pretty.block 
      [Pretty.str "$", Free.pretty_name (fix_vars_name n), 
       Pretty.str " \\in ", tt, Pretty.str "$"]
  end;
  
fun pretty_vars_in_sets vsL = 
    let
      val fixPL = 
          if null vsL then [] else 
            [Pretty.block (pretty_commas_and (map pretty_var_in_set vsL))]
    in if null fixPL then []
       else if null fixPL then [pretty_sep_block " " (fixPL)]
       else [pretty_sep_block " \\mbox{and} " (fixPL)]
    end;
    
fun pretty_and_fixes context ptab = 
    let
      val tvsL = rev (Trm.TypParams.get_plist (Cx.get_typps_of_ptab ptab))
      val vsL = rev (Trm.TrmParams.get_plist (Cx.get_trmps_of_ptab ptab))
      val fix_typesPL = 
          if null tvsL then [] else 
          [Pretty.block
             [Pretty.block (pretty_commas_and (map (pretty_tfix_nl context) tvsL))]]
      val fixPL = 
          if null vsL then [] else 
          [Pretty.block 
             [Pretty.block (pretty_commas_and (map (pretty_fix_nl_english context) vsL))]]
    in if null fix_typesPL andalso null fixPL then []
       else if null fix_typesPL orelse null fixPL then 
              [pretty_sep_block " " (fix_typesPL @ fixPL)]
       else [pretty_sep_block " \\mbox{and} " (fix_typesPL @ fixPL)]
    end;

    
fun pretty_qfixes prf gname = 
    let
      val cxs = get_ndname_cx prf gname
      val fixes = Cx.get_lfixes cxs
      val f = prettyL_fixes_nl
    in
      (Pretty.block o (f (get_context prf))) fixes
    end  

fun pretty_qfixes_english caps prf gname = 
    let
      val cxs = get_ndname_cx prf gname
      val fixes = Cx.get_lfixes cxs
      val f = prettyL_fixes_nl_english caps
    in
      (Pretty.block o (f (get_context prf))) fixes
    end
    
fun vars_from_name ctxt thmname = 
    let
      val trms = map Thm.full_prop_of (Proof_Context.get_thms ctxt thmname)
      val vars = maps (fn x => Term.add_vars x []) trms 
                  |> map (remove_schematic o Term.string_of_vname o fst)
    in
      remove_duplicates (rev vars)
    end

(* Pretty printing functions *)
fun pretty_id_of_mnlp (NLProofNode D) =
    Pretty.unbreakable (Pretty.list "[" "] " (map Pretty.str (map Int.toString (rev (#node_id D)))))
    
fun pretty_nl_proof_node (NLProofNode D) = #text D
    
fun pretty_top_goal env (NLProofTree (NLProofNode D,_)) = 
let
  val prf = #proof D
  val tpg = #top_goal D
  val s = Pretty.str ("\\[" ^ uncurried_string_of_named_goal prf tpg ^ "\\]")
  val label = "\\label{"^tpg^"}"
in
  Pretty.chunks
    (latex_env env label [pretty_qfixes_english true prf tpg, s])
end
    
(* pretty trees with and all children *)
fun pretty_nlp_tree (NLProofTree (mnlp, ch)) = 
let 
  val pretty_node = 
    Pretty.block [Pretty.str "%", 
                  pretty_id_of_mnlp mnlp,
                  Pretty.chunks [Pretty.str "",
                                 pretty_nl_proof_node mnlp
                                 ]
                  ]
in
  Pretty.chunks (pretty_node :: (map (pretty_nlp_tree) ch))
end

fun mk_latex_document title author date document = 
  Pretty.chunks 
    ((map Pretty.str ["\\documentclass{article}",
                     "\\usepackage{amsmath,amsthm,amssymb}",
                     "\\newcommand\\numberthis{\\addtocounter{equation}{1}\\tag{\\theequation}}",
                     "\\usepackage{color}",
                     "\\usepackage[letterpaper, margin=3.8cm]{geometry}",
                     "\\definecolor{gray}{gray}{0.4}",
                     "\\newtheorem*{theorem}{Theorem}",
                     "\\newtheorem{lemma}{Lemma}",
                     "\\theoremstyle{definition}",
                     "\\newtheorem{definition}{Definition}",
                     "",
                     "\\title{"^title^"}",
                     "\\author{"^author^"}",
                     "\\date{"^date^"}",
                     "",
                     "\\begin{document}",
                     "\\maketitle",
                     ""])
    @ [document, Pretty.str "", Pretty.str "\\end{document}"])
    
fun pretty_typ typ =
    let
      val (arg_tys, concl_ty) = Term.strip_type typ
      fun is_compound_typ ty = case Term.strip_type ty of ([],_) => false | _ => true;
      val pretty_args = map (fn ty => if is_compound_typ ty
                                      then Pretty.list "(" ")" [Pretty.str (fix_typ_name (Old_Datatype_Aux.name_of_typ ty)) (*Trm.pretty_typ ctxt ty*)]
                                      else Pretty.block [Pretty.str (fix_typ_name (Old_Datatype_Aux.name_of_typ ty)) (*Trm.pretty_typ ctxt ty*)]) arg_tys
      val concl_pretty = (case concl_ty of Type("HOL.bool", _) => Pretty.str "\\mathbb{B}"
                                        | Type("Nat.nat", _) => Pretty.str "\\mathbb{N}"
                                        | _ => Pretty.str (fix_typ_name (Old_Datatype_Aux.name_of_typ concl_ty)) (*Trm.pretty_typ ctxt concl_ty*))
    in
      if is_compound_typ typ then
        Pretty.block
            ((Pretty.separate " \\times " pretty_args)
            @ [Pretty.str " \\to ", concl_pretty])
      else concl_pretty
    end
    
fun ground_typs_of_typ typ =
    let
      val (arg_tys, concl_ty) = Term.strip_type typ
    in
      remove_duplicates (concl_ty :: arg_tys)
    end
    
fun get_deps_from_nlproof_tree (NLProofTree (NLProofNode aD,ach)) = 
  (#deps aD) @ List.concat (map get_deps_from_nlproof_tree ach)
  
fun dest_alls (Const ("Pure.all",x) $ Abs (v,typ,t)) = 
  snd (Logic.dest_all (Const ("Pure.all",x) $ Abs (v,typ, dest_alls t)))
  | dest_alls t = t
  
fun get_concl (Const ("Pure.imp",x) $ p $ c) = c
  | get_concl t = t
  
fun betareduce ((Abs (x,ty,t)) $ tt) = betapply (Abs (x,ty,t), betareduce tt)
  | betareduce (t1 $ t2) = (betareduce t1) $ (betareduce t2)
  | betareduce t = t
    
fun define_set_from_type ctxt tn =
let
  val tname = (*if tn = "Nat.nat" orelse tn = "nat" then "\\mathbb{N}"
              else if tn = "HOL.bool" orelse tn = "bool" then "\\mathbb{B}"
              else*) tn
  val x = hd (Sledgehammer_Util.thms_of_name ctxt (tname^".induct"))
  val typ = Proof_Context.read_typ ctxt tname
  val ft = Proof_Context.read_typ ctxt (tname ^ " => bool")
  val trm = Syntax.read_term ctxt ("\<lambda> x::"^ tname ^". x \<in> " ^ tname)
  val inst_thm = Thm.certify_instantiate ([],[((("P",0), ft), trm)]) x
  val terms = Thm.prems_of (inst_thm)
  
  fun get_qvars term = 
  case term of 
    Const ("Pure.all",_) $ Abs (v,typ,t) => (v,typ) :: get_qvars t
  | _ => []
  
  fun get_qvars_and_dest_alls t = (get_qvars t, betareduce (get_concl (dest_alls t)))
  val p = map get_qvars_and_dest_alls terms
(*  
  fun qvars vs = Pretty.block ([Pretty.str "if "]@(pretty_vars_in_sets vs)@[Pretty.str " then "])

  fun prettify_vars_and_term (vs,trm) = 
    Pretty.block [Pretty.str "\\item ", qvars vs, 
                  Pretty.str "$", Pretty.str (term_to_FO_string trm), Pretty.str "$"]
  
  val all_pretty = map prettify_vars_and_term p*)

  fun get_const (Const (c,_)) = (List.last (space_explode "." c), Term.type_of (Syntax.read_term ctxt c))
    | get_const (t1 $ t2) = get_const t2 handle _ => get_const t1
    
  (* THIS IS A REALLY CONVOLUTED WAY OF GETTING THE CONSTRUCTORS, BUT IT WORKS FOR THE MOMENT *)
  val constructors = map (get_const o snd) p
  val gtyps_of_const = maps (ground_typs_of_typ o snd) constructors
  
  val bool_appears = in_list @{typ HOL.bool} gtyps_of_const 
  val bool_def = 
    if bool_appears 
    then [Pretty.str "Let $\\mathbb{B} = \\{\\lozenge, \\blacklozenge \\}$ where $\\lozenge \\neq \\blacklozenge$. "] 
    else []
  val nat_appears = in_list @{typ Nat.nat} gtyps_of_const 
  val nat_def = 
    if nat_appears 
    then [Pretty.str "Let $\\mathbb{N}$ be the set of natural numbers, with ${\\tt Suc}$ the \\textit{successor} function. "]
    else []
  
  val extra_typ_defs = bool_def @ nat_def
  val constructors_str = map (fix_const_name o fst) constructors
  val constructors_str_math = map (string_latex_mathmode o fix_const_name o fst) constructors
  
  fun pretty_const_and_type (c,ty) = 
    Pretty.block [Pretty.str "$",
                  Pretty.str (fix_const_name c), 
                  Pretty.str " : ",
                  pretty_typ ty,
                  Pretty.str "$"]
    
  val distinct_thmN = tname^".distinct"
  val distinct_terms = map (fix_vars_and_consts_in_term o Thm.prop_of) (Sledgehammer_Util.thms_of_name ctxt distinct_thmN)
  fun treat_vars s = "$"^ fix_vars_name s^"$"
  val pretty_math_terms = map Pretty.str (remove_duplicates (map (string_latex_mathmode o remove_schematic o term_to_FO_string) distinct_terms))
  fun math_terms t = Pretty.str ((string_latex_mathmode o (remove_schematic o term_to_FO_string)) t)
  val pretty_distinct_thm = 
    Pretty.block (Pretty.str ("\\item for every " ^ (commas_and (map treat_vars (vars_from_name ctxt distinct_thmN))) ^ ", we have ")
                  :: pretty_commas_and pretty_math_terms)
    
in 
   [Pretty.block (extra_typ_defs @ [Pretty.str ("Let $"^ fix_typ_name tname ^"$ be a set and " )]
                  @ (pretty_commas_and (map pretty_const_and_type constructors))
                  @ [Pretty.str (" functions such that all of the following conditions are met: ")]),
    Pretty.str "\\begin{itemize}",
    Pretty.str ("\\item " ^ commas_and constructors_str_math ^ " are injective, "), 
    Pretty.block [pretty_distinct_thm, Pretty.str ","],
    Pretty.str ("\\item $"^ fix_typ_name tname ^"$  is \\textit{covered} by " ^ commas_and constructors_str_math 
                ^ " (i.e., $"^ (sep_with_string (map (fn x => "\\mbox{\\it image}("^x^")") constructors_str) "\\cup") 
                ^ " = " ^ fix_typ_name tname ^"$)\\footnote{This fact allows us to prove theorems about all the elements of $" 
                ^ fix_typ_name tname ^ "$ by induction over the structure given by " ^ commas_and constructors_str_math ^ ".}.")
    ]
   @ [Pretty.str "\\end{itemize}", Pretty.str "" ]
end

fun pretty_nlp ctxt fname L =
  let 
    val (h::t) = L
    fun state_and_prove thm_env x = 
      Pretty.chunks [pretty_top_goal thm_env x, 
                     Pretty.str "\\begin{proof}", 
                     pretty_nlp_tree x, 
                     Pretty.str ("Thus we conclude the proof of this " ^ thm_env ^ "."),
                     Pretty.str "\\end{proof}"]

    val ftyp = Term.type_of (Syntax.read_term ctxt fname)
    val all_grtyps = map Old_Datatype_Aux.name_of_typ (ground_typs_of_typ ftyp)
    val grtyps = 
      filter 
        (fn x => not (x = "nat" orelse x = "Nat.nat" orelse x = "bool" orelse x = "HOL.bool"))
          all_grtyps
    
    val pretty_type_def = maps (define_set_from_type ctxt) grtyps
    
    val fname_new = fix_const_name fname
    
    val pretty_fun_def = [Pretty.str "\\noindent Then we can proceed to define a function over this set.", 
                          Pretty.str "",
                          Pretty.str "\\begin{definition}",
                          Pretty.block [Pretty.str ("Let $" ^ fname_new ^ " : "), 
                                       pretty_typ ftyp, 
                                       Pretty.str "$ be the recursive function determined by the following equations (for any ",
                                       Pretty.str (commas_and (map string_latex_mathmode (vars_from_name ctxt (fname^".simps")))),
                                       Pretty.str "): "]]
                        @ pretty_thmL_from_fname ctxt fname
                        @ [Pretty.str "\\end{definition}", Pretty.str ""]
    
    val pretty_lemmas = if null t then [] 
                        else [Pretty.str "\\section{The Lemmas}", 
                              Pretty.str "We begin by proving some necessary lemmas."] 
                           @ (map (state_and_prove "lemma") (rev t))
    val pretty_thm_section = [Pretty.str "\\section{The Theorem}",
                           if null t 
                             then Pretty.str "" 
                              else Pretty.str "In this section we prove the main result of this article.",
                           state_and_prove "theorem" h]
  in
    mk_latex_document "My paper title"
                      "My name"
                      "The date"
                      (Pretty.chunks (pretty_type_def @ pretty_fun_def @ pretty_lemmas @ pretty_thm_section))
  end

fun print ctxt fname = Pretty.writeln o (pretty_nlp ctxt fname)

(* initialise an NLProofTree from the trace of a proof.
   i is assumed to be the number of the node in the sibling list
   parent_id is the id given to the parent of the node that the function is creating
   pt is assumed to be the parent node; assumed to be initialised as NONE*)
fun nlproof_tree_mk full_prf (TTree (D,ch)) = 
  let 
     (* basic info *)
    val rst = #rstate D
    val top_goal = #top_goal D
    val id = #node_id D
    val goals = #goals D   
    
    val name = DescripCInfo.string_of_rst rst

   (* val fname = #fname D*)
    
    (*
    fun pretty_step (TTree (D,ch)) =
      if String.isSubstring start_rippling_str (DescripCInfo.string_of_rst (#rstate D)) 
      then 
        let val (TTree (D',ch')) = (hd ch)
            val rst' = (#rstate D')
        in ()
        end
      else raise ERROR "Not stepcase!"*)
      val _ = if goals = [] then () else
        let 
          val goal_name = hd goals 
          val step_asm_names = get_ndname_lasms full_prf goal_name 
          val _ = writeln goal_name
          val _ =  map writeln step_asm_names
          val _ =  writeln name
          val _ = writeln "--"
        in () 
        end;
            
    val recursed_ch = 
      if String.isSubstring RstName.start_rippling_str name 
      then []
      else map (nlproof_tree_mk full_prf) ch
      
    (* what is shown *)
    val (text,more_deps) = 
      if String.isSubstring RstName.basecase_str name then
        let 
          val qfixes_base = pretty_qfixes full_prf (hd goals)
          val pretty_base = Pretty.str (uncurried_string_of_named_goal full_prf (hd goals))
        in
          (Pretty.chunks
            ([Pretty.str ("% (" ^ name ^ ") Current goals: [" ^ (commas goals) ^ "]" ^  ", top goal: " ^ top_goal),
              Pretty.str "\\vskip 1em",
              Pretty.str "\\noindent For the \\textbf{base of induction} we need to prove the following statement:"]
             @ (latex_env "align*" "" [pretty_cut_or_tie_latex qfixes_base pretty_base])),[])
        end
      else
      
      if String.isSubstring RstName.basecase_simp_str name then
        (Pretty.chunks [Pretty.str ("% (" ^ name ^ ") Current goals: [" ^ (commas goals) ^ "]" ^  ", top goal: " ^ top_goal),
                       Pretty.str ("This follows trivially from our definitions. \\\\"),
                       Pretty.str ""],[])
        
      else
      if String.isSubstring RstName.induction_on_str name then
        (Pretty.chunks [
          Pretty.str (String.concat ["% (", name, ") Current goals: [", (commas goals) ^ "]", ", top goal: ", top_goal]),
          Pretty.str ("We proceed by induction on $" ^ find_induction_var_in_rstname name ^ "$. "),
          Pretty.str ""],[])
        
      else
      if String.isSubstring RstName.start_rippling_str name then
        let     
          val step_name = hd goals 
          val step_asm_names = get_ndname_lasms full_prf step_name
          
          val qfixes_step = pretty_qfixes_english false full_prf step_name
          val qfixesL_stepasms = map (pretty_qfixes full_prf) step_asm_names       
          val pretty_step_goal = Pretty.str (uncurried_string_of_named_goal full_prf step_name)
          val pretty_stepasms = 
            map (Pretty.str o (uncurried_string_of_named_goal full_prf)) step_asm_names
          val x = get_goals_and_meths_rippling full_prf (TTree (D,ch))
          val deps_here = List.concat (map (deps_of_mth o snd) x)
        in 
         (Pretty.chunks
          (Pretty.block [Pretty.str "\\noindent For the \\textbf{step of induction} we need to show that ",
                          qfixes_step,
                          Pretty.str (String.concat 
                                        ([", the inductive hypothesis (\\ref{",
                                          String.concat step_asm_names,
                                          "}) entails the inductive goal (\\ref{",step_name,"})."])
                                      )
                          ]
           :: (latex_env "align" "" 
                    (([Pretty.str ("\\label{"^(String.concat step_asm_names)^"} ")]
                      @ (map_many (map pretty_cut_or_tie_latex qfixesL_stepasms)
                                  pretty_stepasms) @ [Pretty.str ("\\tag{IH$_{"^"\\thesection"^(*^"\\ref{"step_name"}"^*)"}$}")]
                     )
                     @ [Pretty.str "\\\\",
                        Pretty.str ("\\label{"^step_name^"} \\tag{IG$_{\\thesection}$}"), 
                        Pretty.block [Pretty.str "&", pretty_step_goal]
                       ]
                    )
                 )
           @ make_and_display_Uchains full_prf x @
          [(*Pretty.str "We show this with the following chain of equalities: ",
           make_Uchain_align full_prf x,*) Pretty.str ""]), deps_here)
        end
        
      else
      if String.isSubstring RstName.lemcalc_str name then
        (Pretty.chunks
          [Pretty.str ("% (" ^ name ^ ") Current goals: [" ^ (commas goals) ^ "]" ^  ", top goal: " ^ top_goal),
           Pretty.str (String.concat ["This can be proved using lemma ", "\\ref{", find_lem_name_in_string name ,"}"])],[])

      else
        (Pretty.str ("% NO MATCH. Current goals: [" ^ (commas goals) ^ "] " ^ name),[])

    val deps = maps get_deps_from_nlproof_tree recursed_ch
    val deps_upd = deps @ more_deps
    val D = {proof = full_prf, top_goal = top_goal, node_id = id, name = name, text = text, deps = deps_upd}
  in
    NLProofTree (NLProofNode D, recursed_ch)
  end

    
fun nlproof_init rst fname =
  let 
    val prf = PPlan.get_prf (RState.get_pplan rst)
    val prf_is_complete = null (RState.get_goalnames rst)
    val fs = if prf_is_complete then fst else 
              (fn x => case (snd x) of NONE => [] 
              | SOME t => (t |> HTraceCInfo.get_from_trace |> fst))
    val htr = rst |> RState.get_cinfo 
                  |> HTraceCInfo.I.get_from_cinfo 
                  |> HTraceCInfo.get_from_trace |> fs |> hd 
                  |> mk_ttrees prf fname
  in
     map (nlproof_tree_mk prf) htr
  end



end; (* local *)
end; (* NLProof *)
