(* Natural Language Proof *)
signature NL_PROOF =
sig

  (*  mini_nl_proof is a name plus an explanation that goes with each node. *)
  
  type id_mnlp = int list
  type text_mnlp = Pretty.T (* This probably will contain the canned text; pretty is good *)
  datatype mini_nl_proof = MiniNLProof of (id_mnlp * bool * text_mnlp)
  datatype nl_proof_tree = NLProofTree of (mini_nl_proof * nl_proof_tree list)
  datatype lemma_tree = LemmaTree of ((string * nl_proof_tree) * lemma_tree list)
  datatype nlproof = NLProof of (nl_proof_tree * (lemma_tree list))
  
  (* initialise a NLProofTree from a reasoning state *)
  val nlproof_mk : int 
                   -> int list 
                   -> HTraceCInfo.tree option
                   -> string list
                   -> string
                   -> bool
                   -> Prf.T
                   -> HTraceCInfo.tree
                   -> nlproof
  val nlproof_init : RState.T -> nlproof

  
  (* operators for nltrees and nlproofs *)
  val toggle_expandability : id_mnlp -> nlproof -> nlproof

  val expand_all : nl_proof_tree -> nl_proof_tree
  val collapse_all : nl_proof_tree -> nl_proof_tree
  val expand_branch : id_mnlp -> nl_proof_tree -> nl_proof_tree
  val collapse_branch : id_mnlp -> nl_proof_tree -> nl_proof_tree
  val expand_recursively : nl_proof_tree -> nl_proof_tree
  val collapse_recursively : nl_proof_tree -> nl_proof_tree
  
  (* auxiliary *)
  val get_id_from_tree : nl_proof_tree -> id_mnlp
  val isprefix : ''a list -> ''a list -> bool
  val get_branch_with_id : id_mnlp -> nl_proof_tree -> nl_proof_tree
  val map_numbering : int -> (int -> 'a -> 'b) -> ('a list) -> ('b list)

  (* pretty *)
  val pretty_trm : Prf.T -> Term.term -> Pretty.T
  val pretty_nlp_tree : nl_proof_tree -> Pretty.T
  val pretty_lemma_tree : lemma_tree -> Pretty.T
  val pretty_nlproof : nlproof -> Pretty.T
  val print : nlproof -> unit

end;


structure NLProof : NL_PROOF =
struct
  local open HTraceCInfo; open Prf; in

  type id_mnlp = int list (* TEMP! do we really want lists of numbers? *)
  type text_mnlp = Pretty.T (* This probably will contain the canned text; pretty is good *)
  datatype mini_nl_proof = MiniNLProof of (id_mnlp * bool * text_mnlp)
  datatype nl_proof_tree = NLProofTree of (mini_nl_proof * nl_proof_tree list )
  datatype lemma_tree = LemmaTree of ((string * nl_proof_tree) * lemma_tree list)
  datatype nlproof = NLProof of (nl_proof_tree * (lemma_tree list))
  
  val nl_proof_tree_dummy =  NLProofTree (MiniNLProof ([], false, Pretty.str "NONEXISTENT"), []);
  
  (* auxiliary *)
  fun get_mnlp_of_tree (NLProofTree (x,ch)) = x
  fun get_id_from_tree (NLProofTree (MiniNLProof (id,_,_), _)) = id
  fun get_id_from_mnlp (MiniNLProof (id,_,_), _) = id
  fun get_id_from_lemmat (LemmaTree ((_,nlpt),_)) = get_id_from_tree nlpt
  fun get_lemma_name (LemmaTree ((name,_),_)) = name
  fun get_nlpt_from_lemmat  (LemmaTree ((_,nlpt),_)) = nlpt
  fun get_ptree (NLProof (ptree,ltreeL)) = ptree
  fun get_ltreeL (NLProof (ptree,ltreeL)) = ltreeL

  fun is_eq_term t = 
      is_some (Subst.move_to_concl_eq (Zipper.mktop t));

  fun isprefix [ ] l = true
    | isprefix l [ ] = false 
    | isprefix (a :: l) (b :: m) = (a = b) andalso (isprefix l m)

  fun get_branch_with_id id (t as (NLProofTree ((MiniNLProof (nd,_,_)),ch))) = (* same id *)
        if nd = id then t
        else
          case List.find (fn n => isprefix (get_id_from_tree n) id) ch of
              NONE => nl_proof_tree_dummy
            | SOME x => x

  fun change_expandability (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch)) =
        NLProofTree (MiniNLProof (nd,(not is_expandable),txt),ch)

  fun toggle_expandability_t id (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch)) =
      if isprefix nd id then
        if nd = id then 
          NLProofTree (MiniNLProof (nd, not is_expandable, txt), ch)
        else 
          NLProofTree (MiniNLProof (nd, is_expandable, txt), 
                            map (toggle_expandability_t id) ch)
      else
        NLProofTree (MiniNLProof (nd, is_expandable, txt), ch)

  fun toggle_expandability_l id (LemmaTree ((name,nlpt),ltL)) =
      let val (yl,nl) = List.partition ((fn lid => isprefix lid id) o get_id_from_lemmat) ltL
      in 
        if null yl then (LemmaTree ((name, toggle_expandability_t id nlpt), ltL))
        else (LemmaTree ((name, nlpt), nl @ (map (toggle_expandability_l id) yl)))
      end


  fun toggle_expandability id (NLProof (nlpt,ltL)) =
      let val (yl,nl) = List.partition ((fn lid => isprefix lid id) o get_id_from_lemmat) ltL
      in 
        if null yl then 
          NLProof (toggle_expandability_t id nlpt, ltL)
        else 
          NLProof (nlpt, nl @ (map (toggle_expandability_l id) yl))
      end

  fun expand_branch id (x as (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch))) =
      if is_expandable then
        if nd = id then 
          NLProofTree (MiniNLProof (nd,false,txt), ch) (* children, same id *)
        else NLProofTree (MiniNLProof (nd,true,txt), ch) (* children, dif id *)
      else
        NLProofTree (MiniNLProof (nd,false,txt), map (expand_branch id) ch)

  fun collapse_branch id (NLProofTree (x,[])) =  (* not collapsable because is leaf *)
        NLProofTree (x,[])
    | collapse_branch id (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch)) =
        if is_expandable then
          NLProofTree (MiniNLProof (nd,true,txt),ch)
        else
          if nd = id then NLProofTree (MiniNLProof (id,true,txt), ch) (* collapsable because is *)
          else NLProofTree (MiniNLProof (nd,is_expandable,txt), map (collapse_branch id) ch) (* children, dif id *)

  fun expand_all (t as (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch))) =
      if is_expandable then expand_branch nd t
      else (NLProofTree (MiniNLProof (nd,is_expandable,txt), map expand_all ch))

  fun tree_is_expandable (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch)) = is_expandable
  fun tree_is_leaf (NLProofTree (x, ch)) = null ch

  fun collapse_all (NLProofTree (MiniNLProof (nd,is_expandable,txt), h::t)) = (* assumes all children have same expandability *)
      if (tree_is_expandable h) then 
        (NLProofTree (MiniNLProof (nd,true,txt), (h::t)))
      else if (tree_is_leaf h) then
        (NLProofTree (MiniNLProof (nd,true,txt), (h::t)))
      else  
        (NLProofTree (MiniNLProof (nd,is_expandable,txt), map collapse_all (h::t)))

  fun expand_recursively (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch)) =
      (NLProofTree (MiniNLProof (nd,false,txt), map expand_recursively ch))

  fun collapse_recursively (NLProofTree (MiniNLProof (nd,is_expandable,txt),ch)) =
        (NLProofTree (MiniNLProof (nd,true,txt), map collapse_recursively ch))

  fun destroy_children (Tree ((k,rst),ch)) = (Tree ((k,rst),[]))

  fun map_numbering i f [] = []
    | map_numbering i f (h::t) = (f i h)::(map_numbering (i+1) f t)

  fun map_many fs [] = []
    | map_many [] l = l
    | map_many (fh::ft) (h::t) = (fh h) :: (map_many ft t)

  (* pretty *)
  val pretty_breaking = (fn x => Pretty.blk (0,x)) o Pretty.breaks 
                  o (map Pretty.str) o (space_explode " ") o Pretty.string_of

  fun pretty_trm p t = Pretty.unbreakable (Trm.pretty (APrf.get_context p) t);

  fun list_sep x [] = []
    | list_sep x [a] = [a]
    | list_sep x (h::(t as h2::t2)) = 
      h :: x :: (list_sep x t);

  fun pretty_match_lists [] l = []
    | pretty_match_lists l [] = []
    | pretty_match_lists (h1::t1) (h2::t2) = 
          ((Pretty.block [h1, h2]) :: pretty_match_lists t1 t2)

  fun pretty_match_lists_break [] l = []
    | pretty_match_lists_break l [] = []
    | pretty_match_lists_break (h1::t1) (h2::t2) = 
          ((Pretty.block [h1, Pretty.fbrk, h2]) :: pretty_match_lists_break t1 t2)

  fun pretty_sep_block s l = 
      Pretty.block (list_sep (Pretty.str s) l);

  fun pretty_goals prf = (pretty_trm prf) o (get_ndname_ctrm prf)

  fun pretty_tfix_nl thry (n,srt) =  (* needs to change *)
      let val t = Pretty.string_of (Trm.pretty_sort thry srt)
      in
        (Pretty.block 
          [if String.isPrefix "type" t then Pretty.str "set" else Pretty.str t, 
          Pretty.str " ", TFree.pretty_name n])
      end;

  fun pretty_fix_nl thry (n,typ) = (* includes naturals booleans and lists *)
    let 
      val k = Datatype_Aux.name_of_typ typ 
      val t = if k = "" then Pretty.string_of (Trm.pretty_typ thry typ) else k
    in
       Pretty.block 
        [Free.pretty_name n , Pretty.str " ",
         if String.isPrefix "nat" t then Pretty.str "natural number"
         else if String.isPrefix "bool" t then Pretty.str "boolean"
         else 
          let val explodes = space_explode " " t in 
            if length explodes > 1 andalso String.isPrefix "list" (hd (tl explodes)) then 
              Pretty.str ("list of elements of " ^ (hd explodes)) 
            else Pretty.str ("element of " ^ t)
          end
              ]
    end;

  fun pretty_commas_and [] = []
    | pretty_commas_and [l] = [l]
    | pretty_commas_and [ll,l] = [ll,Pretty.str " and ",l]
    | pretty_commas_and (h::t) = [h,Pretty.str ", "] @ (pretty_commas_and t)

  fun pretty_block_commas_and [] = []
    | pretty_block_commas_and [l] = [l]
    | pretty_block_commas_and [ll,l] = ll :: [Pretty.block [Pretty.str " and ", l]]
    | pretty_block_commas_and (h1::(h2::t)) = 
        h1 :: (pretty_block_commas_and ((Pretty.block [Pretty.str ", ", h2]) :: t))
  (* with types/sorts *)
  fun prettyL_fixes_nl caps context ptab = 
      let
        val tvsL = rev (Trm.TypParams.get_plist (Cx.get_typps_of_ptab ptab))
        val vsL = rev (Trm.TrmParams.get_plist (Cx.get_trmps_of_ptab ptab))
        val fix_typesPL = 
            if null tvsL then [] else 
            [Pretty.block
               [Pretty.str ((if caps then "F" else "f") ^"or every "), 
                Pretty.block (pretty_commas_and (map (pretty_tfix_nl context) tvsL))]]
        val fixPL = 
            if null vsL then [] else 
            [Pretty.block 
               [Pretty.str ((if caps then "F" else "f") ^"or every "), 
                Pretty.block (pretty_commas_and (map (pretty_fix_nl context) vsL))]]
      in if null fix_typesPL andalso null fixPL then []
         else if null fix_typesPL orelse null fixPL then 
                [pretty_sep_block " " (fix_typesPL @ fixPL)]
         else [pretty_sep_block " and " (fix_typesPL @ fixPL)]
      end;

  fun pretty_qfixes caps prf gname = 
      let
        val cxs = get_ndname_cx prf gname
        val fixes = Cx.get_lfixes cxs
        val f = prettyL_fixes_nl caps
      in
        (Pretty.block o (f (get_context prf))) fixes
      end

(* Pretty printing functions, cmp is for a compressed version, ie with
   all higher subtree's closed (not showing subnodes). *)
  fun pretty_id_of_mnlp (MiniNLProof (id,_,_)) =
      Pretty.unbreakable (Pretty.list "[" "] " (map Pretty.str (map Int.toString id)))
  fun pretty_mini_nl_proof (MiniNLProof (id,ie,x)) = x

  val pretty_hline = 
      Pretty.str 
        "--------------------------------------------------------------------------------------------";

  (* pretty trees with and all children *)
  fun pretty_nlp_tree (NLProofTree (mnlp as MiniNLProof (id,is_expandable,txt), [])) = 
        Pretty.indent ((length id * 3) + 4) (Pretty.block [pretty_mini_nl_proof mnlp, Pretty.fbrk])
    | pretty_nlp_tree (NLProofTree (mnlp as MiniNLProof (id,is_expandable,txt), hch::tch)) = 
        if is_expandable then 
          (Pretty.block [Pretty.str " + ", pretty_id_of_mnlp mnlp, 
                        pretty_mini_nl_proof mnlp, Pretty.fbrk])
        else
          Pretty.chunks
           ([Pretty.blk
             ((length id * 3) + 4,[Pretty.str " - ", pretty_id_of_mnlp mnlp, 
              pretty_mini_nl_proof (get_mnlp_of_tree hch), 
              Pretty.fbrk])]
             @ map pretty_nlp_tree tch)

  fun pretty_lemma_tree (LemmaTree ((lname, nlpt), ltL)) =
      Pretty.chunks 
          ([Pretty.str (lname ^": "), pretty_nlp_tree nlpt]
         @ (map pretty_lemma_tree ltL))
        

  fun pretty_nlproof (NLProof (nlpt,ltL)) =
    Pretty.chunks [
      if null ltL then
        pretty_nlp_tree nlpt
      else
        Pretty.chunks ([Pretty.str "The following lemmas are used in the proof: "]
                     @ (map pretty_lemma_tree ltL) 
                     @ [Pretty.str "", pretty_hline, pretty_nlp_tree nlpt]),
      pretty_hline]


  val print = Pretty.writeln o pretty_nlproof


  (* names to identify techniques (rst names) *)
  val basecaseN =  "Solve the base";
  val induct_and_rippleN = "Solve using Induction";
  val induct_and_ripple_with_ruleN = "Solve using Induction (custom rule) and Rippling.";
  val strong_fertN = "Strong fertilisation";  
  val weak_fert_startN = "Weak fertilisation"; 
  val weak_fert_leftN = "Weak fertilisation on left";
  val weak_fert_rightN = "Weak fertilisation on right";
  val end_fertN = "end fertilisation";
  val end_ripplingN = "end rippling";
  val start_ripplingN = "Start Rippling with state: ";
  val update_stepN = "Ripple Step by "
  val solved_by_ripplingN = "Rippling solves the goal directly";
  val stepcase_by_ripplingN = "Solve the step case using rippling.";
  val induction_onN = "Induction on";
  val simpN = "simp";
  val lemcalcN = "Proving goal";
  val back_resolN = "Resolution backward"
  val solvedN = "Solved";

  fun solved_by_simp (Tree ((k,rst),ch)) = 
      String.isPrefix solvedN (DescripCInfo.string_of_rst rst)
  fun is_base_case (Tree ((k,rst),ch)) = 
      String.isPrefix basecaseN (DescripCInfo.string_of_rst rst)
  fun get_rst_name (Tree ((k,rst),ch)) = DescripCInfo.string_of_rst rst
  fun get_prf_from_tree (Tree ((k,rst),ch)) = PPlan.get_prf (RState.get_pplan rst)
  fun get_the_lemma (Tree ((k,rst),ch)) =
      case List.find (String.isPrefix back_resolN) (map get_rst_name ch) of
        NONE => "MAGICAL"
      | SOME s => String.substring (s, Int.min(String.size(s)-1,35), 1)
  fun get_the_lemma_fromL l = 
      case List.find (not o (String.isPrefix "MA")) (map get_the_lemma l) of
        NONE => "MAGICAL"
      | SOME s => s
  fun get_goals_from_tree (Tree ((k,rst),ch)) = RState.get_goalnames rst
  fun get_pretty_goals_from_tree (Tree ((k,rst),ch)) = 
      let val prf = PPlan.get_prf (RState.get_pplan rst) in
        map (pretty_goals prf) (get_goals_from_tree (Tree ((k,rst),ch))) end
      
  fun get_qfixes_open (Tree ((k,rst),ch)) =  
      let
        val prf = PPlan.get_prf (RState.get_pplan rst)
        val context = get_context prf
        val open_goal_names = RState.get_goalnames rst
      in  map (pretty_qfixes false prf) open_goal_names end

  fun get_qfixes_from_gname gname (Tree ((k,rst),ch)) = 
      let
        val prf = PPlan.get_prf (RState.get_pplan rst)
      in pretty_qfixes false prf gname end

  fun get_bases_and_steps p open_gnames = 
      List.partition (null o (get_ndname_lasms p)) open_gnames

  fun get_left_and_right [] = []
    | get_left_and_right ((Tree ((_,rst),_)) :: t) = 
        let 
          val open_goal_names = RState.get_goalnames rst
          val prf = PPlan.get_prf (RState.get_pplan rst)
          val zs = map (Zipper.mktop o APrf.nd_get_trm o (Prf.get_nd prf)) open_goal_names
          val lhs = map Subst.move_to_lhs_of_eq zs
          val rhs = map Subst.move_to_rhs_of_eq zs
        in (lhs,rhs)::(get_left_and_right t) end

  fun get_ch_of_treeO (SOME (Tree ((k,rst),ch))) = ch
    | get_ch_of_treeO NONE = []
  fun reverse_ch_in_tree (Tree ((k,rst),ch)) = (Tree ((k,rst), rev ch))
  fun give_last_ch c (Tree ((k,rst),ch)) = (Tree ((k,rst),ch @ [c]))
  fun get_first_ch (Tree ((k,rst),ch)) = hd ch
  fun get_second_ch (Tree ((k,rst),ch)) = hd (tl ch)
  fun erase_nth_element n [] = []
    | erase_nth_element 0 (h::t) = t
    | erase_nth_element n (h::t) = h :: (erase_nth_element (n-1) t)
  fun erase_nth_child n (Tree ((k,rst),ch)) = 
      (Tree ((k,rst), erase_nth_element n ch))
  fun replace_nth_element 0 e l = e :: (tl l)
    | replace_nth_element n e [] = []
    | replace_nth_element n e l = 
        (hd l) :: (replace_nth_element (n-1) e (tl l))

  fun give_last_nlch c (NLProofTree (m, ch)) = (NLProofTree (m, ch @ [c]))

  fun repair_induction_tree_nlch nlch indnd fid base_is_trivial =
      let
        val open_gnames = get_goals_from_tree indnd
        val prf = get_prf_from_tree indnd
        val step_nltree = List.last nlch
        val (bases,steps) = get_bases_and_steps prf open_gnames
        val pretty_steps = map (pretty_goals prf) steps
        val new_text = 
              Pretty.chunks 
                  ((map (Pretty.indent 3) pretty_steps)
                 @ [Pretty.str "", 
                    pretty_breaking 
                        (Pretty.str "thus reaching what we wanted to prove.")])
        val step_conc_nd = NLProofTree (MiniNLProof (fid,true,new_text),[])
        val new_step_nd = give_last_nlch step_conc_nd step_nltree
        val n = if base_is_trivial then 2 else 3
      in replace_nth_element n new_step_nd nlch
      end
  fun print_rstn t = writeln (get_rst_name t)

  fun sort_rippling_tree_ch ch =
   let val fertTreeCh = get_ch_of_treeO (SOME (hd (tl ch)))
   in
    if not (null fertTreeCh) then
      if length ch > 4 then
        let (* HORRIBLE! *)
          val rch0 = (tl (rev ch))
          val rch = if get_rst_name (hd rch0) = get_rst_name (hd (tl rch0)) then 
                        rev (tl rch0) else rev rch0 (* chidlren list *)
          val ftree0 = hd (tl rch) (* Fertilisation tree *)
          val dummy = get_first_ch ftree0
          val ftree = erase_nth_child 0 ftree0
          val fertn = get_first_ch ftree 
          val rch2 = (hd rch) :: (fertn :: (tl rch))
          val ftree2 = erase_nth_child 0 ftree
          val ftree3 = give_last_ch (nth rch2 3) ftree2 
          val ftree4 = reverse_ch_in_tree ftree3
          val fertd = get_second_ch ftree4
          val ftree5 = give_last_ch fertd ftree4
          val ftree6 = erase_nth_child 1 ftree5
          val rch3 = erase_nth_element 3 rch2
          val rch4 = replace_nth_element 2 ftree6 rch3
          val rch5 = 
              let val tl0 = tl rch4 
                  val tl1 = tl tl0 
                  val tl2 = tl tl1 
              in (hd rch4) :: ((hd tl0) :: ((hd tl1) :: (dummy :: tl2))) 
              end
        in rch5 end
      else
        let
          val rch0 = (tl (rev ch))
          val rch = if get_rst_name (hd rch0) = get_rst_name (hd (tl rch0)) then 
                        rev (tl rch0) else rev rch0 (* chidlren list *)
          val ftree0 = hd (tl rch) (* Fertilisation tree *)
          val ftree = erase_nth_child 0 ftree0
          val fertn = get_first_ch ftree 
          val rch2 = (hd rch) :: (fertn :: (tl rch))
          val ftree2 = erase_nth_child 0 ftree

          val ftree3 = reverse_ch_in_tree ftree2
          val rch3 = replace_nth_element 2 ftree3 rch2
        in
          rch3
        end
     else
       rev ch
   end

  fun get_goals_from_parent_and_number i NONE = []
    | get_goals_from_parent_and_number i (SOME (Tree ((k,rst),ch))) = 
        if i < 0 then [] else get_goals_from_tree (nth ch i)
        
  (* initialise an NLProofTree from the trace of a proof.
     i is assumed to be the number of the node in the sibling list
     parent_id is the id given to the parent of the node that the function is creating
     pt is assumed to be the parent node; assumed to be initialised as NONE*)
  fun nlproof_mk i parent_id pn previous_goal_names top_goal_name prf_is_complete full_prf (Tree ((k,rst),ch)) = 
      let 
        (* basic sources of information *)
        val name = DescripCInfo.string_of_rst rst
        val pplan = RState.get_pplan rst
        val prf = PPlan.get_prf pplan
        val context = get_context prf

        (* goals *)
        val open_goal_names = RState.get_goalnames rst
        val updated_top_goal_name = if String.isPrefix lemcalcN name then 
                                      ("lem_" ^ (get_the_lemma (Tree ((k,rst),ch)))) 
                                    else top_goal_name
        val updated_previous_goal_names =
              let val g = get_goals_from_parent_and_number (i-1) pn in
                if null g then previous_goal_names else g
              end
        val pretty_open_goals = map (pretty_goals prf) open_goal_names
        val pretty_top_goal = pretty_goals prf updated_top_goal_name

        (* assumptions for open goals *)
        val asm_names = map (get_ndname_lasms prf) open_goal_names
        val pretty_asms = map (map (pretty_goals prf)) asm_names

        (* pretty blocks of variables separated by commas and ands *)
        val qfixes_top = pretty_qfixes false prf updated_top_goal_name
        val qFixes_top = pretty_qfixes true prf updated_top_goal_name
        val qfixesL_open = map (pretty_qfixes false prf) open_goal_names
        val qfixesL_asm = map (map (pretty_qfixes false prf)) asm_names
(*
        (* methods *)
        val meths = map (get_ndname_meth full_prf) updated_previous_goal_names
        fun mname0 (Meth (optmeth,_)) = optmeth
          | mname0 AsmMeth = MOpen
        fun mname MOpen = ("open", updated_top_goal_name)
          | mname (MClosed (MKindRes g, _)) = ("res",updated_top_goal_name)
          | mname (MClosed (MKindSubst g, _)) = ("subst", updated_top_goal_name)
          | mname (MClosed (MKindPrf (mname,_), _)) = ("COOL!", mname)
          | mname (MClosed (MKindThm th, _)) = ("thm", updated_top_goal_name)
          | mname (MClosed (MKindTac (th,(tac,p)), _)) = ("tac", updated_top_goal_name)

        val mnames = map (mname o mname0) meths
        val x = if null mnames then updated_top_goal_name else snd (hd mnames)
        val y = if String.isPrefix "subst_w_thm: " x then String.extract (x,13,NONE) else updated_top_goal_name

        val thmq =  @{thm} y
        val _ = Pretty.writeln (Display.pretty_thm context thm) *)
(*val wrules = WRules.wrules_of (WRulesGCtxt.get_from_ctxt context)*)
(*WRules.rule_of_wrule*)
        

        (* useful conditions and data *)
        val some_goals = not (null open_goal_names)
        val one_goal = ((length open_goal_names) = 1)
        val (base_is_trivial, is_bases_level) = 
            let val pch = case pn of NONE => [] | SOME (Tree ((pk,prst),x)) => x
            in (exists solved_by_simp pch, exists is_base_case pch) end
        val base_is_trivial_ind_level = exists solved_by_simp ch
        val is_induction_tree = String.isPrefix "Solve using Induction" name
        val is_lemma_tree = String.isPrefix lemcalcN name
        val is_rippling_tree = String.isPrefix stepcase_by_ripplingN name
        val is_fert_tree = (String.isPrefix weak_fert_startN name) 
                              andalso not (String.isPrefix weak_fert_leftN name 
                                            orelse String.isPrefix weak_fert_rightN name)
        val lemma_is_required = not (String.isPrefix "MA" (get_the_lemma_fromL ch) )
        val depth = length parent_id

        (* singular or plural functions *)
        fun sorp x y = if some_goals then 
                          (if one_goal then x else y) 
                       else "empty"
        val sorp_pretty = Pretty.str oo sorp

        (* what will be shown *)
        val text =
           if String.isPrefix induct_and_rippleN name then 
              if depth < 2 then
                Pretty.chunks
                   [pretty_breaking 
                      (Pretty.block [Pretty.str "By induction, we prove that, ", qfixes_top]), 
                    Pretty.str "",
                    Pretty.indent 3 pretty_top_goal, 
                    Pretty.str ""]
              else Pretty.chunks [pretty_breaking qFixes_top, Pretty.str "", 
                                  Pretty.indent 3 pretty_top_goal]

           else if String.isPrefix induct_and_ripple_with_ruleN name then 
                  if depth < 2 then
                    Pretty.chunks
                       [pretty_breaking 
                          (Pretty.block [Pretty.str ("By induction, we prove that, "), qfixes_top]), 
                        Pretty.str "",
                        Pretty.indent 3 pretty_top_goal, 
                        Pretty.str ""]
                  else Pretty.chunks [pretty_breaking qFixes_top, Pretty.str "", 
                                      Pretty.indent 3 pretty_top_goal] (* with rule *)

              (* not ready for induction with multiple steps; also is hacky because it 
                relies on the fact that the step has assumptions and the base doesn't *)
           else if String.isPrefix induction_onN name then 
            let val induction_var =  (* unstable; depends on name *)
                      String.str (String.sub (name, Int.min(String.size(name)-1,14)))
                val (base_goals, step_goals) = get_bases_and_steps prf open_goal_names
                val step_asms = map (get_ndname_lasms prf) step_goals
                val qfixesL_bases = map (pretty_qfixes false prf) base_goals
                val qfixesL_steps = map (pretty_qfixes false prf) step_goals
                val qfixesLL_stepasms = map (map (pretty_qfixes false prf)) step_asms
                val pretty_bases = map (pretty_goals prf) base_goals
                val pretty_steps = map (pretty_goals prf) step_goals
                val pretty_stepasms = map (map (pretty_goals prf)) step_asms
            in
              Pretty.chunks 
                  [Pretty.chunks 
                      (if depth < 2 then 
                          [pretty_breaking 
                            (Pretty.block [Pretty.str ("We will prove by induction on " 
                                                        ^ induction_var ^ " that, "), 
                                           qfixes_top]), 
                             Pretty.str "", Pretty.indent 3 pretty_top_goal, Pretty.str ""]
                       else [pretty_breaking 
                                (Pretty.indent 2 
                                    (Pretty.str ("We will prove it by induction on " 
                                                ^ induction_var ^ ". ")))]),
                   Pretty.chunks
                        ([pretty_breaking 
                            (Pretty.block 
                                ([Pretty.indent 2 
                                    (Pretty.str "For the induction base we need to prove that ")]
                                @ qfixesL_bases)), 
                          Pretty.str ""] 
                         @ (map (Pretty.indent 3) pretty_bases) 
                         @ [Pretty.str ""]),
                   Pretty.chunks 
                        ([pretty_breaking 
                              (Pretty.block 
                                  ([Pretty.indent 2 
                                      (Pretty.str ("For the induction step"
                                                 ^ " we need to prove that, "))]
                                  @ qfixesL_steps 
                                  @ [Pretty.str ", if the inductive hypothesis"])),
                         Pretty.str ""]
                        @ (map (Pretty.indent 3) (List.concat pretty_stepasms))
                        @ [Pretty.str ""]),
                   Pretty.chunks
                        ([pretty_breaking 
                            (Pretty.block ( [Pretty.str "holds "] 
                                          @ (List.concat qfixesLL_stepasms)
                                          @ [Pretty.str ", then "])), 
                         Pretty.str ""]
                        @ (map (Pretty.indent 3) pretty_steps)
                        @ [Pretty.str ""]),
                   Pretty.block 
                        [Pretty.str "also holds." ]
                   ]
            end

           else if String.isPrefix basecaseN name then
                  if base_is_trivial then 
                    Pretty.chunks [Pretty.str "INDUCTIVE BASE: ",
                      pretty_breaking 
                          (Pretty.indent 2 
                              (Pretty.str "The proof of the induction base is trivial."))]
                  else
                    Pretty.chunks
                       ([Pretty.str "INDUCTIVE BASE: ",
                         pretty_breaking 
                            (Pretty.block 
                                ([Pretty.indent 2 
                                    (Pretty.str ("Simplifying the base goal we can see"
                                               ^ " that it suffices to prove that, "))]
                                @ qfixesL_open)), 
                         Pretty.str ""]
                        @ (map (Pretty.indent 3) pretty_open_goals))

           else if String.isPrefix solvedN name then 
                  Pretty.str "USELESS CELL; SOLVED"

           else if is_lemma_tree then
                  if is_bases_level then 
                    pretty_breaking 
                          (Pretty.str ("This is a direct consequence of lemma " 
                                      ^ updated_top_goal_name ^ "."))
                  else
                    Pretty.chunks [Pretty.str "INDUCTIVE STEP: ",
                       pretty_breaking 
                          (Pretty.block 
                              ([Pretty.indent 2 (Pretty.str ("By lemma " ^ updated_top_goal_name 
                                            ^ " we have that, "))] 
                              @ get_qfixes_open (hd (tl (tl (get_ch_of_treeO pn)))) ))]  (* horrible! *) 

           else if String.isPrefix simpN name then
                  if prf_is_complete then
                    if is_bases_level then 
                        Pretty.str "USELESS CELL; SIMP" 
                      else 
                        Pretty.chunks 
                            [Pretty.str "INDUCTIVE STEP: ",
                             pretty_breaking
                                (Pretty.block 
                                    ([Pretty.indent 2 
                                        (Pretty.str ("To begin, let"
                                                   ^ " us take the following trivial fact that holds "))]
                                    @ get_qfixes_open (hd (tl (tl (get_ch_of_treeO pn)))) (* horrible! *) 
                                    @ [Pretty.str ": "]))]
                  else
                    Pretty.str "simp, base level"

           else if is_rippling_tree then 
                  if prf_is_complete then
                    Pretty.chunks [Pretty.str "INDUCTIVE STEP: ",
                      if lemma_is_required then
                        Pretty.indent 2 
                          (pretty_breaking (Pretty.str ("The step goal is a consequence of lemma lem_"
                                                      ^ (get_the_lemma_fromL ch))))
                      else
                        pretty_breaking (Pretty.str ("The induction step is proved in " 
                                                    ^ Int.toString ((length ch) - 3) 
                                                    ^ " simple steps."))]
                  else Pretty.str "INDUCTIVE STEP (prf incomplete): "

           else if String.isPrefix update_stepN name then
                  if prf_is_complete then
                    Pretty.chunks (map (Pretty.indent 3) pretty_open_goals)
                  else Pretty.chunks ([Pretty.str "update step: "]
                                    @ (map (Pretty.indent 3) pretty_open_goals))

           else if String.isPrefix start_ripplingN name then 
                pretty_breaking (Pretty.str "But that implies ")

           else if String.isPrefix strong_fertN name then 
                  if prf_is_complete then
                    Pretty.chunks
                        ([Pretty.str "By the inductive hypothesis we have that", 
                          Pretty.str ""] 
                        @ pretty_open_goals)
                  else
                    Pretty.chunks ([Pretty.str "Strong Fert: "] 
                                @ (map (Pretty.indent 3) pretty_open_goals))

           else if is_fert_tree then
                  if prf_is_complete then
                    if not (null ch) then 
                      Pretty.chunks
                        ([pretty_breaking 
                            (Pretty.str ("If we apply the inductive hypothesis "
                                       ^ "to that expression, we get that ")), 
                          Pretty.str ""] 
                        @ (map (Pretty.indent 3) (get_pretty_goals_from_tree (hd ch))))
                    else
                      pretty_breaking 
                        (Pretty.str ("If we apply the induction hypothesis "
                                    ^ Int.toString (length (get_ch_of_treeO pn) - 1) 
                                    ^ " times, we obtain the following results: "))
                  else
                    Pretty.chunks ([Pretty.str "fert: "] 
                                @ (map (Pretty.indent 3) (get_pretty_goals_from_tree (hd ch))))

           else if String.isPrefix weak_fert_leftN name then
                  if prf_is_complete then
                    Pretty.chunks (map (Pretty.indent 3) pretty_open_goals)
                  else 
                    Pretty.chunks ([Pretty.str "weak fert left: "] 
                                @ (map (Pretty.indent 3) pretty_open_goals))


           else if String.isPrefix weak_fert_rightN name then
                  if prf_is_complete then 
                    Pretty.chunks (map (Pretty.indent 3) pretty_open_goals)
                  else
                    Pretty.chunks ([Pretty.str "weak fert right: "] 
                                @ (map (Pretty.indent 3) pretty_open_goals))
                    
           else if String.isPrefix end_fertN name then
                  if prf_is_complete then 
                    pretty_breaking 
                      (Pretty.str ("Furthermore, this implies the next, and each of the"
                                 ^ " expressions, in the following chain of deduction: "))
                  else
                    Pretty.str "End of fert"

           else if String.isPrefix solved_by_ripplingN name 
              then pretty_breaking (Pretty.str "And that is what we wanted to prove!")

           else if String.isPrefix end_ripplingN name then
                  if prf_is_complete then 
                    Pretty.indent 3 (Pretty.block pretty_open_goals)
                  else
                    Pretty.indent 3 (Pretty.block (pretty_open_goals 
                                                @ [Pretty.str " end of rippling"]))

           else if String.isPrefix back_resolN name 
              then Pretty.str "Resolution Backward!"

           else Pretty.str "The margin is too narrow for my wonderful proof"
        
        (* values for recursive application *)
        val new_id = (parent_id @ [i])

        val new_parent_node = (SOME (Tree ((k,rst), map destroy_children ch)))

        val (recursed_ch, new_ltreeL) = 
            (* for the case of using a new lemma, the branch is cut and the 
              nlprooftree of the lemma is moved to the lemma tree *)
            if is_lemma_tree then 
              let 
                val htree = hd (tl ch)
                 (* here, recursion occurs! (if is_lemma_tree) *)
                val x = (nlproof_mk 0 new_id new_parent_node updated_previous_goal_names updated_top_goal_name prf_is_complete full_prf htree) 
                val ptree = get_ptree x
                val ltreeL = get_ltreeL x
              in
                ([], [LemmaTree ((updated_top_goal_name, ptree), ltreeL)] )
              end
            (* when it's not a new lemma, its nlprooftree is continued along the branch it was in *)
            else 
              let
                (* updated children, because rearrangements might be needed *)
                val uch = 
                  (* here I reverse and rearrange the children in rippling and fert levels *)
                  if is_rippling_tree andalso not (null ch) andalso prf_is_complete then
                      (* this condition asks that fertilisation actually does something *)
                      if length (get_ch_of_treeO (SOME (hd (tl ch)))) > 2 then
                        sort_rippling_tree_ch ch
                      else erase_nth_element 1 ch
                  else
                  (* This is the dodgiest part, because it will break when 
                    there is more than one base or more than one step *)
                  (* here I erase a trivial node *)
                  if is_induction_tree andalso base_is_trivial_ind_level andalso not (null ch) then 
                    if depth < 2 then erase_nth_element 2 (rev ch)
                    else erase_nth_element 3 (rev ch) 
                  else rev ch
                (* here, recursion occurs! (if not is_lemma_tree) *)
                val xL = map_numbering 0 
                            (fn i => nlproof_mk i new_id 
                                      new_parent_node updated_previous_goal_names updated_top_goal_name prf_is_complete full_prf) 
                             uch
                val nlchL = map get_ptree xL
                             (* This will also break if there is more than 
                              one base or more than one step *)
                val ptreeL = if is_induction_tree andalso not (null ch) then 
                                let 
                                  val n = if depth < 2 then 2 else 3
                                  val fid = new_id @ [n,length (get_ch_of_treeO (SOME (nth ch n)))]
                                in 
                                  if depth < 2 then 
                                    repair_induction_tree_nlch nlchL 
                                                               (List.last ch) 
                                                               fid 
                                                               base_is_trivial_ind_level 
                                  else
                                    (hd nlchL) :: (repair_induction_tree_nlch 
                                                                      (tl nlchL) 
                                                                      (hd (tl (rev ch))) 
                                                                      fid 
                                                                      base_is_trivial_ind_level)
                                end 
                             else nlchL
                val ltreeL = List.concat (map get_ltreeL xL)
              in (* defining (recursed_ch, new_ltreeL) *)
                 (ptreeL, ltreeL)
              end

      in
        NLProof (NLProofTree (MiniNLProof (new_id, true, text), recursed_ch), 
                 new_ltreeL)
      end

  fun nlproof_init rst =
    let 
      val prf = PPlan.get_prf (RState.get_pplan rst)
      val prf_is_complete = null (RState.get_goalnames rst)
      val fs = if prf_is_complete then fst else 
                (fn x => case (snd x) of NONE => [] 
                | SOME t => (t |> HTraceCInfo.get_from_trace |> fst))
      val htr = rst |> RState.get_cinfo 
                    |> HTraceCInfo.I.get_from_cinfo 
                    |> HTraceCInfo.get_from_trace |> fs |> hd 
      val top_goal = "g1"
      val previous_goal_names = []
      val parent_node = NONE
      val init_id = []
    in
       nlproof_mk 0 init_id NONE previous_goal_names top_goal prf_is_complete prf htr
    end

  (* top level interface *)
  fun top_level rst = ()





end; (* local *)
end; (* NLProof *)
