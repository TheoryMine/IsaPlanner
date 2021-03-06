(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      gproof/unify/pattern.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  

Based on Isabelle's: Pure/pattern.ML

Uses Instantiation environments instead of combined maxidx and
isabelle envir.

Unification of Higher-Order Patterns.

See also:
Tobias Nipkow. Functional Unification of Higher-Order Patterns.
In Proceedings of the 8th IEEE Symposium Logic in Computer Science, 1993.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

infix aeconv;

signature MYPATTERN =
sig

exception dbg_unif_exp 
of (string * Term.typ) list * (Term.term * Term.term) * InstEnv.T;

  (* does not pattern unify, or is not a HO pattern *)
  exception Unif
  exception Pattern

  (* does not match *)
  exception MATCH
  
  (* trace flag *)
  val trace_unify_fail: bool Unsynchronized.ref

  (* matching/unif *)
  val match: term * term -> InstEnv.T -> InstEnv.T
  val unify: term * term -> InstEnv.T -> InstEnv.T
  val first_order_match: term * term -> InstEnv.T -> InstEnv.T

  (* term relations *)
  val matches: Proof.context -> term * term -> bool
  val matches_subterm: Proof.context -> term * term -> bool

  val aeconv: term * term -> bool
  val equiv: Proof.context -> term * term -> bool

  val first_order: term -> bool
  val pattern: term -> bool

  (* tools *)
  val eta_contract_atom: term -> term
  val rewrite_term: Proof.context -> (term * term) list -> (term -> term option) list -> term -> term

end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
structure DB_MyPattern
= struct 

exception Unif;
exception Pattern;

val trace_unify_fail = Unsynchronized.ref false;

fun string_of_term ienv binders t = 
    Syntax.string_of_term (InstEnv.get_ctxt ienv) 
      (NormalForms.beta_inst ienv (subst_bounds(map Free binders,t)));

fun bname binders i = fst (nth binders i);
fun bnames binders is = space_implode " " (map (bname binders) is);

fun typ_clash (ienv,T,U) =
  if !trace_unify_fail
  then 
    let 
      val t = Syntax.string_of_typ (InstEnv.get_ctxt ienv) (NormalForms.inst_type ienv T)
      and u = Syntax.string_of_typ (InstEnv.get_ctxt ienv) (NormalForms.inst_type ienv U)
    in tracing("The following types do not unify:\n" ^ t ^ "\n" ^ u) end
  else ()

fun clash a b =
  if !trace_unify_fail then tracing("Clash: " ^ a ^ " =/= " ^ b) else ()

fun boundVar binders i =
  "bound variable " ^ bname binders i ^ " (depth " ^ string_of_int i ^ ")";

fun clashBB binders i j =
  if !trace_unify_fail then clash (boundVar binders i) (boundVar binders j)
  else ()

fun clashB binders i s =
  if !trace_unify_fail then clash (boundVar binders i) s
  else ()

fun proj_fail (ienv,binders,F,_,is,t) =
  if !trace_unify_fail
  then let val f = Term.string_of_vname F
           val xs = bnames binders is
           val u = string_of_term ienv binders t
           val ys = bnames binders (subtract (op =) is (loose_bnos t))
       in tracing("Cannot unify variable " ^ f ^
               " (depending on bound variables " ^ xs ^ ")\nwith term " ^ u ^
               "\nTerm contains additional bound variable(s) " ^ ys)
       end
  else ()

fun ocheck_fail (F,t,binders,ienv) =
  if !trace_unify_fail
  then let val f = Term.string_of_vname F
           val u = string_of_term ienv binders t
       in tracing("Variable " ^ f ^ " occurs in term\n" ^ u ^
                  "\nCannot unify!\n")
       end
  else ()

(* term level occurs check with lookup of vars instantiation from instenv, 
   F = var name to look for occ in t *)
fun occurs (F,t,ienv) =
    let fun occ (Var (G, T)) = 
            (case InstEnv.lookup_var_inst ienv G of
               SOME(ty,t) => occ t  
             | NONE       => F = G)
          | occ(t1$t2)      = occ t1 orelse occ t2
          | occ(Abs(_,_,t)) = occ t
          | occ _           = false
    in occ t end;

fun mapbnd f =
    let fun mpb d (Bound(i))     = if i < d then Bound(i) else Bound(f(i-d)+d)
          | mpb d (Abs(s,T,t))   = Abs(s,T,mpb(d+1) t)
          | mpb d ((u1 $ u2))    = (mpb d u1)$(mpb d u2)
          | mpb _ atom           = atom
    in mpb 0 end;

fun idx [] j     = raise Unif
  | idx(i::is) j = if (i:int) =j then length is else idx is j;

fun mkabs (binders,is,t)  =
    let fun mk(i::is) = let val (x,T) = nth binders i
                        in Abs(x,T,mk is) end
          | mk []     = t
    in mk is end;

val incr = mapbnd (fn i => i+1);

fun ints_of []             = []
  | ints_of (Bound i ::bs) =
      let val is = ints_of bs
      in if member (op =) is i then raise Pattern else i::is end
  | ints_of _              = raise Pattern;

fun ints_of' ienv ts = ints_of (map (NormalForms.head_norm ienv) ts);

fun app (s,(i::is)) = app (s$Bound(i),is)
  | app (s,[])      = s;

fun red (Abs(_,_,s)) (i::is) js = red s is (i::js)
  | red t            []      [] = t
  | red t            is      jn = app (mapbnd (nth jn) t,is);


(* split_type ([T1,....,Tn]---> T,n,[]) = ([Tn,...,T1],T) *)
fun split_type (T,0,Ts)                    = (Ts,T)
  | split_type (Type ("fun",[T1,T2]),n,Ts) = split_type (T2,n-1,T1::Ts)
  | split_type _                           = error("split_type");

fun type_of_G ienv (T,n,is) =
  let val (Ts, U) = split_type (NormalForms.inst_type ienv T, n, [])
  in map (nth Ts) is ---> U end;

fun mkhnf (binders,is,G,js) = mkabs (binders, is, app(G,js));

fun mknewhnf (ienv,binders,is,F as (a,_),T,js) =
  let 
    val ty = type_of_G ienv (T,length is,js)
    val (n2,ienv2) = InstEnv.new_uninst_var ((a,0), ty) ienv
  in
    InstEnv.add_var_inst (n2, (T, mkhnf (binders, is, Var(n2,ty), js))) ienv2
  end;

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;

(* mk_proj_list(is) = [ |is| - k | 1 <= k <= |is| and is[k] >= 0 ] *)
fun mk_proj_list is =
    let fun mk(i::is,j) = if is_some i then j :: mk(is,j-1) else mk(is,j-1)
          | mk([],_)    = []
    in mk(is,length is - 1) end;

fun proj (s,ienv,binders,is) =
    let fun trans d i = if i<d then i else (idx is (i-d))+d;
        fun pr(s,ienv,d,binders) = (case NormalForms.head_norm ienv s of
              Abs(a,T,t) => let val (t',ienv') = pr(t,ienv,d+1,((a,T)::binders))
                            in (Abs(a,T,t'),ienv') end
            | t => (case strip_comb t of
                (c as Const _,ts) =>
                         let val (ts',ienv') = prs(ts,ienv,d,binders)
                         in (list_comb(c,ts'),ienv') end
                 | (f as Free _,ts) =>
                         let val (ts',ienv') = prs(ts,ienv,d,binders)
                         in (list_comb(f,ts'),ienv') end
                 | (Bound(i),ts) =>
                         let val j = trans d i
                             val (ts',ienv') = prs(ts,ienv,d,binders)
                         in (list_comb(Bound j,ts'),ienv') end
                 | (Var(F as (a,_),Fty),ts) =>
                      let val js = ints_of' ienv ts;
                          val js' = map (try (trans d)) js;
                          val ks = mk_proj_list js';
                          val ls = map_filter I js'
                          val Hty = type_of_G ienv (Fty,length js,ks)
                          val (a2,ienv') = InstEnv.new_uninst_var ((a,0), Hty) ienv
                          val H = Var(a2,Hty);
                          val ienv'' =
                              InstEnv.add_var_inst 
                                (F, (Fty, mkhnf (binders, js, H, ks))) 
                                ienv'
                      in (app(H,ls),ienv'') end
                 | _  => raise Pattern))
        and prs(s::ss,ienv,d,binders) =
              let val (s',ienv1) = pr(s,ienv,d,binders)
                  val (ss',ienv2) = prs(ss,ienv1,d,binders)
              in (s'::ss',ienv2) end
          | prs([],ienv,_,_) = ([],ienv)
   in if downto0(is,length binders - 1) then (s,ienv)
      else pr(s,ienv,0,binders)
   end;


(* mk_ff_list(is,js) = [ length(is) - k | 1 <= k <= |is| and is[k] = js[k] ] *)
fun mk_ff_list(is,js) =
    let fun mk([],[],_)        = []
          | mk(i::is,j::js, k) = if (i:int) = j then k :: mk(is,js,k-1)
                                        else mk(is,js,k-1)
          | mk _               = error"mk_ff_list"
    in mk(is,js,length is-1) end;

fun flexflex1(env,binders,F,Fty,is,js) =
  if is=js then env
  else let val ks = mk_ff_list(is,js)
       in mknewhnf(env,binders,is,F,Fty,ks) end;

fun flexflex2(ienv,binders,F,Fty,is,G,Gty,js) =
  let fun ff(F,Fty,is,G as (a,_),Gty,js) =
            if subset (op =) (js, is)
            then let val t= mkabs(binders,is,app(Var(G,Gty),map (idx is) js))
                 in InstEnv.add_var_inst (F, (Fty, t)) ienv end
            else let val ks = inter (op =) js is
                     val Hty = type_of_G ienv (Fty,length is,map (idx is) ks)
                     val (a2,ienv') = InstEnv.new_uninst_var ((a,0), Hty) ienv
                     val H = Var(a2,Hty)
                     fun lam (is) = mkabs(binders,is,app(H,map (idx is) ks));
                 in 
                   ienv' |> InstEnv.add_var_inst (G, (Gty, lam js))
                         |> InstEnv.add_var_inst (F, (Fty, lam is))
                 end;
  in if Term_Ord.indexname_ord (G,F) = LESS then
       ff(F,Fty,is,G,Gty,js) else ff(G,Gty,js,F,Fty,is) end

fun unify_types (T,U) ienv =
  (if T=U then ienv
   else snd (TypUnify.unify (U, T) ienv))
    handle TypUnify.TUNIFY => (typ_clash (ienv,T,U); raise Unif);

exception dbg_unif_exp 
of (string * Term.typ) list * (Term.term * Term.term) * InstEnv.T;

fun unif binders (s,t) ienv = 
    (case (NormalForms.head_norm ienv s, NormalForms.head_norm ienv t) of
      (Abs(ns,Ts,ts),Abs(nt,Tt,tt)) =>
         let val name = if ns = "" then nt else ns
         in unif ((name,Ts)::binders) (ts,tt) ienv end
    | (Abs(ns,Ts,ts),t) => unif ((ns,Ts)::binders) (ts,(incr t)$Bound(0)) ienv
    | (t,Abs(nt,Tt,tt)) => unif ((nt,Tt)::binders) ((incr t)$Bound(0),tt) ienv
    | p => cases (binders,ienv,p))
    handle ListPair.UnequalLengths => 
           raise dbg_unif_exp (binders, (s,t), ienv)
                 
and cases (binders,ienv,(s,t)) = case (strip_comb s,strip_comb t) of
       ((Var(F,Fty),ss),(Var(G,Gty),ts)) =>
         if F = G 
         then flexflex1(ienv,binders,F,Fty,ints_of' ienv ss,ints_of' ienv ts)
         else flexflex2(ienv,binders,F,Fty,ints_of' ienv ss,G,Gty,ints_of' ienv ts)
      | ((Var(F,Fty),ss),_)           => flexrigid (ienv,binders,F,Fty,ints_of' ienv ss,t)
      | (_,(Var(F,Fty),ts))           => flexrigid (ienv,binders,F,Fty,ints_of' ienv ts,s)
      | ((Const c,ss),(Const d,ts))   => rigidrigid (ienv,binders,c,d,ss,ts)
      | ((Free(f),ss),(Free(g),ts))   => rigidrigid (ienv,binders,f,g,ss,ts)
      | ((Bound(i),ss),(Bound(j),ts)) => rigidrigidB (ienv,binders,i,j,ss,ts)
      | ((Abs(_),_),_)                => raise Pattern
      | (_,(Abs(_),_))                => raise Pattern
      | ((Const(c,_),_),(Free(f,_),_)) => (clash c f; raise Unif)
      | ((Const(c,_),_),(Bound i,_))   => (clashB binders i c; raise Unif)
      | ((Free(f,_),_),(Const(c,_),_)) => (clash f c; raise Unif)
      | ((Free(f,_),_),(Bound i,_))    => (clashB binders i f; raise Unif)
      | ((Bound i,_),(Const(c,_),_))   => (clashB binders i c; raise Unif)
      | ((Bound i,_),(Free(f,_),_))    => (clashB binders i f; raise Unif)


and rigidrigid (ienv,binders,(a,Ta),(b,Tb),ss,ts) =
      if a<>b then (clash a b; raise Unif)
      else ienv |> unify_types (Ta,Tb) |> fold (unif binders) (ss~~ts)

and rigidrigidB (ienv,binders,i,j,ss,ts) =
     if i <> j then (clashBB binders i j; raise Unif)
     else fold (unif binders) (ss~~ts) ienv

and flexrigid (params as (ienv,binders,F,Fty,is,t)) =
      if occurs(F,t,ienv) then (ocheck_fail (F,t,binders,ienv); raise Unif)
      else (let val (u,ienv') = proj(t,ienv,binders,is)
            in ienv' |> InstEnv.add_var_inst (F, (Fty, mkabs (binders, is, u))) end
            handle Unif => (proj_fail params; raise Unif));

val unify = unif [];


(*Eta-contract a term from outside: just enough to reduce it to an atom
DOESN'T QUITE WORK!
*)
fun eta_contract_atom (t0 as Abs(a, T, body)) =
      (case eta_contract2 body  of
        body' as (f $ Bound 0) =>
            if loose_bvar1(f,0) then Abs(a,T,body')
            else eta_contract_atom (incr_boundvars ~1 f)
      | _ => t0)
  | eta_contract_atom t = t
and eta_contract2 (f$t) = f $ eta_contract_atom t
  | eta_contract2 t     = eta_contract_atom t;


(*Tests whether 2 terms are alpha/eta-convertible and have same type.
  Note that Consts and Vars may have more than one type.*)
fun t aeconv u = aconv_aux (eta_contract_atom t, eta_contract_atom u)
and aconv_aux (Const(a,T), Const(b,U)) = a=b  andalso  T=U
  | aconv_aux (Free(a,T),  Free(b,U))  = a=b  andalso  T=U
  | aconv_aux (Var(v,T),   Var(w,U))   = Term.eq_ix(v,w) andalso  T=U
  | aconv_aux (Bound i,    Bound j)    = i=j
  | aconv_aux (Abs(_,T,t), Abs(_,U,u)) = (t aeconv u)  andalso  T=U
  | aconv_aux (f$t,        g$u)        = (f aeconv g)  andalso (t aeconv u)
  | aconv_aux _ =  false;


(*** Matching ***)

exception MATCH;

fun typ_match TU ienv = TypUnify.match TU ienv
  handle TypUnify.TYPE_MATCH => raise MATCH;

(*First-order matching;
  The pattern and object may have variables in common.
  Instantiation does not affect the object, so matching ?a with ?a+1 works.
  Object is eta-contracted on the fly (by eta-expanding the pattern).
  Precondition: the pattern is already eta-contracted!
  Types are matched on the fly*)
val first_order_match =
  let
    fun mtch ienv = fn
        (Var(ixn,T), t)  =>
          if loose_bvar(t,0) then raise MATCH
          else (case InstEnv.lookup_var_inst ienv ixn of
                  NONE => 
                  ienv |> typ_match (T, fastype_of t)
                       |> InstEnv.add_var_inst (ixn, (T, t))
                | SOME (_,u) => if t aeconv u then ienv else raise MATCH)
      | (Free (a,T), Free (b,U)) =>
          if a=b then typ_match (T,U) ienv else raise MATCH
      | (Const (a,T), Const (b,U))  =>
          if a=b then typ_match (T,U) ienv else raise MATCH
      | (Bound i, Bound j)  =>  if  i=j  then ienv else raise MATCH
      | (Abs(_,T,t), Abs(_,U,u))  =>
          mtch (typ_match (T,U) ienv) (t,u)
      | (f$t, g$u) => mtch (mtch ienv (f,g)) (t, u)
      | (t, Abs(_,U,u))  =>  mtch ienv ((incr t)$(Bound 0), u)
      | _ => raise MATCH
  in fn tu => fn env => mtch env tu end;


(* Matching of higher-order patterns *)
fun match_bind (ienv,binders,ixn,T,is,t) =
  let val js = loose_bnos t
  in if null is
     then if null js then InstEnv.add_var_inst (ixn, (T, t)) ienv else raise MATCH
     else if subset (op =) (js, is)
          then let val t' = if downto0(is,length binders - 1) then t
                            else mapbnd (idx is) t
               in InstEnv.add_var_inst (ixn, (T, mkabs (binders, is, t')))
                                        ienv end
          else raise MATCH
  end;

fun match (po as (pat,obj)) ienv =
let
  (* Pre: pat and obj have same type *)
  fun mtch binders (pat,obj) ienv =
    case pat of
      Abs(ns,Ts,ts) =>
        (case obj of
           Abs(nt,Tt,tt) => mtch ((nt,Tt)::binders) (ts,tt) ienv
         | _ => let val Tt = InstEnv.inst_typ_tvars ienv Ts
                in mtch((ns,Tt)::binders) (ts,(incr obj)$Bound(0)) ienv end)
    | _ => (case obj of
              Abs(nt,Tt,tt) =>
                mtch((nt,Tt)::binders) ((incr pat)$Bound(0),tt) ienv
            | _ => cases(binders,ienv,pat,obj))
  and cases (binders,ienv,pat,obj) =
    let val (ph,pargs) = strip_comb pat
        fun rigrig1(iTs,oargs) = fold (mtch binders) (pargs~~oargs) ienv
        fun rigrig2((a:string,Ta),(b,Tb),oargs) =
              if a <> b then raise MATCH
              else rigrig1(typ_match (Ta,Tb) ienv, oargs)
    in case ph of
         Var(ixn,T) =>
           let val is = ints_of pargs
           in case InstEnv.lookup_var_inst ienv ixn of
                NONE => match_bind(ienv,binders,ixn,T,is,obj)
              | SOME (_,u) => if obj aeconv (red u is []) then ienv
                              else raise MATCH
           end
       | _ =>
           let val (oh,oargs) = strip_comb obj
           in case (ph,oh) of
                (Const c,Const d) => rigrig2(c,d,oargs)
              | (Free f,Free g)   => rigrig2(f,g,oargs)
              | (Bound i,Bound j) => if i<>j then raise MATCH
                                     else rigrig1(ienv,oargs)
              | (Abs _, _)        => raise Pattern
              | (_, Abs _)        => raise Pattern
              | _                 => raise MATCH
           end
    end;
  val pT = fastype_of pat
  and oT = fastype_of obj
  val ienv' = typ_match (pT, oT) ienv;
in mtch [] po ienv' handle Pattern => first_order_match po ienv' end;

fun matches ctxt po = 
    (match po (InstEnv.init ctxt); true) handle MATCH => false;

fun equiv ctxt (t, u) = matches ctxt (t, u) andalso matches ctxt (u, t);


(* Does pat match a subterm of obj? *)
fun matches_subterm ctxt (pat, obj) =
  let
    fun msub bounds obj = matches ctxt (pat, obj) orelse
      (case obj of
        Abs (x, T, t) => msub (bounds + 1) (snd (Term.dest_abs (Name.bound bounds, T, t)))
      | t $ u => msub bounds t orelse msub bounds u
      | _ => false)
  in msub 0 obj end;

fun first_order (Abs(_,_,t)) = first_order t
  | first_order (t $ u) = first_order t andalso first_order u andalso
                         not(is_Var t)
  | first_order _ = true;

fun pattern (Abs (_, _, t)) = pattern t
  | pattern t =
      let val (head, args) = strip_comb t in
        if is_Var head then
          forall is_Bound args andalso not (has_duplicates (op aconv) args)
        else forall pattern args
      end;


(* rewriting -- simple but fast *)

fun rewrite_term ctxt rules procs tm =
  let
    val skel0 = Bound 0;

    fun variant_absfree bounds (x, T, t) =
      let
        val (x', t') = Term.dest_abs (Name.bound bounds, T, t);
        fun abs u = Abs (x, T, abstract_over (Free (x', T), u));
      in (abs, t') end;

    fun match_rew tm (tm1, tm2) =
      let val rtm = the_default tm2 (Term.rename_abs tm1 tm tm2) in
        SOME (InstEnv.inst_trm (match (tm1, tm) (InstEnv.init ctxt)) rtm, rtm)
          handle MATCH => NONE
      end;

    fun rew (Abs (_, _, body) $ t) = SOME (subst_bound (t, body), skel0)
      | rew tm = (case get_first (match_rew tm) rules of
          NONE => Option.map (rpair skel0) (get_first (fn p => p tm) procs)
        | x => x);

    fun rew1 bounds (Var _) _ = NONE
      | rew1 bounds skel tm = (case rew2 bounds skel tm of
          SOME tm1 => (case rew tm1 of
              SOME (tm2, skel') => SOME (the_default tm2 (rew1 bounds skel' tm2))
            | NONE => SOME tm1)
        | NONE => (case rew tm of
              SOME (tm1, skel') => SOME (the_default tm1 (rew1 bounds skel' tm1))
            | NONE => NONE))

    and rew2 bounds skel (tm1 $ tm2) = (case tm1 of
            Abs (_, _, body) =>
              let val tm' = subst_bound (tm2, body)
              in SOME (the_default tm' (rew2 bounds skel0 tm')) end
          | _ =>
            let val (skel1, skel2) = (case skel of
                skel1 $ skel2 => (skel1, skel2)
              | _ => (skel0, skel0))
            in case rew1 bounds skel1 tm1 of
                SOME tm1' => (case rew1 bounds skel2 tm2 of
                    SOME tm2' => SOME (tm1' $ tm2')
                  | NONE => SOME (tm1' $ tm2))
              | NONE => (case rew1 bounds skel2 tm2 of
                    SOME tm2' => SOME (tm1 $ tm2')
                  | NONE => NONE)
            end)
      | rew2 bounds skel (Abs body) =
          let
            val (abs, tm') = variant_absfree bounds body;
            val skel' = (case skel of Abs (_, _, skel') => skel' | _ => skel0)
          in case rew1 (bounds + 1) skel' tm' of
              SOME tm'' => SOME (abs tm'')
            | NONE => NONE
          end
      | rew2 _ _ _ = NONE;

  in the_default tm (rew1 0 skel0 tm) end;

end;

structure MyPattern : MYPATTERN = DB_MyPattern;

val my_trace_unify_fail = MyPattern.trace_unify_fail;

