(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      gproof/trm_rename.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
                Initially written Oct 2005, Updated 10 Mar 2006        *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Renames variables in a term. Defined abstractly over generic
    notion of trm. 

*)

signature TRM_RENAME =
sig
    type T

    type ingoretf = TVar.name * TVar.sort -> bool
    type ingorevf = Var.name * Var.typ -> bool

    val ignore_none : ingoretf * ingorevf

    val empty : T

    val init : Trm.vtab -> T

    val names_of : T -> Trm.vtab

    val renamings_of : T -> 
          (TVar.name * (TVar.name * TVar.sort)) list
          * (Var.name * (Var.name * Var.typ)) list 

    val rename_var :
        ingorevf -> T 
        -> Var.name * Var.typ 
        -> T * Var.name
    val rename_all_var :
        T -> Var.name * Var.typ 
        -> T * Var.name
    val rename_tvar : 
        ingoretf -> T 
        -> TVar.name * TVar.sort -> 
        T * TVar.name
    val rename_all_tvar : 
        T -> TVar.name * TVar.sort -> 
        T * TVar.name
    val rename_type :
       ingoretf -> T -> Var.typ -> T * Var.typ
    val rename_all_type :
       T -> Var.typ -> T * Var.typ

    val rename_trm : ingoretf * ingorevf -> T -> Trm.T -> T * Trm.T
    val rename_all_trm :  T -> Trm.T -> T * Trm.T

    val rename_trm' : ingoretf * ingorevf -> Trm.T -> T * Trm.T

    (* just rename the vtab *)
    val rename_vtab : Trm.vtab -> T -> T

end;


structure TrmRename : TRM_RENAME 
= struct

    type ingoretf = TVar.name * TVar.sort -> bool;
    type ingorevf = Var.name * Var.typ -> bool;

   (* contains a dummy entry for each variable that is not renamed 
      this allows a fast algorithm for renaming 
    *)
    datatype T = RenameTab 
             of (TVar.name TVar.NTab.T (* renamings *)
                 * TVar.sort TVar.NTab.T) * (* all new names *)
                (Var.name Var.NTab.T (* renamings *)
                 * Var.typ Var.NTab.T); (* all new names *)

    (* filter out dummy renamings *)
    fun renamings_of (RenameTab ((tyrn, sorts), (vrns, typs))) =
          (List.foldr 
             (fn ((n1,n2),L) => 
                 if n1 = n2 then L else 
                 (n1, (n2, TVar.NTab.get sorts n2))::L)
             [] (TVar.NTab.list_of tyrn),
           List.foldr 
             (fn ((n1,n2),L) => 
                 if n1 = n2 then L else 
                 (n1, (n2, Var.NTab.get typs n2))::L)
             [] (Var.NTab.list_of vrns));

   val empty = 
       RenameTab ((TVar.NTab.empty , TVar.NTab.empty), 
                  (Var.NTab.empty, Var.NTab.empty));

   fun init vtab = 
       let val (tvnames,vnames) = Trm.dest_vtab vtab
       in
         (RenameTab ((TVar.NTab.empty, tvnames), 
                     (Var.NTab.empty, vnames)))
       end;

   fun names_of (RenameTab ((_, tvnames), (_, vnames))) = 
       Trm.mk_vtab (tvnames, vnames);

   val ignore_none : ingoretf * ingorevf = (K false, K false);

   fun rename_tvar ignoref (vtab as RenameTab ((tyrn, tyns), vs))
                   (x as (n, srt)) = 
         if ignoref x then 
           (case TVar.NTab.try_ins (n,srt) tyns
                of NONE => vtab 
                 | SOME tyns' => RenameTab ((tyrn,tyns'),vs),
            n)
         else 
           case TVar.NTab.lookup tyrn n  
            of NONE => let val (n', tyns') = 
                               TVar.NTab.add (n,srt) tyns 
                       in (RenameTab 
                             ((TVar.NTab.update_new (n,n') tyrn, 
                               tyns'),vs), 
                           n')
                       end
             | (SOME n') => (vtab,n');

   val rename_all_tvar = rename_tvar (K false);

   (* results in vns containing the new name 
      will contain a dummy entry for each variable that is not renamed
   *)
   fun rename_var ignoref (vtab as RenameTab (tys, (vrn, vns))) 
                  (x as (n, typ)) = 
         if ignoref x then 
           (case Var.NTab.try_ins (n,typ) vns
                of NONE => vtab 
                 | SOME vns' => RenameTab (tys,(vrn,vns')),
            n)
         else 
           case Var.NTab.lookup vrn n
            of NONE => let val (n', vns') = Var.NTab.add (n,typ) vns 
                       in (RenameTab 
                             (tys, 
                              (Var.NTab.update_new (n,n') vrn,
                               vns')), 
                           n')
                       end
             | (SOME n') => (vtab,n');

   val rename_all_var = rename_var (K false);

   fun rename_tvar' ignoref vtab ((n,srt),typ) = 
       let val (vtab2,n2) = rename_tvar ignoref vtab (n,srt)
       in (vtab2,Trm.mk_tvar (n2,srt)) end;

   fun rename_var' ignoref vtab ((n,typ),trm) = 
       let val (vtab2,n2) = rename_var ignoref vtab (n,typ) 
       in (vtab2, Trm.mk_var (n2,typ)) end;

   fun rename_type ignoref vtab typ = 
       Trm.foldmap_typ_tvars (rename_tvar' ignoref) vtab typ;

   val rename_all_type = rename_type (K false);
   
   (* rename a term to avoid vtab names, but ignore the given names. *)
   fun rename_trm (ignorefs as (ignoret,ignorev)) vtab t = 
       let 
         val (vtab1,t1) = 
             Trm.foldmap_trm_tvars (rename_tvar' ignoret) vtab t
         val (vtab2,t2) = 
             Trm.foldmap_trm_vars (rename_var' ignorev) vtab1 t1
       in (vtab2,t2) end;

   val rename_all_trm = rename_trm ignore_none;

   (* basically an efficient version of zero var indexes *)
   fun rename_trm' ignorefs t = rename_trm ignorefs empty t;

   (* *)
   fun rename_vtab vtab rntab = 
       let 
         val (typs_vtab, trm_vtab) = Trm.dest_vtab vtab
       in 
         rntab
           |> (fold (fn v => fn tab => fst (rename_tvar (K false) tab v))
                    (TVar.NTab.list_of typs_vtab))
           |> (fold (fn v => fn tab => fst (rename_var (K false) tab v))
                    (Var.NTab.list_of trm_vtab))
       end;
end;
