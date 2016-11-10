
structure TermAnalysis =
struct

fun Tname (Type (name, _)) = name
  | Tname _ = ""

fun typ_of_dtyp _ typ_assoc (Old_Datatype_Aux.DtTFree a) =
    the (AList.lookup (op =) typ_assoc (Old_Datatype_Aux.DtTFree a))
  | typ_of_dtyp descr typ_assoc (Old_Datatype_Aux.DtType (s, Us)) =
    Type (s, map (typ_of_dtyp descr typ_assoc) Us)
  | typ_of_dtyp descr typ_assoc (Old_Datatype_Aux.DtRec i) =
    let val (s, ds, _) = the (AList.lookup (op =) descr i) in
      Type (s, map (typ_of_dtyp descr typ_assoc) ds)
    end
exception REFUTE of string * string; 
fun ground_types ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    fun collect_types T acc =
      (case T of
        Type (@{type_name fun}, [T1, T2]) => collect_types T1 (collect_types T2 acc)
      | Type (@{type_name prop}, []) => acc
      | Type (@{type_name set}, [T1]) => collect_types T1 acc
      | Type (s, Ts) =>
          (case BNF_LFP_Compat.get_info thy [] s of
            SOME info =>  (* inductive datatype *)
              let
                val index = #index info
                val descr = #descr info
                val (_, typs, _) = the (AList.lookup (op =) descr index)
                val typ_assoc = typs ~~ Ts
                (* sanity check: every element in 'dtyps' must be a *)
                (* 'DtTFree'                                        *)
                val _ = if Library.exists (fn d =>
                  case d of Old_Datatype_Aux.DtTFree _ => false | _ => true) typs then
                  raise REFUTE ("ground_types", "datatype argument (for type "
                    ^ Syntax.string_of_typ ctxt T ^ ") is not a variable")
                else ()
                (* required for mutually recursive datatypes; those need to   *)
                (* be added even if they are an instance of an otherwise non- *)
                (* recursive datatype                                         *)
                fun collect_dtyp d acc =
                  let
                    val dT = typ_of_dtyp descr typ_assoc d
                  in
                    case d of
                      Old_Datatype_Aux.DtTFree _ =>
                      collect_types dT acc
                    | Old_Datatype_Aux.DtType (_, ds) =>
                      collect_types dT (fold_rev collect_dtyp ds acc)
                    | Old_Datatype_Aux.DtRec i =>
                      if member (op =) acc dT then
                        acc  (* prevent infinite recursion *)
                      else
                        let
                          val (_, dtyps, dconstrs) = the (AList.lookup (op =) descr i)
                          (* if the current type is a recursive IDT (i.e. a depth *)
                          (* is required), add it to 'acc'                        *)
                          val acc_dT = if Library.exists (fn (_, ds) =>
                            Library.exists Old_Datatype_Aux.is_rec_type ds) dconstrs then
                              insert (op =) dT acc
                            else acc
                          (* collect argument types *)
                          val acc_dtyps = fold_rev collect_dtyp dtyps acc_dT
                          (* collect constructor types *)
                          val acc_dconstrs = fold_rev collect_dtyp (maps snd dconstrs) acc_dtyps
                        in
                          acc_dconstrs
                        end
                  end
              in
                (* argument types 'Ts' could be added here, but they are also *)
                (* added by 'collect_dtyp' automatically                      *)
                collect_dtyp (Old_Datatype_Aux.DtRec index) acc
              end
          | NONE =>
            (* not an inductive datatype, e.g. defined via "typedef" or *)
            (* "typedecl"                                               *)
            insert (op =) T (fold collect_types Ts acc))
      | TFree _ => insert (op =) T acc
      | TVar _ => insert (op =) T acc)
  in
    fold_types collect_types t []
  end;


fun tnames_of_list [] = []
  | tnames_of_list ((Type (n1,_))::t) = n1::(tnames_of_list t)
  | tnames_of_list (_::t) = tnames_of_list t

fun type_names_of_thm ctxt thm = tnames_of_list (ground_types ctxt (Thm.prop_of thm))
end