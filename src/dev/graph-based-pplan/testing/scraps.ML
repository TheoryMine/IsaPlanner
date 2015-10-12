(* add at most one thing to gtab, put the rest in the list of extras *)
fun group_extras gtab l = 
    let fun group_extra (h as (n,_),(gtab,extras)) = 
            if GTab.contains gtab n then (gtab,h::extras)
            else (GTab.doadd h gtab, extras);
    in List.foldr group_extra (gtab,[]) l end;
