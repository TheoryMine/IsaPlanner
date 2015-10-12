

signature PLAN_SPEC_CTXT 
= sig

type gname
type state
type ctxt

val add_goalchoice : string -> (gname -> state -> gname list * gname list)
    -> ctxt -> ctxt 

val get_goalchoice: ctxt -> string -> 

end;


signature PLAN_SPEC 
= sig

type state

ctxt -> string -> (state -> 
