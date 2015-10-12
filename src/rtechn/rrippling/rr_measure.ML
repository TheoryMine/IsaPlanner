(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rr_measure.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Modified:   20 Oct 2004  
    Created:    24 Feb 2004
    Modified:   Dominic Mulligan
                12 Sept 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Measures for rippling: ie for a given single annoatted term. 
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature BASIC_RRIPPLE_MEASURE = 
  sig 
    type T
    val name : string
    val ord : T * T -> order
    val of_eterm : RREmbeddingLib.eterm -> T list
    val aterm_of : T -> RRipplingATerms.T
    val success_chk : T -> bool
    val pretty : T -> Pretty.T
  end;

functor RRippleMeasureFUN(val name : string
                          val atermifier : RREmbeddingLib.eterm -> RRipplingATerms.T list
                          val measuref : RRipplingATerms.T -> (int * int)) : BASIC_RRIPPLE_MEASURE =
  struct (* functional wave-fronts in goal, relational wave-fronts in goal *)
    type T = (RRipplingATerms.T * (int * int));

    val name = name;

    fun ord ((at1, x), (at2, y)) = 
      let
        fun aux (x1, x2) (y1, y2) =
          case Library.int_ord(x1, y1) of
            EQUAL => Library.int_ord(x2, y2)
          | z => z
      in
        aux x y
      end
   
    fun of_eterm etrm =
      map (fn a => (a, measuref a)) (atermifier etrm)

    val aterm_of = fst

    fun pretty (_,(x,y)) = Pretty.str ((Int.toString x) ^ ", " ^ (Int.toString y))

    fun success_chk (_,(x, y)) = (x=0 andalso y=0)
  end
