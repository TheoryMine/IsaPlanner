(* ***  IN PROGRESS *** *)

(*  *)
signature SYNTH_TERM_ORACLE = sig 
  type param
  val default_param : param (* contains global timing params, as well as local ones also *)

  type result
  val check' : Theory.theory -> Term.term -> param -> (result option * param)
  val check : Term.term -> Theory.theory -> (result option * Theory.theory)

  val ThyData : THEORY_DATA 
  sharing ThyData.T = param;

end;

(*  *)
signature SYNTH_COUNTER_EXAMPLE_FINDER = SYNTH_TERM_ORACLE;

(*  *)
signature SYNTH_PROVER = SYNTH_TERM_ORACLE;

(* *)
signature SYNTH_PARAM = sig
  structure CounterEx : SYNTH_COUNTER_EXAMPLE_FINDER;
  structure Prover : SYNTH_PROVER;
end;


structure CounterEx : SYNTH_COUNTER_EXAMPLE_FINDER = 
struct
  (* config for counter example finding *)
  structure Config = struct
    type config = 
         {size : int, 
          iterations : int, 
          default_type = Term.typ option };
    val default = 
        {size = 5, 
         iterations = 5, 
         default_type = SOME (Type("Int.int", [])) 
        };
    fun get_size rep = #size rep; 
    fun get_iterations rep = #iterations rep; 
    fun get_default_type rep = #default_type rep; 
    fun update_size f rep = 
        {size = f (#size rep), 
         iterations = (#iterations rep),
         default_type = (#default_type rep)};
    fun update_iterations f rep = 
        {size = (#size rep), 
         iterations = f (#iterations rep),
         default_type = (#default_type rep)};
    fun update_default_type f rep = 
        {size = (#size rep), 
         iterations = (#iterations rep),
         default_type = f (#default_type rep)};
  end;

  (* statistics for counter-example finding *)
  structure Stats =
  struct 
    type stats = 
         {last_timing : Time.time, 
          total_timing : Time.time,
          cex_sum : int };
    val default = 
        {last_timing = Time.zeroTime, 
         total_timing = Time.zeroTime,
         cex_sum = 0};
    fun get_last_timing rep = #last_timing rep; 
    fun get_total_timing rep = #total_timing rep; 
    fun get_cex_sum rep = #cex_sum rep; 
    fun update_last_timing f rep = 
        {last_timing = f (#last_timing rep), 
         total_timing = (#total_timing rep),
         cex_sum = (#cex_sum rep)};
    fun update_total_timing f rep = 
        {last_timing = (#last_timing rep), 
         total_timing = f (#total_timing rep),
         cex_sum = (#cex_sum rep)};
    fun update_cex_sum f rep = 
        {last_timing = (#last_timing rep), 
         total_timing = (#total_timing rep),
         cex_sum = f (#cex_sum rep)};

    (* imagine s1 happened before s2 *)
    fun precompose s1 s2 = 
        { last_timing = (get_last_timing s2), 
          total_timing = (get_total_timing s1) + (get_total_timing s2),
          cex_sum = (get_cex s1) + (get_cex s2) };
    
    fun add_new_time t s = 
        s |> set_last_timing t 
          |> update_total_timing (fn t' => t + t');
    fun add_new_counter_example s = 
        s |> update_cex_sum (fn n => n + 1);

   end;

  (* theory parametrisation for counter example finding: config & stats *)
  structure Param
     type param = { config : cex_param, 
                    stats : stats };
     fun get_config p = #config rep;
     fun get_stats p = #stats rep;
     fun update_config f rep = 
          {config = f (#config rep)
           stats = (#stats rep)};
     fun update_stats f rep = 
          {config = (#config rep)
           stats = f (#stats rep)};
    val set_stats = update_stats o K; 
    val set_config = update_config o K; 
  
    (*  *)
    val default = 
        { config = Config.default, 
          stats = Stats.default };
  
    fun reset_stats = set_stats Stats.default;  
    (* imagine p1 happened before p2 *)
    fun precompose p1 p2 = 
        p2 |> update_stats (Stats.precompose (get_stats p1));
  
    (* make data that lives in the theory *)
    structure ThyData = Theory_Data
    (
      type T = param;
      val empty = default;
      val extend = I;
      fun merge (p1, p2) = precompose p1 p2;
    );
    val of_ctxt = ThyData.get o ProofContext.theory_of;
    val of_thy = ThyData.get;

    fun add_new_time t p = update_stats ()
  end;

  (* Counter-example checking *)
  fun check' thy t param =
    let 
      val timer = Timer.startCPUTimer ();
      (* Change any Type-Variables to Frees *)
      val t' = Type.legacy_freeze trm
      val result = (CounterExCInfo.quickcheck_term thy (#cex param, []) t')
                   handle ERROR _ => NONE;
      val time2 = (#usr (Timer.checkCPUTimer timer));
      val param2 = 
          param 
            |> Param.add_new_time time2
            |> (if is_some result then Param.add_new_counter_example else I)
    in (result, param) end;
    
  fun check' t thy = 
      let val (res,p2) = check' thy (of_thy thy) t
      in (res,ThyData.put p2 thy)

end;



structure Prover : SYNTH_PROVER = 
struct
  
end;



structure SynthParam =
struct

  structure Prover : SYNTH_PROVER = 
  struct
    
  end;

  structure Thy = struct
    
  end;

  structure Ctxt = struct 
    
  end;
end;

