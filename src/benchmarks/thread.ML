(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./thread.ML
    Author:     Moa Johansson
                Lucas Dixon
              
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Code for threading and timouts. Useful for benchmarking!
    Changed name to IsaThread as there is a Thread in PolyML now.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

signature ISA_THREAD =
sig
  (* given timeout in seconds run function limited by timeout *)
  val usr_timeout : Time.time -> (unit -> 'a) -> 'a option;

  (* probably do not want to use these: PolyML 5.1 + has proper thread library *)
  val mk_real_timer : (bool -> 'a) -> Time.time -> Posix.Process.pid -> 'a
  val mk_cpu_usr_timer : (Time.time -> bool -> 'a) 
                         -> Time.time -> Posix.Process.pid -> 'a
  val split : 
      (Posix.Process.pid -> 'a) (* child *)
      -> (unit -> 'a) (* parent *)
      -> 'a  
end;

structure IsaThread : ISA_THREAD =
struct

(* Kills the process with the given pid after tmax seconds if it*)
(* hasn't finished                                              *)
fun mk_real_timer endf tmax pid =
    let 
      val timenow = Timer.startRealTimer();
      val nap = Time.fromSeconds 1;

      fun timeout_chk timer =
          if (Timer.checkRealTimer timer) >= tmax then 
            (Posix.Process.kill(Posix.Process.K_PROC(pid),
                                Posix.Signal.kill);
             endf true)
          else
            let 
              val finished = Posix.Process.waitpid_nh 
                               ((Posix.Process.W_CHILD(pid)), [])
            in
              case finished of
                NONE => ((OS.Process.sleep nap); timeout_chk timer)
              | SOME (p, exit_stat) =>
                endf false
            end
    in timeout_chk timenow end;

fun mk_cpu_usr_timer endf tmax pid =
    let 
      val timenow = Timer.startCPUTimer();
      val nap = Time.fromSeconds 1;

      fun timeout_chk timer =
          let val curtime = (#usr (Timer.checkCPUTimer timer)) in
            if curtime >= tmax then 
              (Posix.Process.kill(Posix.Process.K_PROC(pid),
                                  Posix.Signal.kill);
               endf curtime true)
            else
              let 
                val finished = Posix.Process.waitpid_nh 
                                 ((Posix.Process.W_CHILD(pid)), [])
              in
                case finished of
                  (* PolyML note: Posix.Process.sleep is buggy and
                                  leaves mad processor usage. *) 
                  NONE => ((OS.Process.sleep nap); timeout_chk timer)
                | SOME (p, exit_stat) =>
                  endf curtime false
              end
          end
    in timeout_chk timenow end;


(* Splits execution in two branches, one executing the function *) 
(* 'parent_f' and the other 'child_f'                           *)
fun split parent_f child_f =
    let val isChild = Posix.Process.fork()
    in
      case isChild of 
        NONE => child_f()
      | SOME pid => parent_f pid
    end;

fun usr_timeout maxt f =  
    let 
      val return_mutex = Mutex.mutex ();
      val wait_for_return_mutex = Mutex.mutex ();
      val _  = Mutex.lock wait_for_return_mutex;
      val return_value = ref NONE;
      val working_thread = 
          Thread.fork ((fn () => let val v = f();
                                     val _ = Mutex.lock return_mutex;
                                     val _ = return_value := SOME v;
                                     val _ = Mutex.unlock wait_for_return_mutex;
                                 in Thread.exit () end), []);
      val sleeping_thread = 
          Thread.fork ((fn () => (OS.Process.sleep maxt;
                                  Mutex.lock return_mutex;
                                  Mutex.unlock wait_for_return_mutex;
                                  Thread.exit ())), []);
      fun try_kill thread = 
          ((Thread.kill thread) handle Thread _ => ());
    in 
      (Mutex.lock wait_for_return_mutex; 
       try_kill working_thread; 
       try_kill sleeping_thread; 
       (!return_value))
    end;


end;


(* testing code: 

fun f s 0 = print (s ^ "-end\n")
  | f s n = (print (s ^ "\n");
             Posix.Process.sleep (Time.fromSeconds 1); 
             f s (n - 1));

fun f s n = 
    let val timer = Timer.startCPUTimer();
      fun timestr () = Time.toString (#usr (Timer.checkCPUTimer timer));
      fun f' s 0 = print (s ^ "-end: " ^ (timestr()) ^ "\n")
        | f' s n = (print (s ^ ":" ^ (string_of_int n) ^ ":" 
                           ^ (timestr()) ^ "\n");
                    OS.Process.sleep (Time.fromSeconds 1); 
                    f s (n - 1));
    in f' s n end;


fun f2 n () = (f2 (n + n) (); ());


fun fk () = 
    case (Posix.Process.fork()) 
     of NONE => (f "a" 3; Posix.Process.exit (Word8.fromInt 0))
      | SOME pid => (f "b" 3);

Thread.split 
   (fn pid => Thread.mk_cpu_usr_timer 
        (fn t => (fn true => writeln ("killed baby: " 
                                      ^ (Time.toString t))
                   | false => writeln ("baby finished naturally" 
                                       ^ (Time.toString t))))
        (Time.fromSeconds 2)
        pid)
   (f2 1);

   (fn _ => (f "child" 15; exit 0));

   (f2 1);


 (f "c" 3));

*)
