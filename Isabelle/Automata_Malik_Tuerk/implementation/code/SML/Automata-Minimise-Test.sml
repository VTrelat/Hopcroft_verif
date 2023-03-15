structure list_org = List;
use "Leiss/set.sml";
use "Leiss/fm.sml";
use "Automata_RBT.sml";
structure List = list_org;

use "../Automata_10000_50_2.sml";
open NFA_string


fun input_to_DFA (f, d) = 
let
  val dfa = dfa_construct ([], [],
      List.map (fn (q1, a, q2) => (q1, [string_Sigma_param.int_to_Sigma a], q2)) d, [0], f);
in
  dfa
end;

fun DFA_to_fm dfa = 
let
  val (q, a, d, i, f) = nfa_destruct_simple dfa;
  val M = Fm.make{final=f,start=i,trans=d};
in
  M
end;


fun measure_gen f a =
let
  val st = Time.now();
  val r = f a;
  val et = Time.now();
  val t1 = Time.toMilliseconds (Time.- (et, st))
in
  t1
end;

fun measure_gen_list f l = measure_gen (fn () => foldl (fn (x, _) => (f x; ())) () l)

fun measure_gen_list f l = measure_gen (fn () => map f l) 

use "../Automata_1000_2500_2.sml";

fun measure_input_file dfas =
let
  val dfa_list = List.map input_to_DFA dfas
  val fm_list = List.map DFA_to_fm dfa_list
  val _ = PolyML.fullGC ();
  val tt = measure_gen_list nfa_Hopcroft dfa_list ()
  val _ = print (Int.toString tt);
  val _ = print "\n";
  val _ = PolyML.fullGC ();
  val tb = measure_gen_list Fm.minimize fm_list () 
  val _ = PolyML.fullGC ();
in
  (print ("Tuerk " ^ ((Int.toString tt) ^ " ms - "));
   print ("Leiss " ^ ((Int.toString tb) ^ " ms\n")))
end;

val _ = measure_input_file dfas;


(*

val (_, my_DFA) = input_to_fm_DFA (List.nth dfas 40)

PolyML.exception_trace (fn () => nfa_Hopcroft my_DFA)

open NFA_string 

PolyML.export ("Dummy.exe", measure_input_file)


fun NFA_to_FM nfa =
let
  val (Q, A, D, I, F) = nfa_destruct_simple nfa
  val M = Fm.make{final=F,start=I,trans=D};
in
  (length Q, M)
end


fun measure_compare s1 f1 s2 f2 (st_no, nfa1, nfa2) =
let
  val st = Time.now();
  val r = f1 nfa1;
  val et = Time.now();
  val t1 = Time.toMilliseconds (Time.- (et, st))

  val st = Time.now();
  val r = f2 nfa2;
  val et = Time.now();
  val t2 = Time.toMilliseconds (Time.- (et, st))

  val _ = print ((Int.toString st_no) ^ " states: ");
  val _ = print (s1 ^ (Int.toString t1) ^ " ms   -   ");
  val _ = print (s2 ^ (Int.toString t2) ^ " ms\n");
in
  ()
end;

fun measure_compare_simple s1 f1 s2 f2 (st_no, nfa) =
    measure_compare s1 f1 s2 f2 (st_no, nfa, nfa)

fun measure_single s1 f1 (st_no, nfa) =
let
  val _ = print ((Int.toString st_no) ^ " states: ");

  val st = Time.now();
  val r = f1 nfa;
  val et = Time.now();
  val t1 = Time.toMilliseconds (Time.- (et, st))

  val _ = print (s1 ^ (Int.toString t1) ^ " ms\n");
in
  r
end;


(* compare Hopcroft and Brzozowski *)

val minimise_NFA_compare =
  measure_compare_simple "Brzozowski " nfa_Brzozowski
     "Hopcroft NFA " nfa_Hopcroft_NFA

val minimise_DFA_compare =
  measure_compare_simple "Brzozowski " nfa_Brzozowski
     "Hopcroft DFA " nfa_Hopcroft

val determinise_measure =
  measure_single "determinise " nfa_determinise

val Hopcroft_NFA_measure =
  measure_single "Hopcroft NFA " nfa_Hopcroft_NFA

val Hopcroft_ICDFA_measure =
  measure_single "Hopcroft DFA " nfa_Hopcroft

val Brzozowski_measure =
  measure_single "Brzozowski " nfa_Brzozowski

fun NFA_to_FM nfa =
let
  val (Q, A, D, I, F) = nfa_destruct_simple nfa
  val M = Fm.make{final=F,start=I,trans=D};
in
  (length Q, M)
end

fun minimise_FM_compare X =
  measure_compare "FM " Fm.minimize
     "Hopcroft NFA " nfa_Hopcroft_NFA X


(* Generate some random NFAs
 
   generate_random_NFAs #NFAs #states #labels #density #desity_accepting
*)

fun normalise_NFA nfa =
let
  val nfa' = nfa_normalise nfa
  val st_no = nfa_states_no nfa
in
  (st_no, nfa')
end

fun normalise_DFA (n, nfa) =
let
  val nfa' = nfa_determinise nfa
  val st_no = nfa_states_no nfa
in
  (st_no, nfa')
end

fun normalise_DFA_FM (n, nfa) =
let
  val nfa' = nfa_determinise nfa
  val (st_no, fm) =  NFA_to_FM nfa'
in
  (st_no, fm, nfa')
end

fun count_states nfa =
let
  val st_no = nfa_states_no nfa
in
  (st_no, nfa)
end

fun fib n =
  let
    fun aux n a b = if n=0 then a else aux (n-1) b (a^b) 
  in aux n "1" "0" end

fun fib_automaton n =
  let 
     val test=fib n;
     val m = String.size test;
     fun trans i = (i mod m, ["a"], (i+1) mod m);
     fun transL i = if i = 0 then [] else (trans (i-1)) :: (transL (i-1));
     fun acceptL i = if i = 0 then [] else 
       (if (String.sub (test, i-1) = #"1") then ((i-1) :: (acceptL (i-1))) else (acceptL (i-1)));
  in
    nfa_construct ([], [], transL m, [0], acceptL m)
  end

val x = Hopcroft_ICDFA_measure (String.size(fib 20), fib_automaton 20)


val random_NFAs___Hopcroft2 = (map normalise_NFA (generate_random_NFAs 10 80 5 0.6 0.2))
val random_NFAs___Hopcroft3 = map normalise_NFA (generate_random_NFAs 10 120 4 0.8 0.2)

val random_NFAs___Hopcroft2_DFA = (map normalise_DFA random_NFAs___Hopcroft2)
val random_NFAs___Hopcroft2_DFA_FM = (map normalise_DFA_FM random_NFAs___Hopcroft2)


val random_NFAs___Hopcroft2_int = (map normalise_NFA (NFA_int.generate_random_NFAs 50 120 2 0.9 0.2))


map minimise_FM_compare random_NFAs___Hopcroft2_DFA_FM

map determinise_measure random_NFAs___Hopcroft2

map Brzozowski_measure random_NFAs___Hopcroft2_DFA
map Hopcroft_ICDFA_measure random_NFAs___Hopcroft2_DFA

map Hopcroft_ICDFA_measure random_NFAs___Hopcroft2_DFA


val nfa = #2 (nth 4 random_NFAs___Hopcroft2_DFA)
val nfa = #2 (nth 1 random_NFAs___Hopcroft2_DFA)

*)