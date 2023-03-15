use "Automata_RBT.sml"

(* Let's construct a dummy automaton *)

val automaton1 = NFA_string.nfa_construct ([], [], [(1, ["a", "b"], 2), (2, ["a"], 1)], [1], [1]);

(* This automaton is hard to read, so there is destructor as well *)
val automaton1_dest = NFA_string.nfa_destruct automaton1

(* This still is not very readable. So the GraphViz can be used as well. *)
val _ = NFA_string.show_NFA NONE automaton1

(* The output can be saved as well *)
val _ = NFA_string.export_NFA "pdf" "automaton1.pdf" NONE automaton1

(* lets test whether the automaton behaves as expected *)
val r = NFA_string.nfa_accept_base automaton1 ["b", "a", "b", "a"]

(* Labels are strings. This is cumbersome to write. Therefore,
   a shorter versions for labels consisting of single chars is
   available as well. *)
val r = NFA_string.nfa_accept automaton1 "baba"

(* if a does not occur at every even position, the word is not accepted *)
val r = NFA_string.nfa_accept automaton1 "bbba"

(* Similarly all words containing lables other than "a" and "b" are rejected. *)
val r = NFA_string.nfa_accept automaton1 "caba"

(* Let's try renaming and normalising *)
val _ = NFA_string.show_NFA NONE (NFA_string.nfa_rename_labels automaton1
   (fn l => ("renamed_"^l)))

val _ = NFA_string.show_NFA NONE automaton1
val _ = NFA_string.show_NFA NONE (NFA_string.nfa_normalise automaton1)

(* Now let's test removing unreachable states! *)
val automaton2 = NFA_string.nfa_construct ([3, 4, 5], [], [(1, ["a", "b"], 2), (2, ["a"], 1), (3, ["a"], 5), (4, ["b", "a"], 2), (5, ["a"], 1),  (5, ["a"], 2)], [1], [1])

val _ = NFA_string.show_NFA NONE automaton2
val _ = NFA_string.show_NFA NONE (NFA_string.nfa_normalise automaton2)

(* Testing product *)
val automaton1 = NFA_string.nfa_construct ([], [], [(1, ["a", "b"], 2), (2, ["a"], 1)], [1], [1])
val automaton2 = NFA_string.nfa_construct ([3, 4, 5], [], [(1, ["a", "b"], 2), (2, ["a"], 1), (3, ["a"], 5), (4, ["b", "a"], 2), (5, ["a"], 1),  (5, ["a"], 2)], [1], [1])
val automaton3 = NFA_string.nfa_product automaton1 automaton2

val _ = NFA_string.show_NFA (SOME "Automaton 1") automaton1
val _ = NFA_string.show_NFA (SOME "Automaton 2") automaton2
val _ = NFA_string.show_NFA (SOME "Automaton 3") automaton3


(* Testing determinisation and minimisation *)
val automaton1 = NFA_string.nfa_construct ([], [], 
   [(1, ["a", "b"], 2), 
    (1, ["a"], 3), 
    (3, ["b"], 2), 
    (3, ["a"], 1), 
    (2, ["a"], 2), 
    (5, ["a"], 1)], 
   [1], [2])

val _ = NFA_string.show_NFA (SOME "Original") automaton1
val a1_is_det = NFA_string.nfa_is_deterministic automaton1

val automaton1_det = NFA_string.nfa_determinise automaton1
val _ = NFA_string.show_NFA (SOME "deterministic") automaton1_det
val a1_det_is_det = NFA_string.nfa_is_deterministic automaton1_det

val automaton1_min1 = NFA_string.nfa_Brzozowski automaton1
val _ = NFA_string.show_NFA (SOME "minimal Brzozowski") automaton1_min1
val a1_min_is_det = NFA_string.nfa_is_deterministic automaton1_min1

val automaton1_min2 = NFA_string.nfa_Hopcroft_NFA automaton1
val _ = NFA_string.show_NFA (SOME "minimal Hopcroft_NFA") automaton1_min2
val a1_min_is_det = NFA_string.nfa_is_deterministic automaton1_min2

(* Hopcroft operates only on desterministic, iniatially connected ones *)
val automaton1_min3 = NFA_string.nfa_Hopcroft automaton1_det
val _ = NFA_string.show_NFA (SOME "minimal Hopcroft") automaton1_min3
val a1_min_is_det = NFA_string.nfa_is_deterministic automaton1_min3

(* applying Hopcroft to nondetermistic ones may lead to strange results or
   even execeptions *)
val automaton1_min3_false = NFA_string.nfa_Hopcroft automaton1
val _ = NFA_string.show_NFA (SOME "minimal Hopcroft - Error") automaton1_min3_false
val a1_min_is_det = NFA_string.nfa_is_deterministic automaton1_min3



(* Presburger Test *)
open Presburger

(* Examples *)
val stamp = Pres_Forall (Pres_Imp (Pres_Le ([~1], ~8), Pres_Exist
  (Pres_Exist (Pres_Eq ([5, 3, ~1], 0)))));

val example = Pres_Forall (Pres_Exist (Pres_Or (Pres_Eq ([1, ~1], 5),
  Pres_Forall (Pres_Forall (Pres_Imp (Pres_Neg (Pres_Le ([~1, 0],
  ~6)), Pres_Imp (Pres_Eq ([1, 6, 0, ~1], 0), Pres_Eq ([0, 1],
  1))))))));

val example2 = Pres_Forall (Pres_Forall (Pres_Forall (Pres_Imp
  (Pres_Neg (Pres_Le ([~1], ~2)), Pres_Imp (Pres_Eq ([1, 2, ~1], 1),
  Pres_Forall (Pres_Forall (Pres_Imp (Pres_Neg (Pres_Le ([~1], ~2)),
  Pres_Imp (Pres_Eq ([1, 2, 0, 0, ~1], 0), Pres_Imp (Pres_Exist
  (Pres_Eq ([2, 0, 0, 0, 0, ~1], 0)), Pres_Eq ([0, 1, 0, ~1],
  0)))))))))));

val harrison1 = Pres_Exist (Pres_Forall (Pres_Imp (Pres_Le
  ([~1, 1], 0), Pres_Exist (Pres_Exist (Pres_And (Pres_Le ([0, ~1],
  0), Pres_And (Pres_Le ([~1], 0), Pres_Eq ([8, 3, ~1], 0))))))));

val harrison2 = Pres_Exist (Pres_Forall (Pres_Imp (Pres_Le
  ([~1, 1], 0), Pres_Exist (Pres_Exist (Pres_And (Pres_Le ([0, ~1],
  0), Pres_And (Pres_Le ([~1], 0), Pres_Eq ([8, 7, ~1], 0))))))));

val stamp_false = Pres_Forall (Pres_Imp (Pres_Le ([~1],
  (~7)), Pres_Exist (Pres_Exist (Pres_Eq ([5, 3, ~1], 0)))));

val example2_false = Pres_Forall (Pres_Forall (Pres_Forall
  (Pres_Imp (Pres_Neg (Pres_Le ([~1], ~2)), Pres_Imp (Pres_Eq ([1, 2,
  ~1], 1), Pres_Forall (Pres_Forall (Pres_Imp (Pres_Neg (Pres_Le
  ([~1], ~2)), Pres_Imp (Pres_Eq ([1, 2, 0, 0, ~1], 0), Pres_Imp
  (Pres_Exist (Pres_Eq ([3, 0, 0, 0, 0, ~1], 0)), Pres_Eq ([0, 1, 0,
  ~1], 0)))))))))));


(* Play around with "example" *)

val example = Pres_Eq ([2, ~1], 0);


val _ = print (pf_to_string example)
val example_DFA = pf_to_DFA example

(* Automata look boring, because they are minimal and only interested 
   in input [] *)
val _ = NFA_bool_list.show_NFA (SOME "2 * x = y") example_DFA
val _ = NFA_bool_list.export_NFA "png" "dioph.eps" NONE example_DFA

(* lets evaluate it using my translation and the one from AFP *)
val example_valid = eval_pf_DFA example
val example_valid = eval_pf_dfa example


fun bool_to_string true = "True"
  | bool_to_string false = "False"

fun repeat f a 0 = f a
  | repeat f a n = ((f a);repeat f a (n-1))

fun measure_fun s rf f a =
let
  val st = Time.now();
  val r = repeat f a 1000;
  val et = Time.now();

  val t = Time.toMilliseconds (Time.- (et, st))
  val _ = print s;
  val _ = print (": "^(rf r)^" ")
  val _ = print ((Int.toString t) ^ " ms\n");
in
  r
end;

fun measure_bool_fun s = measure_fun s bool_to_string;
fun measure_gen_fun s = measure_fun s (fn _ => "");


(* Try all examples *)
val _ = print "\n\n\n"
val stamp_valid          = measure_bool_fun "stamp" eval_pf_DFA stamp
val example_valid        = measure_bool_fun "example" eval_pf_DFA example
val example2_valid       = measure_bool_fun "example2" eval_pf_DFA example2
val harrison1_valid      = measure_bool_fun "harrison1" eval_pf_DFA harrison1
val harrison2_valid      = measure_bool_fun "harrison2" eval_pf_DFA harrison2
val stamp_false_valid    = measure_bool_fun "stamp_false" eval_pf_DFA stamp_false
val example2_false_valid = measure_bool_fun "example2_false" eval_pf_DFA example2_false
val _ = print "\n--------------------------------------------------\n\n"
val stamp_valid          = measure_bool_fun "stamp" eval_pf_dfa stamp
val example_valid        = measure_bool_fun "example" eval_pf_dfa example
val example2_valid       = measure_bool_fun "example2" eval_pf_dfa example2
val harrison1_valid      = measure_bool_fun "harrison1" eval_pf_dfa harrison1
val harrison2_valid      = measure_bool_fun "harrison2" eval_pf_dfa harrison2
val stamp_false_valid    = measure_bool_fun "stamp_false" eval_pf_dfa stamp_false
val example2_false_valid = measure_bool_fun "example2_false" eval_pf_dfa example2_false
val _ = print "\n\n\n";


(* Let's have an automaton for formulas with free vars *)
val free_example = 
  Pres_And (
    Pres_Le ([31, ~53, 2, 18, 5, 2, 3, 4], 17),
    Pres_Eq ([11, ~13, 4, 3, 7, 4, 5, 1], 19));

val free_example_all = Pres_Forall free_example

val free_example_DFA = measure_gen_fun "DFA" pf_to_DFA free_example;
val free_example_dfa = measure_gen_fun "dfa" pf_to_dfa free_example

val min = measure_gen_fun "DFA_min" NFA_bool_list.nfa_Hopcroft free_example_DFA


val free_example_all_DFA = measure_gen_fun "DFA" pf_to_DFA free_example_all
val free_example_all_dfa = measure_gen_fun "dfa" pf_to_dfa free_example_all


val free_example_DFA_min = measure_gen_fun "minimise" NFA_bool_list.nfa_Hopcroft free_example_DFA

NFA_bool_list.nfa_states_no free_example_DFA
NFA_bool_list.nfa_states_no free_example_DFA_min

val free_example_DFA_min = measure_gen_fun "minimise" NFA_bool_list.nfa_Brzozowski free_example_DFA

val _ = NFA_bool_list.show_NFA NONE free_example_DFA
val _ = NFA_bool_list.show_NFA NONE free_example_DFA_min

