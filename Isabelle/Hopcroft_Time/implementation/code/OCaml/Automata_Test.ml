(*
#load "nums.cma";;
#load "unix.cma";;
#use "Automata_Export.ml";;
#use "Automata.ml";;
*)

open Automata.NFA_string

let automaton1 = nfa_construct ([], [], [(1, ["a"; "b"], 2); (2, ["a"], 1)], [1], [1]);;

(* This automaton is hard to read, so there is destructor as well *)
let automaton1_dest = nfa_destruct automaton1;;

(* This still is not very readable. So the GraphViz can be used as well. *)
let _ = show_NFA None automaton1

(* The output can be saved as well *)
let _ = export_NFA "pdf" "automaton1.pdf" None automaton1

(* lets test whether the automaton behaves as expected *)
let r = nfa_accept_base automaton1 ["b"; "a"; "b"; "a"]

(* Labels are strings. This is cumbersome to write. Therefore,
   a shorter versions for labels consisting of single chars is
   available as well. *)
let r = nfa_accept automaton1 "baba"

(* if a does not occur at every even position, the word is not accepted *)
let r = nfa_accept automaton1 "bbba"

(* Similarly all words containing lables other than "a" and "b" are rejected. *)
let r = nfa_accept automaton1 "caba"

(* Let's try renaming and normalising *)
let _ = show_NFA None (nfa_rename_labels automaton1 (fun l -> ("renamed_"^l)))
let _ = show_NFA None automaton1
let _ = show_NFA None (nfa_normalise automaton1)

(* Now let's test removing unreachable states! *)
let automaton2 = nfa_construct ([3; 4; 5], [], 
   [(1, ["a"; "b"], 2); 
    (2, ["a"], 1); 
    (3, ["a"], 5); 
    (4, ["b"; "a"], 2); 
    (5, ["a"], 1); 
    (5, ["a"], 2)], [1], [1])

let _ = show_NFA None automaton2
let _ = show_NFA None (nfa_normalise automaton2)

(* Testing product *)
let automaton1 = nfa_construct ([], [], [(1, ["a"; "b"], 2); (2, ["a"], 1)], [1], [1])
let automaton2 = nfa_construct ([3; 4; 5], [], [(1, ["a"; "b"], 2); (2, ["a"], 1); (3, ["a"], 5); (4, ["b"; "a"], 2); (5, ["a"], 1);  (5, ["a"], 2)], [1], [1])
let automaton3 = nfa_product automaton1 automaton2

let _ = show_NFA (Some "Automaton 1") automaton1
let _ = show_NFA (Some "Automaton 2") automaton2
let _ = show_NFA (Some "Automaton 3") automaton3


(* Testing determinisation and minimisation *)
let automaton1 = nfa_construct ([], [], 
   [(1, ["a"; "b"], 2); 
    (1, ["a"], 3); 
    (3, ["b"], 2); 
    (3, ["a"], 1); 
    (2, ["a"], 2); 
    (5, ["a"], 1)], 
   [1], [2]);;

let _ = show_NFA (Some "Original") automaton1

let automaton1_det = nfa_determinise automaton1
let _ = show_NFA (Some "deterministic") automaton1_det

let automaton1_min1 = nfa_Brzozowski automaton1
let _ = show_NFA (Some "minimal Brzozowski") automaton1_min1

let automaton1_min2 = nfa_Hopcroft_NFA automaton1
let _ = show_NFA (Some "minimal Hopcroft_NFA") automaton1_min2

(* Hopcroft operates only on desterministic, iniatially connected ones *)
let automaton1_min3 = nfa_Hopcroft automaton1_det
let _ = show_NFA (Some "minimal Hopcroft") automaton1_min3

(* applying Hopcroft to nondetermistic ones may lead to strange results or
   even execeptions *)
let automaton1_min3_false = nfa_Hopcroft automaton1
let _ = show_NFA (Some "minimal Hopcroft - Error") automaton1_min3_false
