(*
#load "unix.cma";;
#load "nums.cma";;
#use "Automata_Export.ml";;
*)

open Automata_Export

module type Sigma_Param = 
sig
   type sigma
   type sigma_word
   val sigma_to_string : sigma -> string
   val sigma_word_create : sigma_word -> sigma list
   val sigma_dsarg : sigma Automata_Export.equal * sigma Automata_Export.linorder
   val int_to_sigma: int -> sigma
end;;


module Sigma_Param_string : (Sigma_Param with type sigma = string
                                         and type sigma_word = string) = struct
  type sigma = string
  type sigma_word = string

  open Automata_Export
  let equal_string = ({equal = fun (s1:string) s2 -> (String.compare s1 s2 = 0)} : string equal);;

(*
  let hashcode_string s = 
    try
      Big_int.big_int_of_int(Char.code (String.get s 0))
    with Invalid_argument _ -> Big_int.zero_big_int

  let bounded_hashcode_string na s = mod_nat (hashcode_string s) na;;
  let rec def_hashmap_size_string x = (fun _ -> (Big_int.big_int_of_int 16)) x;;

  let hashable_string =
    ({hashcode = hashcode_string; bounded_hashcode = bounded_hashcode_string;
       def_hashmap_size = def_hashmap_size_string}
      : string hashable);; *)

  let ord_string =
  ({less_eq = (fun s1 s2 -> String.compare s1 s2 <= 0); 
    less = (fun s1 s2 -> String.compare s1 s2 < 0)})
  let preorder_string = {ord_preorder = ord_string}
  let order_string = {preorder_order = preorder_string}
  let linord_string = {order_linorder = order_string}
  let sigma_dsarg = (equal_string, linord_string);;

  let sigma_to_string (s:string) = s

  let sigma_word_create s =
    let rec exp i l =
      if i < 0 then l else exp (i - 1) ((String.make 1 s.[i]) :: l) in
      exp (String.length s - 1) []
 
  let int_to_sigma n = String.make 1 (Char.chr (n+97))
end

module Sigma_Param_int : (Sigma_Param with type sigma = Big_int.big_int
                                       and type sigma_word = int list) = struct
  type sigma = Big_int.big_int
  type sigma_word = int list

  open Automata_Export

  let equal_nat = ({equal = fun (s1:Big_int.big_int) s2 -> (s1 = s2)} : Big_int.big_int equal);;
  let sigma_dsarg = (equal_nat, linorder_nat)

  let sigma_to_string s = Big_int.string_of_big_int s
  let sigma_word_create s = map Big_int.big_int_of_int s
  let int_to_sigma = Big_int.big_int_of_int
end

module Sigma_Param_bool_list : (Sigma_Param with type sigma = bool list
                                             and type sigma_word = string list) = struct

  type sigma = bool list
  type sigma_word = string list

  open Automata_Export

  (*
  val nFA_states_nat = {states_prod_encode = Nat_Bijection.prod_encode, 
                      states_enumerate = (fn i => i)}:(int NFA.nFA_states)
  val ext_state_args = (Arith.equal_nat, HashCode.hashable_nat, nFA_states_nat)
  *)

  let equal_list = {equal = fun (s1:bool list) s2 -> (s1 = s2)}
  let sigma_dsarg = (equal_list, linorder_list (equal_bool, linorder_bool))

  let bool_to_string b = if b then "1" else "0"

  let sigma_to_string bl = String.concat "" (map bool_to_string bl)

  let char_to_bool c =
    match c with 
        'F' -> false
      | 'f' -> false
      | '-' -> false
      | _ -> true

  let string_to_bool_list s =
    let rec exp i l =
      if i < 0 then l else exp (i - 1) ((char_to_bool s.[i]) :: l) in
      exp (String.length s - 1) []

  let sigma_word_create sl = map string_to_bool_list sl

  exception Not_Implemented
  let int_to_sigma n = raise Not_Implemented
end

type 'S nfa = 
(Big_int.big_int, unit) Automata_Export.rbt *
  (('S, unit) Automata_Export.rbt *
   (((Big_int.big_int,
      ('S, (Big_int.big_int, unit) Automata_Export.rbt)
      Automata_Export.rbt)
     Automata_Export.rbt,
     (Big_int.big_int, ('S, Big_int.big_int) Automata_Export.rbt)
     Automata_Export.rbt)
    Automata_Export.lTS_choice *
    ((Big_int.big_int, unit) Automata_Export.rbt *
     ((Big_int.big_int, unit) Automata_Export.rbt *
      unit Automata_Export.nfa_props_ext))));;


module NFA (S : Sigma_Param) :
sig 
  (* construct_nfa is used to construct nfas from 
     a tuple "(Q, A, D, I, F)" where 
   
     Q : is a list of states
     A : is a list of labels 
     D : represents the transition relations. It consists of a list of triples.
         A triple "(q, al, q')" represents 
         all transitions from state q to state q' using a label in the list al.
     I : is the list of initial states
     F : is the list of final states

     Q and A get extended automatically to contain all the states and labels occuring in
     D, I and F. Therefore, they are usually empty lists. Only unreachable states and
     unused labels need to be added explicitly. 

     The result of construct_nfa is always a well-formed nfa,
  *)
  val nfa_construct : 
     (* Q *) int list * 
     (* A *) S.sigma list * 
     (* D *) (int * S.sigma list * int) list * 
     (* I *) int list *
     (* F *) int list 
     -> 
     S.sigma nfa

  (* Use internally a more efficient datastructure, if it can be guaranteed that the
     result is a DFA. *)
  val dfa_construct : 
     (* Q *) int list * 
     (* A *) S.sigma list * 
     (* D *) (int * S.sigma list * int) list * 
     (* I *) int list *
     (* F *) int list 
     -> 
     S.sigma nfa

  (* destruct_nfa is the inverse of construct_nfa. It destructs an nfa into a
     list representation. *)
  val nfa_destruct : S.sigma nfa -> 
     int list * S.sigma list * (int * S.sigma list * int) list * int list * int list

  (* a simpler, faster version without grouping *)
  val nfa_destruct_simple : S.sigma nfa -> 
     int list * S.sigma list * (int * S.sigma * int) list * int list * int list
  
  (* show_nfa uses the GraphViz package in order to display nfas. *)
  val show_NFA : string option -> S.sigma nfa -> unit

  (* export_nfa allows storing the GraphViz output in various file formats *)
  val export_NFA : string (*Format*) -> string (*File*) -> string option (*Label*) -> S.sigma nfa -> unit

  (* random test generation *)
  val generate_random_NFAs : int -> int -> int -> float -> float -> float -> S.sigma nfa list
  val generate_random_ICDFAs : int -> int -> int -> float -> float -> float -> S.sigma nfa list


  (* Operations on nfas *)  
  val nfa_accept_base : S.sigma nfa -> S.sigma list -> bool
  val nfa_accept : S.sigma nfa -> S.sigma_word -> bool

  val nfa_rename_labels : S.sigma nfa -> (S.sigma -> S.sigma) -> S.sigma nfa
  val nfa_normalise : S.sigma nfa -> S.sigma nfa
  val nfa_complement : S.sigma nfa -> S.sigma nfa
  val nfa_bool_comb : (bool -> bool -> bool) -> S.sigma nfa -> S.sigma nfa -> S.sigma nfa 
  val nfa_product : S.sigma nfa -> S.sigma nfa -> S.sigma nfa 
  val nfa_determinise : S.sigma nfa -> S.sigma nfa
  val nfa_reverse : S.sigma nfa -> S.sigma nfa
  val nfa_Brzozowski : S.sigma nfa -> S.sigma nfa
  val nfa_Hopcroft : S.sigma nfa -> S.sigma nfa
  val nfa_Hopcroft_NFA : S.sigma nfa -> S.sigma nfa

  (* Language checks on NFAs *)  
  val nfa_lang_is_empty : S.sigma nfa -> bool
  val nfa_lang_is_univ : S.sigma nfa -> bool
  val nfa_lang_is_subset : S.sigma nfa -> S.sigma nfa -> bool
  val nfa_lang_is_eq : S.sigma nfa -> S.sigma nfa -> bool

  (* Statistics on nfas *)  
  val nfa_states_no : S.sigma nfa -> Big_int.big_int
  val nfa_labels_no : S.sigma nfa -> Big_int.big_int
  val nfa_trans_no : S.sigma nfa -> Big_int.big_int
  val nfa_final_no : S.sigma nfa -> Big_int.big_int
  val nfa_initial_no : S.sigma nfa -> Big_int.big_int


end =
struct

open Automata_Export

let sigma_ord = snd (S.sigma_dsarg)

let nfa_construct (q, a, d, i, f) =
   rs_nfa_construct sigma_ord
    (map Big_int.big_int_of_int q, (a, (map (fun (a, b,c) -> (Big_int.big_int_of_int a, (b, Big_int.big_int_of_int c))) d, 
    (map Big_int.big_int_of_int i, map Big_int.big_int_of_int f))));;

let dfa_construct (q, a, d, i, f) = 
   rs_dfa_construct sigma_ord
    (map Big_int.big_int_of_int q, (a, (map (fun (a, b,c) -> (Big_int.big_int_of_int a, (b, Big_int.big_int_of_int c))) d, (map Big_int.big_int_of_int i, map Big_int.big_int_of_int f))))

let nfa_destruct aa =
   let (q, (a, (d, (i, f)))) = 
    rs_nfa_destruct sigma_ord aa in
   (map Big_int.int_of_big_int q, a, map (fun (a, (b,c)) -> (Big_int.int_of_big_int a, b,Big_int.int_of_big_int c)) d, map Big_int.int_of_big_int i, map Big_int.int_of_big_int f)

let nfa_destruct_simple aa =
   let (q, (a, (d, (i, f)))) = 
    rs_nfa_destruct_simple sigma_ord aa in
   (map Big_int.int_of_big_int q, a, map (fun (a, (b,c)) -> (Big_int.int_of_big_int a, b,Big_int.int_of_big_int c)) d, map Big_int.int_of_big_int i, map Big_int.int_of_big_int f)


let write_dot_graph os labelOpt aa = 
   let (q, a, d, i, f) = nfa_destruct aa in 
   let _ = output_string os "digraph {\n" in
   let _ = match labelOpt with None -> () 
               | Some l -> output_string os (String.concat "" ["label = \""; l; "\"\n"]) in
   let _ = output_string os "rankdir=LR;\n" in 
   let _ = output_string os "\"\" [shape=none];\n" in 

   let get_node_shape n = if (List.mem n f) then "doublecircle" else "circle" in
   let get_node_format n =
     String.concat "" ("shape = " :: (get_node_shape n) :: []) in
   let output_node n =
     output_string os (String.concat "" [string_of_int n; " ["; get_node_format n; "];\n"]) in
   let _ = map output_node q in
   let output_initial_node n =
       output_string os (String.concat "" [
          "\"\" -> "; string_of_int n; ";\n"]) in
   let _ = map output_initial_node i in

   let output_edge (q0, al, q1) =
      (output_string os (String.concat "" [
          string_of_int q0; " -> "; string_of_int q1; " [ label = \"";
          String.concat ", " (List.rev (map S.sigma_to_string al)); "\" ];\n"])) in
   let _ = map output_edge d in
   let _ = output_string os "}\n" in ()


let export_NFA format file labelOpt aa =
   let os = Unix.open_process_out (String.concat "" ["/usr/bin/dot -T"; format; " -o"; file]) in
   let _ = write_dot_graph os labelOpt aa in
   let _ = close_out os in
  ()


let show_NFA labelOpt aa =
   let os = Unix.open_process_out ("/usr/bin/dot -Tx11") in
   let _ = write_dot_graph os labelOpt aa in
   let _ = close_out os in
  ()


(* Basic operations *)
let nfa_accept_base = rs_nfa_accept sigma_ord
let nfa_accept a w = nfa_accept_base a (S.sigma_word_create w)

let nfa_rename_labels = rs_nfa_rename_labels sigma_ord false
let nfa_normalise = rs_nfa_normalise sigma_ord
let nfa_complement = rs_nfa_complement sigma_ord
let nfa_bool_comb = rs_nfa_bool_comb sigma_ord
let nfa_product = nfa_bool_comb (fun b1 b2 -> (b1 && b2))
let nfa_determinise = rs_nfa_determinise sigma_ord
let nfa_reverse = rs_nfa_reverse sigma_ord
let nfa_Brzozowski = rs_nfa_Brzozowski sigma_ord
let nfa_Hopcroft = rs_nfa_Hopcroft sigma_ord
let nfa_Hopcroft_NFA = rs_nfa_Hopcroft_NFA sigma_ord

(* Statistic operations *)
let nfa_states_no = rs_nfa_states_no sigma_ord
let nfa_labels_no = rs_nfa_labels_no sigma_ord
let nfa_trans_no = rs_nfa_trans_no sigma_ord
let nfa_final_no = rs_nfa_final_no sigma_ord
let nfa_initial_no = rs_nfa_initial_no sigma_ord

(* Language operations *)
let nfa_lang_is_empty = rs_nfa_language_is_empty sigma_ord
let nfa_lang_is_univ = rs_nfa_language_is_univ sigma_ord
let nfa_lang_is_subset = rs_nfa_language_is_subset sigma_ord
let nfa_lang_is_eq = rs_nfa_language_is_eq sigma_ord


(* Generating random automata *)
let generate_random_NFAs number st_no label_no (den:float) (fden:float) (iden:float) =
  let rec generate_labels n = if n = 0 then [] else
     (S.int_to_sigma (n-1)) :: generate_labels (n-1) in
  let generate_transition st_no l_no =
    (Random.int st_no, [S.int_to_sigma (Random.int label_no)], Random.int st_no) in
  let labels = generate_labels label_no in
  let trans_no = int_of_float (den *. (float_of_int (st_no * label_no))) in
  let accept_no = int_of_float (fden *. (float_of_int st_no)) + 1 in
  let init_no = int_of_float (iden *. (float_of_int st_no)) + 1 in

  let rec generate_state_set n = if (n = 0) then [] else
     (Random.int st_no) :: generate_state_set (n-1) in

  let rec replicate_fun n x = if (n = 0) then [] else (x() :: (replicate_fun (n-1) x)) in

  let generate_transitions () = replicate_fun trans_no 
      (fun () -> generate_transition st_no label_no) in

  let generate_NFA () =
   nfa_construct ([], labels, generate_transitions(), generate_state_set init_no, 
     generate_state_set accept_no) in
  replicate_fun number generate_NFA


let generate_random_ICDFAs number st_no label_no den fden iden =
  let nfas = generate_random_NFAs number st_no label_no den fden iden in
  map nfa_determinise nfas

end


module NFA_string = NFA (Sigma_Param_string)
module NFA_int = NFA (Sigma_Param_int)
module NFA_bool_list = NFA (Sigma_Param_bool_list)


module Presburger : 
sig
  type pf
  val pf_to_DFA : pf -> bool list nfa
  val pf_to_dfa : pf -> Big_int.big_int Automata_Export.bdd list * bool list
  val eval_pf_DFA : pf -> bool
  val eval_pf_dfa : pf -> bool
  val pf_to_string : pf -> string
  val pf_get_free_vars_number : pf -> Big_int.big_int   

  val pres_And    : pf * pf -> pf
  val pres_Eq     : int list * int -> pf
  val pres_Exist  : pf -> pf
  val pres_Forall : pf -> pf
  val pres_Imp    : pf * pf -> pf
  val pres_Le     : int list * int -> pf
  val pres_Neg    : pf -> pf
  val pres_Or     : pf * pf -> pf
end = 
struct
  open Automata_Export
  open NFA_bool_list
  type pf =  Automata_Export.pf

  let pres_Eq (cs,nn) = Automata_Export.Eq (List.map Big_int.big_int_of_int cs,Big_int.big_int_of_int nn)
  let pres_Le (cs,nn) = Le (List.map Big_int.big_int_of_int cs, Big_int.big_int_of_int nn)
  let pres_And (pf1,pf2) = And (pf1,pf2)
  let pres_Or (pf1,pf2) = Or (pf1,pf2)
  let pres_Imp (pf1,pf2) = Imp (pf1,pf2)
  let pres_Neg pf = Neg pf
  let pres_Forall pf = Forall pf
  let pres_Exist pf = Exist pf

  let rec pf_get_free_vars_number pf = match pf with
    (Le (cs, nn)) -> Big_int.big_int_of_int (List.length cs)
  | (Eq (cs, nn)) -> Big_int.big_int_of_int (List.length cs)
  | (Neg p) -> pf_get_free_vars_number p
  | (And (p1,p2)) ->
      Big_int.max_big_int (pf_get_free_vars_number p1) (pf_get_free_vars_number p2)
  | (Or (p1,p2)) ->
      Big_int.max_big_int (pf_get_free_vars_number p1) (pf_get_free_vars_number p2)
  | (Imp (p1,p2)) -> 
      Big_int.max_big_int  (pf_get_free_vars_number p1) (pf_get_free_vars_number p2)
  | (Exist p) -> Big_int.sub_big_int (pf_get_free_vars_number p) (Big_int.big_int_of_int 1)
  | (Forall p) -> Big_int.sub_big_int (pf_get_free_vars_number p) (Big_int.big_int_of_int 1)

  let pf_to_DFA p = rs_pres_pf_to_nfa (pf_get_free_vars_number p) p
  let pf_to_dfa p = dfa_of_pf (pf_get_free_vars_number p) p
  let eval_pf_DFA = rs_eval_pf
  let eval_pf_dfa = eval_pf_dfa


let mk_var n = "x_" ^ (string_of_int n)

let factor_to_string n c =
  if (c = 0) then None else
  if (c = 1) then Some (false, mk_var n) else
  if (c = -1) then Some (true, mk_var n) else
  Some (c < 0, string_of_int (abs c) ^ " * "^ (mk_var n))

let rec mk_factors n cs = 
  match cs with [] -> []
    | (c :: cs) ->
    (factor_to_string n (Big_int.int_of_big_int c)) ::
    (mk_factors (n-1) cs)

let rec combine_factors f cs = match f, cs with
    true, [] -> "0"
  | false, [] -> ""
  | f, (None :: cs) -> combine_factors f cs
  | true, (Some (s, fa) :: cs) ->
    (if s then "~" ^ fa else fa) ^ (combine_factors false cs)
  | false, (Some (s, fa) :: cs) ->
    (if s then " - " else " + ") ^ fa ^ (combine_factors false cs)

let dioph_to_string n cs = combine_factors true (mk_factors n cs)
    
let rec pf_to_string_aux n p = match p with
    (Le (cs, nn)) -> "("^ (dioph_to_string n cs) ^ " ≤ " ^ (Big_int.string_of_big_int nn) ^ ")"
  | (Eq (cs, nn)) -> "("^ (dioph_to_string n cs) ^ " = " ^ (Big_int.string_of_big_int nn) ^ ")"
  | (Neg (Le (cs, nn))) -> "("^ (dioph_to_string n cs) ^ " > " ^ (Big_int.string_of_big_int nn) ^ ")"
  | (Neg (Eq (cs, nn))) -> "("^ (dioph_to_string n cs) ^ " ≠ " ^ (Big_int.string_of_big_int nn) ^ ")"
  | (Neg (Neg p)) -> pf_to_string_aux n p
  | (Neg p) -> "Not " ^ (pf_to_string_aux n p)
  | (And (p1,p2)) -> "(" ^ (pf_to_string_aux n p1) ^ " ⋀ " ^ (pf_to_string_aux n p2) ^")"
  | (Or (p1,p2)) -> "(" ^ (pf_to_string_aux n p1) ^ " ⋁ " ^ (pf_to_string_aux n p2) ^")"
  | (Imp (p1,p2)) -> "(" ^ (pf_to_string_aux n p1) ^ " ⇒ " ^ (pf_to_string_aux n p2) ^")"
  | (Exist p) -> "(∃ " ^ (mk_var (n+1)) ^ ". "^ (pf_to_string_aux (n+1) p) ^")"
  | (Forall p) -> "(∀ " ^ (mk_var (n+1)) ^ ". "^ (pf_to_string_aux (n+1) p) ^")"

let pf_to_string p = pf_to_string_aux 
  (Big_int.int_of_big_int (pf_get_free_vars_number p)) p

end























