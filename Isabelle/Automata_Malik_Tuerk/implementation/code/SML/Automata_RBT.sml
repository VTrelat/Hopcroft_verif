use "Automata_Export_RBT.sml";

(* copied from  Isabelle2011-1/src/Pure/library.ML" *)
exception RANDOM;

local
  fun rmod x y = x - y * Real.realFloor (x / y);
  val a = 16807.0;
  val m = 2147483647.0;
  val random_seed = ref 1.0;
in

fun random () = 
  let val r = rmod (a * ! random_seed) m
  in (random_seed := r; r) end;

fun random_range l h =
  if h < l orelse l < 0 then raise RANDOM
  else l + Real.floor (rmod (random ()) (real (h - l + 1)));

end;

signature Sigma_param = sig
   type Sigma
   type Sigma_Word
   val Sigma_to_string : Sigma -> string
   val Sigma_Word_create : Sigma_Word -> Sigma list
   val Sigma_dsarg : Sigma HOL.equal * Sigma Orderings.linorder
   val int_to_Sigma: int -> Sigma
end

structure string_Sigma_param : Sigma_param = struct
  type Sigma = string;
  type Sigma_Word = string

  val string_equal = {equal = fn (s1:string) => fn s2 => (s1 = s2)}

  val string_ord = {less_eq = fn s1 => fn s2 => (String.<= (s1, s2)), 
                   less = fn s1 => fn s2 => (String.< (s1, s2))};
  val string_preorder = {ord_preorder = string_ord};
  val string_order = {preorder_order = string_preorder};
  val string_linorder = {order_linorder=string_order};

  val Sigma_dsarg = (string_equal, string_linorder);

(*
  fun hashcode_String s = 
     Char.ord (String.sub (s, 0))
     handle Subscript => 0
  fun bounded_hashcode_String na s = Arith.mod_nat (hashcode_String s) na;
  fun def_hashmap_size_String x = (fn _ => (16 : IntInf.int)) x;

  val hashable_String =
    {hashcode = hashcode_String, bounded_hashcode = bounded_hashcode_String,
      def_hashmap_size = def_hashmap_size_String}

  val Sigma_dsarg = (string_equal, hashable_String);*)

  fun Sigma_to_string s = s
  fun Sigma_Word_create s = map Char.toString (explode s)
  fun int_to_Sigma n = Char.toString (chr (n+97))
end


functor NFA (S : Sigma_param) : sig
  type NFA

  (* construct_NFA is used to construct NFAs from 
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

     The result of construct_NFA is always a well-formed NFA,
  *)
  val nfa_construct : 
     (* Q *) int list * 
     (* A *) S.Sigma list * 
     (* D *) (int * S.Sigma list * int) list * 
     (* I *) int list *
     (* F *) int list 
     -> 
     NFA;

  (* Use internally a more efficient datastructure, if it can be guaranteed that the
     result is a DFA. *)
  val dfa_construct : 
     (* Q *) int list * 
     (* A *) S.Sigma list * 
     (* D *) (int * S.Sigma list * int) list * 
     (* I *) int list *
     (* F *) int list 
     -> 
     NFA;

  (* destruct_NFA is the inverse of construct_NFA. It destructs an NFA into a
     list representation. *)
  val nfa_destruct : NFA -> 
     int list * S.Sigma list * (int * S.Sigma list * int) list * int list * int list

  (* a simpler, faster version without grouping *)
  val nfa_destruct_simple : NFA -> 
     int list * S.Sigma list * (int * S.Sigma * int) list * int list * int list
  
  (* show_NFA uses the GraphViz package in order to display NFAs. *)
  val show_NFA : string option -> NFA -> unit

  (* export_NFA allows storing the GraphViz output in various file formats *)
  val export_NFA : string (*Format*) -> string (*File*) -> string option (*Label*) -> NFA -> unit

  (* random test generation *)
  val generate_random_NFAs : int -> int -> int -> real -> real -> NFA list
  val generate_random_ICDFAs : int -> int -> int -> real -> real -> NFA list


  (* Operations on NFAs *)  
  val nfa_accept_base : NFA -> S.Sigma list -> bool
  val nfa_accept : NFA -> S.Sigma_Word -> bool

  val nfa_rename_labels : NFA -> (S.Sigma -> S.Sigma) -> NFA
  val nfa_normalise : NFA -> NFA
  val nfa_complement : NFA -> NFA
  val nfa_bool_comb : (bool -> bool -> bool) -> NFA -> NFA -> NFA 
  val nfa_product : NFA -> NFA -> NFA 
  val nfa_determinise : NFA -> NFA
  val nfa_reverse : NFA -> NFA
  val nfa_Brzozowski : NFA -> NFA
  val nfa_Hopcroft : NFA -> NFA
  val nfa_Hopcroft_NFA : NFA -> NFA

  (* Statistics on NFAs *)  
  val nfa_states_no : NFA -> int
  val nfa_labels_no : NFA -> int
  val nfa_trans_no : NFA -> int
  val nfa_final_no : NFA -> int
  val nfa_initial_no : NFA -> int

  (* Language checks on NFAs *)  
  val nfa_lang_is_empty : NFA -> bool
  val nfa_lang_is_univ : NFA -> bool
  val nfa_lang_is_subset : NFA -> NFA -> bool
  val nfa_lang_is_eq : NFA -> NFA -> bool

end = struct

type NFA = 
      (int, unit) RBT.rbt *
      ((S.Sigma, unit) RBT.rbt *
      (((int, (S.Sigma, (int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
      (int, (S.Sigma, int) RBT.rbt) RBT.rbt) LTSByLTS_DLTS.lTS_choice *
      ((int, unit) RBT.rbt *
      ((int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))

(*
val nFA_states_nat = {states_enumerate = (fn i => i)}:(int NFA.nFA_states)
val equal_nat = {equal = fn (s1:int) => fn s2 => (s1 = s2)}
val state_args = (nFA_states_nat, Arith.linorder_nat)
val ext_state_args = (equal_nat, nFA_states_nat, Arith.linorder_nat)
*)

val sigma_linord = #2 (S.Sigma_dsarg)

fun nfa_construct (Q, A, D, I, F) = 
   (RBT_NFAImpl.rs_nfa_construct sigma_linord
    (Q, (A, (map (fn (a, b,c) => (a, (b,c))) D, (I, F))))):NFA;

fun dfa_construct (Q, A, D, I, F) = 
   RBT_NFAImpl.rs_dfa_construct sigma_linord
    (Q, (A, (map (fn (a, b,c) => (a, (b,c))) D, (I, F)))):NFA;

fun nfa_destruct (AA:NFA) =
   let val (Q, (A, (D, (I, F)))) = 
    RBT_NFAImpl.rs_nfa_destruct sigma_linord AA in
   (Q, A, map (fn (a, (b,c)) => (a, b,c)) D, I, F) end;

fun nfa_destruct_simple (AA:NFA) =
   let val (Q, (A, (D, (I, F)))) = 
    RBT_NFAImpl.rs_nfa_destruct_simple sigma_linord AA in
   (Q, A, map (fn (a, (b,c)) => (a, b,c)) D, I, F) end;

fun write_dot_graph os labelOpt AA =
let 
   val (Q, A, D, I, F) = nfa_destruct AA;
   val _ = TextIO.output (os, "digraph {\n")
   val _ = case labelOpt of NONE => () 
               | SOME l => TextIO.output (os, "label = \"" ^ l ^ "\"\n")
   val _ = TextIO.output (os, "rankdir=LR;\n")
   val _ = TextIO.output (os, "\"\" [shape=none];\n")

   fun separate_list x [] = []
     | separate_list x [s] = [s]
     | separate_list x (s1 :: s2 :: sl) =
       s1 :: x :: (separate_list x (s2 :: sl));

   fun separate x sl = String.concat (separate_list x sl) 

   fun mem x [] = false
     | mem x (x' :: xs) = if x = x' then true else mem x xs

   fun get_node_shape n =
      if (mem n F) then "doublecircle" else "circle"
   fun get_node_format n =
     String.concat ("shape = " :: (get_node_shape n) :: []);
   fun output_node n =
     TextIO.output (os, Int.toString n ^ " ["^get_node_format n^"];\n")
   fun output_initial_node n =
      (TextIO.output (os, String.concat [
          "\"\" -> ", Int.toString n, ";\n"]))
   val _ = map output_node Q;
   val _ = map output_initial_node I;

   fun output_edge (q0, al, q1) =
      (TextIO.output (os, String.concat [
          Int.toString q0, " -> ", Int.toString q1, " [ label = \"",
          separate ", " (rev (map S.Sigma_to_string al)), "\" ];\n"]))
   val _ = map output_edge D;
   val _ = TextIO.output (os, "}\n");   
in
   ()
end


fun export_NFA format file labelOpt AA =
let
   val proc = Unix.execute ("/usr/bin/dot", ["-T"^format, "-o"^file])
   val os = Unix.textOutstreamOf proc

   val _ = write_dot_graph os labelOpt AA
   val _ = TextIO.closeOut os;
in
  ()
end;

fun show_NFA labelOpt AA =
let
   val proc = Unix.execute ("/usr/bin/dot", ["-Tx11"])
   val os = Unix.textOutstreamOf proc

   val _ = write_dot_graph os labelOpt AA
   val _ = TextIO.closeOut os;
in
  ()
end;


open RBT_NFAImpl

(* Basic operations *)
val nfa_accept_base = rs_nfa_accept sigma_linord:(NFA -> S.Sigma list -> bool)
fun nfa_accept A w = nfa_accept_base A (S.Sigma_Word_create w)

val nfa_rename_labels = (rs_nfa_rename_labels sigma_linord false):(NFA -> (S.Sigma -> S.Sigma) -> NFA) 
val nfa_normalise = (rs_nfa_normalise sigma_linord):(NFA -> NFA)
val nfa_complement = (rs_nfa_complement sigma_linord):(NFA -> NFA)
val nfa_bool_comb = (rs_nfa_bool_comb sigma_linord):(
   (bool -> bool -> bool) -> NFA -> NFA -> NFA)
val nfa_product = nfa_bool_comb (fn b1 => fn b2 => b1 andalso b2)
val nfa_determinise = (rs_nfa_determinise sigma_linord):(NFA -> NFA)
val nfa_reverse = (rs_nfa_reverse sigma_linord):(NFA -> NFA)
val nfa_Brzozowski = (rs_nfa_Brzozowski sigma_linord):(NFA -> NFA)
val nfa_Hopcroft = (rs_nfa_Hopcroft sigma_linord):(NFA -> NFA)
val nfa_Hopcroft_NFA = (rs_nfa_Hopcroft_NFA sigma_linord):(NFA -> NFA)


(* Statistic operations *)
val nfa_states_no = (rs_nfa_states_no sigma_linord):(NFA -> int)
val nfa_labels_no = (rs_nfa_labels_no sigma_linord):(NFA -> int)
val nfa_trans_no = (rs_nfa_trans_no sigma_linord) :(NFA -> int)
val nfa_final_no = (rs_nfa_final_no sigma_linord):(NFA -> int)
val nfa_initial_no = (rs_nfa_initial_no sigma_linord):(NFA -> int)

(* Language operations *)
val nfa_lang_is_empty = (rs_nfa_language_is_empty sigma_linord):(NFA -> bool)
val nfa_lang_is_univ = (rs_nfa_language_is_univ sigma_linord):(NFA -> bool)
val nfa_lang_is_subset = (rs_nfa_language_is_subset sigma_linord):(NFA -> NFA -> bool)
val nfa_lang_is_eq = (rs_nfa_language_is_eq sigma_linord):(NFA -> NFA -> bool)

(* Generating random automata *)

fun generate_random_NFAs number st_no label_no (den:real) (fden:real) =
let
  fun generate_labels 0 = []
    | generate_labels n = (S.int_to_Sigma n) :: generate_labels (n-1)

  fun generate_transition st_no l_no =
    (random_range 0 st_no, [S.int_to_Sigma (random_range 1 label_no)], random_range 0 st_no)


  val labels = generate_labels label_no;
  val trans_no = Real.round(den * (Real.fromInt (st_no * label_no)));
  val accept_no = Real.round(fden * (Real.fromInt st_no)) + 1;

  fun generate_state_set 0 = []
    | generate_state_set n = (random_range 0 st_no) :: generate_state_set (n-1)

  fun replicate 0 x = []
    | replicate n x = x :: (replicate (n-1) x)

  fun generate_transitions () = map (fn f => f ()) (replicate trans_no 
      (fn () => generate_transition st_no label_no))

  fun generate_NFA () =
   nfa_construct ([], labels, generate_transitions(), [0], 
     generate_state_set accept_no)
in
  map (fn f => f ()) (replicate number generate_NFA)
end

fun generate_random_ICDFAs number st_no label_no (den:real) (fden:real) =
let
  val NFAs = generate_random_NFAs number st_no label_no (den:real) (fden:real)
in
  map nfa_determinise NFAs
end

end



structure int_Sigma_param : Sigma_param = struct
  type Sigma = int;
  type Sigma_Word = int list

  (*
  val nFA_states_nat = {states_prod_encode = Nat_Bijection.prod_encode, 
                      states_enumerate = (fn i => i)}:(int NFA.nFA_states)
  val ext_state_args = (Arith.equal_nat, HashCode.hashable_nat, nFA_states_nat)
  *)

  val equal_nat = {equal = fn (s1:int) => fn s2 => (s1 = s2)}
  val Sigma_dsarg = (equal_nat, Arith.linorder_nat);

  fun Sigma_to_string s = Int.toString s
  fun Sigma_Word_create s = s
  fun int_to_Sigma n = n
end

structure bool_list_Sigma_param : Sigma_param = struct
  type Sigma = bool list;
  type Sigma_Word = string list

  (*
  val nFA_states_nat = {states_prod_encode = Nat_Bijection.prod_encode, 
                      states_enumerate = (fn i => i)}:(int NFA.nFA_states)
  val ext_state_args = (Arith.equal_nat, HashCode.hashable_nat, nFA_states_nat)
  *)

  val equal_list = {equal = fn (s1:bool list) => fn s2 => (s1 = s2)}
  val Sigma_dsarg = (equal_list, RBT_Presburger_Impl.linorder_list (Product_Type.equal_bool, RBT_Presburger_Impl.linorder_bool));


  fun bool_to_string true = "1"
    | bool_to_string false = "0"

  fun Sigma_to_string bl = concat (map bool_to_string bl)

  fun char_to_bool #"0" = false
    | char_to_bool #"F" = false
    | char_to_bool #"f" = false
    | char_to_bool #"-" = false
    | char_to_bool _ = true

  fun string_to_bool_list s =
    map char_to_bool (explode s)

  fun Sigma_Word_create sl = 
    map string_to_bool_list sl

  exception Not_Implemented
  fun int_to_Sigma n = raise Not_Implemented
end

structure NFA_string = NFA (string_Sigma_param)
structure NFA_int = NFA (int_Sigma_param)
structure NFA_bool_list = NFA (bool_list_Sigma_param)


structure Presburger : sig
  type pf
  val pf_to_DFA : pf -> NFA_bool_list.NFA
  val pf_to_dfa : pf -> int Presburger_Automata.bdd list * bool list
  val eval_pf_DFA : pf -> bool
  val eval_pf_dfa : pf -> bool
  val pf_to_string : pf -> string
  val pf_get_free_vars_number : pf -> int   

  val Pres_And    : pf * pf -> pf
  val Pres_Eq     : int list * int -> pf
  val Pres_Exist  : pf -> pf
  val Pres_Forall : pf -> pf
  val Pres_Imp    : pf * pf -> pf
  val Pres_Le     : int list * int -> pf
  val Pres_Neg    : pf -> pf
  val Pres_Or     : pf * pf -> pf

end = struct
  type pf = Presburger_Automata.pf

  val Pres_Eq = Presburger_Automata.Eq
  val Pres_Le = Presburger_Automata.Le
  val Pres_And = Presburger_Automata.And
  val Pres_Or = Presburger_Automata.Or
  val Pres_Imp = Presburger_Automata.Imp
  val Pres_Neg = Presburger_Automata.Neg
  val Pres_Forall = Presburger_Automata.Forall
  val Pres_Exist = Presburger_Automata.Exist


fun pf_get_free_vars_number (Presburger_Automata.Le (cs, nn)) = length cs
  | pf_get_free_vars_number (Presburger_Automata.Eq (cs, nn)) = length cs
  | pf_get_free_vars_number (Presburger_Automata.Neg p) = pf_get_free_vars_number p
  | pf_get_free_vars_number (Presburger_Automata.And (p1,p2)) = 
      Int.max (pf_get_free_vars_number p1, pf_get_free_vars_number p2)
  | pf_get_free_vars_number (Presburger_Automata.Or (p1,p2)) = 
      Int.max (pf_get_free_vars_number p1, pf_get_free_vars_number p2)
  | pf_get_free_vars_number (Presburger_Automata.Imp (p1,p2)) = 
      Int.max (pf_get_free_vars_number p1, pf_get_free_vars_number p2)
  | pf_get_free_vars_number (Presburger_Automata.Exist p) = (pf_get_free_vars_number p) - 1
  | pf_get_free_vars_number (Presburger_Automata.Forall p) = (pf_get_free_vars_number p) - 1


  fun pf_to_DFA p = RBT_Presburger_Impl.rs_pres_pf_to_nfa (pf_get_free_vars_number p) p
  fun pf_to_dfa p = Presburger_Automata.dfa_of_pf (pf_get_free_vars_number p) p
  val eval_pf_DFA = RBT_Presburger_Impl.rs_eval_pf
  val eval_pf_dfa = RBT_Presburger_Impl.eval_pf_dfa


fun mk_var n = "x_" ^ (Int.toString n)

fun factor_to_string n c =
  if (c = 0) then NONE else
  if (c = 1) then SOME (false, mk_var n) else
  if (c = ~1) then SOME (true, mk_var n) else
  SOME (c < 0, Int.toString (abs c) ^ " * "^ (mk_var n))

fun mk_factors n [] = []
  | mk_factors n (c :: cs) =
    (factor_to_string n c) ::
    (mk_factors (n-1) cs)

fun combine_factors true [] = "0"
  | combine_factors false [] = ""
  | combine_factors f (NONE :: cs) =
    combine_factors f cs
  | combine_factors true (SOME (s, fa) :: cs) =
    (if s then "~" ^ fa else fa) ^ (combine_factors false cs)
  | combine_factors false (SOME (s, fa) :: cs) =
    (if s then " - " else " + ") ^ fa ^ (combine_factors false cs)

fun dioph_to_string n cs = combine_factors true (mk_factors n cs)
    
fun pf_to_string_aux n (Presburger_Automata.Le (cs, nn)) = 
  "("^ (dioph_to_string n cs) ^ " <= " ^ (Int.toString nn) ^ ")"
  | pf_to_string_aux n (Presburger_Automata.Eq (cs, nn)) = 
  "("^ (dioph_to_string n cs) ^ " = " ^ (Int.toString nn) ^ ")"
  | pf_to_string_aux n (Presburger_Automata.Neg (Presburger_Automata.Le (cs, nn))) = 
  "("^ (dioph_to_string n cs) ^ " > " ^ (Int.toString nn) ^ ")"
  | pf_to_string_aux n (Presburger_Automata.Neg (Presburger_Automata.Eq (cs, nn))) = 
  "("^ (dioph_to_string n cs) ^ " =/= " ^ (Int.toString nn) ^ ")"
  | pf_to_string_aux n (Presburger_Automata.Neg (Presburger_Automata.Neg p)) = 
    pf_to_string_aux n p
  | pf_to_string_aux n (Presburger_Automata.Neg p) = 
  "Not " ^ (pf_to_string_aux n p)
  | pf_to_string_aux n (Presburger_Automata.And (p1,p2)) = 
  "(" ^ (pf_to_string_aux n p1) ^ " /\\ " ^ (pf_to_string_aux n p2) ^")"
  | pf_to_string_aux n (Presburger_Automata.Or (p1,p2)) = 
  "(" ^ (pf_to_string_aux n p1) ^ " \\/ " ^ (pf_to_string_aux n p2) ^")"
  | pf_to_string_aux n (Presburger_Automata.Imp (p1,p2)) = 
  "(" ^ (pf_to_string_aux n p1) ^ " --> " ^ (pf_to_string_aux n p2) ^")"
  | pf_to_string_aux n (Presburger_Automata.Exist p) = 
  "(Exist " ^ (mk_var (n+1)) ^ ". "^ (pf_to_string_aux (n+1) p) ^")"
  | pf_to_string_aux n (Presburger_Automata.Forall p) = 
  "(Forall " ^ (mk_var (n+1)) ^ ". "^ (pf_to_string_aux (n+1) p) ^")"

fun pf_to_string p = pf_to_string_aux (pf_get_free_vars_number p) p

end;









