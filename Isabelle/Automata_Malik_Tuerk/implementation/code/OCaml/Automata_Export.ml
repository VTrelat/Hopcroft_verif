
module STArray = struct

type 'a cell = Value of 'a array | Invalid;;

exception AccessedOldVersion;;
exception Size;;

type 'a arrayref = ('a cell) ref;;

let fromList l = ref (Value (Array.of_list l));;
let array (size, v) = ref (Value (Array.make size v));;
let tabulate (size, f) = ref (Value (Array.init size f));;
let sub (aref, idx) = match !aref with
  Invalid -> raise AccessedOldVersion |
  (Value a) -> Array.get a idx;;

let update (aref,idx,v) =
  match !aref with
    Invalid -> raise AccessedOldVersion |
    (Value a) -> (
      aref := Invalid;
      Array.set a idx v;
      ref (Value a)
    );;

let length aref = match !aref with Invalid -> raise AccessedOldVersion |
                                   Value a -> Array.length a

let grow (aref, i, x) = match !aref with 
  Invalid -> raise AccessedOldVersion |
  (Value a) -> (
    let len=Array.length a in
    let na = Array.make (len+i) x in 
    (
      aref := Invalid;
      Array.blit a 0 na 0 len;
      ref (Value na)
    ));;

let shrink (aref, sz) = match !aref with
  Invalid -> raise AccessedOldVersion |
  (Value a) -> (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      tabulate (sz,fun i -> Array.get a i)
    )
  );;

module IsabelleMapping = struct
type 'a arrayType = 'a arrayref;;

let new_array (a:'a) (n:Big_int.big_int) = array (Big_int.int_of_big_int n, a);;

let array_length (a:'a arrayType) = Big_int.big_int_of_int (length a);;

let array_get (a:'a arrayType) i = sub (a, Big_int.int_of_big_int i);;

let array_set (a:'a arrayType) i (e:'a) = update (a, Big_int.int_of_big_int i, e);;

let array_of_list (xs:'a list) = fromList xs;;

let array_grow (a:'a arrayType) i (x:'a) = grow (a, Big_int.int_of_big_int i, x);;

let array_shrink (a:'a arrayType) sz = shrink (a,Big_int.int_of_big_int sz);;

end

end


module Automata_Export : sig
  val id : 'a -> 'a
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  type color = R | B
  type ('a, 'b) rbta = Empty |
    Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder = {ord_preorder : 'a ord}
  type 'a order = {preorder_order : 'a preorder}
  type 'a linorder = {order_linorder : 'a order}
  type ('a, 'b) rbt = Rbt of ('a, 'b) rbta
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val collect : ('a -> bool) -> 'a -> bool
  val is_none : 'a option -> bool
  val dom : ('a -> 'b option) -> 'a -> bool
  val suc : Big_int.big_int -> Big_int.big_int
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val map : ('a -> 'b) -> 'a list -> 'b list
  val minus_nat : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val nth : 'a list -> Big_int.big_int -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val null : 'a list -> bool
  val empty : 'a linorder -> ('a, 'b) rbt
  val ord_int : Big_int.big_int ord
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val ord_nat : Big_int.big_int ord
  val the : 'a option -> 'a
  val impl_of : 'a linorder -> ('a, 'b) rbt -> ('a, 'b) rbta
  val paint : color -> ('a, 'b) rbta -> ('a, 'b) rbta
  val balance : ('a, 'b) rbta -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val balance_left : ('a, 'b) rbta -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val combine : ('a, 'b) rbta -> ('a, 'b) rbta -> ('a, 'b) rbta
  val balance_right :
    ('a, 'b) rbta -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val del : 'a linorder -> 'a -> ('a, 'b) rbta -> ('a, 'b) rbta
  val del_from_right :
    'a linorder ->
      'a -> ('a, 'b) rbta -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val del_from_left :
    'a linorder ->
      'a -> ('a, 'b) rbta -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val deletea : 'a linorder -> 'a -> ('a, 'b) rbta -> ('a, 'b) rbta
  val delete : 'a linorder -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val ins :
    'a linorder ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val insert_with_key :
    'a linorder ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val insertb : 'a linorder -> 'a -> 'b -> ('a, 'b) rbta -> ('a, 'b) rbta
  val insert : 'a linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val lookupa : 'a linorder -> ('a, 'b) rbta -> 'a -> 'b option
  val lookup : 'a linorder -> ('a, 'b) rbt -> 'a -> 'b option
  val gen_dfs :
    ('a -> 'a list) ->
      ('a -> 'b -> 'b) -> ('a -> 'b -> bool) -> 'b -> 'a list -> 'b
  type 'a plus = {plus : 'a -> 'a -> 'a}
  val plus : 'a plus -> 'a -> 'a -> 'a
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  val abs_int : Big_int.big_int -> Big_int.big_int
  val plus_int : Big_int.big_int plus
  val sgn_int : Big_int.big_int -> Big_int.big_int
  val zero_inta : Big_int.big_int
  val zero_int : Big_int.big_int zero
  val member : 'a equal -> 'a list -> 'a -> bool
  val inserta : 'a equal -> 'a -> 'a list -> 'a list
  val zero_nata : Big_int.big_int
  val zero_nat : Big_int.big_int zero
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  val product : 'a list -> 'b list -> ('a * 'b) list
  type 'a semigroup_add = {plus_semigroup_add : 'a plus}
  type 'a monoid_add =
    {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero}
  val listsum : 'a monoid_add -> 'a list -> 'a
  val eu_sng : (unit -> 'a) -> ('b -> 'c -> 'a -> 'a) -> 'b -> 'c -> 'a
  val it_add :
    ('a -> 'b -> 'c -> 'c) ->
      ('d -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c) ->
        'c -> 'd -> 'c
  val less_eq_prod_aux :
    'a equal * 'a ord -> 'b ord -> 'a * 'b -> 'a * 'b -> bool
  val equal_proda : 'a equal -> 'b equal -> 'a * 'b -> 'a * 'b -> bool
  val less_prod :
    'a equal * 'a ord -> 'b equal * 'b ord -> 'a * 'b -> 'a * 'b -> bool
  val less_eq_prod : 'a equal * 'a ord -> 'b ord -> 'a * 'b -> 'a * 'b -> bool
  val ord_prod : 'a equal * 'a ord -> 'b equal * 'b ord -> ('a * 'b) ord
  val equal_nat : Big_int.big_int equal
  val preorder_nat : Big_int.big_int preorder
  val order_nat : Big_int.big_int order
  val ei_sng : (unit -> 'a) -> ('b -> 'a -> 'a) -> 'b -> 'a
  val list_all : ('a -> bool) -> 'a list -> bool
  val merge : 'a equal * 'a linorder -> 'a list -> 'a list -> 'a list
  val it_size :
    ('a ->
      (Big_int.big_int -> bool) ->
        ('b -> Big_int.big_int -> Big_int.big_int) ->
          Big_int.big_int -> Big_int.big_int) ->
      'a -> Big_int.big_int
  val iti_sel :
    ('a ->
      ('b option -> bool) ->
        ('c -> 'b option -> 'b option) -> 'b option -> 'b option) ->
      'a -> ('c -> 'b option) -> 'b option
  val maxa : ('a -> 'a -> bool) -> 'a -> 'a -> 'a
  val max : 'a ord -> 'a -> 'a -> 'a
  val it_diff :
    ('a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b) ->
      ('c -> 'b -> 'b) -> 'b -> 'a -> 'b
  val it_sizea :
    ('a ->
      (Big_int.big_int -> bool) ->
        ('b -> Big_int.big_int -> Big_int.big_int) ->
          Big_int.big_int -> Big_int.big_int) ->
      'a -> Big_int.big_int
  val sel_sel :
    ('a -> ('b -> 'b option) -> 'b option) -> 'a -> ('b -> bool) -> 'b option
  val equal_lista : 'a equal -> 'a list -> 'a list -> bool
  val equal_list : 'a equal -> ('a list) equal
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val replicate : Big_int.big_int -> 'a -> 'a list
  val size_list : 'a list -> Big_int.big_int
  val sel_ball :
    ('a -> ('b * 'c -> unit option) -> unit option) ->
      'a -> ('b * 'c -> bool) -> bool
  val preorder_prod :
    'a equal * 'a order -> 'b equal * 'b order -> ('a * 'b) preorder
  val order_prod : 'a equal * 'a order -> 'b equal * 'b order -> ('a * 'b) order
  val s_ins : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val s_sel :
    ('a -> ('b * unit -> 'c option) -> 'c option) ->
      'a -> ('b -> 'c option) -> 'c option
  val it_inter :
    ('a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b) ->
      ('c -> 'd -> bool) -> (unit -> 'b) -> ('c -> 'b -> 'b) -> 'a -> 'd -> 'b
  val iti_ball :
    ('a -> (bool -> bool) -> ('b -> bool -> bool) -> bool -> bool) ->
      'a -> ('b -> bool) -> bool
  val rm_empty : 'a linorder -> unit -> ('a, 'b) rbt
  val rm_update : 'a linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rm_sng : 'a linorder -> 'a -> 'b -> ('a, 'b) rbt
  val rs_ins : 'a linorder -> 'a -> ('a, unit) rbt -> ('a, unit) rbt
  val rs_empty : 'a linorder -> unit -> ('a, unit) rbt
  val rs_sng : 'a linorder -> 'a -> ('a, unit) rbt
  val fst : 'a * 'b -> 'a
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_int :
    Big_int.big_int -> Big_int.big_int -> Big_int.big_int * Big_int.big_int
  val div_int : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val div_nat : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val snd : 'a * 'b -> 'b
  val mod_int : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val sza_isSng :
    ('a ->
      (Big_int.big_int -> bool) ->
        ('b -> Big_int.big_int -> Big_int.big_int) ->
          Big_int.big_int -> Big_int.big_int) ->
      'a -> bool
  type 'a nfa_props_ext = Nfa_props_ext of bool * bool * 'a
  val fields : bool -> bool -> unit nfa_props_ext
  val linorder_nat : Big_int.big_int linorder
  val s_memb : ('a -> 'b -> 'c option) -> 'a -> 'b -> bool
  val sza_isSnga :
    ('a ->
      (Big_int.big_int -> bool) ->
        ('b -> Big_int.big_int -> Big_int.big_int) ->
          Big_int.big_int -> Big_int.big_int) ->
      'a -> bool
  val iam_empty : unit -> ('a option) STArray.IsabelleMapping.arrayType
  val iam_increment : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val iam_update :
    Big_int.big_int ->
      'a -> ('a option) STArray.IsabelleMapping.arrayType ->
              ('a option) STArray.IsabelleMapping.arrayType
  val iam_sng :
    Big_int.big_int -> 'a -> ('a option) STArray.IsabelleMapping.arrayType
  val rm_iterateoi :
    ('a, 'b) rbta -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_iterateoia :
    'a linorder ->
      ('a, 'b) rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_iteratei :
    'a linorder ->
      ('a, 'b) rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_sel :
    'a linorder -> ('a, 'b) rbt -> ('a * 'b -> 'c option) -> 'c option
  val rm_ball : 'a linorder -> ('a, 'b) rbt -> ('a * 'b -> bool) -> bool
  val rm_size : 'a linorder -> ('a, 'b) rbt -> Big_int.big_int
  val rm_delete : 'a linorder -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rs_delete : 'a linorder -> 'a -> ('a, unit) rbt -> ('a, unit) rbt
  val s_iteratei :
    ('a -> ('b -> bool) -> ('c * unit -> 'b -> 'b) -> 'b -> 'b) ->
      'a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b
  val rs_iteratei :
    'a linorder ->
      ('a, unit) rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rr_diff :
    'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> ('a, unit) rbt
  val rs_ball : 'a linorder -> ('a, unit) rbt -> ('a -> bool) -> bool
  val rs_size : 'a linorder -> ('a, unit) rbt -> Big_int.big_int
  val ltsga_copy :
    ('a -> ('b -> bool) -> ('c * ('d * 'c) -> 'e -> 'e) -> 'e -> 'e) ->
      (unit -> 'e) -> ('c -> 'd -> 'c -> 'e -> 'e) -> 'a -> 'e
  val list_update : 'a list -> Big_int.big_int -> 'a -> 'a list
  val equal_color : color -> color -> bool
  val equal_rbtb :
    'a equal -> 'b equal -> ('a, 'b) rbta -> ('a, 'b) rbta -> bool
  val equal_rbta :
    'a equal * 'a linorder -> 'b equal -> ('a, 'b) rbt -> ('a, 'b) rbt -> bool
  val equal_rbt : 'a equal * 'a linorder -> 'b equal -> ('a, 'b) rbt equal
  val s_alpha : ('a -> 'b -> unit option) -> 'a -> 'b -> bool
  val iflt_image : (('a -> 'b option) -> 'c -> 'd) -> ('a -> 'b) -> 'c -> 'd
  val iam_iteratei_aux :
    Big_int.big_int ->
      ('a option) STArray.IsabelleMapping.arrayType ->
        ('b -> bool) -> (Big_int.big_int * 'a -> 'b -> 'b) -> 'b -> 'b
  val iam_iteratei :
    ('a option) STArray.IsabelleMapping.arrayType ->
      ('b -> bool) -> (Big_int.big_int * 'a -> 'b -> 'b) -> 'b -> 'b
  val iam_sel :
    ('a option) STArray.IsabelleMapping.arrayType ->
      (Big_int.big_int * 'a -> 'b option) -> 'b option
  val iam_ball :
    ('a option) STArray.IsabelleMapping.arrayType ->
      (Big_int.big_int * 'a -> bool) -> bool
  val iam_size :
    ('a option) STArray.IsabelleMapping.arrayType -> Big_int.big_int
  val rm_isSng : 'a linorder -> ('a, 'b) rbt -> bool
  val ball_subset :
    ('a -> ('b -> bool) -> bool) -> ('b -> 'c -> bool) -> 'a -> 'c -> bool
  val rm_lookup : 'a linorder -> 'a -> ('a, 'b) rbt -> 'b option
  val rs_memb : 'a linorder -> 'a -> ('a, unit) rbt -> bool
  val rr_subset : 'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> bool
  val subset_equal :
    ('a -> 'b -> bool) -> ('b -> 'a -> bool) -> 'a -> 'b -> bool
  val rr_equal : 'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> bool
  val rs_isSng : 'a linorder -> ('a, unit) rbt -> bool
  val worklist :
    ('a -> bool) -> ('a -> 'b -> 'a * 'b list) -> 'a * 'b list -> 'a * 'b list
  val semigroup_add_int : Big_int.big_int semigroup_add
  val monoid_add_int : Big_int.big_int monoid_add
  type ('a, 'b) lTS_choice = Lts of 'a | Dlts of 'b
  val iti_isEmpty :
    ('a -> (bool -> bool) -> ('b -> bool -> bool) -> bool -> bool) -> 'a -> bool
  val linorder_prod :
    'a equal * 'a linorder -> 'b equal * 'b linorder -> ('a * 'b) linorder
  val less_bool : bool -> bool -> bool
  val less_eq_bool : bool -> bool -> bool
  val ord_bool : bool ord
  val rm_add : 'a linorder -> ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt
  val iti_sel_no_map :
    ('a ->
      ('b option -> bool) ->
        ('b -> 'b option -> 'b option) -> 'b option -> 'b option) ->
      'a -> ('b -> bool) -> 'b option
  val rm_reverse_iterateoi :
    ('a, 'b) rbta -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_reverse_iterateoia :
    'a linorder ->
      ('a, 'b) rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_max :
    'a linorder -> ('a, 'b) rbt -> ('a * 'b -> bool) -> ('a * 'b) option
  val rm_min :
    'a linorder -> ('a, 'b) rbt -> ('a * 'b -> bool) -> ('a * 'b) option
  val iti_sel_no_mapa :
    ('a ->
      ('b option -> bool) ->
        ('b -> 'b option -> 'b option) -> 'b option -> 'b option) ->
      'a -> ('b -> bool) -> 'b option
  val rs_reverse_iterateoi :
    'a linorder ->
      ('a, unit) rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rs_max : 'a linorder -> ('a, unit) rbt -> ('a -> bool) -> 'a option
  val rs_iterateoi :
    'a linorder ->
      ('a, unit) rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rs_min : 'a linorder -> ('a, unit) rbt -> ('a -> bool) -> 'a option
  val rs_sel : 'a linorder -> ('a, unit) rbt -> ('a -> 'b option) -> 'b option
  val s_ins_dj : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val iflt_filter : (('a -> 'a option) -> 'b -> 'c) -> ('a -> bool) -> 'b -> 'c
  val iam_isSng : ('a option) STArray.IsabelleMapping.arrayType -> bool
  val rm_update_dj : 'a linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rs_ins_dj : 'a linorder -> 'a -> ('a, unit) rbt -> ('a, unit) rbt
  val it_image_filter :
    ('a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b) ->
      (unit -> 'b) -> ('d -> 'b -> 'b) -> ('c -> 'd option) -> 'a -> 'b
  val rr_inj_image_filter :
    'a linorder -> 'b linorder ->
      ('a -> 'b option) -> ('a, unit) rbt -> ('b, unit) rbt
  val rr_filter :
    'a linorder -> ('a -> bool) -> ('a, unit) rbt -> ('a, unit) rbt
  val merge_list :
    'a equal * 'a linorder -> ('a list) list -> ('a list) list -> 'a list
  type ('a, 'b, 'c, 'd) map_ops_ext =
    Map_ops_ext of
      ('c -> 'a -> 'b option) * ('c -> bool) * (unit -> 'c) * ('a -> 'b -> 'c) *
        ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c) *
        ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'c) *
        (('a * 'b -> bool) -> 'c -> 'c) * ('c -> 'c -> 'c) * ('c -> 'c -> 'c) *
        ('c -> bool) * ('c -> bool) * ('c -> ('a * 'b -> bool) -> bool) *
        ('c -> ('a * 'b -> bool) -> bool) * ('c -> Big_int.big_int) *
        (Big_int.big_int -> 'c -> Big_int.big_int) *
        ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * ('c -> ('a * 'b) list) *
        (('a * 'b) list -> 'c) * 'd
  val map_op_sng : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'b -> 'c
  val rm_sela :
    'a linorder -> ('a, 'b) rbt -> ('a * 'b -> bool) -> ('a * 'b) option
  val rs_sela : 'a linorder -> ('a, unit) rbt -> ('a -> bool) -> 'a option
  type ('a, 'b, 'c) set_ops_ext =
    Set_ops_ext of
      ('b -> 'a -> bool) * ('b -> bool) * (unit -> 'b) * ('a -> 'b) *
        ('a -> 'b -> bool) * ('a -> 'b -> 'b) * ('a -> 'b -> 'b) *
        ('a -> 'b -> 'b) * ('b -> bool) * ('b -> bool) *
        ('b -> ('a -> bool) -> bool) * ('b -> ('a -> bool) -> bool) *
        ('b -> Big_int.big_int) * (Big_int.big_int -> 'b -> Big_int.big_int) *
        ('b -> 'b -> 'b) * ('b -> 'b -> 'b) * ('b -> 'b -> 'b) *
        (('a -> bool) -> 'b -> 'b) * ('b -> 'b -> 'b) * ('b -> 'b -> bool) *
        ('b -> 'b -> bool) * ('b -> 'b -> bool) * ('b -> 'b -> 'a option) *
        ('b -> ('a -> bool) -> 'a option) * ('b -> 'a list) * ('a list -> 'b) *
        'c
  val neg_ball_bexists :
    ('a -> ('b * 'c -> bool) -> bool) -> 'a -> ('b * 'c -> bool) -> bool
  val rm_bexists : 'a linorder -> ('a, 'b) rbt -> ('a * 'b -> bool) -> bool
  val neg_ball_bexistsa :
    ('a -> ('b -> bool) -> bool) -> 'a -> ('b -> bool) -> bool
  val rs_bexists : 'a linorder -> ('a, unit) rbt -> ('a -> bool) -> bool
  val ltsga_reverse :
    (unit -> 'a) ->
      ('b -> 'c -> 'b -> 'a -> 'a) ->
        ('d -> ('e -> bool) -> ('b * ('c * 'b) -> 'a -> 'a) -> 'a -> 'a) ->
          'd -> 'a
  val foldli : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  type ('a, 'b, 'c, 'd) omap_ops_ext =
    Omap_ops_ext of
      ('c -> ('a * 'b -> bool) -> ('a * 'b) option) *
        ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * 'd
  val preorder_bool : bool preorder
  val order_bool : bool order
  val rm_alpha : 'a linorder -> ('a, 'b) rbt -> 'a -> 'b option
  val rs_alpha : 'a linorder -> ('a, unit) rbt -> 'a -> bool
  val rs_image_filter :
    'a linorder -> 'b linorder ->
      ('a -> 'b option) -> ('a, unit) rbt -> ('b, unit) rbt
  val rs_image :
    'a linorder -> 'b linorder -> ('a -> 'b) -> ('a, unit) rbt -> ('b, unit) rbt
  val rs_inter :
    'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> ('a, unit) rbt
  val rs_union :
    'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> ('a, unit) rbt
  val ball_disjoint :
    ('a -> ('b -> bool) -> 'c) -> ('b -> 'd -> bool) -> 'a -> 'd -> 'c
  type ('a, 'b, 'c) oset_ops_ext =
    Oset_ops_ext of
      ('b -> ('a -> bool) -> 'a option) * ('b -> ('a -> bool) -> 'a option) * 'c
  val set_op_diff : ('a, 'b, 'c) set_ops_ext -> 'b -> 'b -> 'b
  val iam_bexists :
    ('a option) STArray.IsabelleMapping.arrayType ->
      (Big_int.big_int * 'a -> bool) -> bool
  val rr_disjoint : 'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> bool
  val it_map_image_filter :
    ('a -> ('b -> bool) -> ('c * 'd -> 'b -> 'b) -> 'b -> 'b) ->
      (unit -> 'b) ->
        ('e -> 'f -> 'b -> 'b) -> ('c * 'd -> ('e * 'f) option) -> 'a -> 'b
  val it_map_restrict :
    ('a -> ('b -> bool) -> ('c * 'd -> 'b -> 'b) -> 'b -> 'b) ->
      (unit -> 'b) -> ('c -> 'd -> 'b -> 'b) -> ('c * 'd -> bool) -> 'a -> 'b
  val rr_restrict :
    'a linorder -> ('a * 'b -> bool) -> ('a, 'b) rbt -> ('a, 'b) rbt
  val iam_add :
    ('a option) STArray.IsabelleMapping.arrayType ->
      ('a option) STArray.IsabelleMapping.arrayType ->
        ('a option) STArray.IsabelleMapping.arrayType
  val it_map_to_list :
    ('a ->
      ('b list -> bool) -> ('b -> 'b list -> 'b list) -> 'b list -> 'b list) ->
      'a -> 'b list
  val iti_size_abort :
    ('a ->
      (Big_int.big_int -> bool) ->
        ('b -> Big_int.big_int -> Big_int.big_int) ->
          Big_int.big_int -> Big_int.big_int) ->
      Big_int.big_int -> 'a -> Big_int.big_int
  val map_op_empty : ('a, 'b, 'c, 'd) map_ops_ext -> unit -> 'c
  val rm_add_dj : 'a linorder -> ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt
  val gen_list_to_map_aux : ('a -> 'b -> 'c -> 'c) -> 'c -> ('a * 'b) list -> 'c
  val gen_list_to_map :
    (unit -> 'a) -> ('b -> 'c -> 'a -> 'a) -> ('b * 'c) list -> 'a
  val list_to_rm : 'a linorder -> ('a * 'b) list -> ('a, 'b) rbt
  val rm_isEmpty : 'a equal * 'a linorder -> 'b equal -> ('a, 'b) rbt -> bool
  val rm_to_list : 'a linorder -> ('a, 'b) rbt -> ('a * 'b) list
  val rm_size_abort :
    'a linorder -> Big_int.big_int -> ('a, 'b) rbt -> Big_int.big_int
  val rm_ops :
    'a equal * 'a linorder -> 'b equal ->
      ('a, 'b, ('a, 'b) rbt, ('a, 'b, ('a, 'b) rbt, unit) omap_ops_ext)
        map_ops_ext
  val gen_list_to_set_aux : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val gen_list_to_set : (unit -> 'a) -> ('b -> 'a -> 'a) -> 'b list -> 'a
  val list_to_rs : 'a linorder -> 'a list -> ('a, unit) rbt
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit equal
  val rs_isEmpty : 'a equal * 'a linorder -> ('a, unit) rbt -> bool
  val it_set_to_list :
    ('a ->
      ('b list -> bool) -> ('b -> 'b list -> 'b list) -> 'b list -> 'b list) ->
      'a -> 'b list
  val rs_to_list : 'a linorder -> ('a, unit) rbt -> 'a list
  val iti_size_aborta :
    ('a ->
      (Big_int.big_int -> bool) ->
        ('b -> Big_int.big_int -> Big_int.big_int) ->
          Big_int.big_int -> Big_int.big_int) ->
      Big_int.big_int -> 'a -> Big_int.big_int
  val rs_size_abort :
    'a linorder -> Big_int.big_int -> ('a, unit) rbt -> Big_int.big_int
  val rs_union_dj :
    'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> ('a, unit) rbt
  val sel_disjoint_witness :
    ('a -> ('b -> 'b option) -> 'c) -> ('b -> 'd -> bool) -> 'a -> 'd -> 'c
  val rr_disjoint_witness :
    'a linorder -> ('a, unit) rbt -> ('a, unit) rbt -> 'a option
  val rs_ops :
    'a equal * 'a linorder ->
      ('a, ('a, unit) rbt, ('a, ('a, unit) rbt, unit) oset_ops_ext) set_ops_ext
  val iam_sela :
    ('a option) STArray.IsabelleMapping.arrayType ->
      (Big_int.big_int * 'a -> bool) -> (Big_int.big_int * 'a) option
  val map_op_lookup : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'c -> 'b option
  val map_op_update : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'b -> 'c -> 'c
  type pf = Eq of Big_int.big_int list * Big_int.big_int |
    Le of Big_int.big_int list * Big_int.big_int | And of pf * pf |
    Or of pf * pf | Imp of pf * pf | Forall of pf | Exist of pf | Neg of pf
  val iam_update_dj :
    Big_int.big_int ->
      'a -> ('a option) STArray.IsabelleMapping.arrayType ->
              ('a option) STArray.IsabelleMapping.arrayType
  val imim_restrict :
    (Big_int.big_int * 'a -> bool) ->
      ('a option) STArray.IsabelleMapping.arrayType ->
        ('a option) STArray.IsabelleMapping.arrayType
  val iam_alpha :
    ('a option) STArray.IsabelleMapping.arrayType ->
      Big_int.big_int -> 'a option
  val iam_size_abort :
    Big_int.big_int ->
      ('a option) STArray.IsabelleMapping.arrayType -> Big_int.big_int
  val iam_add_dj :
    ('a option) STArray.IsabelleMapping.arrayType ->
      ('a option) STArray.IsabelleMapping.arrayType ->
        ('a option) STArray.IsabelleMapping.arrayType
  val iam_delete :
    Big_int.big_int ->
      ('a option) STArray.IsabelleMapping.arrayType ->
        ('a option) STArray.IsabelleMapping.arrayType
  val iam_lookup :
    Big_int.big_int ->
      ('a option) STArray.IsabelleMapping.arrayType -> 'a option
  val iam_isEmpty : ('a option) STArray.IsabelleMapping.arrayType -> bool
  val iam_to_list :
    ('a option) STArray.IsabelleMapping.arrayType -> (Big_int.big_int * 'a) list
  val list_to_iam :
    (Big_int.big_int * 'a) list -> ('a option) STArray.IsabelleMapping.arrayType
  val iam_ops :
    (Big_int.big_int, 'a, (('a option) STArray.IsabelleMapping.arrayType), unit)
      map_ops_ext
  val insertion_sort : 'a equal * 'a ord -> 'a -> 'a list -> 'a list
  val triangle : Big_int.big_int -> Big_int.big_int
  type 'a bdd = Leaf of 'a | Brancha of 'a bdd * 'a bdd
  val equal_boola : bool -> bool -> bool
  val equal_bool : bool equal
  val equal_prod : 'a equal -> 'b equal -> ('a * 'b) equal
  val while_option : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a option
  val whilea : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
  val rs_dlts_it :
    'a linorder -> 'b linorder ->
      ('a, ('b, 'c) rbt) rbt ->
        ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val dltsbc_add :
    ('a -> 'b -> 'a -> 'c -> 'c) ->
      ('a -> 'b -> 'a -> 'd -> 'd) ->
        'a -> 'b -> 'a -> ('c, 'd) lTS_choice -> ('c, 'd) lTS_choice
  val sum_encode : (Big_int.big_int, Big_int.big_int) sum -> Big_int.big_int
  val int_encode : Big_int.big_int -> Big_int.big_int
  val tr_lookup : (bool list) list -> Big_int.big_int -> Big_int.big_int -> bool
  val check_eq :
    Big_int.big_int bdd -> Big_int.big_int bdd -> (bool list) list -> bool
  val fold_map_idx :
    (Big_int.big_int -> 'a -> 'b -> 'a * 'c) ->
      Big_int.big_int -> 'a -> 'b list -> 'a * 'c list
  val iter :
    Big_int.big_int bdd list * bool list ->
      (bool list) list -> bool * (bool list) list
  val rs_dlts_add :
    'a linorder -> 'b linorder ->
      'a -> 'b -> 'a -> ('a, ('b, 'a) rbt) rbt -> ('a, ('b, 'a) rbt) rbt
  val rs_nfa_props :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        unit nfa_props_ext
  val prod_encode : Big_int.big_int * Big_int.big_int -> Big_int.big_int
  val bv_or : bool list -> bool list -> bool list
  val fixpt :
    Big_int.big_int bdd list * bool list -> (bool list) list -> (bool list) list
  val map_index :
    ('a -> Big_int.big_int -> 'b) -> 'a list -> Big_int.big_int -> 'b list
  val rquot_ins : Big_int.big_int -> bool list -> bool list
  val rquot_empt : Big_int.big_int bdd list * bool list -> bool list
  val rquot_memb : Big_int.big_int -> bool list -> bool
  val bdd_lookup : 'a bdd -> bool list -> 'a
  val rquot_succs :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int -> Big_int.big_int -> Big_int.big_int list
  val rquot_dfs :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int -> Big_int.big_int -> bool list
  val nfa_accepting : bool list -> bool list -> bool
  val rquot :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int -> Big_int.big_int bdd list * bool list
  val set_iterator_emp : ('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a
  val set_iterator_sng : 'a -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rs_dlts_succ_it :
    'a linorder -> 'b linorder ->
      ('a, ('b, 'a) rbt) rbt ->
        'a -> 'b -> ('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c
  val rs_ts_C_it :
    'a linorder -> 'b linorder -> 'c linorder ->
      ('a, ('b, ('c, unit) rbt) rbt) rbt ->
        'a -> 'b -> ('d -> bool) -> ('c -> 'd -> 'd) -> 'd -> 'd
  val rs_lts_dlts_succ :
    'a linorder -> 'b linorder ->
      (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt) lTS_choice ->
        'a -> 'b -> 'a option
  val rs_nfa_accept_dfa :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        'a list -> bool
  val rs_nfa_accept_nfa :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        'a list -> bool
  val nfa_prop_is_complete_deterministic : 'a nfa_props_ext -> bool
  val rs_nfa_accept :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        'a list -> bool
  val lss_ins : 'a equal * 'a linorder -> 'a -> 'a list -> 'a list
  val lss_sng : 'a -> 'a list
  val make_bdd :
    (Big_int.big_int list -> 'a) ->
      Big_int.big_int -> Big_int.big_int list -> 'a bdd
  val dioph_ins :
    Big_int.big_int ->
      (Big_int.big_int option) list * Big_int.big_int list ->
        (Big_int.big_int option) list * Big_int.big_int list
  val dioph_empt :
    Big_int.big_int list ->
      Big_int.big_int -> (Big_int.big_int option) list * Big_int.big_int list
  val dioph_memb :
    Big_int.big_int ->
      (Big_int.big_int option) list * Big_int.big_int list -> bool
  val eval_dioph :
    Big_int.big_int list -> Big_int.big_int list -> Big_int.big_int
  val mk_nat_vecs : Big_int.big_int -> (Big_int.big_int list) list
  val dioph_succs :
    Big_int.big_int ->
      Big_int.big_int list -> Big_int.big_int -> Big_int.big_int list
  val dioph_dfs :
    Big_int.big_int ->
      Big_int.big_int list ->
        Big_int.big_int -> (Big_int.big_int option) list * Big_int.big_int list
  val eq_dfa :
    Big_int.big_int ->
      Big_int.big_int list ->
        Big_int.big_int -> Big_int.big_int bdd list * bool list
  val prod_ins :
    Big_int.big_int * Big_int.big_int ->
      ((Big_int.big_int option) list) list *
        (Big_int.big_int * Big_int.big_int) list ->
        ((Big_int.big_int option) list) list *
          (Big_int.big_int * Big_int.big_int) list
  val prod_empt :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int bdd list * bool list ->
        ((Big_int.big_int option) list) list *
          (Big_int.big_int * Big_int.big_int) list
  val prod_memb :
    Big_int.big_int * Big_int.big_int ->
      ((Big_int.big_int option) list) list *
        (Big_int.big_int * Big_int.big_int) list ->
        bool
  val bdd_binop : ('a -> 'b -> 'c) -> 'a bdd -> 'b bdd -> 'c bdd
  val add_leaves : 'a equal -> 'a bdd -> 'a list -> 'a list
  val prod_succs :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int bdd list * bool list ->
        Big_int.big_int * Big_int.big_int ->
          (Big_int.big_int * Big_int.big_int) list
  val prod_dfs :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int bdd list * bool list ->
        Big_int.big_int * Big_int.big_int ->
          ((Big_int.big_int option) list) list *
            (Big_int.big_int * Big_int.big_int) list
  val binop_dfa :
    (bool -> bool -> bool) ->
      Big_int.big_int bdd list * bool list ->
        Big_int.big_int bdd list * bool list ->
          Big_int.big_int bdd list * bool list
  val or_dfa :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int bdd list * bool list ->
        Big_int.big_int bdd list * bool list
  val rs_dlts_empty :
    'a linorder -> 'b linorder -> unit -> ('a, ('b, 'a) rbt) rbt
  val rs_hop_lts_add :
    'a linorder ->
      Big_int.big_int ->
        'a -> Big_int.big_int ->
                ('a, (((Big_int.big_int list) option)
                       STArray.IsabelleMapping.arrayType))
                  rbt ->
                  ('a, (((Big_int.big_int list) option)
                         STArray.IsabelleMapping.arrayType))
                    rbt
  val rs_ts_it :
    'a linorder -> 'b linorder -> 'c linorder ->
      ('a, ('b, ('c, unit) rbt) rbt) rbt ->
        ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val ltsbc_emp_lts : (unit -> 'a) -> unit -> ('a, 'b) lTS_choice
  val rs_ts_empty :
    'a linorder -> 'b linorder -> 'c linorder ->
      unit -> ('a, ('b, ('c, unit) rbt) rbt) rbt
  val rs_lts_dlts_empty_lts :
    'a linorder -> 'b linorder -> 'c linorder ->
      unit -> (('a, ('b, ('c, unit) rbt) rbt) rbt, 'd) lTS_choice
  val rs_ts_add :
    'a linorder -> 'b linorder -> 'c linorder ->
      'a -> 'b -> 'c -> ('a, ('b, ('c, unit) rbt) rbt) rbt ->
                          ('a, ('b, ('c, unit) rbt) rbt) rbt
  val ltsbc_add_simple :
    ('a -> 'b -> 'a -> 'c -> 'c) ->
      ('d -> 'c) -> 'a -> 'b -> 'a -> ('c, 'd) lTS_choice -> ('c, 'd) lTS_choice
  val rs_dlts_lts_copy :
    'a linorder -> 'b linorder ->
      ('a, ('b, 'a) rbt) rbt -> ('a, ('b, ('a, unit) rbt) rbt) rbt
  val rs_lts_dlts_add_simple :
    'a linorder -> 'b linorder ->
      'a -> 'b -> 'a -> (('a, ('b, ('a, unit) rbt) rbt) rbt,
                          ('a, ('b, 'a) rbt) rbt)
                          lTS_choice ->
                          (('a, ('b, ('a, unit) rbt) rbt) rbt,
                            ('a, ('b, 'a) rbt) rbt)
                            lTS_choice
  val rs_lts_dlts_reverse :
    'a linorder -> 'b linorder ->
      (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt) lTS_choice ->
        (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt) lTS_choice
  val rs_nfa_reverse :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val iterate_size :
    ((Big_int.big_int -> bool) ->
      ('a -> Big_int.big_int -> Big_int.big_int) ->
        Big_int.big_int -> Big_int.big_int) ->
      Big_int.big_int
  val accepts : ('a -> 'b -> 'a) -> ('a -> 'c) -> 'a -> 'b list -> 'c
  val and_dfa :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int bdd list * bool list ->
        Big_int.big_int bdd list * bool list
  val bdd_map : ('a -> 'b) -> 'a bdd -> 'b bdd
  val subsetbdd :
    (bool list) bdd list -> bool list -> (bool list) bdd -> (bool list) bdd
  val bddinsert : 'a bdd -> bool list -> 'a -> 'a bdd
  val subset_ins :
    bool list ->
      (Big_int.big_int option) bdd * (bool list) list ->
        (Big_int.big_int option) bdd * (bool list) list
  val subset_empt : (Big_int.big_int option) bdd * (bool list) list
  val subset_memb :
    bool list -> (Big_int.big_int option) bdd * (bool list) list -> bool
  val nfa_emptybdd : Big_int.big_int -> (bool list) bdd
  val subset_succs :
    (bool list) bdd list * bool list -> bool list -> (bool list) list
  val subset_dfs :
    (bool list) bdd list * bool list ->
      bool list -> (Big_int.big_int option) bdd * (bool list) list
  val nfa_startnode : (bool list) bdd list * bool list -> bool list
  val nfa_acceptinga : (bool list) bdd list * bool list -> bool list -> bool
  val det_nfa :
    (bool list) bdd list * bool list -> Big_int.big_int bdd list * bool list
  val imp_dfa :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int bdd list * bool list ->
        Big_int.big_int bdd list * bool list
  val make_tr :
    (Big_int.big_int -> 'a) -> Big_int.big_int -> Big_int.big_int -> 'a list
  val init_tr : Big_int.big_int bdd list * bool list -> (bool list) list
  val mk_eqcla :
    (Big_int.big_int option) list ->
      Big_int.big_int ->
        Big_int.big_int ->
          Big_int.big_int -> (bool list) list -> (Big_int.big_int option) list
  val mk_eqcl :
    (Big_int.big_int option) list ->
      Big_int.big_int list ->
        Big_int.big_int ->
          (bool list) list -> Big_int.big_int list * Big_int.big_int list
  val min_dfa :
    Big_int.big_int bdd list * bool list -> Big_int.big_int bdd list * bool list
  val rs_hop_lts_copy : 'a -> 'a
  val lss_iteratei : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val lss_empty : unit -> 'a list
  val lss_union_list : 'a equal * 'a linorder -> ('a list) list -> 'a list
  val rs_hop_lts_get_succs :
    'a linorder ->
      ('a, (((Big_int.big_int list) option) STArray.IsabelleMapping.arrayType))
        rbt ->
        Big_int.big_int list -> 'a -> Big_int.big_int list
  val states_enumerate_nat : Big_int.big_int -> Big_int.big_int
  val l_insert_impl :
    Big_int.big_int ->
      ('a * Big_int.big_int) list -> 'a list -> ('a * Big_int.big_int) list
  val sm_update :
    (Big_int.big_int, 'a, 'b, 'c) map_ops_ext ->
      ('a, 'd, 'e, 'f) map_ops_ext ->
        'd -> 'e -> 'b -> Big_int.big_int -> Big_int.big_int -> 'e
  val hopcroft_code_step_compute_iM_swap_check :
    ('a, (Big_int.big_int * 'b), 'c, 'd) map_ops_ext ->
      ('e, 'a, 'f, 'g) map_ops_ext ->
        ('e, Big_int.big_int, 'h, 'i) map_ops_ext ->
          (Big_int.big_int, 'e, 'j, 'k) map_ops_ext ->
            ('a, Big_int.big_int, 'l, 'm) map_ops_ext ->
              ('n ->
                ('o -> bool) ->
                  ('e -> 'l * ('h * 'j) -> 'l * ('h * 'j)) -> 'l * 'p -> 'q) ->
                'p -> 'n -> 'c * ('f * 'r) -> 'q
  val hopcroft_code_step :
    ('a ->
      ('b -> bool) ->
        (Big_int.big_int * Big_int.big_int ->
          ('c * ('d * Big_int.big_int)) * ('e * Big_int.big_int) list ->
            ('c * ('d * Big_int.big_int)) * ('e * Big_int.big_int) list) ->
          ('c * ('d * 'f)) * 'g -> 'h * 'i) ->
      ('j ->
        ('k -> bool) ->
          ('l -> 'm * ('n * 'o) -> 'm * ('n * 'o)) ->
            'm * 'p -> 'a * ('q * 'o)) ->
        (Big_int.big_int, Big_int.big_int, 'm, 'r) map_ops_ext ->
          (Big_int.big_int, 'l, 'o, 's) map_ops_ext ->
            ('l, Big_int.big_int, 'n, 't) map_ops_ext ->
              ('l, Big_int.big_int, 'd, 'u) map_ops_ext ->
                (Big_int.big_int, (Big_int.big_int * Big_int.big_int), 'c, 'v)
                  map_ops_ext ->
                  'e list ->
                    'j -> 'c * ('d * 'f) -> 'g -> 'p -> ('h * 'i) * ('q * 'o)
  val class_map_init_pred_code :
    'f zero ->
      ('a ->
        ('b -> bool) ->
          ('c -> ('d * 'e) * Big_int.big_int -> ('d * 'e) * Big_int.big_int) ->
            ('d * 'e) * 'f -> ('d * 'e) * 'f) ->
        ('c, Big_int.big_int, 'd, 'g) map_ops_ext ->
          (Big_int.big_int, 'c, 'e, 'h) map_ops_ext ->
            'a -> 'a -> ('d * 'e) * ('f * 'f)
  val hopcroft_code :
    (Big_int.big_int, Big_int.big_int, 'a, 'b) map_ops_ext ->
      ('c ->
        ('d -> bool) ->
          ('e -> 'a * ('f * 'g) -> 'a * ('f * 'g)) ->
            'a * ('f * 'g) -> 'h * ('f * 'g)) ->
        ('h ->
          ('i -> bool) ->
            (Big_int.big_int * Big_int.big_int ->
              ('j * ('k * Big_int.big_int)) * ('l * Big_int.big_int) list ->
                ('j * ('k * Big_int.big_int)) * ('l * Big_int.big_int) list) ->
              ('j * ('k * Big_int.big_int)) * ('l * Big_int.big_int) list ->
                ('j * ('k * Big_int.big_int)) * ('l * Big_int.big_int) list) ->
          ('m -> ('n -> bool) -> ('e -> 'k -> 'k) -> 'k -> 'k) ->
            ('e, Big_int.big_int, 'k, 'o) map_ops_ext ->
              (Big_int.big_int, (Big_int.big_int * Big_int.big_int), 'j, 'p)
                map_ops_ext ->
                (Big_int.big_int, 'e, 'g, 'q) map_ops_ext ->
                  ('e, Big_int.big_int, 'f, 'r) map_ops_ext ->
                    ('m ->
                      ('s -> bool) ->
                        ('e ->
                          ('f * 'g) * Big_int.big_int ->
                            ('f * 'g) * Big_int.big_int) ->
                          ('f * 'g) * Big_int.big_int ->
                            ('f * 'g) * Big_int.big_int) ->
                      ('t, 'm, 'u) set_ops_ext ->
                        'm -> 'm -> 'l list ->
                                      ('l ->
'g -> Big_int.big_int * Big_int.big_int -> 'c) ->
('j * ('k * Big_int.big_int)) * ('f * 'g)
  val nfa_prop_is_initially_connected : 'a nfa_props_ext -> bool
  val rs_lts_dlts_add_dlts :
    'a linorder -> 'b linorder ->
      'a -> 'b -> 'a -> (('a, ('b, ('a, unit) rbt) rbt) rbt,
                          ('a, ('b, 'a) rbt) rbt)
                          lTS_choice ->
                          (('a, ('b, ('a, unit) rbt) rbt) rbt,
                            ('a, ('b, 'a) rbt) rbt)
                            lTS_choice
  val ltsbc_filter_it :
    (('a -> bool) ->
      ('b -> bool) ->
        ('a -> bool) ->
          ('a * ('b * 'a) -> bool) ->
            'c -> ('d -> bool) -> ('a * ('b * 'a) -> 'd -> 'd) -> 'd -> 'd) ->
      (('a -> bool) ->
        ('b -> bool) ->
          ('a -> bool) ->
            ('a * ('b * 'a) -> bool) ->
              'e -> ('d -> bool) -> ('a * ('b * 'a) -> 'd -> 'd) -> 'd -> 'd) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                ('c, 'e) lTS_choice ->
                  ('d -> bool) -> ('a * ('b * 'a) -> 'd -> 'd) -> 'd -> 'd
  val rs_dlts_filter_it :
    'a linorder -> 'b linorder ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('c -> bool) ->
            ('a * ('b * 'c) -> bool) ->
              ('a, ('b, 'c) rbt) rbt ->
                ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val rs_ts_filter_it :
    'a linorder -> 'b linorder -> 'c linorder ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('c -> bool) ->
            ('a * ('b * 'c) -> bool) ->
              ('a, ('b, ('c, unit) rbt) rbt) rbt ->
                ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val rs_lts_dlts_filter_it :
    'a linorder -> 'b linorder ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('a -> bool) ->
            ('a * ('b * 'a) -> bool) ->
              (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt)
                lTS_choice ->
                ('c -> bool) -> ('a * ('b * 'a) -> 'c -> 'c) -> 'c -> 'c
  val ltsbc_emp_dlts : (unit -> 'a) -> unit -> ('b, 'a) lTS_choice
  val rs_lts_dlts_empty_dlts :
    'b linorder -> 'c linorder ->
      unit -> ('a, ('b, ('c, 'b) rbt) rbt) lTS_choice
  val rs_lts_dlts_image_filter_dlts :
    'a linorder -> 'b linorder -> 'c linorder -> 'd linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt)
                  lTS_choice ->
                  (('c, ('d, ('c, unit) rbt) rbt) rbt, ('c, ('d, 'c) rbt) rbt)
                    lTS_choice
  val rs_lts_dlts_image_dlts :
    'a linorder -> 'b linorder -> 'c linorder -> 'd linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt)
          lTS_choice ->
          (('c, ('d, ('c, unit) rbt) rbt) rbt, ('c, ('d, 'c) rbt) rbt)
            lTS_choice
  val rs_nfa_rename_states_dfa :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int -> Big_int.big_int) ->
          (Big_int.big_int, unit) rbt *
            (('a, unit) rbt *
              (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                 (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                 lTS_choice *
                ((Big_int.big_int, unit) rbt *
                  ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val hopcroft_class_map_alpha_impl :
    (Big_int.big_int -> 'a option) ->
      Big_int.big_int -> Big_int.big_int -> 'a list
  val rs_nfa_Hopcroft :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val ltsga_list_to_collect_list :
    'a equal -> 'c equal -> ('a * ('b * 'c)) list -> ('a * ('b list * 'c)) list
  val rs_lts_dlts_to_list :
    'a linorder -> 'b linorder ->
      (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt) lTS_choice ->
        ('a * ('b * 'a)) list
  val rs_lts_dlts_to_collect_list :
    'a equal * 'a linorder -> 'b linorder ->
      (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt) lTS_choice ->
        ('a * ('b list * 'a)) list
  val rs_nfa_destruct :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int list *
          ('a list *
            ((Big_int.big_int * ('a list * Big_int.big_int)) list *
              (Big_int.big_int list * Big_int.big_int list)))
  val rs_nfa_final_no :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int
  val rs_nfa_trans_no :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int
  val lexord_lexord_less : 'a equal * 'a linorder -> 'a list -> 'a list -> bool
  val less_list : 'a equal * 'a linorder -> 'a list -> 'a list -> bool
  val lexord_lexord_less_eq :
    'a equal * 'a linorder -> 'a list -> 'a list -> bool
  val less_eq_list : 'a equal * 'a linorder -> 'a list -> 'a list -> bool
  val ord_list : 'a equal * 'a linorder -> ('a list) ord
  val dioph_ineq_succs :
    Big_int.big_int ->
      Big_int.big_int list -> Big_int.big_int -> Big_int.big_int list
  val dioph_ineq_dfs :
    Big_int.big_int ->
      Big_int.big_int list ->
        Big_int.big_int -> (Big_int.big_int option) list * Big_int.big_int list
  val ineq_dfa :
    Big_int.big_int ->
      Big_int.big_int list ->
        Big_int.big_int -> Big_int.big_int bdd list * bool list
  val rs_nfa_construct_gen :
    'a linorder ->
      unit nfa_props_ext ->
        Big_int.big_int list *
          ('a list *
            ((Big_int.big_int * ('a list * Big_int.big_int)) list *
              (Big_int.big_int list * Big_int.big_int list))) ->
          (Big_int.big_int, unit) rbt *
            (('a, unit) rbt *
              (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                 (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                 lTS_choice *
                ((Big_int.big_int, unit) rbt *
                  ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_dfa_construct :
    'a linorder ->
      Big_int.big_int list *
        ('a list *
          ((Big_int.big_int * ('a list * Big_int.big_int)) list *
            (Big_int.big_int list * Big_int.big_int list))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_ts_BC_it :
    'a linorder -> 'b linorder -> 'c linorder ->
      ('a, ('b, ('c, unit) rbt) rbt) rbt ->
        'a -> ('d -> bool) -> ('b * 'c -> 'd -> 'd) -> 'd -> 'd
  val rs_dlts_succ_label_it :
    'a linorder -> 'b linorder ->
      ('a, ('b, 'a) rbt) rbt ->
        'a -> ('c -> bool) -> ('b * 'a -> 'c -> 'c) -> 'c -> 'c
  val rs_lts_dlts_add_choice :
    'a linorder -> 'b linorder ->
      bool ->
        'a -> 'b -> 'a -> (('a, ('b, ('a, unit) rbt) rbt) rbt,
                            ('a, ('b, 'a) rbt) rbt)
                            lTS_choice ->
                            (('a, ('b, ('a, unit) rbt) rbt) rbt,
                              ('a, ('b, 'a) rbt) rbt)
                              lTS_choice
  val rs_nfa_dfa_construct_reachable :
    'b linorder -> 'c linorder ->
      bool ->
        ('a -> 'b) ->
          'a list ->
            ('c, unit) rbt ->
              ('a -> bool) ->
                ('a ->
                  ((('b, Big_int.big_int) rbt * Big_int.big_int) *
                     (((Big_int.big_int, ('c, (Big_int.big_int, unit) rbt) rbt)
                         rbt,
                        (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                        lTS_choice *
                       'a list) ->
                    bool) ->
                    ('c * 'a ->
                      (('b, Big_int.big_int) rbt * Big_int.big_int) *
                        (((Big_int.big_int,
                            ('c, (Big_int.big_int, unit) rbt) rbt)
                            rbt,
                           (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                           lTS_choice *
                          'a list) ->
                        (('b, Big_int.big_int) rbt * Big_int.big_int) *
                          (((Big_int.big_int,
                              ('c, (Big_int.big_int, unit) rbt) rbt)
                              rbt,
                             (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                             lTS_choice *
                            'a list)) ->
                      (('b, Big_int.big_int) rbt * Big_int.big_int) *
                        (((Big_int.big_int,
                            ('c, (Big_int.big_int, unit) rbt) rbt)
                            rbt,
                           (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                           lTS_choice *
                          'd list) ->
                        (('b, Big_int.big_int) rbt * Big_int.big_int) *
                          (((Big_int.big_int,
                              ('c, (Big_int.big_int, unit) rbt) rbt)
                              rbt,
                             (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                             lTS_choice *
                            'a list)) ->
                  (Big_int.big_int, unit) rbt *
                    (('c, unit) rbt *
                      (((Big_int.big_int, ('c, (Big_int.big_int, unit) rbt) rbt)
                          rbt,
                         (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                         lTS_choice *
                        ((Big_int.big_int, unit) rbt *
                          ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_bool_comb_gen :
    'a linorder ->
      ('a, unit) rbt ->
        (bool -> bool -> bool) ->
          (Big_int.big_int, unit) rbt *
            (('a, unit) rbt *
              (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                 (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                 lTS_choice *
                ((Big_int.big_int, unit) rbt *
                  ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
            (Big_int.big_int, unit) rbt *
              (('a, unit) rbt *
                (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                   (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                   lTS_choice *
                  ((Big_int.big_int, unit) rbt *
                    ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
              (Big_int.big_int, unit) rbt *
                (('a, unit) rbt *
                  (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt)
                      rbt,
                     (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                     lTS_choice *
                    ((Big_int.big_int, unit) rbt *
                      ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_bool_comb :
    'a linorder ->
      (bool -> bool -> bool) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
          (Big_int.big_int, unit) rbt *
            (('a, unit) rbt *
              (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                 (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                 lTS_choice *
                ((Big_int.big_int, unit) rbt *
                  ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
            (Big_int.big_int, unit) rbt *
              (('a, unit) rbt *
                (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                   (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                   lTS_choice *
                  ((Big_int.big_int, unit) rbt *
                    ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_construct :
    'a linorder ->
      Big_int.big_int list *
        ('a list *
          ((Big_int.big_int * ('a list * Big_int.big_int)) list *
            (Big_int.big_int list * Big_int.big_int list))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_labels_no :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int
  val rs_nfa_normalise :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_states_no :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int
  val negate_dfa :
    Big_int.big_int bdd list * bool list -> Big_int.big_int bdd list * bool list
  val nfa_of_dfa :
    Big_int.big_int bdd list * bool list -> (bool list) bdd list * bool list
  val quantify_bdd : Big_int.big_int -> (bool list) bdd -> (bool list) bdd
  val quantify_nfa :
    Big_int.big_int ->
      (bool list) bdd list * bool list -> (bool list) bdd list * bool list
  val dfa_of_pf : Big_int.big_int -> pf -> Big_int.big_int bdd list * bool list
  val dfa_trans :
    Big_int.big_int bdd list * bool list ->
      Big_int.big_int -> bool list -> Big_int.big_int
  val rs_dfa_construct_reachable :
    'b linorder -> 'c linorder ->
      ('a -> 'b) ->
        'a list ->
          ('c, unit) rbt ->
            ('a -> bool) ->
              ('a ->
                ((('b, Big_int.big_int) rbt * Big_int.big_int) *
                   (((Big_int.big_int, ('c, (Big_int.big_int, unit) rbt) rbt)
                       rbt,
                      (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                      lTS_choice *
                     'a list) ->
                  bool) ->
                  ('c * 'a ->
                    (('b, Big_int.big_int) rbt * Big_int.big_int) *
                      (((Big_int.big_int, ('c, (Big_int.big_int, unit) rbt) rbt)
                          rbt,
                         (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                         lTS_choice *
                        'a list) ->
                      (('b, Big_int.big_int) rbt * Big_int.big_int) *
                        (((Big_int.big_int,
                            ('c, (Big_int.big_int, unit) rbt) rbt)
                            rbt,
                           (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                           lTS_choice *
                          'a list)) ->
                    (('b, Big_int.big_int) rbt * Big_int.big_int) *
                      (((Big_int.big_int, ('c, (Big_int.big_int, unit) rbt) rbt)
                          rbt,
                         (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                         lTS_choice *
                        'd list) ->
                      (('b, Big_int.big_int) rbt * Big_int.big_int) *
                        (((Big_int.big_int,
                            ('c, (Big_int.big_int, unit) rbt) rbt)
                            rbt,
                           (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                           lTS_choice *
                          'a list)) ->
                (Big_int.big_int, unit) rbt *
                  (('c, unit) rbt *
                    (((Big_int.big_int, ('c, (Big_int.big_int, unit) rbt) rbt)
                        rbt,
                       (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                       lTS_choice *
                      ((Big_int.big_int, unit) rbt *
                        ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_determinise :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_Brzozowski :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_complement :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_initial_no :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int
  val preorder_list : 'a equal * 'a linorder -> ('a list) preorder
  val order_list : 'a equal * 'a linorder -> ('a list) order
  type pres_NFA_state = Pres_NFA_state_error |
    Pres_NFA_state_int of Big_int.big_int
  val linorder_bool : bool linorder
  val linorder_list : 'a equal * 'a linorder -> ('a list) linorder
  val rs_nfa_Hopcroft_NFA :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val pres_NFA_state_to_nat : pres_NFA_state -> Big_int.big_int
  val rs_dfa_construct_reachable_fun :
    'b linorder -> 'c linorder ->
      ('a -> 'b) ->
        'a -> ('c, unit) rbt ->
                ('a -> bool) ->
                  ('a -> 'c -> 'a) ->
                    (Big_int.big_int, unit) rbt *
                      (('c, unit) rbt *
                        (((Big_int.big_int,
                            ('c, (Big_int.big_int, unit) rbt) rbt)
                            rbt,
                           (Big_int.big_int, ('c, Big_int.big_int) rbt) rbt)
                           lTS_choice *
                          ((Big_int.big_int, unit) rbt *
                            ((Big_int.big_int, unit) rbt *
                              unit nfa_props_ext))))
  val nat_of_bool : bool -> Big_int.big_int
  val pres_DFA_eq_ineq_trans_fun :
    bool ->
      Big_int.big_int list -> pres_NFA_state -> bool list -> pres_NFA_state
  val rs_DFA_eq_ineq :
    ((bool list), unit) rbt ->
      bool ->
        'a -> Big_int.big_int list ->
                Big_int.big_int ->
                  (Big_int.big_int, unit) rbt *
                    (((bool list), unit) rbt *
                      (((Big_int.big_int,
                          ((bool list), (Big_int.big_int, unit) rbt) rbt)
                          rbt,
                         (Big_int.big_int, ((bool list), Big_int.big_int) rbt)
                           rbt)
                         lTS_choice *
                        ((Big_int.big_int, unit) rbt *
                          ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_cache_alpha :
    (Big_int.big_int, ((bool list), unit) rbt) rbt ->
      Big_int.big_int ->
        (Big_int.big_int, ((bool list), unit) rbt) rbt * ((bool list), unit) rbt
  val rs_lts_dlts_image_filter :
    'a linorder -> 'b linorder -> 'c linorder -> 'd linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt)
                  lTS_choice ->
                  (('c, ('d, ('c, unit) rbt) rbt) rbt, ('c, ('d, 'c) rbt) rbt)
                    lTS_choice
  val rs_lts_dlts_image :
    'a linorder -> 'b linorder -> 'c linorder -> 'd linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        (('a, ('b, ('a, unit) rbt) rbt) rbt, ('a, ('b, 'a) rbt) rbt)
          lTS_choice ->
          (('c, ('d, ('c, unit) rbt) rbt) rbt, ('c, ('d, 'c) rbt) rbt)
            lTS_choice
  val rs_nfa_rename_labels_gen :
    'a linorder ->
      bool ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
          'b -> ('a -> 'a) ->
                  (Big_int.big_int, unit) rbt *
                    ('b * (((Big_int.big_int,
                              ('a, (Big_int.big_int, unit) rbt) rbt)
                              rbt,
                             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                             lTS_choice *
                            ((Big_int.big_int, unit) rbt *
                              ((Big_int.big_int, unit) rbt *
                                unit nfa_props_ext))))
  val rs_nfa_right_quotient_lists :
    'a linorder ->
      ('a -> bool) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
          (Big_int.big_int, unit) rbt *
            (('a, unit) rbt *
              (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                 (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                 lTS_choice *
                ((Big_int.big_int, unit) rbt *
                  ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_pres_nfa_of_pf :
    Big_int.big_int ->
      pf -> (Big_int.big_int, ((bool list), unit) rbt) rbt ->
              ((Big_int.big_int, unit) rbt *
                (((bool list), unit) rbt *
                  (((Big_int.big_int,
                      ((bool list), (Big_int.big_int, unit) rbt) rbt)
                      rbt,
                     (Big_int.big_int, ((bool list), Big_int.big_int) rbt) rbt)
                     lTS_choice *
                    ((Big_int.big_int, unit) rbt *
                      ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))) *
                (Big_int.big_int, ((bool list), unit) rbt) rbt
  val rs_pres_pf_to_nfa :
    Big_int.big_int ->
      pf -> (Big_int.big_int, unit) rbt *
              (((bool list), unit) rbt *
                (((Big_int.big_int,
                    ((bool list), (Big_int.big_int, unit) rbt) rbt)
                    rbt,
                   (Big_int.big_int, ((bool list), Big_int.big_int) rbt) rbt)
                   lTS_choice *
                  ((Big_int.big_int, unit) rbt *
                    ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_eval_pf : pf -> bool
  val dfa_accepting :
    Big_int.big_int bdd list * bool list -> Big_int.big_int -> bool
  val eval_pf_dfa : pf -> bool
  val rs_nfa_rename_labels :
    'a linorder ->
      bool ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
          ('a -> 'a) ->
            (Big_int.big_int, unit) rbt *
              (('a, unit) rbt *
                (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
                   (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
                   lTS_choice *
                  ((Big_int.big_int, unit) rbt *
                    ((Big_int.big_int, unit) rbt * unit nfa_props_ext))))
  val rs_nfa_language_is_empty :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        bool
  val rs_nfa_language_is_subset :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
          bool
  val rs_nfa_language_is_eq :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        (Big_int.big_int, unit) rbt *
          (('a, unit) rbt *
            (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
               (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
               lTS_choice *
              ((Big_int.big_int, unit) rbt *
                ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
          bool
  val rs_nfa_destruct_simple :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        Big_int.big_int list *
          ('a list *
            ((Big_int.big_int * ('a * Big_int.big_int)) list *
              (Big_int.big_int list * Big_int.big_int list)))
  val rs_nfa_language_is_univ :
    'a linorder ->
      (Big_int.big_int, unit) rbt *
        (('a, unit) rbt *
          (((Big_int.big_int, ('a, (Big_int.big_int, unit) rbt) rbt) rbt,
             (Big_int.big_int, ('a, Big_int.big_int) rbt) rbt)
             lTS_choice *
            ((Big_int.big_int, unit) rbt *
              ((Big_int.big_int, unit) rbt * unit nfa_props_ext)))) ->
        bool
end = struct

let rec id x = (fun xa -> xa) x;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

type color = R | B;;

type ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

type ('a, 'b) rbt = Rbt of ('a, 'b) rbta;;

let rec hd (x :: xs) = x;;

let rec tl = function [] -> []
             | x :: xs -> xs;;

let rec collect p = p;;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec dom m = collect (fun a -> not (is_none (m a)));;

let rec suc n = Big_int.add_big_int n (Big_int.big_int_of_int 1);;

let rec comp f g = (fun x -> f (g x));;

let rec map
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs -> f x :: map f xs;;

let rec minus_nat
  n m = Big_int.max_big_int Big_int.zero_big_int (Big_int.sub_big_int n m);;

let rec nth
  (x :: xs) n =
    (if Big_int.eq_big_int n (Big_int.big_int_of_int 0) then x
      else nth xs (minus_nat n (Big_int.big_int_of_int 1)));;

let rec fold
  f x1 = match f, x1 with f, [] -> id
    | f, x :: xs -> comp (fold f xs) (f x);;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec empty _A = Rbt Empty;;

let ord_int =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

let rec foldl
  f a x2 = match f, a, x2 with f, a, [] -> a
    | f, a, x :: xs -> foldl f (f a x) xs;;

let ord_nat =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

let rec the (Some x) = x;;

let rec impl_of _A (Rbt x) = x;;

let rec paint
  c x1 = match c, x1 with c, Empty -> Empty
    | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combine
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combine b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combine b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec del _A
  x xa1 = match x, xa1 with x, Empty -> Empty
    | x, Branch (c, a, y, s, b) ->
        (if less _A.order_linorder.preorder_order.ord_preorder x y
          then del_from_left _A x a y s b
          else (if less _A.order_linorder.preorder_order.ord_preorder y x
                 then del_from_right _A x a y s b else combine a b))
and del_from_right _A
  x a y s xa4 = match x, a, y, s, xa4 with
    x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (del _A x (Branch (B, lt, z, v, rt)))
    | x, a, y, s, Empty -> Branch (R, a, y, s, del _A x Empty)
    | x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, del _A x (Branch (R, va, vb, vc, vd)))
and del_from_left _A
  x xa1 y s b = match x, xa1, y, s, b with
    x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (del _A x (Branch (B, lt, z, v, rt))) y s b
    | x, Empty, y, s, b -> Branch (R, del _A x Empty, y, s, b)
    | x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, del _A x (Branch (R, va, vb, vc, vd)), y, s, b);;

let rec deletea _A k t = paint B (del _A k t);;

let rec delete _A k t = Rbt (deletea _A k (impl_of _A t));;

let rec ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if less _A.order_linorder.preorder_order.ord_preorder k x
          then balance (ins _A f k v l) x y r
          else (if less _A.order_linorder.preorder_order.ord_preorder x k
                 then balance l x y (ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if less _A.order_linorder.preorder_order.ord_preorder k x
          then Branch (R, ins _A f k v l, x, y, r)
          else (if less _A.order_linorder.preorder_order.ord_preorder x k
                 then Branch (R, l, x, y, ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec insert_with_key _A f k v t = paint B (ins _A f k v t);;

let rec insertb _A = insert_with_key _A (fun _ _ nv -> nv);;

let rec insert _A k v t = Rbt (insertb _A k v (impl_of _A t));;

let rec lookupa _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if less _A.order_linorder.preorder_order.ord_preorder k x
          then lookupa _A l k
          else (if less _A.order_linorder.preorder_order.ord_preorder x k
                 then lookupa _A r k else Some y));;

let rec lookup _A t = lookupa _A (impl_of _A t);;

let rec gen_dfs
  succs ins memb s wl =
    (match wl with [] -> s
      | x :: xs ->
        (if memb x s then gen_dfs succs ins memb s xs
          else gen_dfs succs ins memb (ins x s) (succs x @ xs)));;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let rec abs_int
  i = (if Big_int.lt_big_int i (Big_int.big_int_of_int 0)
        then Big_int.minus_big_int i else i);;

let plus_int = ({plus = Big_int.add_big_int} : Big_int.big_int plus);;

let rec sgn_int
  i = (if Big_int.eq_big_int i (Big_int.big_int_of_int 0)
        then (Big_int.big_int_of_int 0)
        else (if Big_int.lt_big_int (Big_int.big_int_of_int 0) i
               then (Big_int.big_int_of_int 1)
               else Big_int.minus_big_int (Big_int.big_int_of_int 1)));;

let zero_inta : Big_int.big_int = (Big_int.big_int_of_int 0);;

let zero_int = ({zero = zero_inta} : Big_int.big_int zero);;

let rec member _A
  x0 y = match x0, y with [], y -> false
    | x :: xs, y -> eq _A x y || member _A xs y;;

let rec inserta _A x xs = (if member _A xs x then xs else x :: xs);;

let zero_nata : Big_int.big_int = (Big_int.big_int_of_int 0);;

let zero_nat = ({zero = zero_nata} : Big_int.big_int zero);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

let rec product
  x0 uu = match x0, uu with [], uu -> []
    | x :: xs, ys -> map (fun a -> (x, a)) ys @ product xs ys;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

let rec listsum _A
  xs = fold (fun x y -> plus _A.semigroup_add_monoid_add.plus_semigroup_add y x)
         xs (zero _A.zero_monoid_add);;

let rec eu_sng empt update k v = update k v (empt ());;

let rec it_add
  update iti m1 m2 = iti m2 (fun _ -> true) (fun (a, b) -> update a b) m1;;

let rec less_eq_prod_aux (_A1, _A2) _B
  (a1, a2) (b1, b2) = less _A2 a1 b1 || eq _A1 a1 b1 && less_eq _B a2 b2;;

let rec equal_proda _A _B (aa, ba) (a, b) = eq _A aa a && eq _B ba b;;

let rec less_prod (_A1, _A2) (_B1, _B2)
  a b = not (equal_proda _A1 _B1 a b) && less_eq_prod_aux (_A1, _A2) _B2 a b;;

let rec less_eq_prod (_A1, _A2) _B a b = less_eq_prod_aux (_A1, _A2) _B a b;;

let rec ord_prod (_A1, _A2) (_B1, _B2) =
  ({less_eq = less_eq_prod (_A1, _A2) _B2;
     less = less_prod (_A1, _A2) (_B1, _B2)}
    : ('a * 'b) ord);;

let equal_nat = ({equal = Big_int.eq_big_int} : Big_int.big_int equal);;

let preorder_nat = ({ord_preorder = ord_nat} : Big_int.big_int preorder);;

let order_nat = ({preorder_order = preorder_nat} : Big_int.big_int order);;

let rec ei_sng e i x = i x (e ());;

let rec list_all
  p x1 = match p, x1 with p, [] -> true
    | p, x :: xs -> p x && list_all p xs;;

let rec merge (_A1, _A2)
  x0 l2 = match x0, l2 with [], l2 -> l2
    | v :: va, [] -> v :: va
    | x1 :: l1, x2 :: l2 ->
        (if less _A2.order_linorder.preorder_order.ord_preorder x1 x2
          then x1 :: merge (_A1, _A2) l1 (x2 :: l2)
          else (if eq _A1 x1 x2 then x1 :: merge (_A1, _A2) l1 l2
                 else x2 :: merge (_A1, _A2) (x1 :: l1) l2));;

let rec it_size
  iti m = iti m (fun _ -> true) (fun _ -> suc) (Big_int.big_int_of_int 0);;

let rec iti_sel iti m f = iti m is_none (fun x _ -> f x) None;;

let rec maxa less_eq a b = (if less_eq a b then b else a);;

let rec max _A = maxa (less_eq _A);;

let rec it_diff it del s1 s2 = it s2 (fun _ -> true) del s1;;

let rec it_sizea
  iti s = iti s (fun _ -> true) (fun _ -> suc) (Big_int.big_int_of_int 0);;

let rec sel_sel sel s p = sel s (fun x -> (if p x then Some x else None));;

let rec equal_lista _A
  x0 x1 = match x0, x1 with a :: lista, [] -> false
    | [], a :: lista -> false
    | aa :: listaa, a :: lista -> eq _A aa a && equal_lista _A listaa lista
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        let (yes, no) = partition p xs in
        (if p x then (x :: yes, no) else (yes, x :: no));;

let rec replicate
  n x = (if Big_int.eq_big_int n (Big_int.big_int_of_int 0) then []
          else x :: replicate (minus_nat n (Big_int.big_int_of_int 1)) x);;

let rec size_list
  = function [] -> (Big_int.big_int_of_int 0)
    | a :: lista ->
        Big_int.add_big_int (size_list lista) (suc (Big_int.big_int_of_int 0));;

let rec sel_ball
  sel s p = is_none (sel s (fun kv -> (if not (p kv) then Some () else None)));;

let rec preorder_prod (_A1, _A2) (_B1, _B2) =
  ({ord_preorder =
      (ord_prod (_A1, _A2.preorder_order.ord_preorder)
        (_B1, _B2.preorder_order.ord_preorder))}
    : ('a * 'b) preorder);;

let rec order_prod (_A1, _A2) (_B1, _B2) =
  ({preorder_order = (preorder_prod (_A1, _A2) (_B1, _B2))} : ('a * 'b) order);;

let rec s_ins update x s = update x () s;;

let rec s_sel sel s f = sel s (fun (u, _) -> f u);;

let rec it_inter
  iteratei1 memb2 empt3 insrt3 s1 s2 =
    iteratei1 s1 (fun _ -> true)
      (fun x s -> (if memb2 x s2 then insrt3 x s else s))
      (empt3 ());;

let rec iti_ball iti s p = iti s (fun c -> c) (fun x _ -> p x) true;;

let rec rm_empty _A = (fun _ -> empty _A);;

let rec rm_update _A = insert _A;;

let rec rm_sng _A = eu_sng (rm_empty _A) (rm_update _A);;

let rec rs_ins _A = s_ins (rm_update _A);;

let rec rs_empty _A = rm_empty _A;;

let rec rs_sng _A = ei_sng (rs_empty _A) (rs_ins _A);;

let rec fst (a, b) = a;;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_int
  k l = (if Big_int.eq_big_int k (Big_int.big_int_of_int 0)
          then ((Big_int.big_int_of_int 0), (Big_int.big_int_of_int 0))
          else (if Big_int.eq_big_int l (Big_int.big_int_of_int 0)
                 then ((Big_int.big_int_of_int 0), k)
                 else apsnd (Big_int.mult_big_int (sgn_int l))
                        (if Big_int.eq_big_int (sgn_int k) (sgn_int l)
                          then Big_int.quomod_big_int (Big_int.abs_big_int k)
                                 (Big_int.abs_big_int l)
                          else let (r, s) =
                                 Big_int.quomod_big_int (Big_int.abs_big_int k)
                                   (Big_int.abs_big_int l)
                                 in
                               (if Big_int.eq_big_int s
                                     (Big_int.big_int_of_int 0)
                                 then (Big_int.minus_big_int r,
(Big_int.big_int_of_int 0))
                                 else (Big_int.sub_big_int
 (Big_int.minus_big_int r) (Big_int.big_int_of_int 1),
Big_int.sub_big_int (abs_int l) s)))));;

let rec div_int a b = fst (divmod_int a b);;

let rec div_nat m n = fst (Big_int.quomod_big_int m n);;

let rec snd (a, b) = b;;

let rec mod_int a b = snd (divmod_int a b);;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec sza_isSng
  iti m =
    Big_int.eq_big_int
      (iti m (fun sigma -> Big_int.lt_big_int sigma (Big_int.big_int_of_int 2))
         (fun _ -> suc)
        (Big_int.big_int_of_int 0))
      (Big_int.big_int_of_int 1);;

type 'a nfa_props_ext = Nfa_props_ext of bool * bool * 'a;;

let rec fields
  nfa_prop_is_complete_deterministic nfa_prop_is_initially_connected =
    Nfa_props_ext
      (nfa_prop_is_complete_deterministic, nfa_prop_is_initially_connected,
        ());;

let linorder_nat = ({order_linorder = order_nat} : Big_int.big_int linorder);;

let rec s_memb lookup x s = not (is_none (lookup x s));;

let rec sza_isSnga
  iti s =
    Big_int.eq_big_int
      (iti s (fun sigma -> Big_int.lt_big_int sigma (Big_int.big_int_of_int 2))
         (fun _ -> suc)
        (Big_int.big_int_of_int 0))
      (Big_int.big_int_of_int 1);;

let rec iam_empty x = (fun _ -> STArray.IsabelleMapping.array_of_list []) x;;

let rec iam_increment
  l idx =
    max ord_nat
      (minus_nat (Big_int.add_big_int idx (Big_int.big_int_of_int 1)) l)
      (Big_int.add_big_int (Big_int.mult_big_int (Big_int.big_int_of_int 2) l)
        (Big_int.big_int_of_int 3));;

let rec iam_update
  k v a =
    let l = STArray.IsabelleMapping.array_length a in
    let aa =
      (if Big_int.lt_big_int k l then a
        else STArray.IsabelleMapping.array_grow a (iam_increment l k) None)
      in
    STArray.IsabelleMapping.array_set aa k (Some v);;

let rec iam_sng x = eu_sng iam_empty iam_update x;;

let rec rm_iterateoi
  x0 c f sigma = match x0, c, f, sigma with Empty, c, f, sigma -> sigma
    | Branch (col, l, k, v, r), c, f, sigma ->
        (if c sigma
          then let sigmaa = rm_iterateoi l c f sigma in
               (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa)
                 else sigmaa)
          else sigma);;

let rec rm_iterateoia _A r = rm_iterateoi (impl_of _A r);;

let rec rm_iteratei _A = rm_iterateoia _A;;

let rec rm_sel _A = iti_sel (rm_iteratei _A);;

let rec rm_ball _A = sel_ball (rm_sel _A);;

let rec rm_size _A = it_size (rm_iteratei _A);;

let rec rm_delete _A = delete _A;;

let rec rs_delete _A = rm_delete _A;;

let rec s_iteratei it s c f = it s c (fun x -> f (fst x));;

let rec rs_iteratei _A = s_iteratei (rm_iteratei _A);;

let rec rr_diff _A = it_diff (rs_iteratei _A) (rs_delete _A);;

let rec rs_ball _A = iti_ball (rs_iteratei _A);;

let rec rs_size _A = it_sizea (rs_iteratei _A);;

let rec ltsga_copy
  it emp add l = it l (fun _ -> true) (fun (q, (a, b)) -> add q a b) (emp ());;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if Big_int.eq_big_int i (Big_int.big_int_of_int 0) then y :: xs
          else x :: list_update xs (minus_nat i (Big_int.big_int_of_int 1)) y);;

let rec equal_color
  x0 x1 = match x0, x1 with B, R -> false
    | R, B -> false
    | B, B -> true
    | R, R -> true;;

let rec equal_rbtb _A _B
  x0 x1 = match x0, x1 with Branch (color, rbt1, a, b, rbt2), Empty -> false
    | Empty, Branch (color, rbt1, a, b, rbt2) -> false
    | Branch (colora, rbt1a, aa, ba, rbt2a), Branch (color, rbt1, a, b, rbt2) ->
        equal_color colora color &&
          (equal_rbtb _A _B rbt1a rbt1 &&
            (eq _A aa a && (eq _B ba b && equal_rbtb _A _B rbt2a rbt2)))
    | Empty, Empty -> true;;

let rec equal_rbta (_A1, _A2) _B
  ra r = equal_rbtb _A1 _B (impl_of _A2 ra) (impl_of _A2 r);;

let rec equal_rbt (_A1, _A2) _B =
  ({equal = equal_rbta (_A1, _A2) _B} : ('a, 'b) rbt equal);;

let rec s_alpha alpha m = dom (alpha m);;

let rec iflt_image iflt f s = iflt (fun x -> Some (f x)) s;;

let rec iam_iteratei_aux
  v a c f sigma =
    (if Big_int.eq_big_int v (Big_int.big_int_of_int 0) then sigma
      else (if c sigma
             then iam_iteratei_aux
                    (minus_nat (suc (minus_nat v (Big_int.big_int_of_int 1)))
                      (Big_int.big_int_of_int 1))
                    a c f
                    (match
                      STArray.IsabelleMapping.array_get a
                        (minus_nat
                          (suc (minus_nat v (Big_int.big_int_of_int 1)))
                          (Big_int.big_int_of_int 1))
                      with None -> sigma
                      | Some x ->
                        f (minus_nat
                             (suc (minus_nat v (Big_int.big_int_of_int 1)))
                             (Big_int.big_int_of_int 1),
                            x)
                          sigma)
             else sigma));;

let rec iam_iteratei
  a = iam_iteratei_aux (STArray.IsabelleMapping.array_length a) a;;

let rec iam_sel x = iti_sel iam_iteratei x;;

let rec iam_ball x = sel_ball iam_sel x;;

let rec iam_size x = it_size iam_iteratei x;;

let rec rm_isSng _A = sza_isSng (rm_iteratei _A);;

let rec ball_subset ball1 mem2 s1 s2 = ball1 s1 (fun x -> mem2 x s2);;

let rec rm_lookup _A k m = lookup _A m k;;

let rec rs_memb _A = s_memb (rm_lookup _A);;

let rec rr_subset _A = ball_subset (rs_ball _A) (rs_memb _A);;

let rec subset_equal ss1 ss2 s1 s2 = ss1 s1 s2 && ss2 s2 s1;;

let rec rr_equal _A = subset_equal (rr_subset _A) (rr_subset _A);;

let rec rs_isSng _A = sza_isSnga (rs_iteratei _A);;

let rec worklist
  b f x2 = match b, f, x2 with
    b, f, (s, e :: wl) ->
      (if b s then let (sa, n) = f s e in
                   worklist b f (sa, n @ wl)
        else (s, e :: wl))
    | b, f, (s, []) -> (s, []);;

let semigroup_add_int =
  ({plus_semigroup_add = plus_int} : Big_int.big_int semigroup_add);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    Big_int.big_int monoid_add);;

type ('a, 'b) lTS_choice = Lts of 'a | Dlts of 'b;;

let rec iti_isEmpty iti m = iti m (fun c -> c) (fun _ _ -> false) true;;

let rec linorder_prod (_A1, _A2) (_B1, _B2) =
  ({order_linorder =
      (order_prod (_A1, _A2.order_linorder) (_B1, _B2.order_linorder))}
    : ('a * 'b) linorder);;

let rec less_bool x0 b = match x0, b with true, b -> false
                    | false, b -> b;;

let rec less_eq_bool x0 b = match x0, b with true, b -> b
                       | false, b -> true;;

let ord_bool = ({less_eq = less_eq_bool; less = less_bool} : bool ord);;

let rec rm_add _A = it_add (rm_update _A) (rm_iteratei _A);;

let rec iti_sel_no_map
  iti m p = iti m is_none (fun x _ -> (if p x then Some x else None)) None;;

let rec rm_reverse_iterateoi
  x0 c f sigma = match x0, c, f, sigma with Empty, c, f, sigma -> sigma
    | Branch (col, l, k, v, r), c, f, sigma ->
        (if c sigma
          then let sigmaa = rm_reverse_iterateoi r c f sigma in
               (if c sigmaa then rm_reverse_iterateoi l c f (f (k, v) sigmaa)
                 else sigmaa)
          else sigma);;

let rec rm_reverse_iterateoia _A r = rm_reverse_iterateoi (impl_of _A r);;

let rec rm_max _A = iti_sel_no_map (rm_reverse_iterateoia _A);;

let rec rm_min _A = iti_sel_no_map (rm_iterateoia _A);;

let rec iti_sel_no_mapa
  iti s f = iti s is_none (fun x _ -> (if f x then Some x else None)) None;;

let rec rs_reverse_iterateoi _A = s_iteratei (rm_reverse_iterateoia _A);;

let rec rs_max _A = iti_sel_no_mapa (rs_reverse_iterateoi _A);;

let rec rs_iterateoi _A = s_iteratei (rm_iterateoia _A);;

let rec rs_min _A = iti_sel_no_mapa (rs_iterateoi _A);;

let rec rs_sel _A = s_sel (rm_sel _A);;

let rec s_ins_dj update_dj x s = update_dj x () s;;

let rec iflt_filter
  iflt p s = iflt (fun x -> (if p x then Some x else None)) s;;

let rec iam_isSng x = sza_isSng iam_iteratei x;;

let rec rm_update_dj _A = rm_update _A;;

let rec rs_ins_dj _A = s_ins_dj (rm_update_dj _A);;

let rec it_image_filter
  iteratei1 empty2 ins2 f s =
    iteratei1 s (fun _ -> true)
      (fun x res -> (match f x with None -> res | Some v -> ins2 v res))
      (empty2 ());;

let rec rr_inj_image_filter _A _B
  = it_image_filter (rs_iteratei _A) (rs_empty _B) (rs_ins_dj _B);;

let rec rr_filter _A = iflt_filter (rr_inj_image_filter _A _A);;

let rec merge_list (_A1, _A2)
  acc2 x1 = match acc2, x1 with [], [] -> []
    | [], [l] -> l
    | la :: acc2, [] -> merge_list (_A1, _A2) [] (la :: acc2)
    | la :: acc2, [l] -> merge_list (_A1, _A2) [] (l :: la :: acc2)
    | acc2, l1 :: l2 :: ls ->
        merge_list (_A1, _A2) (merge (_A1, _A2) l1 l2 :: acc2) ls;;

type ('a, 'b, 'c, 'd) map_ops_ext =
  Map_ops_ext of
    ('c -> 'a -> 'b option) * ('c -> bool) * (unit -> 'c) * ('a -> 'b -> 'c) *
      ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c) *
      ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'c) *
      (('a * 'b -> bool) -> 'c -> 'c) * ('c -> 'c -> 'c) * ('c -> 'c -> 'c) *
      ('c -> bool) * ('c -> bool) * ('c -> ('a * 'b -> bool) -> bool) *
      ('c -> ('a * 'b -> bool) -> bool) * ('c -> Big_int.big_int) *
      (Big_int.big_int -> 'c -> Big_int.big_int) *
      ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * ('c -> ('a * 'b) list) *
      (('a * 'b) list -> 'c) * 'd;;

let rec map_op_sng
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
    = map_op_sng;;

let rec rm_sela _A = iti_sel_no_map (rm_iteratei _A);;

let rec rs_sela _A = sel_sel (rs_sel _A);;

type ('a, 'b, 'c) set_ops_ext =
  Set_ops_ext of
    ('b -> 'a -> bool) * ('b -> bool) * (unit -> 'b) * ('a -> 'b) *
      ('a -> 'b -> bool) * ('a -> 'b -> 'b) * ('a -> 'b -> 'b) *
      ('a -> 'b -> 'b) * ('b -> bool) * ('b -> bool) *
      ('b -> ('a -> bool) -> bool) * ('b -> ('a -> bool) -> bool) *
      ('b -> Big_int.big_int) * (Big_int.big_int -> 'b -> Big_int.big_int) *
      ('b -> 'b -> 'b) * ('b -> 'b -> 'b) * ('b -> 'b -> 'b) *
      (('a -> bool) -> 'b -> 'b) * ('b -> 'b -> 'b) * ('b -> 'b -> bool) *
      ('b -> 'b -> bool) * ('b -> 'b -> bool) * ('b -> 'b -> 'a option) *
      ('b -> ('a -> bool) -> 'a option) * ('b -> 'a list) * ('a list -> 'b) *
      'c;;

let rec neg_ball_bexists ball s p = not (ball s (fun kv -> not (p kv)));;

let rec rm_bexists _A = neg_ball_bexists (rm_ball _A);;

let rec neg_ball_bexistsa ball s p = not (ball s (fun x -> not (p x)));;

let rec rs_bexists _A = neg_ball_bexistsa (rs_ball _A);;

let rec ltsga_reverse
  e a it l = it l (fun _ -> true) (fun (v, (ea, va)) -> a va ea v) (e ());;

let rec foldli
  x0 c f sigma = match x0, c, f, sigma with [], c, f, sigma -> sigma
    | x :: xs, c, f, sigma ->
        (if c sigma then foldli xs c f (f x sigma) else sigma);;

type ('a, 'b, 'c, 'd) omap_ops_ext =
  Omap_ops_ext of
    ('c -> ('a * 'b -> bool) -> ('a * 'b) option) *
      ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * 'd;;

let preorder_bool = ({ord_preorder = ord_bool} : bool preorder);;

let order_bool = ({preorder_order = preorder_bool} : bool order);;

let rec rm_alpha _A = lookup _A;;

let rec rs_alpha _A = s_alpha (rm_alpha _A);;

let rec rs_image_filter _A _B
  = it_image_filter (rs_iteratei _A) (rs_empty _B) (rs_ins _B);;

let rec rs_image _A _B = iflt_image (rs_image_filter _A _B);;

let rec rs_inter _A
  = it_inter (rs_iteratei _A) (rs_memb _A) (rs_empty _A) (rs_ins_dj _A);;

let rec rs_union _A = rm_add _A;;

let rec ball_disjoint ball1 memb2 s1 s2 = ball1 s1 (fun x -> not (memb2 x s2));;

type ('a, 'b, 'c) oset_ops_ext =
  Oset_ops_ext of
    ('b -> ('a -> bool) -> 'a option) * ('b -> ('a -> bool) -> 'a option) * 'c;;

let rec set_op_diff
  (Set_ops_ext
    (set_op_alpha, set_op_invar, set_op_empty, set_op_sng, set_op_memb,
      set_op_ins, set_op_ins_dj, set_op_delete, set_op_isEmpty, set_op_isSng,
      set_op_ball, set_op_bexists, set_op_size, set_op_size_abort, set_op_union,
      set_op_union_dj, set_op_diff, set_op_filter, set_op_inter, set_op_subset,
      set_op_equal, set_op_disjoint, set_op_disjoint_witness, set_op_sel,
      set_op_to_list, set_op_from_list, more))
    = set_op_diff;;

let rec iam_bexists x = neg_ball_bexists iam_ball x;;

let rec rr_disjoint _A = ball_disjoint (rs_ball _A) (rs_memb _A);;

let rec it_map_image_filter
  map_it map_emp map_up_dj f m =
    map_it m (fun _ -> true)
      (fun kv sigma ->
        (match f kv with None -> sigma | Some (k, v) -> map_up_dj k v sigma))
      (map_emp ());;

let rec it_map_restrict
  map_it map_emp map_up_dj p =
    it_map_image_filter map_it map_emp map_up_dj
      (fun (k, v) -> (if p (k, v) then Some (k, v) else None));;

let rec rr_restrict _A
  = it_map_restrict (rm_iteratei _A) (rm_empty _A) (rm_update_dj _A);;

let rec iam_add x = it_add iam_update iam_iteratei x;;

let rec it_map_to_list iti m = iti m (fun _ -> true) (fun a b -> a :: b) [];;

let rec iti_size_abort
  iti n m =
    iti m (fun sigma -> Big_int.lt_big_int sigma n) (fun _ -> suc)
      (Big_int.big_int_of_int 0);;

let rec map_op_empty
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
    = map_op_empty;;

let rec rm_add_dj _A = rm_add _A;;

let rec gen_list_to_map_aux
  upd accs x2 = match upd, accs, x2 with upd, accs, [] -> accs
    | upd, accs, (k, v) :: l -> gen_list_to_map_aux upd (upd k v accs) l;;

let rec gen_list_to_map empt upd l = gen_list_to_map_aux upd (empt ()) (rev l);;

let rec list_to_rm _A = gen_list_to_map (rm_empty _A) (rm_update _A);;

let rec rm_isEmpty (_A1, _A2) _B
  m = eq (equal_rbt (_A1, _A2) _B) m (empty _A2);;

let rec rm_to_list _A = it_map_to_list (rm_reverse_iterateoia _A);;

let rec rm_size_abort _A = iti_size_abort (rm_iteratei _A);;

let rec rm_ops (_A1, _A2) _B
  = Map_ops_ext
      (rm_alpha _A2, (fun _ -> true), rm_empty _A2, rm_sng _A2, rm_lookup _A2,
        rm_update _A2, rm_update_dj _A2, rm_delete _A2, rr_restrict _A2,
        rm_add _A2, rm_add_dj _A2, rm_isEmpty (_A1, _A2) _B, rm_isSng _A2,
        rm_ball _A2, rm_bexists _A2, rm_size _A2, rm_size_abort _A2,
        rm_sela _A2, rm_to_list _A2, list_to_rm _A2,
        Omap_ops_ext (rm_min _A2, rm_max _A2, ()));;

let rec gen_list_to_set_aux
  ins accs x2 = match ins, accs, x2 with ins, accs, [] -> accs
    | ins, accs, x :: l -> gen_list_to_set_aux ins (ins x accs) l;;

let rec gen_list_to_set empt ins = gen_list_to_set_aux ins (empt ());;

let rec list_to_rs _A = gen_list_to_set (rs_empty _A) (rs_ins _A);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec rs_isEmpty (_A1, _A2) = rm_isEmpty (_A1, _A2) equal_unit;;

let rec it_set_to_list iti s = iti s (fun _ -> true) (fun a b -> a :: b) [];;

let rec rs_to_list _A = it_set_to_list (rs_reverse_iterateoi _A);;

let rec iti_size_aborta
  iti m s =
    iti s (fun sigma -> Big_int.lt_big_int sigma m) (fun _ -> suc)
      (Big_int.big_int_of_int 0);;

let rec rs_size_abort _A = iti_size_aborta (rs_iteratei _A);;

let rec rs_union_dj _A = rm_add_dj _A;;

let rec sel_disjoint_witness
  sel1 mem2 s1 s2 = sel1 s1 (fun x -> (if mem2 x s2 then Some x else None));;

let rec rr_disjoint_witness _A = sel_disjoint_witness (rs_sel _A) (rs_memb _A);;

let rec rs_ops (_A1, _A2)
  = Set_ops_ext
      (rs_alpha _A2, (fun _ -> true), rs_empty _A2, rs_sng _A2, rs_memb _A2,
        rs_ins _A2, rs_ins_dj _A2, rs_delete _A2, rs_isEmpty (_A1, _A2),
        rs_isSng _A2, rs_ball _A2, rs_bexists _A2, rs_size _A2,
        rs_size_abort _A2, rs_union _A2, rs_union_dj _A2, rr_diff _A2,
        rr_filter _A2, rs_inter _A2, rr_subset _A2, rr_equal _A2,
        rr_disjoint _A2, rr_disjoint_witness _A2, rs_sela _A2, rs_to_list _A2,
        list_to_rs _A2, Oset_ops_ext (rs_min _A2, rs_max _A2, ()));;

let rec iam_sela x = iti_sel_no_map iam_iteratei x;;

let rec map_op_lookup
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
    = map_op_lookup;;

let rec map_op_update
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
    = map_op_update;;

type pf = Eq of Big_int.big_int list * Big_int.big_int |
  Le of Big_int.big_int list * Big_int.big_int | And of pf * pf | Or of pf * pf
  | Imp of pf * pf | Forall of pf | Exist of pf | Neg of pf;;

let rec iam_update_dj x = iam_update x;;

let rec imim_restrict
  x = it_map_restrict iam_iteratei iam_empty iam_update_dj x;;

let rec iam_alpha
  a i = (if Big_int.lt_big_int i (STArray.IsabelleMapping.array_length a)
          then STArray.IsabelleMapping.array_get a i else None);;

let rec iam_size_abort x = iti_size_abort iam_iteratei x;;

let rec iam_add_dj x = iam_add x;;

let rec iam_delete
  k a = (if Big_int.lt_big_int k (STArray.IsabelleMapping.array_length a)
          then STArray.IsabelleMapping.array_set a k None else a);;

let rec iam_lookup k a = iam_alpha a k;;

let rec iam_isEmpty x = iti_isEmpty iam_iteratei x;;

let rec iam_to_list x = it_map_to_list iam_iteratei x;;

let rec list_to_iam x = gen_list_to_map iam_empty iam_update x;;

let iam_ops :
  (Big_int.big_int, 'a, (('a option) STArray.IsabelleMapping.arrayType), unit)
    map_ops_ext
  = Map_ops_ext
      (iam_alpha, (fun _ -> true), iam_empty, iam_sng, iam_lookup, iam_update,
        iam_update_dj, iam_delete, imim_restrict, iam_add, iam_add_dj,
        iam_isEmpty, iam_isSng, iam_ball, iam_bexists, iam_size, iam_size_abort,
        iam_sela, iam_to_list, list_to_iam, ());;

let rec insertion_sort (_A1, _A2)
  x xa1 = match x, xa1 with x, [] -> [x]
    | x, y :: xs ->
        (if less _A2 y x then y :: insertion_sort (_A1, _A2) x xs
          else (if eq _A1 x y then y :: xs else x :: y :: xs));;

let rec triangle
  n = div_nat (Big_int.mult_big_int n (suc n)) (Big_int.big_int_of_int 2);;

type 'a bdd = Leaf of 'a | Brancha of 'a bdd * 'a bdd;;

let rec equal_boola
  p pa = match p, pa with p, true -> p
    | p, false -> not p
    | true, p -> p
    | false, p -> not p;;

let equal_bool = ({equal = equal_boola} : bool equal);;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec while_option b c s = (if b s then while_option b c (c s) else Some s);;

let rec whilea b c s = the (while_option b c s);;

let rec rs_dlts_it _A _B
  = (fun m1 c f ->
      rm_iteratei _A m1 c
        (fun (v1, m2) ->
          rm_iteratei _B m2 c (fun (e, v2) -> f (v1, (e, v2)))));;

let rec dltsbc_add
  l_add d_add qa a q x5 = match l_add, d_add, qa, a, q, x5 with
    l_add, d_add, qa, a, q, Lts l -> Lts (l_add qa a q l)
    | l_add, d_add, qa, a, q, Dlts d -> Dlts (d_add qa a q d);;

let rec sum_encode
  x = (match x with Inl a -> Big_int.mult_big_int (Big_int.big_int_of_int 2) a
        | Inr b -> suc (Big_int.mult_big_int (Big_int.big_int_of_int 2) b));;

let rec int_encode
  i = sum_encode
        (if Big_int.le_big_int (Big_int.big_int_of_int 0) i
          then Inl (Big_int.max_big_int Big_int.zero_big_int i)
          else Inr (Big_int.max_big_int Big_int.zero_big_int
                     (Big_int.sub_big_int (Big_int.minus_big_int i)
                       (Big_int.big_int_of_int 1))));;

let rec tr_lookup
  x = (fun t i j ->
        (if Big_int.eq_big_int i j then false
          else (if Big_int.lt_big_int j i
                 then nth (nth t (minus_nat i (Big_int.big_int_of_int 1))) j
                 else nth (nth t (minus_nat j (Big_int.big_int_of_int 1))) i)))
        x;;

let rec check_eq
  x0 x1 t = match x0, x1, t with Leaf i, Leaf j, t -> not (tr_lookup t i j)
    | Brancha (l, r), Leaf i, t ->
        check_eq l (Leaf i) t && check_eq r (Leaf i) t
    | Leaf i, Brancha (l, r), t ->
        check_eq (Leaf i) l t && check_eq (Leaf i) r t
    | Brancha (l1, r1), Brancha (l2, r2), t ->
        check_eq l1 l2 t && check_eq r1 r2 t;;

let rec fold_map_idx
  f i y x3 = match f, i, y, x3 with f, i, y, [] -> (y, [])
    | f, i, y, x :: xs ->
        let (ya, xa) = f i y x in
        let (yb, xsa) = fold_map_idx f (suc i) ya xs in
        (yb, xa :: xsa);;

let rec iter
  x = (fun (bd, _) t ->
        fold_map_idx
          (fun i ->
            fold_map_idx
              (fun j c b ->
                let ba = b || not (check_eq (nth bd i) (nth bd j) t) in
                (c || not (equal_boola b ba), ba))
              (Big_int.big_int_of_int 0))
          (Big_int.big_int_of_int 1) false t)
        x;;

let rec rs_dlts_add _A _B
  = (fun v w va l ->
      (match rm_lookup _A v l with None -> rm_update _A v (rm_sng _B w va) l
        | Some m2 -> rm_update _A v (rm_update _B w va m2) l));;

let rec rs_nfa_props _A (q, (a, (d, (i, (f, flags))))) = flags;;

let rec prod_encode
  x = (fun (m, n) -> Big_int.add_big_int (triangle (Big_int.add_big_int m n)) m)
        x;;

let rec bv_or
  x0 x1 = match x0, x1 with [], [] -> []
    | x :: xs, y :: ys -> (x || y) :: bv_or xs ys;;

let rec fixpt
  m t = (match iter m t with (true, t2) -> fixpt m t2 | (false, t2) -> t2);;

let rec map_index
  f x1 n = match f, x1, n with f, [], n -> []
    | f, x :: xs, n -> f x n :: map_index f xs (suc n);;

let rec rquot_ins x = (fun xa l -> list_update l xa true) x;;

let rec rquot_empt m = replicate (size_list (fst m)) false;;

let rec rquot_memb x = (fun xa l -> nth l xa) x;;

let rec bdd_lookup
  x0 bs = match x0, bs with Leaf x, bs -> x
    | Brancha (l, r), b :: bs -> bdd_lookup (if b then r else l) bs;;

let rec rquot_succs
  m = (fun n x -> [bdd_lookup (nth (fst m) x) (replicate n false)]);;

let rec rquot_dfs
  m n x = gen_dfs (rquot_succs m n) rquot_ins rquot_memb (rquot_empt m) [x];;

let rec nfa_accepting
  x0 bs = match x0, bs with [], bs -> false
    | v :: va, [] -> false
    | a :: asa, b :: bs -> a && b || nfa_accepting asa bs;;

let rec rquot
  x = (fun (bd, asa) v ->
        (bd, map_index (fun _ n -> nfa_accepting asa (rquot_dfs (bd, asa) v n))
               asa (Big_int.big_int_of_int 0)))
        x;;

let rec set_iterator_emp c f sigma_0 = sigma_0;;

let rec set_iterator_sng
  x c f sigma_0 = (if c sigma_0 then f x sigma_0 else sigma_0);;

let rec rs_dlts_succ_it _A _B
  = (fun m1 v e ->
      (match rm_lookup _A v m1 with None -> set_iterator_emp
        | Some m2 ->
          (match rm_lookup _B e m2 with None -> set_iterator_emp
            | Some a -> set_iterator_sng a)));;

let rec rs_ts_C_it _A _B _C
  = (fun m1 a b ->
      (match rm_lookup _A a m1 with None -> (fun _ _ sigma_0 -> sigma_0)
        | Some m2 ->
          (match rm_lookup _B b m2 with None -> (fun _ _ sigma_0 -> sigma_0)
            | Some aa -> rs_iteratei _C aa)));;

let rec rs_lts_dlts_succ _A _B
  = (fun l q a ->
      (match l with Lts aa -> rs_ts_C_it _A _B _A aa
        | Dlts aa -> rs_dlts_succ_it _A _B aa)
        q
        a
        is_none
        (fun x _ -> Some x)
        None);;

let rec rs_nfa_accept_dfa _A
  = (fun (_, (_, (d, (i, (f, _))))) w ->
      rs_bexists linorder_nat i
        (fun q ->
          (match
            foldli w (fun q_opt -> not (is_none q_opt))
              (fun sigma q_opt ->
                rs_lts_dlts_succ linorder_nat _A d (the q_opt) sigma)
              (Some q)
            with None -> false | Some qa -> rs_memb linorder_nat qa f)));;

let rec rs_nfa_accept_nfa _A
  = (fun (_, (_, (d, (i, (f, _))))) w ->
      not (rr_disjoint linorder_nat
            (foldl
              (fun q a ->
                rs_iteratei linorder_nat q (fun _ -> true)
                  (fun qa ->
                    (match d
                      with Lts aa -> rs_ts_C_it linorder_nat _A linorder_nat aa
                      | Dlts aa -> rs_dlts_succ_it linorder_nat _A aa)
                      qa
                      a
                      (fun _ -> true)
                      (rs_ins linorder_nat))
                  (rs_empty linorder_nat ()))
              i w)
            f));;

let rec nfa_prop_is_complete_deterministic
  (Nfa_props_ext
    (nfa_prop_is_complete_deterministic, nfa_prop_is_initially_connected, more))
    = nfa_prop_is_complete_deterministic;;

let rec rs_nfa_accept _A
  a w = (if nfa_prop_is_complete_deterministic (rs_nfa_props _A a)
          then rs_nfa_accept_dfa _A a w else rs_nfa_accept_nfa _A a w);;

let rec lss_ins (_A1, _A2)
  x l = insertion_sort (_A1, _A2.order_linorder.preorder_order.ord_preorder) x
          l;;

let rec lss_sng x = [x];;

let rec make_bdd
  f n xs =
    (if Big_int.eq_big_int n (Big_int.big_int_of_int 0) then Leaf (f xs)
      else Brancha
             (make_bdd f (minus_nat n (Big_int.big_int_of_int 1))
                (xs @ [(Big_int.big_int_of_int 0)]),
               make_bdd f (minus_nat n (Big_int.big_int_of_int 1))
                 (xs @ [(Big_int.big_int_of_int 1)])));;

let rec dioph_ins
  m = (fun (is, js) ->
        (list_update is (int_encode m) (Some (size_list js)), js @ [m]));;

let rec dioph_empt
  ks l =
    (replicate
       (Big_int.max_big_int Big_int.zero_big_int
         (Big_int.add_big_int
           (Big_int.mult_big_int (Big_int.big_int_of_int 2)
             (max ord_int (abs_int l)
               (listsum monoid_add_int (map abs_int ks))))
           (Big_int.big_int_of_int 1)))
       None,
      []);;

let rec dioph_memb m = (fun (is, _) -> not (is_none (nth is (int_encode m))));;

let rec eval_dioph
  ks xs = match ks, xs with
    k :: ks, x :: xs ->
      Big_int.add_big_int (Big_int.mult_big_int k x) (eval_dioph ks xs)
    | [], xs -> (Big_int.big_int_of_int 0)
    | ks, [] -> (Big_int.big_int_of_int 0);;

let rec mk_nat_vecs
  n = (if Big_int.eq_big_int n (Big_int.big_int_of_int 0) then [[]]
        else let yss = mk_nat_vecs (minus_nat n (Big_int.big_int_of_int 1)) in
             map (fun a -> (Big_int.big_int_of_int 0) :: a) yss @
               map (fun a -> (Big_int.big_int_of_int 1) :: a) yss);;

let rec dioph_succs
  n ks m =
    map_filter
      (fun xs ->
        (if Big_int.eq_big_int
              (mod_int (eval_dioph ks xs) (Big_int.big_int_of_int 2))
              (mod_int m (Big_int.big_int_of_int 2))
          then Some (div_int (Big_int.sub_big_int m (eval_dioph ks xs))
                      (Big_int.big_int_of_int 2))
          else None))
      (mk_nat_vecs n);;

let rec dioph_dfs
  n ks l =
    gen_dfs (dioph_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l];;

let rec eq_dfa
  n ks l =
    let (is, js) = dioph_dfs n ks l in
    (map (fun j ->
           make_bdd
             (fun xs ->
               (if Big_int.eq_big_int
                     (mod_int (eval_dioph ks xs) (Big_int.big_int_of_int 2))
                     (mod_int j (Big_int.big_int_of_int 2))
                 then the (nth is
                            (int_encode
                              (div_int
                                (Big_int.sub_big_int j (eval_dioph ks xs))
                                (Big_int.big_int_of_int 2))))
                 else size_list js))
             n [])
       js @
       [Leaf (size_list js)],
      map (fun j -> Big_int.eq_big_int j (Big_int.big_int_of_int 0)) js @
        [false]);;

let rec prod_ins
  x = (fun (i, j) (tab, ps) ->
        (list_update tab i (list_update (nth tab i) j (Some (size_list ps))),
          ps @ [(i, j)]))
        x;;

let rec prod_empt
  a b = (replicate (size_list (fst a)) (replicate (size_list (fst b)) None),
          []);;

let rec prod_memb
  x = (fun (i, j) (tab, _) -> not (is_none (nth (nth tab i) j))) x;;

let rec bdd_binop
  f x1 x2 = match f, x1, x2 with f, Leaf x, Leaf y -> Leaf (f x y)
    | f, Brancha (l, r), Leaf y ->
        Brancha (bdd_binop f l (Leaf y), bdd_binop f r (Leaf y))
    | f, Leaf x, Brancha (l, r) ->
        Brancha (bdd_binop f (Leaf x) l, bdd_binop f (Leaf x) r)
    | f, Brancha (l_1, r_1), Brancha (l_2, r_2) ->
        Brancha (bdd_binop f l_1 l_2, bdd_binop f r_1 r_2);;

let rec add_leaves _A
  x0 xs = match x0, xs with Leaf x, xs -> inserta _A x xs
    | Brancha (b, c), xs -> add_leaves _A c (add_leaves _A b xs);;

let rec prod_succs
  a b = (fun (i, j) ->
          add_leaves (equal_prod equal_nat equal_nat)
            (bdd_binop (fun aa ba -> (aa, ba)) (nth (fst a) i) (nth (fst b) j))
            []);;

let rec prod_dfs
  a b x = gen_dfs (prod_succs a b) prod_ins prod_memb (prod_empt a b) [x];;

let rec binop_dfa
  f a b =
    let (tab, ps) =
      prod_dfs a b ((Big_int.big_int_of_int 0), (Big_int.big_int_of_int 0)) in
    (map (fun (i, j) ->
           bdd_binop (fun k l -> the (nth (nth tab k) l)) (nth (fst a) i)
             (nth (fst b) j))
       ps,
      map (fun (i, j) -> f (nth (snd a) i) (nth (snd b) j)) ps);;

let rec or_dfa x = binop_dfa (fun a b -> a || b) x;;

let rec rs_dlts_empty _A _B = rm_empty _A;;

let rec rs_hop_lts_add _A
  = (fun q a v l ->
      (match rm_lookup _A a l
        with None -> rm_update _A a (iam_sng q (lss_sng v)) l
        | Some m2 ->
          (match iam_lookup q m2
            with None -> rm_update _A a (iam_update q (lss_sng v) m2) l
            | Some s3 ->
              rm_update _A a
                (iam_update q (lss_ins (equal_nat, linorder_nat) v s3) m2)
                l)));;

let rec rs_ts_it _A _B _C
  = (fun m1 c f ->
      rm_iteratei _A m1 c
        (fun (a, m2) ->
          rm_iteratei _B m2 c
            (fun (b, s3) -> rs_iteratei _C s3 c (fun ca -> f (a, (b, ca))))));;

let rec ltsbc_emp_lts l_emp = (fun _ -> Lts (l_emp ()));;

let rec rs_ts_empty _A _B _C = rm_empty _A;;

let rec rs_lts_dlts_empty_lts _A _B _C = ltsbc_emp_lts (rs_ts_empty _A _B _C);;

let rec rs_ts_add _A _B _C
  = (fun v w va l ->
      (match rm_lookup _A v l
        with None -> rm_update _A v (rm_sng _B w (rs_sng _C va)) l
        | Some m2 ->
          (match rm_lookup _B w m2
            with None -> rm_update _A v (rm_update _B w (rs_sng _C va) m2) l
            | Some s3 ->
              rm_update _A v (rm_update _B w (rs_ins _C va s3) m2) l)));;

let rec ltsbc_add_simple
  l_add copy qa a q x5 = match l_add, copy, qa, a, q, x5 with
    l_add, copy, qa, a, q, Lts l -> Lts (l_add qa a q l)
    | l_add, copy, qa, a, q, Dlts d -> Lts (l_add qa a q (copy d));;

let rec rs_dlts_lts_copy _A _B
  = ltsga_copy (rs_dlts_it _A _B) (rs_ts_empty _A _B _A) (rs_ts_add _A _B _A);;

let rec rs_lts_dlts_add_simple _A _B
  = ltsbc_add_simple (rs_ts_add _A _B _A) (rs_dlts_lts_copy _A _B);;

let rec rs_lts_dlts_reverse _A _B
  = (fun l ->
      (match l with Lts a -> rs_ts_it _A _B _A a | Dlts a -> rs_dlts_it _A _B a)
        (fun _ -> true)
        (fun (v, (e, va)) -> rs_lts_dlts_add_simple _A _B va e v)
        (rs_lts_dlts_empty_lts _A _B _A ()));;

let rec rs_nfa_reverse _A
  = (fun (q, (a, (d, (i, (f, _))))) ->
      (q, (a, (rs_lts_dlts_reverse linorder_nat _A d,
                (f, (i, fields false false))))));;

let rec iterate_size
  it = it (fun _ -> true) (fun _ -> suc) (Big_int.big_int_of_int 0);;

let rec accepts tr p s asa = p (foldl tr s asa);;

let rec and_dfa x = binop_dfa (fun a b -> a && b) x;;

let rec bdd_map
  f x1 = match f, x1 with f, Leaf a -> Leaf (f a)
    | f, Brancha (l, r) -> Brancha (bdd_map f l, bdd_map f r);;

let rec subsetbdd
  x0 x1 bdd = match x0, x1, bdd with [], [], bdd -> bdd
    | bdda :: bdds, b :: bs, bdd ->
        (if b then subsetbdd bdds bs (bdd_binop bv_or bdd bdda)
          else subsetbdd bdds bs bdd);;

let rec bddinsert
  xa0 xa1 x = match xa0, xa1, x with Leaf a, [], x -> Leaf x
    | Leaf a, w :: ws, x ->
        (if w then Brancha (Leaf a, bddinsert (Leaf a) ws x)
          else Brancha (bddinsert (Leaf a) ws x, Leaf a))
    | Brancha (l, r), w :: ws, x ->
        (if w then Brancha (l, bddinsert r ws x)
          else Brancha (bddinsert l ws x, r));;

let rec subset_ins
  qs = (fun (bdd, qss) ->
         (bddinsert bdd qs (Some (size_list qss)), qss @ [qs]));;

let subset_empt : (Big_int.big_int option) bdd * (bool list) list
  = (Leaf None, []);;

let rec subset_memb qs = (fun (bdd, _) -> not (is_none (bdd_lookup bdd qs)));;

let rec nfa_emptybdd n = Leaf (replicate n false);;

let rec subset_succs
  a qs =
    add_leaves (equal_list equal_bool)
      (subsetbdd (fst a) qs (nfa_emptybdd (size_list qs))) [];;

let rec subset_dfs
  a x = gen_dfs (subset_succs a) subset_ins subset_memb subset_empt [x];;

let rec nfa_startnode
  a = list_update (replicate (size_list (fst a)) false)
        (Big_int.big_int_of_int 0) true;;

let rec nfa_acceptinga a = nfa_accepting (snd a);;

let rec det_nfa
  a = let (bdd, qss) = subset_dfs a (nfa_startnode a) in
      (map (fun qs ->
             bdd_map (fun qsa -> the (bdd_lookup bdd qsa))
               (subsetbdd (fst a) qs (nfa_emptybdd (size_list qs))))
         qss,
        map (nfa_acceptinga a) qss);;

let rec imp_dfa x = binop_dfa (fun a b -> (if a then b else true)) x;;

let rec make_tr
  f n i =
    (if Big_int.eq_big_int n (Big_int.big_int_of_int 0) then []
      else f i :: make_tr f (minus_nat n (Big_int.big_int_of_int 1)) (suc i));;

let rec init_tr
  x = (fun (bd, asa) ->
        make_tr
          (fun i ->
            make_tr (fun j -> not (equal_boola (nth asa i) (nth asa j))) i
              (Big_int.big_int_of_int 0))
          (minus_nat (size_list bd) (Big_int.big_int_of_int 1))
          (Big_int.big_int_of_int 1))
        x;;

let rec mk_eqcla
  x0 i j l t = match x0, i, j, l, t with [], i, j, l, t -> []
    | x :: xs, i, j, l, t ->
        (if tr_lookup t j i || not (is_none x) then x else Some l) ::
          mk_eqcla xs i (suc j) l t;;

let rec mk_eqcl
  x0 zs i t = match x0, zs, i, t with [], zs, i, t -> ([], zs)
    | None :: xs, zs, i, t ->
        let (xsa, a) =
          mk_eqcl (mk_eqcla xs i (suc i) (size_list zs) t) (zs @ [i]) (suc i) t
          in
        (size_list zs :: xsa, a)
    | Some l :: xs, zs, i, t ->
        let (xsa, a) = mk_eqcl xs zs (suc i) t in
        (l :: xsa, a);;

let rec min_dfa
  x = (fun (bd, asa) ->
        let (os, ns) =
          mk_eqcl (replicate (size_list bd) None) [] (Big_int.big_int_of_int 0)
            (fixpt (bd, asa) (init_tr (bd, asa)))
          in
        (map (fun p -> bdd_map (nth os) (nth bd p)) ns, map (nth asa) ns))
        x;;

let rec rs_hop_lts_copy x = id x;;

let rec lss_iteratei l = foldli l;;

let rec lss_empty x = (fun _ -> []) x;;

let rec lss_union_list (_A1, _A2) l = merge_list (_A1, _A2) [] l;;

let rec rs_hop_lts_get_succs _A
  = (fun l vs a ->
      (match rm_lookup _A a l with None -> lss_empty ()
        | Some im ->
          lss_union_list (equal_nat, linorder_nat)
            (map_filter (fun q -> iam_lookup q im) vs)));;

let rec states_enumerate_nat q = q;;

let rec l_insert_impl
  i l x2 = match i, l, x2 with i, l, [] -> l
    | i, l, a :: asa -> l_insert_impl i ((a, i) :: l) asa;;

let rec sm_update
  pim_ops sm_ops n sm pim p v =
    (if Big_int.eq_big_int v (Big_int.big_int_of_int 0) then sm
      else let q = the (map_op_lookup pim_ops p pim) in
           let sma = map_op_update sm_ops q n sm in
           sm_update pim_ops sm_ops n sma pim (suc p)
             (minus_nat (suc (minus_nat v (Big_int.big_int_of_int 1)))
               (Big_int.big_int_of_int 1)));;

let rec hopcroft_code_step_compute_iM_swap_check
  im_ops sm_ops pm_ops pim_ops iM_ops pre_it cm pre =
    (fun (im, (sm, _)) ->
      pre_it pre (fun _ -> true)
        (fun q (iM, (pm, pim)) ->
          let i = the (map_op_lookup sm_ops q sm) in
          let s =
            (match map_op_lookup iM_ops i iM
              with None -> let (l, _) = the (map_op_lookup im_ops i im) in
                           l
              | Some s -> s)
            in
          let iq = the (map_op_lookup pm_ops q pm) in
          let iMa = map_op_update iM_ops i (suc s) iM in
          (if Big_int.eq_big_int iq s then (iMa, (pm, pim))
            else let qs = the (map_op_lookup pim_ops s pim) in
                 let pima =
                   map_op_update pm_ops qs iq (map_op_update pm_ops q s pm) in
                 let pma =
                   map_op_update pim_ops iq qs (map_op_update pim_ops s q pim)
                   in
                 (iMa, (pima, pma))))
        (map_op_empty iM_ops (), cm));;

let rec hopcroft_code_step
  iM_it pre_it iM_ops pim_ops pm_ops sm_ops im_ops aL pre p l cm =
    let (iM, cma) =
      hopcroft_code_step_compute_iM_swap_check im_ops sm_ops pm_ops pim_ops
        iM_ops pre_it cm pre p
      in
    let (pa, la) =
      iM_it iM (fun _ -> true)
        (fun (pa, s) (a, b) ->
          let (im, (sm, n)) = a in
          (fun la ->
            let (pt, (pct, (pf, pcf))) =
              let (lb, u) = the (map_op_lookup im_ops pa im) in
              ((lb, minus_nat s (Big_int.big_int_of_int 1)),
                (minus_nat s lb, ((s, u), minus_nat (suc u) s)))
              in
            (if Big_int.eq_big_int pcf (Big_int.big_int_of_int 0)
              then ((im, (sm, n)), la)
              else let (pmin, pmax) =
                     (if Big_int.lt_big_int pcf pct then (pf, pt) else (pt, pf))
                     in
                   let lb = l_insert_impl n la aL in
                   let pb =
                     (map_op_update im_ops n pmin
                        (map_op_update im_ops pa pmax im),
                       (sm_update pim_ops sm_ops n sm (snd cma) (fst pmin)
                          (minus_nat (suc (snd pmin)) (fst pmin)),
                         suc n))
                     in
                   (pb, lb)))
            b)
        (p, l)
      in
    ((pa, la), cma);;

let rec class_map_init_pred_code _F
  cm_it pm_ops pim_ops qf f =
    let cm0 = (map_op_empty pm_ops (), map_op_empty pim_ops ()) in
    let (cm1, s) =
      cm_it qf (fun _ -> true)
        (fun q (a, b) ->
          let (pm, pim) = a in
          (fun i ->
            ((map_op_update pm_ops q i pm, map_op_update pim_ops i q pim),
              suc i))
            b)
        (cm0, zero _F)
      in
    let (cm2, m) =
      cm_it f (fun _ -> true)
        (fun q (a, b) ->
          let (pm, pim) = a in
          (fun i ->
            ((map_op_update pm_ops q i pm, map_op_update pim_ops i q pim),
              suc i))
            b)
        (cm1, s)
      in
    (cm2, (s, m));;

let rec hopcroft_code
  iM_ops pre_it iM_it sm_it sm_ops im_ops pim_ops pm_ops cm_it s_ops q f al
    pre_fun =
    let x = set_op_diff s_ops q f in
    let (a, (aa, ba)) =
      class_map_init_pred_code zero_nat cm_it pm_ops pim_ops x f in
    (if Big_int.eq_big_int ba (Big_int.big_int_of_int 0)
      then ((map_op_empty im_ops (),
              (map_op_empty sm_ops (), (Big_int.big_int_of_int 0))),
             a)
      else (if Big_int.eq_big_int ba aa
             then ((map_op_sng im_ops (Big_int.big_int_of_int 0)
                      ((Big_int.big_int_of_int 0),
                        minus_nat ba (Big_int.big_int_of_int 1)),
                     (sm_it q (fun _ -> true)
                        (fun qa ->
                          map_op_update sm_ops qa (Big_int.big_int_of_int 0))
                        (map_op_empty sm_ops ()),
                       (Big_int.big_int_of_int 1))),
                    a)
             else let ((ac, _), bb) =
                    whilea (fun pl -> not (null (snd (fst pl))))
                      (fun ((ac, bc), (ad, bd)) ->
                        let (ae, be) = hd bc in
                        let xd =
                          pre_fun ae bd (the (map_op_lookup im_ops be (fst ac)))
                          in
                        let (ab, b) =
                          hopcroft_code_step iM_it pre_it iM_ops pim_ops pm_ops
                            sm_ops im_ops al xd ac (tl bc) (ad, bd)
                          in
                        (ab, b))
                      (((if Big_int.eq_big_int aa (Big_int.big_int_of_int 0)
                          then (map_op_sng im_ops (Big_int.big_int_of_int 0)
                                  ((Big_int.big_int_of_int 0),
                                    minus_nat ba (Big_int.big_int_of_int 1)),
                                 (sm_it q (fun _ -> true)
                                    (fun qa ->
                                      map_op_update sm_ops qa
(Big_int.big_int_of_int 0))
                                    (map_op_empty sm_ops ()),
                                   (Big_int.big_int_of_int 1)))
                          else (map_op_update im_ops
                                  (suc (Big_int.big_int_of_int 0))
                                  ((Big_int.big_int_of_int 0),
                                    minus_nat aa (Big_int.big_int_of_int 1))
                                  (map_op_sng im_ops (Big_int.big_int_of_int 0)
                                    (aa, minus_nat ba
   (Big_int.big_int_of_int 1))),
                                 (sm_it f (fun _ -> true)
                                    (fun qa ->
                                      map_op_update sm_ops qa
(Big_int.big_int_of_int 0))
                                    (sm_it x (fun _ -> true)
                                       (fun qa ->
 map_op_update sm_ops qa (Big_int.big_int_of_int 1))
                                      (map_op_empty sm_ops ())),
                                   (Big_int.big_int_of_int 2)))),
                         l_insert_impl (Big_int.big_int_of_int 0) [] al),
                        a)
                    in
                  (ac, bb)));;

let rec nfa_prop_is_initially_connected
  (Nfa_props_ext
    (nfa_prop_is_complete_deterministic, nfa_prop_is_initially_connected, more))
    = nfa_prop_is_initially_connected;;

let rec rs_lts_dlts_add_dlts _A _B
  = dltsbc_add (rs_ts_add _A _B _A) (rs_dlts_add _A _B);;

let rec ltsbc_filter_it
  l_it d_it p_qa p_a p_q p x6 = match l_it, d_it, p_qa, p_a, p_q, p, x6 with
    l_it, d_it, p_qa, p_a, p_q, p, Lts l -> l_it p_qa p_a p_q p l
    | l_it, d_it, p_qa, p_a, p_q, p, Dlts d -> d_it p_qa p_a p_q p d;;

let rec rs_dlts_filter_it _A _B
  = (fun p_v1 p_e p_v2 p m1 c f ->
      rm_iteratei _A m1 c
        (fun (v1, m2) sigma ->
          (if p_v1 v1
            then rm_iteratei _B m2 c
                   (fun (e, v2) sigmaa ->
                     (if p_v2 v2 && (p_e e && p (v1, (e, v2)))
                       then f (v1, (e, v2)) sigmaa else sigmaa))
                   sigma
            else sigma)));;

let rec rs_ts_filter_it _A _B _C
  = (fun p_a p_b p_c p m1 c f ->
      rm_iteratei _A m1 c
        (fun (a, m2) sigma ->
          (if p_a a
            then rm_iteratei _B m2 c
                   (fun (b, s3) sigmaa ->
                     (if p_b b
                       then rs_iteratei _C s3 c
                              (fun ca sigmab ->
                                (if p_c ca && p (a, (b, ca))
                                  then f (a, (b, ca)) sigmab else sigmab))
                              sigmaa
                       else sigmaa))
                   sigma
            else sigma)));;

let rec rs_lts_dlts_filter_it _A _B
  = ltsbc_filter_it (rs_ts_filter_it _A _B _A) (rs_dlts_filter_it _A _B);;

let rec ltsbc_emp_dlts d_emp = (fun _ -> Dlts (d_emp ()));;

let rec rs_lts_dlts_empty_dlts _B _C = ltsbc_emp_dlts (rs_dlts_empty _B _C);;

let rec rs_lts_dlts_image_filter_dlts _A _B _C _D
  = (fun f p_v1 p_e p_v2 p l ->
      rs_lts_dlts_filter_it _A _B p_v1 p_e p_v2 p l (fun _ -> true)
        (fun vev la ->
          let (v, (e, va)) = f vev in
          rs_lts_dlts_add_dlts _C _D v e va la)
        (rs_lts_dlts_empty_dlts _C _D ()));;

let rec rs_lts_dlts_image_dlts _A _B _C _D
  = (fun f ->
      rs_lts_dlts_image_filter_dlts _A _B _C _D f (fun _ -> true)
        (fun _ -> true) (fun _ -> true) (fun _ -> true));;

let rec rs_nfa_rename_states_dfa _A
  (q, (a, (d, (i, (fa, p))))) f =
    (rs_image linorder_nat linorder_nat f q,
      (a, (rs_lts_dlts_image_dlts linorder_nat _A linorder_nat _A
             (fun (qb, (aa, qa)) -> (f qb, (aa, f qa))) d,
            (rs_image linorder_nat linorder_nat f i,
              (rs_image linorder_nat linorder_nat f fa,
                fields true (nfa_prop_is_initially_connected p))))));;

let rec hopcroft_class_map_alpha_impl
  pim l u =
    (if Big_int.le_big_int l u
      then the (pim l) :: hopcroft_class_map_alpha_impl pim (suc l) u else []);;

let rec rs_nfa_Hopcroft _A
  (q, (a, (d, (i, (f, p))))) =
    let al = rs_to_list _A a in
    let rv_D =
      rs_hop_lts_copy
        (ltsga_reverse (rm_empty _A) (rs_hop_lts_add _A)
          (fun aa ->
            (match aa with Lts ab -> rs_ts_it linorder_nat _A linorder_nat ab
              | Dlts ab -> rs_dlts_it linorder_nat _A ab))
          d)
      in
    let pre_fun =
      (fun aa pim (l, u) ->
        rs_hop_lts_get_succs _A rv_D
          (hopcroft_class_map_alpha_impl (fun ia -> iam_lookup ia pim) l u) aa)
      in
    let (b, c) =
      hopcroft_code (rm_ops (equal_nat, linorder_nat) equal_nat) lss_iteratei
        (rm_iteratei linorder_nat) (rs_iteratei linorder_nat) iam_ops iam_ops
        iam_ops iam_ops (rs_iteratei linorder_nat)
        (rs_ops (equal_nat, linorder_nat)) q f al pre_fun
      in
    let (_, (sm, _)) = b in
    (fun _ ->
      rs_nfa_rename_states_dfa _A (q, (a, (d, (i, (f, p)))))
        (fun qa -> states_enumerate_nat (the (iam_lookup qa sm))))
      c;;

let rec ltsga_list_to_collect_list _A _C
  = function [] -> []
    | (va, (e, v)) :: l ->
        let (yes, no) =
          partition (fun vev -> eq _A (fst vev) va && eq _C (snd (snd vev)) v) l
          in
        (va, (e :: map (comp fst snd) yes, v)) ::
          ltsga_list_to_collect_list _A _C no;;

let rec rs_lts_dlts_to_list _A _B
  = (fun x ->
      (match x with Lts a -> rs_ts_it _A _B _A a | Dlts a -> rs_dlts_it _A _B a)
        (fun _ -> true)
        (fun a b -> a :: b)
        []);;

let rec rs_lts_dlts_to_collect_list (_A1, _A2) _B
  = (fun l ->
      ltsga_list_to_collect_list _A1 _A1 (rs_lts_dlts_to_list _A2 _B l));;

let rec rs_nfa_destruct _A
  (q, (a, (d, (i, (f, p))))) =
    (rs_to_list linorder_nat q,
      (rs_to_list _A a,
        (rs_lts_dlts_to_collect_list (equal_nat, linorder_nat) _A d,
          (rs_to_list linorder_nat i, rs_to_list linorder_nat f))));;

let rec rs_nfa_final_no _A (q, (a, (d, (i, (f, p))))) = rs_size linorder_nat f;;

let rec rs_nfa_trans_no _A
  (q, (a, (d, (i, (f, p))))) =
    iterate_size
      (match d with Lts aa -> rs_ts_it linorder_nat _A linorder_nat aa
        | Dlts aa -> rs_dlts_it linorder_nat _A aa);;

let rec lexord_lexord_less (_A1, _A2)
  x0 x1 = match x0, x1 with
    x :: xs, y :: ys ->
      (if less _A2.order_linorder.preorder_order.ord_preorder x y then true
        else (if eq _A1 x y then lexord_lexord_less (_A1, _A2) xs ys
               else false))
    | x :: xs, [] -> false
    | [], y :: ys -> true
    | [], [] -> false;;

let rec less_list (_A1, _A2) l1 l2 = lexord_lexord_less (_A1, _A2) l1 l2;;

let rec lexord_lexord_less_eq (_A1, _A2)
  x0 x1 = match x0, x1 with
    x :: xs, y :: ys ->
      (if less _A2.order_linorder.preorder_order.ord_preorder x y then true
        else (if eq _A1 x y then lexord_lexord_less_eq (_A1, _A2) xs ys
               else false))
    | x :: xs, [] -> false
    | [], y :: ys -> true
    | [], [] -> true;;

let rec less_eq_list (_A1, _A2) l1 l2 = lexord_lexord_less_eq (_A1, _A2) l1 l2;;

let rec ord_list (_A1, _A2) =
  ({less_eq = less_eq_list (_A1, _A2); less = less_list (_A1, _A2)} :
    ('a list) ord);;

let rec dioph_ineq_succs
  n ks m =
    map (fun xs ->
          div_int (Big_int.sub_big_int m (eval_dioph ks xs))
            (Big_int.big_int_of_int 2))
      (mk_nat_vecs n);;

let rec dioph_ineq_dfs
  n ks l =
    gen_dfs (dioph_ineq_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l];;

let rec ineq_dfa
  n ks l =
    let (is, js) = dioph_ineq_dfs n ks l in
    (map (fun j ->
           make_bdd
             (fun xs ->
               the (nth is
                     (int_encode
                       (div_int (Big_int.sub_big_int j (eval_dioph ks xs))
                         (Big_int.big_int_of_int 2)))))
             n [])
       js,
      map (Big_int.le_big_int (Big_int.big_int_of_int 0)) js);;

let rec rs_nfa_construct_gen _A
  p (ql, (al, (dl, (il, fl)))) =
    foldl (fun (q, (a, (d, (i, (f, props))))) (q1, (l, q2)) ->
            (rs_ins linorder_nat q1 (rs_ins linorder_nat q2 q),
              (foldl (fun s x -> rs_ins _A x s) a l,
                (foldl (fun da aa ->
                         rs_lts_dlts_add_simple linorder_nat _A q1 aa q2 da)
                   d l,
                  (i, (f, props))))))
      (list_to_rs linorder_nat (ql @ il @ fl),
        (list_to_rs _A al,
          (rs_lts_dlts_empty_dlts linorder_nat _A (),
            (list_to_rs linorder_nat il, (list_to_rs linorder_nat fl, p)))))
      dl;;

let rec rs_dfa_construct _A = rs_nfa_construct_gen _A (fields true false);;

let rec rs_ts_BC_it _A _B _C
  = (fun m1 a ->
      (match rm_lookup _A a m1 with None -> (fun _ _ sigma_0 -> sigma_0)
        | Some m2 ->
          (fun c f ->
            rm_iteratei _B m2 c
              (fun (b, s3) -> rs_iteratei _C s3 c (fun ca -> f (b, ca))))));;

let rec rs_dlts_succ_label_it _A _B
  = (fun m1 v ->
      (match rm_lookup _A v m1 with None -> (fun _ _ sigma_0 -> sigma_0)
        | Some a -> rm_iteratei _B a));;

let rec rs_lts_dlts_add_choice _A _B
  b = (if b then rs_lts_dlts_add_dlts _A _B else rs_lts_dlts_add_simple _A _B);;

let rec rs_nfa_dfa_construct_reachable _B _C
  det ff i a fp d_it =
    let (b, c) =
      foldl (fun (aa, b) ->
              let (qm, n) = aa in
              (fun is q ->
                ((rm_update_dj _B (ff q) (states_enumerate_nat n) qm, suc n),
                  rs_ins_dj linorder_nat (states_enumerate_nat n) is))
                b)
        ((rm_empty _B (), (Big_int.big_int_of_int 0)), rs_empty linorder_nat ())
        i
      in
    let (qm, n) = b in
    (fun is ->
      let (aa, ba) =
        worklist (fun _ -> true)
          (fun (aa, ba) ->
            let (qma, na) = aa in
            (fun (qs, (asa, (dd, (isa, (fs, p))))) q ->
              let r = the (rm_lookup _B (ff q) qma) in
              (if rs_memb linorder_nat r qs
                then (((qma, na), (qs, (asa, (dd, (isa, (fs, p)))))), [])
                else let (ab, bb) =
                       d_it q (fun _ -> true)
                         (fun (ab, qa) (bb, ca) ->
                           let (qmb, nb) = bb in
                           (fun (dda, naa) ->
                             let r_opt = rm_lookup _B (ff qa) qmb in
                             let (bc, cb) =
                               (if is_none r_opt
                                 then let ra = states_enumerate_nat nb in
                                      ((rm_update_dj _B (ff qa) ra qmb, suc nb),
ra)
                                 else ((qmb, nb), the r_opt))
                               in
                             let (qmc, nc) = bc in
                             (fun ra ->
                               ((qmc, nc),
                                 (rs_lts_dlts_add_choice linorder_nat _C det r
                                    ab ra dda,
                                   qa :: naa)))
                               cb)
                             ca)
                         ((qma, na), (dd, []))
                       in
                     let (qmb, nb) = ab in
                     (fun (dda, ac) ->
                       (((qmb, nb),
                          (rs_ins_dj linorder_nat r qs,
                            (asa, (dda, (isa,
  ((if fp q then rs_ins_dj linorder_nat r fs else fs), p)))))),
                         ac))
                       bb))
              ba)
          (((qm, n),
             (rs_empty linorder_nat (),
               (a, (rs_lts_dlts_empty_dlts linorder_nat _C (),
                     (is, (rs_empty linorder_nat (), fields det true)))))),
            i)
        in
      let (_, aaa) = aa in
      (fun _ -> aaa)
        ba)
      c;;

let rec rs_nfa_bool_comb_gen _A
  a bc (q1, (a1, (d1, (i1, (f1, p1))))) (q2, (a2, (d2, (i2, (f2, p2))))) =
    rs_nfa_dfa_construct_reachable
      (linorder_prod (equal_nat, linorder_nat) (equal_nat, linorder_nat)) _A
      (nfa_prop_is_complete_deterministic p1 &&
        nfa_prop_is_complete_deterministic p2)
      rs_hop_lts_copy
      (product (rs_to_list linorder_nat i1) (rs_to_list linorder_nat i2)) a
      (fun (q1a, q2a) ->
        bc (rs_memb linorder_nat q1a f1) (rs_memb linorder_nat q2a f2))
      (fun (q1a, q2a) c f ->
        (match d1 with Lts aa -> rs_ts_BC_it linorder_nat _A linorder_nat aa
          | Dlts aa -> rs_dlts_succ_label_it linorder_nat _A aa)
          q1a
          c
          (fun (aa, q1b) ->
            (match d2 with Lts ab -> rs_ts_C_it linorder_nat _A linorder_nat ab
              | Dlts ab -> rs_dlts_succ_it linorder_nat _A ab)
              q2a
              aa
              c
              (fun q2b -> f (aa, (q1b, q2b)))));;

let rec rs_nfa_bool_comb _A
  bc (q1, (a1, (d1, (i1, (f1, p1))))) (q2, (a2, (d2, (i2, (f2, p2))))) =
    rs_nfa_bool_comb_gen _A a1 bc (q1, (a1, (d1, (i1, (f1, p1)))))
      (q2, (a2, (d2, (i2, (f2, p2)))));;

let rec rs_nfa_construct _A = rs_nfa_construct_gen _A (fields false false);;

let rec rs_nfa_labels_no _A (q, (a, (d, (i, (f, p))))) = rs_size _A a;;

let rec rs_nfa_normalise _A
  = (fun (q, (a, (d, (i, (f, p))))) ->
      (if nfa_prop_is_initially_connected p then (q, (a, (d, (i, (f, p)))))
        else rs_nfa_dfa_construct_reachable linorder_nat _A
               (nfa_prop_is_complete_deterministic p) rs_hop_lts_copy
               (rs_to_list linorder_nat i) a
               (fun qa -> rs_memb linorder_nat qa f)
               (match d
                 with Lts aa -> rs_ts_BC_it linorder_nat _A linorder_nat aa
                 | Dlts aa -> rs_dlts_succ_label_it linorder_nat _A aa)));;

let rec rs_nfa_states_no _A
  (q, (a, (d, (i, (f, p))))) = rs_size linorder_nat q;;

let rec negate_dfa x = (fun (t, a) -> (t, map not a)) x;;

let rec nfa_of_dfa
  x = (fun (bdd, a) ->
        (map (bdd_map
               (fun q -> list_update (replicate (size_list bdd) false) q true))
           bdd,
          a))
        x;;

let rec quantify_bdd
  i x1 = match i, x1 with i, Leaf q -> Leaf q
    | i, Brancha (l, r) ->
        (if Big_int.eq_big_int i (Big_int.big_int_of_int 0)
          then bdd_binop bv_or l r
          else Brancha
                 (quantify_bdd (minus_nat i (Big_int.big_int_of_int 1)) l,
                   quantify_bdd (minus_nat i (Big_int.big_int_of_int 1)) r));;

let rec quantify_nfa i = (fun (bdds, a) -> (map (quantify_bdd i) bdds, a));;

let rec dfa_of_pf
  n x1 = match n, x1 with n, Eq (ks, l) -> eq_dfa n ks l
    | n, Le (ks, l) -> ineq_dfa n ks l
    | n, And (p, q) -> and_dfa (dfa_of_pf n p) (dfa_of_pf n q)
    | n, Or (p, q) -> or_dfa (dfa_of_pf n p) (dfa_of_pf n q)
    | n, Imp (p, q) -> imp_dfa (dfa_of_pf n p) (dfa_of_pf n q)
    | n, Exist p ->
        min_dfa
          (rquot
            (det_nfa
              (quantify_nfa (Big_int.big_int_of_int 0)
                (nfa_of_dfa (dfa_of_pf (suc n) p))))
            n)
    | n, Forall p -> dfa_of_pf n (Neg (Exist (Neg p)))
    | n, Neg p -> negate_dfa (dfa_of_pf n p);;

let rec dfa_trans a q bs = bdd_lookup (nth (fst a) q) bs;;

let rec rs_dfa_construct_reachable _B _C
  = rs_nfa_dfa_construct_reachable _B _C true;;

let rec rs_nfa_determinise _A
  (q1, (a1, (d1, (i1, (f1, p1))))) =
    (if nfa_prop_is_initially_connected p1 &&
          nfa_prop_is_complete_deterministic p1
      then (q1, (a1, (d1, (i1, (f1, p1)))))
      else let re_map =
             fst (rs_iteratei linorder_nat q1 (fun _ -> true)
                   (fun q (m, n) ->
                     (rm_update_dj linorder_nat q n m,
                       Big_int.mult_big_int (Big_int.big_int_of_int 2) n))
                   (rm_empty linorder_nat (), (Big_int.big_int_of_int 1)))
             in
           rs_dfa_construct_reachable linorder_nat _A
             (fun q ->
               rs_iteratei linorder_nat q (fun _ -> true)
                 (fun qa n ->
                   Big_int.add_big_int n
                     (the (rm_lookup linorder_nat qa re_map)))
                 (Big_int.big_int_of_int 0))
             [i1] a1 (fun q -> not (rr_disjoint linorder_nat q f1))
             (fun s c f ->
               rs_iteratei _A a1 c
                 (fun x ->
                   f (x, rs_iteratei linorder_nat s (fun _ -> true)
                           (fun a ->
                             (match d1
                               with Lts aa ->
                                 rs_ts_C_it linorder_nat _A linorder_nat aa
                               | Dlts aa -> rs_dlts_succ_it linorder_nat _A aa)
                               a
                               x
                               (fun _ -> true)
                               (rs_ins linorder_nat))
                           (rs_empty linorder_nat ())))));;

let rec rs_nfa_Brzozowski _A
  a = rs_nfa_determinise _A
        (rs_nfa_reverse _A (rs_nfa_determinise _A (rs_nfa_reverse _A a)));;

let rec rs_nfa_complement _A
  = (fun (q, (a, (d, (i, (f, p))))) ->
      (q, (a, (d, (i, (rr_diff linorder_nat q f, p))))));;

let rec rs_nfa_initial_no _A
  (q, (a, (d, (i, (f, p))))) = rs_size linorder_nat i;;

let rec preorder_list (_A1, _A2) =
  ({ord_preorder = (ord_list (_A1, _A2))} : ('a list) preorder);;

let rec order_list (_A1, _A2) =
  ({preorder_order = (preorder_list (_A1, _A2))} : ('a list) order);;

type pres_NFA_state = Pres_NFA_state_error |
  Pres_NFA_state_int of Big_int.big_int;;

let linorder_bool = ({order_linorder = order_bool} : bool linorder);;

let rec linorder_list (_A1, _A2) =
  ({order_linorder = (order_list (_A1, _A2))} : ('a list) linorder);;

let rec rs_nfa_Hopcroft_NFA _A
  = (fun a -> rs_nfa_Hopcroft _A (rs_nfa_determinise _A a));;

let rec pres_NFA_state_to_nat
  = function Pres_NFA_state_error -> (Big_int.big_int_of_int 0)
    | Pres_NFA_state_int m ->
        Big_int.add_big_int (int_encode m) (Big_int.big_int_of_int 1);;

let rec rs_dfa_construct_reachable_fun _B _C
  ff i a fp d_fun =
    rs_dfa_construct_reachable _B _C ff [i] a fp
      (fun q c f -> rs_iteratei _C a c (fun x -> f (x, d_fun q x)));;

let rec nat_of_bool
  = function false -> (Big_int.big_int_of_int 0)
    | true -> (Big_int.big_int_of_int 1);;

let rec pres_DFA_eq_ineq_trans_fun
  ineq ks x2 uu = match ineq, ks, x2, uu with
    ineq, ks, Pres_NFA_state_error, uu -> Pres_NFA_state_error
    | ineq, ks, Pres_NFA_state_int j, bs ->
        (if ineq ||
              Big_int.eq_big_int
                (mod_int (eval_dioph ks (map nat_of_bool bs))
                  (Big_int.big_int_of_int 2))
                (mod_int j (Big_int.big_int_of_int 2))
          then Pres_NFA_state_int
                 (div_int
                   (Big_int.sub_big_int j (eval_dioph ks (map nat_of_bool bs)))
                   (Big_int.big_int_of_int 2))
          else Pres_NFA_state_error);;

let rec rs_DFA_eq_ineq
  a ineq n ks l =
    rs_dfa_construct_reachable_fun linorder_nat
      (linorder_list (equal_bool, linorder_bool)) pres_NFA_state_to_nat
      (Pres_NFA_state_int l) a
      (if ineq
        then (fun aa ->
               (match aa with Pres_NFA_state_error -> false
                 | Pres_NFA_state_int ab ->
                   Big_int.le_big_int (Big_int.big_int_of_int 0) ab))
        else (fun aa ->
               (match aa with Pres_NFA_state_error -> false
                 | Pres_NFA_state_int m ->
                   Big_int.eq_big_int m (Big_int.big_int_of_int 0))))
      (pres_DFA_eq_ineq_trans_fun ineq ks);;

let rec rs_cache_alpha
  m n = (if Big_int.eq_big_int n (Big_int.big_int_of_int 0)
          then (m, rs_sng (linorder_list (equal_bool, linorder_bool)) [])
          else (match
                 rm_lookup linorder_nat
                   (suc (minus_nat n (Big_int.big_int_of_int 1))) m
                 with None ->
                   let (ma, bl) =
                     rs_cache_alpha m (minus_nat n (Big_int.big_int_of_int 1))
                     in
                   let bla =
                     rs_union (linorder_list (equal_bool, linorder_bool))
                       (rs_image (linorder_list (equal_bool, linorder_bool))
                         (linorder_list (equal_bool, linorder_bool))
                         (fun a -> true :: a) bl)
                       (rs_image (linorder_list (equal_bool, linorder_bool))
                         (linorder_list (equal_bool, linorder_bool))
                         (fun a -> false :: a) bl)
                     in
                   let mb =
                     rm_update linorder_nat
                       (suc (minus_nat n (Big_int.big_int_of_int 1))) bla ma
                     in
                   (mb, bla)
                 | Some a -> (m, a)));;

let rec rs_lts_dlts_image_filter _A _B _C _D
  = (fun f p_v1 p_e p_v2 p l ->
      rs_lts_dlts_filter_it _A _B p_v1 p_e p_v2 p l (fun _ -> true)
        (fun vev la ->
          let (v, (e, va)) = f vev in
          rs_lts_dlts_add_simple _C _D v e va la)
        (rs_lts_dlts_empty_lts _C _D _C ()));;

let rec rs_lts_dlts_image _A _B _C _D
  = (fun f ->
      rs_lts_dlts_image_filter _A _B _C _D f (fun _ -> true) (fun _ -> true)
        (fun _ -> true) (fun _ -> true));;

let rec rs_nfa_rename_labels_gen _A
  det (q, (aa, (d, (i, (fa, p))))) a f =
    (q, (a, (rs_lts_dlts_image linorder_nat _A linorder_nat _A
               (fun (qb, (ab, qa)) -> (qb, (f ab, qa))) d,
              (i, (fa, fields det (nfa_prop_is_initially_connected p))))));;

let rec rs_nfa_right_quotient_lists _A
  ap (q, (a, (d, (i, (f, p))))) =
    let m =
      rs_lts_dlts_filter_it linorder_nat _A (fun _ -> true) ap (fun _ -> true)
        (fun _ -> true) d (fun _ -> true)
        (fun (qb, (_, qa)) m ->
          let s =
            (match rm_lookup linorder_nat qa m
              with None -> rs_empty linorder_nat () | Some s -> s)
            in
          rm_update linorder_nat qa (rs_ins linorder_nat qb s) m)
        (rm_empty linorder_nat ())
      in
    let fa =
      fst (worklist (fun _ -> true)
            (fun s e ->
              (if rs_memb linorder_nat e s then (s, [])
                else (rs_ins linorder_nat e s,
                       (match rm_lookup linorder_nat e m with None -> []
                         | Some aa -> rs_to_list linorder_nat aa))))
            (rs_empty linorder_nat (), rs_to_list linorder_nat f))
      in
    (q, (a, (d, (i, (fa, p)))));;

let rec rs_pres_nfa_of_pf
  n x1 c = match n, x1, c with
    n, Neg p, c ->
      let (pa, a) = rs_pres_nfa_of_pf n p c in
      (rs_nfa_complement (linorder_list (equal_bool, linorder_bool)) pa, a)
    | n, Forall p, c ->
        let (ca, a) = rs_cache_alpha c n in
        let (pa, b) = rs_pres_nfa_of_pf (suc n) p ca in
        (rs_nfa_complement (linorder_list (equal_bool, linorder_bool))
           (rs_nfa_right_quotient_lists
             (linorder_list (equal_bool, linorder_bool)) (list_all not)
             (rs_nfa_Hopcroft_NFA (linorder_list (equal_bool, linorder_bool))
               (rs_nfa_rename_labels_gen
                 (linorder_list (equal_bool, linorder_bool)) false
                 (rs_nfa_complement (linorder_list (equal_bool, linorder_bool))
                   pa)
                 a tl))),
          b)
    | n, Exist p, c ->
        let (ca, a) = rs_cache_alpha c n in
        let (pa, b) = rs_pres_nfa_of_pf (suc n) p ca in
        (rs_nfa_right_quotient_lists (linorder_list (equal_bool, linorder_bool))
           (list_all not)
           (rs_nfa_Hopcroft_NFA (linorder_list (equal_bool, linorder_bool))
             (rs_nfa_rename_labels_gen
               (linorder_list (equal_bool, linorder_bool)) false pa a tl)),
          b)
    | n, Imp (p, q), c ->
        let (pa, ca) = rs_pres_nfa_of_pf n p c in
        let (qa, a) = rs_pres_nfa_of_pf n q ca in
        (rs_nfa_bool_comb (linorder_list (equal_bool, linorder_bool))
           (fun aa b -> (if aa then b else true)) pa qa,
          a)
    | n, Or (p, q), c ->
        let (pa, ca) = rs_pres_nfa_of_pf n p c in
        let (qa, a) = rs_pres_nfa_of_pf n q ca in
        (rs_nfa_bool_comb (linorder_list (equal_bool, linorder_bool))
           (fun aa b -> aa || b) pa qa,
          a)
    | n, And (p, q), c ->
        let (pa, ca) = rs_pres_nfa_of_pf n p c in
        let (qa, a) = rs_pres_nfa_of_pf n q ca in
        (rs_nfa_bool_comb (linorder_list (equal_bool, linorder_bool))
           (fun aa b -> aa && b) pa qa,
          a)
    | n, Le (ks, l), c ->
        let (ca, a) = rs_cache_alpha c n in
        (rs_DFA_eq_ineq a true n ks l, ca)
    | n, Eq (ks, l), c ->
        let (ca, a) = rs_cache_alpha c n in
        (rs_DFA_eq_ineq a false n ks l, ca);;

let rec rs_pres_pf_to_nfa
  n pf = fst (rs_pres_nfa_of_pf n pf (rm_empty linorder_nat ()));;

let rec rs_eval_pf
  pf = rs_nfa_accept (linorder_list (equal_bool, linorder_bool))
         (rs_pres_pf_to_nfa (Big_int.big_int_of_int 0) pf) [];;

let rec dfa_accepting a q = nth (snd a) q;;

let rec eval_pf_dfa
  pf = accepts (dfa_trans (dfa_of_pf (Big_int.big_int_of_int 0) pf))
         (dfa_accepting (dfa_of_pf (Big_int.big_int_of_int 0) pf))
         (Big_int.big_int_of_int 0) [];;

let rec rs_nfa_rename_labels _A
  det = (fun (q, (a, (d, (i, f)))) fa ->
          rs_nfa_rename_labels_gen _A det (q, (a, (d, (i, f))))
            (rs_image _A _A fa a) fa);;

let rec rs_nfa_language_is_empty _A
  n = let (_, (_, (_, (_, (f, _))))) = rs_nfa_normalise _A n in
      rs_isEmpty (equal_nat, linorder_nat) f;;

let rec rs_nfa_language_is_subset _A
  a1 a2 =
    rs_nfa_language_is_empty _A
      (rs_nfa_bool_comb _A (fun a b -> a && b) a1
        (rs_nfa_complement _A (rs_nfa_determinise _A a2)));;

let rec rs_nfa_language_is_eq _A
  a1 a2 =
    rs_nfa_language_is_subset _A a1 a2 && rs_nfa_language_is_subset _A a2 a1;;

let rec rs_nfa_destruct_simple _A
  (q, (a, (d, (i, (f, p))))) =
    (rs_to_list linorder_nat q,
      (rs_to_list _A a,
        (rs_lts_dlts_to_list linorder_nat _A d,
          (rs_to_list linorder_nat i, rs_to_list linorder_nat f))));;

let rec rs_nfa_language_is_univ _A
  a = rs_nfa_language_is_empty _A
        (rs_nfa_complement _A (rs_nfa_determinise _A a));;

end;; (*struct Automata_Export*)
