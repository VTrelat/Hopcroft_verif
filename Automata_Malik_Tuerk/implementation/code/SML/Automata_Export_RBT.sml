
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell ref;

fun fromList l = ref (Value (Array.fromList l));
fun array (size, v) = ref (Value (Array.array (size,v)));
fun tabulate (size, f) = ref (Value (Array.tabulate(size, f)));
fun sub (ref Invalid, idx) = raise AccessedOldVersion |
    sub (ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (ref Invalid) => raise AccessedOldVersion |
    (ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      ref (Value a)
    );

fun length (ref Invalid) = raise AccessedOldVersion |
    length (ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of 
  (ref Invalid) => raise AccessedOldVersion |
  (ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (ref Invalid) => raise AccessedOldVersion |
  (ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;

end;




structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val maxa : ('a -> 'a -> bool) -> 'a -> 'a -> 'a
  val max : 'a ord -> 'a -> 'a -> 'a
  type 'a preorder
  val ord_preorder : 'a preorder -> 'a ord
  type 'a order
  val preorder_order : 'a order -> 'a preorder
  val less_bool : bool -> bool -> bool
  val less_eq_bool : bool -> bool -> bool
  val ord_bool : bool ord
  type 'a linorder
  val order_linorder : 'a linorder -> 'a order
  val preorder_bool : bool preorder
  val order_bool : bool order
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun maxa less_eq a b = (if less_eq a b then b else a);

fun max A_ = maxa (less_eq A_);

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

fun less_bool true b = false
  | less_bool false b = b;

fun less_eq_bool true b = b
  | less_eq_bool false b = true;

val ord_bool = {less_eq = less_eq_bool, less = less_bool} : bool ord;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val preorder_bool = {ord_preorder = ord_bool} : bool preorder;

val order_bool = {preorder_order = preorder_bool} : bool order;

end; (*struct Orderings*)

structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val equal_boola : bool -> bool -> bool
  val equal_bool : bool HOL.equal
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
  val equal_unita : unit -> unit -> bool
  val equal_unit : unit HOL.equal
end = struct

fun fst (a, b) = a;

fun snd (a, b) = b;

fun apsnd f (x, y) = (x, f y);

fun equal_boola p true = p
  | equal_boola p false = not p
  | equal_boola true p = p
  | equal_boola false p = not p;

val equal_bool = {equal = equal_boola} : bool HOL.equal;

fun equal_proda A_ B_ (aa, ba) (a, b) = HOL.eq A_ aa a andalso HOL.eq B_ ba b;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) HOL.equal;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit HOL.equal;

end; (*struct Product_Type*)

structure Arith : sig
  val suc : IntInf.int -> IntInf.int
  val ord_int : IntInf.int Orderings.ord
  val ord_nat : IntInf.int Orderings.ord
  type 'a plus
  val plus : 'a plus -> 'a -> 'a -> 'a
  type 'a zero
  val zero : 'a zero -> 'a
  val abs_int : IntInf.int -> IntInf.int
  val plus_int : IntInf.int plus
  val sgn_int : IntInf.int -> IntInf.int
  val zero_inta : IntInf.int
  val zero_int : IntInf.int zero
  val zero_nata : IntInf.int
  val zero_nat : IntInf.int zero
  val equal_nat : IntInf.int HOL.equal
  val preorder_nat : IntInf.int Orderings.preorder
  val order_nat : IntInf.int Orderings.order
  val minus_nat : IntInf.int -> IntInf.int -> IntInf.int
  val divmod_int : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val div_int : IntInf.int -> IntInf.int -> IntInf.int
  val div_nat : IntInf.int -> IntInf.int -> IntInf.int
  val mod_int : IntInf.int -> IntInf.int -> IntInf.int
  val linorder_nat : IntInf.int Orderings.linorder
  type 'a semigroup_add
  val plus_semigroup_add : 'a semigroup_add -> 'a plus
  type 'a monoid_add
  val semigroup_add_monoid_add : 'a monoid_add -> 'a semigroup_add
  val zero_monoid_add : 'a monoid_add -> 'a zero
  val semigroup_add_int : IntInf.int semigroup_add
  val monoid_add_int : IntInf.int monoid_add
end = struct

fun suc n = IntInf.+ (n, (1 : IntInf.int));

val ord_int =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

val ord_nat =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

fun abs_int i = (if IntInf.< (i, (0 : IntInf.int)) then IntInf.~ i else i);

val plus_int = {plus = (fn a => fn b => IntInf.+ (a, b))} : IntInf.int plus;

fun sgn_int i =
  (if ((i : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< ((0 : IntInf.int), i) then (1 : IntInf.int)
           else IntInf.~ (1 : IntInf.int)));

val zero_inta : IntInf.int = (0 : IntInf.int);

val zero_int = {zero = zero_inta} : IntInf.int zero;

val zero_nata : IntInf.int = (0 : IntInf.int);

val zero_nat = {zero = zero_nata} : IntInf.int zero;

val equal_nat = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int HOL.equal;

val preorder_nat = {ord_preorder = ord_nat} : IntInf.int Orderings.preorder;

val order_nat = {preorder_order = preorder_nat} : IntInf.int Orderings.order;

fun minus_nat n m = IntInf.max (0, (IntInf.- (n, m)));

fun divmod_int k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else Product_Type.apsnd (fn a => IntInf.* (sgn_int l, a))
                  (if (((sgn_int k) : IntInf.int) = (sgn_int l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_int l, s)))
                         end)));

fun div_int a b = Product_Type.fst (divmod_int a b);

fun div_nat m n = Product_Type.fst (IntInf.divMod (m, n));

fun mod_int a b = Product_Type.snd (divmod_int a b);

val linorder_nat = {order_linorder = order_nat} : IntInf.int Orderings.linorder;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

val semigroup_add_int = {plus_semigroup_add = plus_int} :
  IntInf.int semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  IntInf.int monoid_add;

end; (*struct Arith*)

structure Option : sig
  val the : 'a option -> 'a
  val is_none : 'a option -> bool
end = struct

fun the (SOME x) = x;

fun is_none (SOME x) = false
  | is_none NONE = true;

end; (*struct Option*)

structure Fun : sig
  val id : 'a -> 'a
end = struct

fun id x = (fn xa => xa) x;

end; (*struct Fun*)

structure More_List : sig
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
end = struct

fun fold f [] = Fun.id
  | fold f (x :: xs) = fold f xs o f x;

end; (*struct More_List*)

structure List : sig
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val nth : 'a list -> IntInf.int -> 'a
  val rev : 'a list -> 'a list
  val null : 'a list -> bool
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val listsum : 'a Arith.monoid_add -> 'a list -> 'a
  val list_all : ('a -> bool) -> 'a list -> bool
  val equal_lista : 'a HOL.equal -> 'a list -> 'a list -> bool
  val equal_list : 'a HOL.equal -> ('a list) HOL.equal
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val replicate : IntInf.int -> 'a -> 'a list
  val size_list : 'a list -> IntInf.int
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val list_update : 'a list -> IntInf.int -> 'a -> 'a list
end = struct

fun hd (x :: xs) = x;

fun tl [] = []
  | tl (x :: xs) = xs;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun nth (x :: xs) n =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then x
    else nth xs (Arith.minus_nat n (1 : IntInf.int)));

fun rev xs = More_List.fold (fn a => fn b => a :: b) xs [];

fun null [] = true
  | null (x :: xs) = false;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

fun insert A_ x xs = (if member A_ xs x then xs else x :: xs);

fun listsum A_ xs =
  More_List.fold
    (fn x => fn y =>
      Arith.plus
        ((Arith.plus_semigroup_add o Arith.semigroup_add_monoid_add) A_) y x)
    xs (Arith.zero (Arith.zero_monoid_add A_));

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun equal_lista A_ (a :: lista) [] = false
  | equal_lista A_ [] (a :: lista) = false
  | equal_lista A_ (aa :: listaa) (a :: lista) =
    HOL.eq A_ aa a andalso equal_lista A_ listaa lista
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) HOL.equal;

fun partition p [] = ([], [])
  | partition p (x :: xs) =
    let
      val (yes, no) = partition p xs;
    in
      (if p x then (x :: yes, no) else (yes, x :: no))
    end;

fun replicate n x =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then []
    else x :: replicate (Arith.minus_nat n (1 : IntInf.int)) x);

fun size_list [] = (0 : IntInf.int)
  | size_list (a :: lista) =
    IntInf.+ (size_list lista, Arith.suc (0 : IntInf.int));

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then y :: xs
      else x :: list_update xs (Arith.minus_nat i (1 : IntInf.int)) y);

end; (*struct List*)

structure DFS : sig
  val gen_dfs :
    ('a -> 'a list) ->
      ('a -> 'b -> 'b) -> ('a -> 'b -> bool) -> 'b -> 'a list -> 'b
end = struct

fun gen_dfs succs ins memb s wl =
  (case wl of [] => s
    | x :: xs =>
      (if memb x s then gen_dfs succs ins memb s xs
        else gen_dfs succs ins memb (ins x s) (succs x @ xs)));

end; (*struct DFS*)

structure Set : sig
  val collect : ('a -> bool) -> 'a -> bool
end = struct

fun collect p = p;

end; (*struct Set*)

structure Map : sig
  val dom : ('a -> 'b option) -> 'a -> bool
end = struct

fun dom m = Set.collect (fn a => not (Option.is_none (m a)));

end; (*struct Map*)

structure RBT_Impl : sig
  datatype color = R | B
  datatype ('a, 'b) rbt = Empty |
    Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt
  val paint : color -> ('a, 'b) rbt -> ('a, 'b) rbt
  val balance : ('a, 'b) rbt -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val balance_left : ('a, 'b) rbt -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val combine : ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt
  val balance_right : ('a, 'b) rbt -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val del : 'a Orderings.linorder -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val del_from_right :
    'a Orderings.linorder ->
      'a -> ('a, 'b) rbt -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val del_from_left :
    'a Orderings.linorder ->
      'a -> ('a, 'b) rbt -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val ins :
    'a Orderings.linorder ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val delete : 'a Orderings.linorder -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val insert_with_key :
    'a Orderings.linorder ->
      ('a -> 'b -> 'b -> 'b) -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val insert : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val lookup : 'a Orderings.linorder -> ('a, 'b) rbt -> 'a -> 'b option
  val equal_color : color -> color -> bool
  val equal_rbt :
    'a HOL.equal -> 'b HOL.equal -> ('a, 'b) rbt -> ('a, 'b) rbt -> bool
end = struct

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun balance_left (Branch (R, a, k, x, b)) s y c =
  Branch (R, Branch (B, a, k, x, b), s, y, c)
  | balance_left Empty k x (Branch (B, a, s, y, b)) =
    balance Empty k x (Branch (R, a, s, y, b))
  | balance_left (Branch (B, va, vb, vc, vd)) k x (Branch (B, a, s, y, b)) =
    balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
  | balance_left Empty k x (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
        balance b t z (paint R c))
  | balance_left Empty k x Empty = Empty
  | balance_left Empty k x (Branch (R, Empty, vb, vc, vd)) = Empty
  | balance_left Empty k x (Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd))
    = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x Empty = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Empty, vf, vg, vh)) = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)) = Empty;

fun combine Empty x = x
  | combine (Branch (v, va, vb, vc, vd)) Empty = Branch (v, va, vb, vc, vd)
  | combine (Branch (R, a, k, x, b)) (Branch (R, c, s, y, d)) =
    (case combine b c
      of Empty => Branch (R, a, k, x, Branch (R, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, a, k, x, b)) (Branch (B, c, s, y, d)) =
    (case combine b c
      of Empty => balance_left a k x (Branch (B, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, va, vb, vc, vd)) (Branch (R, b, k, x, c)) =
    Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
  | combine (Branch (R, a, k, x, b)) (Branch (B, va, vb, vc, vd)) =
    Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));

fun balance_right a k x (Branch (R, b, s, y, c)) =
  Branch (R, a, k, x, Branch (B, b, s, y, c))
  | balance_right (Branch (B, a, k, x, b)) s y Empty =
    balance (Branch (R, a, k, x, b)) s y Empty
  | balance_right (Branch (B, a, k, x, b)) s y (Branch (B, va, vb, vc, vd)) =
    balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z Empty =
    Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, balance (paint R a) k x b, s, y,
        Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
  | balance_right Empty k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Empty)) k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh))) k x Empty
    = Empty
  | balance_right Empty k x (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Empty)) k x
    (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl))) k x
    (Branch (B, va, vb, vc, vd)) = Empty;

fun del A_ x Empty = Empty
  | del A_ x (Branch (c, a, y, s, b)) =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A_)
          x y
      then del_from_left A_ x a y s b
      else (if Orderings.less
                 ((Orderings.ord_preorder o Orderings.preorder_order o
                    Orderings.order_linorder)
                   A_)
                 y x
             then del_from_right A_ x a y s b else combine a b))
and del_from_right A_ x a y s (Branch (B, lt, z, v, rt)) =
  balance_right a y s (del A_ x (Branch (B, lt, z, v, rt)))
  | del_from_right A_ x a y s Empty = Branch (R, a, y, s, del A_ x Empty)
  | del_from_right A_ x a y s (Branch (R, va, vb, vc, vd)) =
    Branch (R, a, y, s, del A_ x (Branch (R, va, vb, vc, vd)))
and del_from_left A_ x (Branch (B, lt, z, v, rt)) y s b =
  balance_left (del A_ x (Branch (B, lt, z, v, rt))) y s b
  | del_from_left A_ x Empty y s b = Branch (R, del A_ x Empty, y, s, b)
  | del_from_left A_ x (Branch (R, va, vb, vc, vd)) y s b =
    Branch (R, del A_ x (Branch (R, va, vb, vc, vd)), y, s, b);

fun ins A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | ins A_ f k v (Branch (B, l, x, y, r)) =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A_)
          k x
      then balance (ins A_ f k v l) x y r
      else (if Orderings.less
                 ((Orderings.ord_preorder o Orderings.preorder_order o
                    Orderings.order_linorder)
                   A_)
                 x k
             then balance l x y (ins A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | ins A_ f k v (Branch (R, l, x, y, r)) =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A_)
          k x
      then Branch (R, ins A_ f k v l, x, y, r)
      else (if Orderings.less
                 ((Orderings.ord_preorder o Orderings.preorder_order o
                    Orderings.order_linorder)
                   A_)
                 x k
             then Branch (R, l, x, y, ins A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun delete A_ k t = paint B (del A_ k t);

fun insert_with_key A_ f k v t = paint B (ins A_ f k v t);

fun insert A_ = insert_with_key A_ (fn _ => fn _ => fn nv => nv);

fun lookup A_ Empty k = NONE
  | lookup A_ (Branch (uu, l, x, y, r)) k =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A_)
          k x
      then lookup A_ l k
      else (if Orderings.less
                 ((Orderings.ord_preorder o Orderings.preorder_order o
                    Orderings.order_linorder)
                   A_)
                 x k
             then lookup A_ r k else SOME y));

fun equal_color B R = false
  | equal_color R B = false
  | equal_color B B = true
  | equal_color R R = true;

fun equal_rbt A_ B_ (Branch (color, rbt1, a, b, rbt2)) Empty = false
  | equal_rbt A_ B_ Empty (Branch (color, rbt1, a, b, rbt2)) = false
  | equal_rbt A_ B_ (Branch (colora, rbt1a, aa, ba, rbt2a))
    (Branch (color, rbt1, a, b, rbt2)) =
    equal_color colora color andalso
      (equal_rbt A_ B_ rbt1a rbt1 andalso
        (HOL.eq A_ aa a andalso
          (HOL.eq B_ ba b andalso equal_rbt A_ B_ rbt2a rbt2)))
  | equal_rbt A_ B_ Empty Empty = true;

end; (*struct RBT_Impl*)

structure RBT : sig
  datatype ('a, 'b) rbt = Rbt of ('a, 'b) RBT_Impl.rbt
  val empty : 'a Orderings.linorder -> ('a, 'b) rbt
  val impl_of : 'a Orderings.linorder -> ('a, 'b) rbt -> ('a, 'b) RBT_Impl.rbt
  val delete : 'a Orderings.linorder -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val insert : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val lookup : 'a Orderings.linorder -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

datatype ('a, 'b) rbt = Rbt of ('a, 'b) RBT_Impl.rbt;

fun empty A_ = Rbt RBT_Impl.Empty;

fun impl_of A_ (Rbt x) = x;

fun delete A_ k t = Rbt (RBT_Impl.delete A_ k (impl_of A_ t));

fun insert A_ k v t = Rbt (RBT_Impl.insert A_ k v (impl_of A_ t));

fun lookup A_ t = RBT_Impl.lookup A_ (impl_of A_ t);

end; (*struct RBT*)

structure Enum : sig
  val product : 'a list -> 'b list -> ('a * 'b) list
end = struct

fun product [] uu = []
  | product (x :: xs) ys = List.map (fn a => (x, a)) ys @ product xs ys;

end; (*struct Enum*)

structure Misc : sig
  val less_eq_prod_aux :
    'a HOL.equal * 'a Orderings.ord -> 'b Orderings.ord ->
      'a * 'b -> 'a * 'b -> bool
  val less_prod :
    'a HOL.equal * 'a Orderings.ord -> 'b HOL.equal * 'b Orderings.ord ->
      'a * 'b -> 'a * 'b -> bool
  val less_eq_prod :
    'a HOL.equal * 'a Orderings.ord -> 'b Orderings.ord ->
      'a * 'b -> 'a * 'b -> bool
  val ord_prod :
    'a HOL.equal * 'a Orderings.ord -> 'b HOL.equal * 'b Orderings.ord ->
      ('a * 'b) Orderings.ord
  val preorder_prod :
    'a HOL.equal * 'a Orderings.order -> 'b HOL.equal * 'b Orderings.order ->
      ('a * 'b) Orderings.preorder
  val order_prod :
    'a HOL.equal * 'a Orderings.order -> 'b HOL.equal * 'b Orderings.order ->
      ('a * 'b) Orderings.order
  val linorder_prod :
    'a HOL.equal * 'a Orderings.linorder ->
      'b HOL.equal * 'b Orderings.linorder -> ('a * 'b) Orderings.linorder
end = struct

fun less_eq_prod_aux (A1_, A2_) B_ (a1, a2) (b1, b2) =
  Orderings.less A2_ a1 b1 orelse
    HOL.eq A1_ a1 b1 andalso Orderings.less_eq B_ a2 b2;

fun less_prod (A1_, A2_) (B1_, B2_) a b =
  not (Product_Type.equal_proda A1_ B1_ a b) andalso
    less_eq_prod_aux (A1_, A2_) B2_ a b;

fun less_eq_prod (A1_, A2_) B_ a b = less_eq_prod_aux (A1_, A2_) B_ a b;

fun ord_prod (A1_, A2_) (B1_, B2_) =
  {less_eq = less_eq_prod (A1_, A2_) B2_,
    less = less_prod (A1_, A2_) (B1_, B2_)}
  : ('a * 'b) Orderings.ord;

fun preorder_prod (A1_, A2_) (B1_, B2_) =
  {ord_preorder =
     ord_prod (A1_, (Orderings.ord_preorder o Orderings.preorder_order) A2_)
       (B1_, (Orderings.ord_preorder o Orderings.preorder_order) B2_)}
  : ('a * 'b) Orderings.preorder;

fun order_prod (A1_, A2_) (B1_, B2_) =
  {preorder_order = preorder_prod (A1_, A2_) (B1_, B2_)} :
  ('a * 'b) Orderings.order;

fun linorder_prod (A1_, A2_) (B1_, B2_) =
  {order_linorder =
     order_prod (A1_, Orderings.order_linorder A2_)
       (B1_, Orderings.order_linorder B2_)}
  : ('a * 'b) Orderings.linorder;

end; (*struct Misc*)

structure LTSGA : sig
  val ltsga_copy :
    ('a -> ('b -> bool) -> ('c * ('d * 'c) -> 'e -> 'e) -> 'e -> 'e) ->
      (unit -> 'e) -> ('c -> 'd -> 'c -> 'e -> 'e) -> 'a -> 'e
  val ltsga_reverse :
    (unit -> 'a) ->
      ('b -> 'c -> 'b -> 'a -> 'a) ->
        ('d -> ('e -> bool) -> ('b * ('c * 'b) -> 'a -> 'a) -> 'a -> 'a) ->
          'd -> 'a
  val ltsga_list_to_collect_list :
    'a HOL.equal -> 'c HOL.equal ->
      ('a * ('b * 'c)) list -> ('a * ('b list * 'c)) list
end = struct

fun ltsga_copy it emp add l =
  it l (fn _ => true) (fn (q, (a, b)) => add q a b) (emp ());

fun ltsga_reverse e a it l =
  it l (fn _ => true) (fn (v, (ea, va)) => a va ea v) (e ());

fun ltsga_list_to_collect_list A_ C_ [] = []
  | ltsga_list_to_collect_list A_ C_ ((va, (e, v)) :: l) =
    let
      val (yes, no) =
        List.partition
          (fn vev =>
            HOL.eq A_ (Product_Type.fst vev) va andalso
              HOL.eq C_ (Product_Type.snd (Product_Type.snd vev)) v)
          l;
    in
      (va, (e :: List.map (Product_Type.fst o Product_Type.snd) yes, v)) ::
        ltsga_list_to_collect_list A_ C_ no
    end;

end; (*struct LTSGA*)

structure MapGA : sig
  val eu_sng : (unit -> 'a) -> ('b -> 'c -> 'a -> 'a) -> 'b -> 'c -> 'a
  val it_add :
    ('a -> 'b -> 'c -> 'c) ->
      ('d -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c) ->
        'c -> 'd -> 'c
  val it_size :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      'a -> IntInf.int
  val iti_sel :
    ('a ->
      ('b option -> bool) ->
        ('c -> 'b option -> 'b option) -> 'b option -> 'b option) ->
      'a -> ('c -> 'b option) -> 'b option
  val sel_ball :
    ('a -> ('b * 'c -> unit option) -> unit option) ->
      'a -> ('b * 'c -> bool) -> bool
  val sza_isSng :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      'a -> bool
  val iti_isEmpty :
    ('a -> (bool -> bool) -> ('b -> bool -> bool) -> bool -> bool) -> 'a -> bool
  val it_map_to_list :
    ('a ->
      ('b list -> bool) -> ('b -> 'b list -> 'b list) -> 'b list -> 'b list) ->
      'a -> 'b list
  val iti_sel_no_map :
    ('a ->
      ('b option -> bool) ->
        ('b -> 'b option -> 'b option) -> 'b option -> 'b option) ->
      'a -> ('b -> bool) -> 'b option
  val iti_size_abort :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      IntInf.int -> 'a -> IntInf.int
  val gen_list_to_map_aux : ('a -> 'b -> 'c -> 'c) -> 'c -> ('a * 'b) list -> 'c
  val gen_list_to_map :
    (unit -> 'a) -> ('b -> 'c -> 'a -> 'a) -> ('b * 'c) list -> 'a
  val it_map_image_filter :
    ('a -> ('b -> bool) -> ('c * 'd -> 'b -> 'b) -> 'b -> 'b) ->
      (unit -> 'b) ->
        ('e -> 'f -> 'b -> 'b) -> ('c * 'd -> ('e * 'f) option) -> 'a -> 'b
  val it_map_restrict :
    ('a -> ('b -> bool) -> ('c * 'd -> 'b -> 'b) -> 'b -> 'b) ->
      (unit -> 'b) -> ('c -> 'd -> 'b -> 'b) -> ('c * 'd -> bool) -> 'a -> 'b
  val neg_ball_bexists :
    ('a -> ('b * 'c -> bool) -> bool) -> 'a -> ('b * 'c -> bool) -> bool
end = struct

fun eu_sng empt update k v = update k v (empt ());

fun it_add update iti m1 m2 =
  iti m2 (fn _ => true) (fn (a, b) => update a b) m1;

fun it_size iti m = iti m (fn _ => true) (fn _ => Arith.suc) (0 : IntInf.int);

fun iti_sel iti m f = iti m Option.is_none (fn x => fn _ => f x) NONE;

fun sel_ball sel s p =
  Option.is_none (sel s (fn kv => (if not (p kv) then SOME () else NONE)));

fun sza_isSng iti m =
  (((iti m (fn sigma => IntInf.< (sigma, (2 : IntInf.int))) (fn _ => Arith.suc)
      (0 : IntInf.int)) : IntInf.int) = (1 : IntInf.int));

fun iti_isEmpty iti m = iti m (fn c => c) (fn _ => fn _ => false) true;

fun it_map_to_list iti m = iti m (fn _ => true) (fn a => fn b => a :: b) [];

fun iti_sel_no_map iti m p =
  iti m Option.is_none (fn x => fn _ => (if p x then SOME x else NONE)) NONE;

fun iti_size_abort iti n m =
  iti m (fn sigma => IntInf.< (sigma, n)) (fn _ => Arith.suc) (0 : IntInf.int);

fun gen_list_to_map_aux upd accs [] = accs
  | gen_list_to_map_aux upd accs ((k, v) :: l) =
    gen_list_to_map_aux upd (upd k v accs) l;

fun gen_list_to_map empt upd l = gen_list_to_map_aux upd (empt ()) (List.rev l);

fun it_map_image_filter map_it map_emp map_up_dj f m =
  map_it m (fn _ => true)
    (fn kv => fn sigma =>
      (case f kv of NONE => sigma | SOME (k, v) => map_up_dj k v sigma))
    (map_emp ());

fun it_map_restrict map_it map_emp map_up_dj p =
  it_map_image_filter map_it map_emp map_up_dj
    (fn (k, v) => (if p (k, v) then SOME (k, v) else NONE));

fun neg_ball_bexists ball s p = not (ball s (fn kv => not (p kv)));

end; (*struct MapGA*)

structure SetGA : sig
  val ei_sng : (unit -> 'a) -> ('b -> 'a -> 'a) -> 'b -> 'a
  val it_diff :
    ('a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b) ->
      ('c -> 'b -> 'b) -> 'b -> 'a -> 'b
  val it_size :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      'a -> IntInf.int
  val sel_sel :
    ('a -> ('b -> 'b option) -> 'b option) -> 'a -> ('b -> bool) -> 'b option
  val it_inter :
    ('a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b) ->
      ('c -> 'd -> bool) -> (unit -> 'b) -> ('c -> 'b -> 'b) -> 'a -> 'd -> 'b
  val iti_ball :
    ('a -> (bool -> bool) -> ('b -> bool -> bool) -> bool -> bool) ->
      'a -> ('b -> bool) -> bool
  val sza_isSng :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      'a -> bool
  val iflt_image : (('a -> 'b option) -> 'c -> 'd) -> ('a -> 'b) -> 'c -> 'd
  val ball_subset :
    ('a -> ('b -> bool) -> bool) -> ('b -> 'c -> bool) -> 'a -> 'c -> bool
  val iflt_filter : (('a -> 'a option) -> 'b -> 'c) -> ('a -> bool) -> 'b -> 'c
  val subset_equal :
    ('a -> 'b -> bool) -> ('b -> 'a -> bool) -> 'a -> 'b -> bool
  val ball_disjoint :
    ('a -> ('b -> bool) -> 'c) -> ('b -> 'd -> bool) -> 'a -> 'd -> 'c
  val it_set_to_list :
    ('a ->
      ('b list -> bool) -> ('b -> 'b list -> 'b list) -> 'b list -> 'b list) ->
      'a -> 'b list
  val iti_sel_no_map :
    ('a ->
      ('b option -> bool) ->
        ('b -> 'b option -> 'b option) -> 'b option -> 'b option) ->
      'a -> ('b -> bool) -> 'b option
  val iti_size_abort :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      IntInf.int -> 'a -> IntInf.int
  val gen_list_to_set_aux : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val gen_list_to_set : (unit -> 'a) -> ('b -> 'a -> 'a) -> 'b list -> 'a
  val it_image_filter :
    ('a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b) ->
      (unit -> 'b) -> ('d -> 'b -> 'b) -> ('c -> 'd option) -> 'a -> 'b
  val neg_ball_bexists :
    ('a -> ('b -> bool) -> bool) -> 'a -> ('b -> bool) -> bool
  val sel_disjoint_witness :
    ('a -> ('b -> 'b option) -> 'c) -> ('b -> 'd -> bool) -> 'a -> 'd -> 'c
end = struct

fun ei_sng e i x = i x (e ());

fun it_diff it del s1 s2 = it s2 (fn _ => true) del s1;

fun it_size iti s = iti s (fn _ => true) (fn _ => Arith.suc) (0 : IntInf.int);

fun sel_sel sel s p = sel s (fn x => (if p x then SOME x else NONE));

fun it_inter iteratei1 memb2 empt3 insrt3 s1 s2 =
  iteratei1 s1 (fn _ => true)
    (fn x => fn s => (if memb2 x s2 then insrt3 x s else s))
    (empt3 ());

fun iti_ball iti s p = iti s (fn c => c) (fn x => fn _ => p x) true;

fun sza_isSng iti s =
  (((iti s (fn sigma => IntInf.< (sigma, (2 : IntInf.int))) (fn _ => Arith.suc)
      (0 : IntInf.int)) : IntInf.int) = (1 : IntInf.int));

fun iflt_image iflt f s = iflt (fn x => SOME (f x)) s;

fun ball_subset ball1 mem2 s1 s2 = ball1 s1 (fn x => mem2 x s2);

fun iflt_filter iflt p s = iflt (fn x => (if p x then SOME x else NONE)) s;

fun subset_equal ss1 ss2 s1 s2 = ss1 s1 s2 andalso ss2 s2 s1;

fun ball_disjoint ball1 memb2 s1 s2 = ball1 s1 (fn x => not (memb2 x s2));

fun it_set_to_list iti s = iti s (fn _ => true) (fn a => fn b => a :: b) [];

fun iti_sel_no_map iti s f =
  iti s Option.is_none (fn x => fn _ => (if f x then SOME x else NONE)) NONE;

fun iti_size_abort iti m s =
  iti s (fn sigma => IntInf.< (sigma, m)) (fn _ => Arith.suc) (0 : IntInf.int);

fun gen_list_to_set_aux ins accs [] = accs
  | gen_list_to_set_aux ins accs (x :: l) =
    gen_list_to_set_aux ins (ins x accs) l;

fun gen_list_to_set empt ins = gen_list_to_set_aux ins (empt ());

fun it_image_filter iteratei1 empty2 ins2 f s =
  iteratei1 s (fn _ => true)
    (fn x => fn res => (case f x of NONE => res | SOME v => ins2 v res))
    (empty2 ());

fun neg_ball_bexists ball s p = not (ball s (fn x => not (p x)));

fun sel_disjoint_witness sel1 mem2 s1 s2 =
  sel1 s1 (fn x => (if mem2 x s2 then SOME x else NONE));

end; (*struct SetGA*)

structure ListAdd : sig
  val merge :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> 'a list
  val merge_list :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a list) list -> ('a list) list -> 'a list
  val insertion_sort :
    'a HOL.equal * 'a Orderings.ord -> 'a -> 'a list -> 'a list
end = struct

fun merge (A1_, A2_) [] l2 = l2
  | merge (A1_, A2_) (v :: va) [] = v :: va
  | merge (A1_, A2_) (x1 :: l1) (x2 :: l2) =
    (if Orderings.less
          ((Orderings.ord_preorder o Orderings.preorder_order o
             Orderings.order_linorder)
            A2_)
          x1 x2
      then x1 :: merge (A1_, A2_) l1 (x2 :: l2)
      else (if HOL.eq A1_ x1 x2 then x1 :: merge (A1_, A2_) l1 l2
             else x2 :: merge (A1_, A2_) (x1 :: l1) l2));

fun merge_list (A1_, A2_) [] [] = []
  | merge_list (A1_, A2_) [] [l] = l
  | merge_list (A1_, A2_) (la :: acc2) [] =
    merge_list (A1_, A2_) [] (la :: acc2)
  | merge_list (A1_, A2_) (la :: acc2) [l] =
    merge_list (A1_, A2_) [] (l :: la :: acc2)
  | merge_list (A1_, A2_) acc2 (l1 :: l2 :: ls) =
    merge_list (A1_, A2_) (merge (A1_, A2_) l1 l2 :: acc2) ls;

fun insertion_sort (A1_, A2_) x [] = [x]
  | insertion_sort (A1_, A2_) x (y :: xs) =
    (if Orderings.less A2_ y x then y :: insertion_sort (A1_, A2_) x xs
      else (if HOL.eq A1_ x y then y :: xs else x :: y :: xs));

end; (*struct ListAdd*)

structure MapSpec : sig
  datatype ('a, 'b, 'c, 'd) map_ops_ext =
    Map_ops_ext of
      ('c -> 'a -> 'b option) * ('c -> bool) * (unit -> 'c) * ('a -> 'b -> 'c) *
        ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c) *
        ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'c) *
        (('a * 'b -> bool) -> 'c -> 'c) * ('c -> 'c -> 'c) * ('c -> 'c -> 'c) *
        ('c -> bool) * ('c -> bool) * ('c -> ('a * 'b -> bool) -> bool) *
        ('c -> ('a * 'b -> bool) -> bool) * ('c -> IntInf.int) *
        (IntInf.int -> 'c -> IntInf.int) *
        ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * ('c -> ('a * 'b) list) *
        (('a * 'b) list -> 'c) * 'd
  val map_op_sng : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'b -> 'c
  datatype ('a, 'b, 'c, 'd) omap_ops_ext =
    Omap_ops_ext of
      ('c -> ('a * 'b -> bool) -> ('a * 'b) option) *
        ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * 'd
  val map_op_empty : ('a, 'b, 'c, 'd) map_ops_ext -> unit -> 'c
  val map_op_lookup : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'c -> 'b option
  val map_op_update : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'b -> 'c -> 'c
end = struct

datatype ('a, 'b, 'c, 'd) map_ops_ext =
  Map_ops_ext of
    ('c -> 'a -> 'b option) * ('c -> bool) * (unit -> 'c) * ('a -> 'b -> 'c) *
      ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c) *
      ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'c) *
      (('a * 'b -> bool) -> 'c -> 'c) * ('c -> 'c -> 'c) * ('c -> 'c -> 'c) *
      ('c -> bool) * ('c -> bool) * ('c -> ('a * 'b -> bool) -> bool) *
      ('c -> ('a * 'b -> bool) -> bool) * ('c -> IntInf.int) *
      (IntInf.int -> 'c -> IntInf.int) *
      ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * ('c -> ('a * 'b) list) *
      (('a * 'b) list -> 'c) * 'd;

fun map_op_sng
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
  = map_op_sng;

datatype ('a, 'b, 'c, 'd) omap_ops_ext =
  Omap_ops_ext of
    ('c -> ('a * 'b -> bool) -> ('a * 'b) option) *
      ('c -> ('a * 'b -> bool) -> ('a * 'b) option) * 'd;

fun map_op_empty
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
  = map_op_empty;

fun map_op_lookup
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
  = map_op_lookup;

fun map_op_update
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
  = map_op_update;

end; (*struct MapSpec*)

structure RBT_add : sig
  val equal_rbta :
    'a HOL.equal * 'a Orderings.linorder -> 'b HOL.equal ->
      ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt -> bool
  val equal_rbt :
    'a HOL.equal * 'a Orderings.linorder -> 'b HOL.equal ->
      ('a, 'b) RBT.rbt HOL.equal
  val rm_iterateoi :
    ('a, 'b) RBT_Impl.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_reverse_iterateoi :
    ('a, 'b) RBT_Impl.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

fun equal_rbta (A1_, A2_) B_ ra r =
  RBT_Impl.equal_rbt A1_ B_ (RBT.impl_of A2_ ra) (RBT.impl_of A2_ r);

fun equal_rbt (A1_, A2_) B_ = {equal = equal_rbta (A1_, A2_) B_} :
  ('a, 'b) RBT.rbt HOL.equal;

fun rm_iterateoi RBT_Impl.Empty c f sigma = sigma
  | rm_iterateoi (RBT_Impl.Branch (col, l, k, v, r)) c f sigma =
    (if c sigma
      then let
             val sigmaa = rm_iterateoi l c f sigma;
           in
             (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa) else sigmaa)
           end
      else sigma);

fun rm_reverse_iterateoi RBT_Impl.Empty c f sigma = sigma
  | rm_reverse_iterateoi (RBT_Impl.Branch (col, l, k, v, r)) c f sigma =
    (if c sigma
      then let
             val sigmaa = rm_reverse_iterateoi r c f sigma;
           in
             (if c sigmaa then rm_reverse_iterateoi l c f (f (k, v) sigmaa)
               else sigmaa)
           end
      else sigma);

end; (*struct RBT_add*)

structure SetSpec : sig
  datatype ('a, 'b, 'c) set_ops_ext =
    Set_ops_ext of
      ('b -> 'a -> bool) * ('b -> bool) * (unit -> 'b) * ('a -> 'b) *
        ('a -> 'b -> bool) * ('a -> 'b -> 'b) * ('a -> 'b -> 'b) *
        ('a -> 'b -> 'b) * ('b -> bool) * ('b -> bool) *
        ('b -> ('a -> bool) -> bool) * ('b -> ('a -> bool) -> bool) *
        ('b -> IntInf.int) * (IntInf.int -> 'b -> IntInf.int) *
        ('b -> 'b -> 'b) * ('b -> 'b -> 'b) * ('b -> 'b -> 'b) *
        (('a -> bool) -> 'b -> 'b) * ('b -> 'b -> 'b) * ('b -> 'b -> bool) *
        ('b -> 'b -> bool) * ('b -> 'b -> bool) * ('b -> 'b -> 'a option) *
        ('b -> ('a -> bool) -> 'a option) * ('b -> 'a list) * ('a list -> 'b) *
        'c
  datatype ('a, 'b, 'c) oset_ops_ext =
    Oset_ops_ext of
      ('b -> ('a -> bool) -> 'a option) * ('b -> ('a -> bool) -> 'a option) * 'c
  val set_op_diff : ('a, 'b, 'c) set_ops_ext -> 'b -> 'b -> 'b
end = struct

datatype ('a, 'b, 'c) set_ops_ext =
  Set_ops_ext of
    ('b -> 'a -> bool) * ('b -> bool) * (unit -> 'b) * ('a -> 'b) *
      ('a -> 'b -> bool) * ('a -> 'b -> 'b) * ('a -> 'b -> 'b) *
      ('a -> 'b -> 'b) * ('b -> bool) * ('b -> bool) *
      ('b -> ('a -> bool) -> bool) * ('b -> ('a -> bool) -> bool) *
      ('b -> IntInf.int) * (IntInf.int -> 'b -> IntInf.int) * ('b -> 'b -> 'b) *
      ('b -> 'b -> 'b) * ('b -> 'b -> 'b) * (('a -> bool) -> 'b -> 'b) *
      ('b -> 'b -> 'b) * ('b -> 'b -> bool) * ('b -> 'b -> bool) *
      ('b -> 'b -> bool) * ('b -> 'b -> 'a option) *
      ('b -> ('a -> bool) -> 'a option) * ('b -> 'a list) * ('a list -> 'b) *
      'c;

datatype ('a, 'b, 'c) oset_ops_ext =
  Oset_ops_ext of
    ('b -> ('a -> bool) -> 'a option) * ('b -> ('a -> bool) -> 'a option) * 'c;

fun set_op_diff
  (Set_ops_ext
    (set_op_alpha, set_op_invar, set_op_empty, set_op_sng, set_op_memb,
      set_op_ins, set_op_ins_dj, set_op_delete, set_op_isEmpty, set_op_isSng,
      set_op_ball, set_op_bexists, set_op_size, set_op_size_abort, set_op_union,
      set_op_union_dj, set_op_diff, set_op_filter, set_op_inter, set_op_subset,
      set_op_equal, set_op_disjoint, set_op_disjoint_witness, set_op_sel,
      set_op_to_list, set_op_from_list, more))
  = set_op_diff;

end; (*struct SetSpec*)

structure RBTMapImpl : sig
  val rm_update :
    'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt
  val rm_iterateoi :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_iteratei :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_add :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt
  val rm_reverse_iterateoi :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
  val rm_max :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('a * 'b -> bool) -> ('a * 'b) option
  val rm_min :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('a * 'b -> bool) -> ('a * 'b) option
  val rm_sel :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('a * 'b -> 'c option) -> 'c option
  val rm_sela :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('a * 'b -> bool) -> ('a * 'b) option
  val rm_alpha : 'a Orderings.linorder -> ('a, 'b) RBT.rbt -> 'a -> 'b option
  val rm_empty : 'a Orderings.linorder -> unit -> ('a, 'b) RBT.rbt
  val rm_add_dj :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt
  val rm_delete :
    'a Orderings.linorder -> 'a -> ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt
  val rm_lookup : 'a Orderings.linorder -> 'a -> ('a, 'b) RBT.rbt -> 'b option
  val list_to_rm : 'a Orderings.linorder -> ('a * 'b) list -> ('a, 'b) RBT.rbt
  val rm_isEmpty :
    'a HOL.equal * 'a Orderings.linorder -> 'b HOL.equal ->
      ('a, 'b) RBT.rbt -> bool
  val rm_to_list : 'a Orderings.linorder -> ('a, 'b) RBT.rbt -> ('a * 'b) list
  val rm_update_dj :
    'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt
end = struct

fun rm_update A_ = RBT.insert A_;

fun rm_iterateoi A_ r = RBT_add.rm_iterateoi (RBT.impl_of A_ r);

fun rm_iteratei A_ = rm_iterateoi A_;

fun rm_add A_ = MapGA.it_add (rm_update A_) (rm_iteratei A_);

fun rm_reverse_iterateoi A_ r = RBT_add.rm_reverse_iterateoi (RBT.impl_of A_ r);

fun rm_max A_ = MapGA.iti_sel_no_map (rm_reverse_iterateoi A_);

fun rm_min A_ = MapGA.iti_sel_no_map (rm_iterateoi A_);

fun rm_sel A_ = MapGA.iti_sel (rm_iteratei A_);

fun rm_sela A_ = MapGA.iti_sel_no_map (rm_iteratei A_);

fun rm_alpha A_ = RBT.lookup A_;

fun rm_empty A_ = (fn _ => RBT.empty A_);

fun rm_add_dj A_ = rm_add A_;

fun rm_delete A_ = RBT.delete A_;

fun rm_lookup A_ k m = RBT.lookup A_ m k;

fun list_to_rm A_ = MapGA.gen_list_to_map (rm_empty A_) (rm_update A_);

fun rm_isEmpty (A1_, A2_) B_ m =
  HOL.eq (RBT_add.equal_rbt (A1_, A2_) B_) m (RBT.empty A2_);

fun rm_to_list A_ = MapGA.it_map_to_list (rm_reverse_iterateoi A_);

fun rm_update_dj A_ = rm_update A_;

end; (*struct RBTMapImpl*)

structure SetByMap : sig
  val s_ins : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val s_sel :
    ('a -> ('b * unit -> 'c option) -> 'c option) ->
      'a -> ('b -> 'c option) -> 'c option
  val s_memb : ('a -> 'b -> 'c option) -> 'a -> 'b -> bool
  val s_alpha : ('a -> 'b -> unit option) -> 'a -> 'b -> bool
  val s_ins_dj : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val s_iteratei :
    ('a -> ('b -> bool) -> ('c * unit -> 'b -> 'b) -> 'b -> 'b) ->
      'a -> ('b -> bool) -> ('c -> 'b -> 'b) -> 'b -> 'b
end = struct

fun s_ins update x s = update x () s;

fun s_sel sel s f = sel s (fn (u, _) => f u);

fun s_memb lookup x s = not (Option.is_none (lookup x s));

fun s_alpha alpha m = Map.dom (alpha m);

fun s_ins_dj update_dj x s = update_dj x () s;

fun s_iteratei it s c f = it s c (fn x => f (Product_Type.fst x));

end; (*struct SetByMap*)

structure RBTSetImpl : sig
  val rs_ins :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val rs_reverse_iterateoi :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rs_max :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a -> bool) -> 'a option
  val rs_iterateoi :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rs_min :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a -> bool) -> 'a option
  val rs_sel :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a -> 'b option) -> 'b option
  val rs_memb : 'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> bool
  val rs_sela :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a -> bool) -> 'a option
  val rs_alpha : 'a Orderings.linorder -> ('a, unit) RBT.rbt -> 'a -> bool
  val rs_empty : 'a Orderings.linorder -> unit -> ('a, unit) RBT.rbt
  val rs_iteratei :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val rs_image_filter :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a -> 'b option) -> ('a, unit) RBT.rbt -> ('b, unit) RBT.rbt
  val rs_image :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a -> 'b) -> ('a, unit) RBT.rbt -> ('b, unit) RBT.rbt
  val rs_ins_dj :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val rs_inter :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val rs_union :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val rs_delete :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val list_to_rs : 'a Orderings.linorder -> 'a list -> ('a, unit) RBT.rbt
  val rs_isEmpty :
    'a HOL.equal * 'a Orderings.linorder -> ('a, unit) RBT.rbt -> bool
  val rs_to_list : 'a Orderings.linorder -> ('a, unit) RBT.rbt -> 'a list
  val rs_union_dj :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
end = struct

fun rs_ins A_ = SetByMap.s_ins (RBTMapImpl.rm_update A_);

fun rs_reverse_iterateoi A_ =
  SetByMap.s_iteratei (RBTMapImpl.rm_reverse_iterateoi A_);

fun rs_max A_ = SetGA.iti_sel_no_map (rs_reverse_iterateoi A_);

fun rs_iterateoi A_ = SetByMap.s_iteratei (RBTMapImpl.rm_iterateoi A_);

fun rs_min A_ = SetGA.iti_sel_no_map (rs_iterateoi A_);

fun rs_sel A_ = SetByMap.s_sel (RBTMapImpl.rm_sel A_);

fun rs_memb A_ = SetByMap.s_memb (RBTMapImpl.rm_lookup A_);

fun rs_sela A_ = SetGA.sel_sel (rs_sel A_);

fun rs_alpha A_ = SetByMap.s_alpha (RBTMapImpl.rm_alpha A_);

fun rs_empty A_ = RBTMapImpl.rm_empty A_;

fun rs_iteratei A_ = SetByMap.s_iteratei (RBTMapImpl.rm_iteratei A_);

fun rs_image_filter A_ B_ =
  SetGA.it_image_filter (rs_iteratei A_) (rs_empty B_) (rs_ins B_);

fun rs_image A_ B_ = SetGA.iflt_image (rs_image_filter A_ B_);

fun rs_ins_dj A_ = SetByMap.s_ins_dj (RBTMapImpl.rm_update_dj A_);

fun rs_inter A_ =
  SetGA.it_inter (rs_iteratei A_) (rs_memb A_) (rs_empty A_) (rs_ins_dj A_);

fun rs_union A_ = RBTMapImpl.rm_add A_;

fun rs_delete A_ = RBTMapImpl.rm_delete A_;

fun list_to_rs A_ = SetGA.gen_list_to_set (rs_empty A_) (rs_ins A_);

fun rs_isEmpty (A1_, A2_) =
  RBTMapImpl.rm_isEmpty (A1_, A2_) Product_Type.equal_unit;

fun rs_to_list A_ = SetGA.it_set_to_list (rs_reverse_iterateoi A_);

fun rs_union_dj A_ = RBTMapImpl.rm_add_dj A_;

end; (*struct RBTSetImpl*)

structure ArrayMapImpl : sig
  val iam_increment : IntInf.int -> IntInf.int -> IntInf.int
  val iam_update :
    IntInf.int ->
      'a -> ('a option) STArray.IsabelleMapping.ArrayType ->
              ('a option) STArray.IsabelleMapping.ArrayType
  val iam_iteratei_aux :
    IntInf.int ->
      ('a option) STArray.IsabelleMapping.ArrayType ->
        ('b -> bool) -> (IntInf.int * 'a -> 'b -> 'b) -> 'b -> 'b
  val iam_iteratei :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      ('b -> bool) -> (IntInf.int * 'a -> 'b -> 'b) -> 'b -> 'b
  val iam_add :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      ('a option) STArray.IsabelleMapping.ArrayType ->
        ('a option) STArray.IsabelleMapping.ArrayType
  val iam_sel :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      (IntInf.int * 'a -> 'b option) -> 'b option
  val iam_sela :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      (IntInf.int * 'a -> bool) -> (IntInf.int * 'a) option
  val iam_alpha :
    ('a option) STArray.IsabelleMapping.ArrayType -> IntInf.int -> 'a option
  val iam_empty : unit -> ('a option) STArray.IsabelleMapping.ArrayType
  val iam_add_dj :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      ('a option) STArray.IsabelleMapping.ArrayType ->
        ('a option) STArray.IsabelleMapping.ArrayType
  val iam_delete :
    IntInf.int ->
      ('a option) STArray.IsabelleMapping.ArrayType ->
        ('a option) STArray.IsabelleMapping.ArrayType
  val iam_lookup :
    IntInf.int -> ('a option) STArray.IsabelleMapping.ArrayType -> 'a option
  val iam_isEmpty : ('a option) STArray.IsabelleMapping.ArrayType -> bool
  val iam_to_list :
    ('a option) STArray.IsabelleMapping.ArrayType -> (IntInf.int * 'a) list
  val list_to_iam :
    (IntInf.int * 'a) list -> ('a option) STArray.IsabelleMapping.ArrayType
  val iam_update_dj :
    IntInf.int ->
      'a -> ('a option) STArray.IsabelleMapping.ArrayType ->
              ('a option) STArray.IsabelleMapping.ArrayType
end = struct

fun iam_increment l idx =
  Orderings.max Arith.ord_nat
    (Arith.minus_nat (IntInf.+ (idx, (1 : IntInf.int))) l)
    (IntInf.+ (IntInf.* ((2 : IntInf.int), l), (3 : IntInf.int)));

fun iam_update k v a =
  let
    val l = STArray.IsabelleMapping.array_length a;
    val aa =
      (if IntInf.< (k, l) then a
        else STArray.IsabelleMapping.array_grow a (iam_increment l k) NONE);
  in
    STArray.IsabelleMapping.array_set aa k (SOME v)
  end;

fun iam_iteratei_aux v a c f sigma =
  (if ((v : IntInf.int) = (0 : IntInf.int)) then sigma
    else (if c sigma
           then iam_iteratei_aux
                  (Arith.minus_nat
                    (Arith.suc (Arith.minus_nat v (1 : IntInf.int)))
                    (1 : IntInf.int))
                  a c f
                  (case STArray.IsabelleMapping.array_get a
                          (Arith.minus_nat
                            (Arith.suc (Arith.minus_nat v (1 : IntInf.int)))
                            (1 : IntInf.int))
                    of NONE => sigma
                    | SOME x =>
                      f (Arith.minus_nat
                           (Arith.suc (Arith.minus_nat v (1 : IntInf.int)))
                           (1 : IntInf.int),
                          x)
                        sigma)
           else sigma));

fun iam_iteratei a =
  iam_iteratei_aux (STArray.IsabelleMapping.array_length a) a;

fun iam_add x = MapGA.it_add iam_update iam_iteratei x;

fun iam_sel x = MapGA.iti_sel iam_iteratei x;

fun iam_sela x = MapGA.iti_sel_no_map iam_iteratei x;

fun iam_alpha a i =
  (if IntInf.< (i, STArray.IsabelleMapping.array_length a)
    then STArray.IsabelleMapping.array_get a i else NONE);

fun iam_empty x = (fn _ => STArray.IsabelleMapping.array_of_list []) x;

fun iam_add_dj x = iam_add x;

fun iam_delete k a =
  (if IntInf.< (k, STArray.IsabelleMapping.array_length a)
    then STArray.IsabelleMapping.array_set a k NONE else a);

fun iam_lookup k a = iam_alpha a k;

fun iam_isEmpty x = MapGA.iti_isEmpty iam_iteratei x;

fun iam_to_list x = MapGA.it_map_to_list iam_iteratei x;

fun list_to_iam x = MapGA.gen_list_to_map iam_empty iam_update x;

fun iam_update_dj x = iam_update x;

end; (*struct ArrayMapImpl*)

structure StdInst : sig
  val rm_sng : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) RBT.rbt
  val rs_sng : 'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt
  val iam_sng :
    IntInf.int -> 'a -> ('a option) STArray.IsabelleMapping.ArrayType
  val rm_ball :
    'a Orderings.linorder -> ('a, 'b) RBT.rbt -> ('a * 'b -> bool) -> bool
  val rm_size : 'a Orderings.linorder -> ('a, 'b) RBT.rbt -> IntInf.int
  val rr_diff :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val rs_ball :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a -> bool) -> bool
  val rs_size : 'a Orderings.linorder -> ('a, unit) RBT.rbt -> IntInf.int
  val iam_ball :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      (IntInf.int * 'a -> bool) -> bool
  val iam_size : ('a option) STArray.IsabelleMapping.ArrayType -> IntInf.int
  val rm_isSng : 'a Orderings.linorder -> ('a, 'b) RBT.rbt -> bool
  val rr_subset :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> bool
  val rr_equal :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> bool
  val rs_isSng : 'a Orderings.linorder -> ('a, unit) RBT.rbt -> bool
  val iam_isSng : ('a option) STArray.IsabelleMapping.ArrayType -> bool
  val rr_inj_image_filter :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a -> 'b option) -> ('a, unit) RBT.rbt -> ('b, unit) RBT.rbt
  val rr_filter :
    'a Orderings.linorder ->
      ('a -> bool) -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val rm_bexists :
    'a Orderings.linorder -> ('a, 'b) RBT.rbt -> ('a * 'b -> bool) -> bool
  val rs_bexists :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a -> bool) -> bool
  val iam_bexists :
    ('a option) STArray.IsabelleMapping.ArrayType ->
      (IntInf.int * 'a -> bool) -> bool
  val rr_disjoint :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> bool
  val rr_restrict :
    'a Orderings.linorder ->
      ('a * 'b -> bool) -> ('a, 'b) RBT.rbt -> ('a, 'b) RBT.rbt
  val imim_restrict :
    (IntInf.int * 'a -> bool) ->
      ('a option) STArray.IsabelleMapping.ArrayType ->
        ('a option) STArray.IsabelleMapping.ArrayType
  val rm_size_abort :
    'a Orderings.linorder -> IntInf.int -> ('a, 'b) RBT.rbt -> IntInf.int
  val rs_size_abort :
    'a Orderings.linorder -> IntInf.int -> ('a, unit) RBT.rbt -> IntInf.int
  val iam_size_abort :
    IntInf.int -> ('a option) STArray.IsabelleMapping.ArrayType -> IntInf.int
  val rr_disjoint_witness :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> 'a option
end = struct

fun rm_sng A_ = MapGA.eu_sng (RBTMapImpl.rm_empty A_) (RBTMapImpl.rm_update A_);

fun rs_sng A_ = SetGA.ei_sng (RBTSetImpl.rs_empty A_) (RBTSetImpl.rs_ins A_);

fun iam_sng x = MapGA.eu_sng ArrayMapImpl.iam_empty ArrayMapImpl.iam_update x;

fun rm_ball A_ = MapGA.sel_ball (RBTMapImpl.rm_sel A_);

fun rm_size A_ = MapGA.it_size (RBTMapImpl.rm_iteratei A_);

fun rr_diff A_ =
  SetGA.it_diff (RBTSetImpl.rs_iteratei A_) (RBTSetImpl.rs_delete A_);

fun rs_ball A_ = SetGA.iti_ball (RBTSetImpl.rs_iteratei A_);

fun rs_size A_ = SetGA.it_size (RBTSetImpl.rs_iteratei A_);

fun iam_ball x = MapGA.sel_ball ArrayMapImpl.iam_sel x;

fun iam_size x = MapGA.it_size ArrayMapImpl.iam_iteratei x;

fun rm_isSng A_ = MapGA.sza_isSng (RBTMapImpl.rm_iteratei A_);

fun rr_subset A_ = SetGA.ball_subset (rs_ball A_) (RBTSetImpl.rs_memb A_);

fun rr_equal A_ = SetGA.subset_equal (rr_subset A_) (rr_subset A_);

fun rs_isSng A_ = SetGA.sza_isSng (RBTSetImpl.rs_iteratei A_);

fun iam_isSng x = MapGA.sza_isSng ArrayMapImpl.iam_iteratei x;

fun rr_inj_image_filter A_ B_ =
  SetGA.it_image_filter (RBTSetImpl.rs_iteratei A_) (RBTSetImpl.rs_empty B_)
    (RBTSetImpl.rs_ins_dj B_);

fun rr_filter A_ = SetGA.iflt_filter (rr_inj_image_filter A_ A_);

fun rm_bexists A_ = MapGA.neg_ball_bexists (rm_ball A_);

fun rs_bexists A_ = SetGA.neg_ball_bexists (rs_ball A_);

fun iam_bexists x = MapGA.neg_ball_bexists iam_ball x;

fun rr_disjoint A_ = SetGA.ball_disjoint (rs_ball A_) (RBTSetImpl.rs_memb A_);

fun rr_restrict A_ =
  MapGA.it_map_restrict (RBTMapImpl.rm_iteratei A_) (RBTMapImpl.rm_empty A_)
    (RBTMapImpl.rm_update_dj A_);

fun imim_restrict x =
  MapGA.it_map_restrict ArrayMapImpl.iam_iteratei ArrayMapImpl.iam_empty
    ArrayMapImpl.iam_update_dj x;

fun rm_size_abort A_ = MapGA.iti_size_abort (RBTMapImpl.rm_iteratei A_);

fun rs_size_abort A_ = SetGA.iti_size_abort (RBTSetImpl.rs_iteratei A_);

fun iam_size_abort x = MapGA.iti_size_abort ArrayMapImpl.iam_iteratei x;

fun rr_disjoint_witness A_ =
  SetGA.sel_disjoint_witness (RBTSetImpl.rs_sel A_) (RBTSetImpl.rs_memb A_);

end; (*struct StdInst*)

structure Workset : sig
  val worklist :
    ('a -> bool) -> ('a -> 'b -> 'a * 'b list) -> 'a * 'b list -> 'a * 'b list
end = struct

fun worklist b f (s, e :: wl) =
  (if b s then let
                 val (sa, n) = f s e;
               in
                 worklist b f (sa, n @ wl)
               end
    else (s, e :: wl))
  | worklist b f (s, []) = (s, []);

end; (*struct Workset*)

structure NFAByLTS : sig
  datatype 'a nfa_props_ext = Nfa_props_ext of bool * bool * 'a
  val fields : bool -> bool -> unit nfa_props_ext
  val hopcroft_class_map_alpha_impl :
    (IntInf.int -> 'a option) -> IntInf.int -> IntInf.int -> 'a list
  val nfa_prop_is_initially_connected : 'a nfa_props_ext -> bool
  val nfa_prop_is_complete_deterministic : 'a nfa_props_ext -> bool
end = struct

datatype 'a nfa_props_ext = Nfa_props_ext of bool * bool * 'a;

fun fields nfa_prop_is_complete_deterministic nfa_prop_is_initially_connected =
  Nfa_props_ext
    (nfa_prop_is_complete_deterministic, nfa_prop_is_initially_connected, ());

fun hopcroft_class_map_alpha_impl pim l u =
  (if IntInf.<= (l, u)
    then Option.the (pim l) :: hopcroft_class_map_alpha_impl pim (Arith.suc l) u
    else []);

fun nfa_prop_is_initially_connected
  (Nfa_props_ext
    (nfa_prop_is_complete_deterministic, nfa_prop_is_initially_connected, more))
  = nfa_prop_is_initially_connected;

fun nfa_prop_is_complete_deterministic
  (Nfa_props_ext
    (nfa_prop_is_complete_deterministic, nfa_prop_is_initially_connected, more))
  = nfa_prop_is_complete_deterministic;

end; (*struct NFAByLTS*)

structure Sum_Type : sig
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
end = struct

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

end; (*struct Sum_Type*)

structure ListIterator : sig
  val foldli : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

end; (*struct ListIterator*)

structure SetIteratorOperations : sig
  val set_iterator_emp : ('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a
  val set_iterator_sng : 'a -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun set_iterator_emp c f sigma_0 = sigma_0;

fun set_iterator_sng x c f sigma_0 =
  (if c sigma_0 then f x sigma_0 else sigma_0);

end; (*struct SetIteratorOperations*)

structure RBT_DLTSImpl : sig
  val rs_dlts_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, 'c) RBT.rbt) RBT.rbt ->
        ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val rs_dlts_add :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      'a -> 'b -> 'a -> ('a, ('b, 'a) RBT.rbt) RBT.rbt ->
                          ('a, ('b, 'a) RBT.rbt) RBT.rbt
  val rs_dlts_empty :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      unit -> ('a, ('b, 'a) RBT.rbt) RBT.rbt
  val rs_dlts_succ_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, 'a) RBT.rbt) RBT.rbt ->
        'a -> 'b -> ('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c
  val rs_dlts_filter_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('c -> bool) ->
            ('a * ('b * 'c) -> bool) ->
              ('a, ('b, 'c) RBT.rbt) RBT.rbt ->
                ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val rs_dlts_succ_label_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, 'a) RBT.rbt) RBT.rbt ->
        'a -> ('c -> bool) -> ('b * 'a -> 'c -> 'c) -> 'c -> 'c
end = struct

fun rs_dlts_it A_ B_ =
  (fn m1 => fn c => fn f =>
    RBTMapImpl.rm_iteratei A_ m1 c
      (fn (v1, m2) =>
        RBTMapImpl.rm_iteratei B_ m2 c (fn (e, v2) => f (v1, (e, v2)))));

fun rs_dlts_add A_ B_ =
  (fn v => fn w => fn va => fn l =>
    (case RBTMapImpl.rm_lookup A_ v l
      of NONE => RBTMapImpl.rm_update A_ v (StdInst.rm_sng B_ w va) l
      | SOME m2 =>
        RBTMapImpl.rm_update A_ v (RBTMapImpl.rm_update B_ w va m2) l));

fun rs_dlts_empty A_ B_ = RBTMapImpl.rm_empty A_;

fun rs_dlts_succ_it A_ B_ =
  (fn m1 => fn v => fn e =>
    (case RBTMapImpl.rm_lookup A_ v m1
      of NONE => SetIteratorOperations.set_iterator_emp
      | SOME m2 =>
        (case RBTMapImpl.rm_lookup B_ e m2
          of NONE => SetIteratorOperations.set_iterator_emp
          | SOME a => SetIteratorOperations.set_iterator_sng a)));

fun rs_dlts_filter_it A_ B_ =
  (fn p_v1 => fn p_e => fn p_v2 => fn p => fn m1 => fn c => fn f =>
    RBTMapImpl.rm_iteratei A_ m1 c
      (fn (v1, m2) => fn sigma =>
        (if p_v1 v1
          then RBTMapImpl.rm_iteratei B_ m2 c
                 (fn (e, v2) => fn sigmaa =>
                   (if p_v2 v2 andalso (p_e e andalso p (v1, (e, v2)))
                     then f (v1, (e, v2)) sigmaa else sigmaa))
                 sigma
          else sigma)));

fun rs_dlts_succ_label_it A_ B_ =
  (fn m1 => fn v =>
    (case RBTMapImpl.rm_lookup A_ v m1
      of NONE => (fn _ => fn _ => fn sigma_0 => sigma_0)
      | SOME a => RBTMapImpl.rm_iteratei B_ a));

end; (*struct RBT_DLTSImpl*)

structure LTSByLTS_DLTS : sig
  datatype ('a, 'b) lTS_choice = Lts of 'a | Dlts of 'b
  val dltsbc_add :
    ('a -> 'b -> 'a -> 'c -> 'c) ->
      ('a -> 'b -> 'a -> 'd -> 'd) ->
        'a -> 'b -> 'a -> ('c, 'd) lTS_choice -> ('c, 'd) lTS_choice
  val ltsbc_emp_lts : (unit -> 'a) -> unit -> ('a, 'b) lTS_choice
  val ltsbc_emp_dlts : (unit -> 'a) -> unit -> ('b, 'a) lTS_choice
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
  val ltsbc_add_simple :
    ('a -> 'b -> 'a -> 'c -> 'c) ->
      ('d -> 'c) -> 'a -> 'b -> 'a -> ('c, 'd) lTS_choice -> ('c, 'd) lTS_choice
end = struct

datatype ('a, 'b) lTS_choice = Lts of 'a | Dlts of 'b;

fun dltsbc_add l_add d_add qa a q (Lts l) = Lts (l_add qa a q l)
  | dltsbc_add l_add d_add qa a q (Dlts d) = Dlts (d_add qa a q d);

fun ltsbc_emp_lts l_emp = (fn _ => Lts (l_emp ()));

fun ltsbc_emp_dlts d_emp = (fn _ => Dlts (d_emp ()));

fun ltsbc_filter_it l_it d_it p_qa p_a p_q p (Lts l) = l_it p_qa p_a p_q p l
  | ltsbc_filter_it l_it d_it p_qa p_a p_q p (Dlts d) = d_it p_qa p_a p_q p d;

fun ltsbc_add_simple l_add copy qa a q (Lts l) = Lts (l_add qa a q l)
  | ltsbc_add_simple l_add copy qa a q (Dlts d) = Lts (l_add qa a q (copy d));

end; (*struct LTSByLTS_DLTS*)

structure RecordMapImpl : sig
  val rm_ops :
    'a HOL.equal * 'a Orderings.linorder -> 'b HOL.equal ->
      ('a, 'b, ('a, 'b) RBT.rbt,
        ('a, 'b, ('a, 'b) RBT.rbt, unit) MapSpec.omap_ops_ext)
        MapSpec.map_ops_ext
  val iam_ops :
    (IntInf.int, 'a, (('a option) STArray.IsabelleMapping.ArrayType), unit)
      MapSpec.map_ops_ext
end = struct

fun rm_ops (A1_, A2_) B_ =
  MapSpec.Map_ops_ext
    (RBTMapImpl.rm_alpha A2_, (fn _ => true), RBTMapImpl.rm_empty A2_,
      StdInst.rm_sng A2_, RBTMapImpl.rm_lookup A2_, RBTMapImpl.rm_update A2_,
      RBTMapImpl.rm_update_dj A2_, RBTMapImpl.rm_delete A2_,
      StdInst.rr_restrict A2_, RBTMapImpl.rm_add A2_, RBTMapImpl.rm_add_dj A2_,
      RBTMapImpl.rm_isEmpty (A1_, A2_) B_, StdInst.rm_isSng A2_,
      StdInst.rm_ball A2_, StdInst.rm_bexists A2_, StdInst.rm_size A2_,
      StdInst.rm_size_abort A2_, RBTMapImpl.rm_sela A2_,
      RBTMapImpl.rm_to_list A2_, RBTMapImpl.list_to_rm A2_,
      MapSpec.Omap_ops_ext (RBTMapImpl.rm_min A2_, RBTMapImpl.rm_max A2_, ()));

val iam_ops :
  (IntInf.int, 'a, (('a option) STArray.IsabelleMapping.ArrayType), unit)
    MapSpec.map_ops_ext
  = MapSpec.Map_ops_ext
      (ArrayMapImpl.iam_alpha, (fn _ => true), ArrayMapImpl.iam_empty,
        StdInst.iam_sng, ArrayMapImpl.iam_lookup, ArrayMapImpl.iam_update,
        ArrayMapImpl.iam_update_dj, ArrayMapImpl.iam_delete,
        StdInst.imim_restrict, ArrayMapImpl.iam_add, ArrayMapImpl.iam_add_dj,
        ArrayMapImpl.iam_isEmpty, StdInst.iam_isSng, StdInst.iam_ball,
        StdInst.iam_bexists, StdInst.iam_size, StdInst.iam_size_abort,
        ArrayMapImpl.iam_sela, ArrayMapImpl.iam_to_list,
        ArrayMapImpl.list_to_iam, ());

end; (*struct RecordMapImpl*)

structure RecordSetImpl : sig
  val rs_ops :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, ('a, unit) RBT.rbt,
        ('a, ('a, unit) RBT.rbt, unit) SetSpec.oset_ops_ext)
        SetSpec.set_ops_ext
end = struct

fun rs_ops (A1_, A2_) =
  SetSpec.Set_ops_ext
    (RBTSetImpl.rs_alpha A2_, (fn _ => true), RBTSetImpl.rs_empty A2_,
      StdInst.rs_sng A2_, RBTSetImpl.rs_memb A2_, RBTSetImpl.rs_ins A2_,
      RBTSetImpl.rs_ins_dj A2_, RBTSetImpl.rs_delete A2_,
      RBTSetImpl.rs_isEmpty (A1_, A2_), StdInst.rs_isSng A2_,
      StdInst.rs_ball A2_, StdInst.rs_bexists A2_, StdInst.rs_size A2_,
      StdInst.rs_size_abort A2_, RBTSetImpl.rs_union A2_,
      RBTSetImpl.rs_union_dj A2_, StdInst.rr_diff A2_, StdInst.rr_filter A2_,
      RBTSetImpl.rs_inter A2_, StdInst.rr_subset A2_, StdInst.rr_equal A2_,
      StdInst.rr_disjoint A2_, StdInst.rr_disjoint_witness A2_,
      RBTSetImpl.rs_sela A2_, RBTSetImpl.rs_to_list A2_,
      RBTSetImpl.list_to_rs A2_,
      SetSpec.Oset_ops_ext (RBTSetImpl.rs_min A2_, RBTSetImpl.rs_max A2_, ()));

end; (*struct RecordSetImpl*)

structure SemiAutomaton : sig
  val states_enumerate_nat : IntInf.int -> IntInf.int
end = struct

fun states_enumerate_nat q = q;

end; (*struct SemiAutomaton*)

structure SetIteratorGA : sig
  val iterate_size :
    ((IntInf.int -> bool) ->
      ('a -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      IntInf.int
end = struct

fun iterate_size it = it (fn _ => true) (fn _ => Arith.suc) (0 : IntInf.int);

end; (*struct SetIteratorGA*)

structure RBT_TripleSetImpl : sig
  val rs_ts_it :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
        ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val rs_ts_add :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      'a -> 'b -> 'c -> ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
                          ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt
  val rs_ts_C_it :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
        'a -> 'b -> ('d -> bool) -> ('c -> 'd -> 'd) -> 'd -> 'd
  val rs_ts_BC_it :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
        'a -> ('d -> bool) -> ('b * 'c -> 'd -> 'd) -> 'd -> 'd
  val rs_ts_empty :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      unit -> ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt
  val rs_ts_filter_it :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('c -> bool) ->
            ('a * ('b * 'c) -> bool) ->
              ('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
                ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
end = struct

fun rs_ts_it A_ B_ C_ =
  (fn m1 => fn c => fn f =>
    RBTMapImpl.rm_iteratei A_ m1 c
      (fn (a, m2) =>
        RBTMapImpl.rm_iteratei B_ m2 c
          (fn (b, s3) =>
            RBTSetImpl.rs_iteratei C_ s3 c (fn ca => f (a, (b, ca))))));

fun rs_ts_add A_ B_ C_ =
  (fn v => fn w => fn va => fn l =>
    (case RBTMapImpl.rm_lookup A_ v l
      of NONE =>
        RBTMapImpl.rm_update A_ v (StdInst.rm_sng B_ w (StdInst.rs_sng C_ va)) l
      | SOME m2 =>
        (case RBTMapImpl.rm_lookup B_ w m2
          of NONE =>
            RBTMapImpl.rm_update A_ v
              (RBTMapImpl.rm_update B_ w (StdInst.rs_sng C_ va) m2) l
          | SOME s3 =>
            RBTMapImpl.rm_update A_ v
              (RBTMapImpl.rm_update B_ w (RBTSetImpl.rs_ins C_ va s3) m2) l)));

fun rs_ts_C_it A_ B_ C_ =
  (fn m1 => fn a => fn b =>
    (case RBTMapImpl.rm_lookup A_ a m1
      of NONE => (fn _ => fn _ => fn sigma_0 => sigma_0)
      | SOME m2 =>
        (case RBTMapImpl.rm_lookup B_ b m2
          of NONE => (fn _ => fn _ => fn sigma_0 => sigma_0)
          | SOME aa => RBTSetImpl.rs_iteratei C_ aa)));

fun rs_ts_BC_it A_ B_ C_ =
  (fn m1 => fn a =>
    (case RBTMapImpl.rm_lookup A_ a m1
      of NONE => (fn _ => fn _ => fn sigma_0 => sigma_0)
      | SOME m2 =>
        (fn c => fn f =>
          RBTMapImpl.rm_iteratei B_ m2 c
            (fn (b, s3) =>
              RBTSetImpl.rs_iteratei C_ s3 c (fn ca => f (b, ca))))));

fun rs_ts_empty A_ B_ C_ = RBTMapImpl.rm_empty A_;

fun rs_ts_filter_it A_ B_ C_ =
  (fn p_a => fn p_b => fn p_c => fn p => fn m1 => fn c => fn f =>
    RBTMapImpl.rm_iteratei A_ m1 c
      (fn (a, m2) => fn sigma =>
        (if p_a a
          then RBTMapImpl.rm_iteratei B_ m2 c
                 (fn (b, s3) => fn sigmaa =>
                   (if p_b b
                     then RBTSetImpl.rs_iteratei C_ s3 c
                            (fn ca => fn sigmab =>
                              (if p_c ca andalso p (a, (b, ca))
                                then f (a, (b, ca)) sigmab else sigmab))
                            sigmaa
                     else sigmaa))
                 sigma
          else sigma)));

end; (*struct RBT_TripleSetImpl*)

structure ListSetImpl_Sorted : sig
  val lss_ins : 'a HOL.equal * 'a Orderings.linorder -> 'a -> 'a list -> 'a list
  val lss_sng : 'a -> 'a list
  val lss_empty : unit -> 'a list
  val lss_iteratei : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val lss_union_list :
    'a HOL.equal * 'a Orderings.linorder -> ('a list) list -> 'a list
end = struct

fun lss_ins (A1_, A2_) x l =
  ListAdd.insertion_sort
    (A1_, (Orderings.ord_preorder o Orderings.preorder_order o
            Orderings.order_linorder)
            A2_)
    x l;

fun lss_sng x = [x];

fun lss_empty x = (fn _ => []) x;

fun lss_iteratei l = ListIterator.foldli l;

fun lss_union_list (A1_, A2_) l = ListAdd.merge_list (A1_, A2_) [] l;

end; (*struct ListSetImpl_Sorted*)

structure RBT_LTS_DLTS_LTSImpl : sig
  val rs_dlts_lts_copy :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, 'a) RBT.rbt) RBT.rbt ->
        ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt
  val rs_lts_dlts_succ :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
        ('a, ('b, 'a) RBT.rbt) RBT.rbt)
        LTSByLTS_DLTS.lTS_choice ->
        'a -> 'b -> 'a option
  val rs_lts_dlts_empty_lts :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      unit ->
        (('a, ('b, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt, 'd)
          LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_filter_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('a -> bool) ->
            ('a * ('b * 'a) -> bool) ->
              (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                LTSByLTS_DLTS.lTS_choice ->
                ('c -> bool) -> ('a * ('b * 'a) -> 'c -> 'c) -> 'c -> 'c
  val rs_lts_dlts_add_simple :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      'a -> 'b -> 'a -> (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                          ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                          LTSByLTS_DLTS.lTS_choice ->
                          (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                            ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                            LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_image_filter :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      'd Orderings.linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                  ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                  LTSByLTS_DLTS.lTS_choice ->
                  (('c, ('d, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                    ('c, ('d, 'c) RBT.rbt) RBT.rbt)
                    LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_image :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      'd Orderings.linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
          ('a, ('b, 'a) RBT.rbt) RBT.rbt)
          LTSByLTS_DLTS.lTS_choice ->
          (('c, ('d, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt,
            ('c, ('d, 'c) RBT.rbt) RBT.rbt)
            LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_reverse :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
        ('a, ('b, 'a) RBT.rbt) RBT.rbt)
        LTSByLTS_DLTS.lTS_choice ->
        (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
          ('a, ('b, 'a) RBT.rbt) RBT.rbt)
          LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_to_list :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
        ('a, ('b, 'a) RBT.rbt) RBT.rbt)
        LTSByLTS_DLTS.lTS_choice ->
        ('a * ('b * 'a)) list
  val rs_lts_dlts_add_dlts :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      'a -> 'b -> 'a -> (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                          ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                          LTSByLTS_DLTS.lTS_choice ->
                          (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                            ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                            LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_add_choice :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      bool ->
        'a -> 'b -> 'a -> (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                            ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                            LTSByLTS_DLTS.lTS_choice ->
                            (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                              ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                              LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_empty_dlts :
    'b Orderings.linorder -> 'c Orderings.linorder ->
      unit -> ('a, ('b, ('c, 'b) RBT.rbt) RBT.rbt) LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_image_filter_dlts :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      'd Orderings.linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                  ('a, ('b, 'a) RBT.rbt) RBT.rbt)
                  LTSByLTS_DLTS.lTS_choice ->
                  (('c, ('d, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                    ('c, ('d, 'c) RBT.rbt) RBT.rbt)
                    LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_image_dlts :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      'd Orderings.linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
          ('a, ('b, 'a) RBT.rbt) RBT.rbt)
          LTSByLTS_DLTS.lTS_choice ->
          (('c, ('d, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt,
            ('c, ('d, 'c) RBT.rbt) RBT.rbt)
            LTSByLTS_DLTS.lTS_choice
  val rs_lts_dlts_to_collect_list :
    'a HOL.equal * 'a Orderings.linorder -> 'b Orderings.linorder ->
      (('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt,
        ('a, ('b, 'a) RBT.rbt) RBT.rbt)
        LTSByLTS_DLTS.lTS_choice ->
        ('a * ('b list * 'a)) list
end = struct

fun rs_dlts_lts_copy A_ B_ =
  LTSGA.ltsga_copy (RBT_DLTSImpl.rs_dlts_it A_ B_)
    (RBT_TripleSetImpl.rs_ts_empty A_ B_ A_)
    (RBT_TripleSetImpl.rs_ts_add A_ B_ A_);

fun rs_lts_dlts_succ A_ B_ =
  (fn l => fn q => fn a =>
    (case l of LTSByLTS_DLTS.Lts aa => RBT_TripleSetImpl.rs_ts_C_it A_ B_ A_ aa
      | LTSByLTS_DLTS.Dlts aa => RBT_DLTSImpl.rs_dlts_succ_it A_ B_ aa)
      q
      a
      Option.is_none
      (fn x => fn _ => SOME x)
      NONE);

fun rs_lts_dlts_empty_lts A_ B_ C_ =
  LTSByLTS_DLTS.ltsbc_emp_lts (RBT_TripleSetImpl.rs_ts_empty A_ B_ C_);

fun rs_lts_dlts_filter_it A_ B_ =
  LTSByLTS_DLTS.ltsbc_filter_it (RBT_TripleSetImpl.rs_ts_filter_it A_ B_ A_)
    (RBT_DLTSImpl.rs_dlts_filter_it A_ B_);

fun rs_lts_dlts_add_simple A_ B_ =
  LTSByLTS_DLTS.ltsbc_add_simple (RBT_TripleSetImpl.rs_ts_add A_ B_ A_)
    (rs_dlts_lts_copy A_ B_);

fun rs_lts_dlts_image_filter A_ B_ C_ D_ =
  (fn f => fn p_v1 => fn p_e => fn p_v2 => fn p => fn l =>
    rs_lts_dlts_filter_it A_ B_ p_v1 p_e p_v2 p l (fn _ => true)
      (fn vev => fn la =>
        let
          val (v, (e, va)) = f vev;
        in
          rs_lts_dlts_add_simple C_ D_ v e va la
        end)
      (rs_lts_dlts_empty_lts C_ D_ C_ ()));

fun rs_lts_dlts_image A_ B_ C_ D_ =
  (fn f =>
    rs_lts_dlts_image_filter A_ B_ C_ D_ f (fn _ => true) (fn _ => true)
      (fn _ => true) (fn _ => true));

fun rs_lts_dlts_reverse A_ B_ =
  (fn l =>
    (case l of LTSByLTS_DLTS.Lts a => RBT_TripleSetImpl.rs_ts_it A_ B_ A_ a
      | LTSByLTS_DLTS.Dlts a => RBT_DLTSImpl.rs_dlts_it A_ B_ a)
      (fn _ => true)
      (fn (v, (e, va)) => rs_lts_dlts_add_simple A_ B_ va e v)
      (rs_lts_dlts_empty_lts A_ B_ A_ ()));

fun rs_lts_dlts_to_list A_ B_ =
  (fn x =>
    (case x of LTSByLTS_DLTS.Lts a => RBT_TripleSetImpl.rs_ts_it A_ B_ A_ a
      | LTSByLTS_DLTS.Dlts a => RBT_DLTSImpl.rs_dlts_it A_ B_ a)
      (fn _ => true)
      (fn a => fn b => a :: b)
      []);

fun rs_lts_dlts_add_dlts A_ B_ =
  LTSByLTS_DLTS.dltsbc_add (RBT_TripleSetImpl.rs_ts_add A_ B_ A_)
    (RBT_DLTSImpl.rs_dlts_add A_ B_);

fun rs_lts_dlts_add_choice A_ B_ b =
  (if b then rs_lts_dlts_add_dlts A_ B_ else rs_lts_dlts_add_simple A_ B_);

fun rs_lts_dlts_empty_dlts B_ C_ =
  LTSByLTS_DLTS.ltsbc_emp_dlts (RBT_DLTSImpl.rs_dlts_empty B_ C_);

fun rs_lts_dlts_image_filter_dlts A_ B_ C_ D_ =
  (fn f => fn p_v1 => fn p_e => fn p_v2 => fn p => fn l =>
    rs_lts_dlts_filter_it A_ B_ p_v1 p_e p_v2 p l (fn _ => true)
      (fn vev => fn la =>
        let
          val (v, (e, va)) = f vev;
        in
          rs_lts_dlts_add_dlts C_ D_ v e va la
        end)
      (rs_lts_dlts_empty_dlts C_ D_ ()));

fun rs_lts_dlts_image_dlts A_ B_ C_ D_ =
  (fn f =>
    rs_lts_dlts_image_filter_dlts A_ B_ C_ D_ f (fn _ => true) (fn _ => true)
      (fn _ => true) (fn _ => true));

fun rs_lts_dlts_to_collect_list (A1_, A2_) B_ =
  (fn l =>
    LTSGA.ltsga_list_to_collect_list A1_ A1_ (rs_lts_dlts_to_list A2_ B_ l));

end; (*struct RBT_LTS_DLTS_LTSImpl*)

structure While_Combinator : sig
  val while_option : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a option
  val whilea : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
end = struct

fun while_option b c s = (if b s then while_option b c (c s) else SOME s);

fun whilea b c s = Option.the (while_option b c s);

end; (*struct While_Combinator*)

structure Hopcroft_Minimisation : sig
  val sm_update :
    (IntInf.int, 'a, 'b, 'c) MapSpec.map_ops_ext ->
      ('a, 'd, 'e, 'f) MapSpec.map_ops_ext ->
        'd -> 'e -> 'b -> IntInf.int -> IntInf.int -> 'e
  val l_insert_impl :
    IntInf.int -> ('a * IntInf.int) list -> 'a list -> ('a * IntInf.int) list
  val hopcroft_code_step_compute_iM_swap_check :
    ('a, (IntInf.int * 'b), 'c, 'd) MapSpec.map_ops_ext ->
      ('e, 'a, 'f, 'g) MapSpec.map_ops_ext ->
        ('e, IntInf.int, 'h, 'i) MapSpec.map_ops_ext ->
          (IntInf.int, 'e, 'j, 'k) MapSpec.map_ops_ext ->
            ('a, IntInf.int, 'l, 'm) MapSpec.map_ops_ext ->
              ('n ->
                ('o -> bool) ->
                  ('e -> 'l * ('h * 'j) -> 'l * ('h * 'j)) -> 'l * 'p -> 'q) ->
                'p -> 'n -> 'c * ('f * 'r) -> 'q
  val hopcroft_code_step :
    ('a ->
      ('b -> bool) ->
        (IntInf.int * IntInf.int ->
          ('c * ('d * IntInf.int)) * ('e * IntInf.int) list ->
            ('c * ('d * IntInf.int)) * ('e * IntInf.int) list) ->
          ('c * ('d * 'f)) * 'g -> 'h * 'i) ->
      ('j ->
        ('k -> bool) ->
          ('l -> 'm * ('n * 'o) -> 'm * ('n * 'o)) ->
            'm * 'p -> 'a * ('q * 'o)) ->
        (IntInf.int, IntInf.int, 'm, 'r) MapSpec.map_ops_ext ->
          (IntInf.int, 'l, 'o, 's) MapSpec.map_ops_ext ->
            ('l, IntInf.int, 'n, 't) MapSpec.map_ops_ext ->
              ('l, IntInf.int, 'd, 'u) MapSpec.map_ops_ext ->
                (IntInf.int, (IntInf.int * IntInf.int), 'c, 'v)
                  MapSpec.map_ops_ext ->
                  'e list ->
                    'j -> 'c * ('d * 'f) -> 'g -> 'p -> ('h * 'i) * ('q * 'o)
  val class_map_init_pred_code :
    'f Arith.zero ->
      ('a ->
        ('b -> bool) ->
          ('c -> ('d * 'e) * IntInf.int -> ('d * 'e) * IntInf.int) ->
            ('d * 'e) * 'f -> ('d * 'e) * 'f) ->
        ('c, IntInf.int, 'd, 'g) MapSpec.map_ops_ext ->
          (IntInf.int, 'c, 'e, 'h) MapSpec.map_ops_ext ->
            'a -> 'a -> ('d * 'e) * ('f * 'f)
  val hopcroft_code :
    (IntInf.int, IntInf.int, 'a, 'b) MapSpec.map_ops_ext ->
      ('c ->
        ('d -> bool) ->
          ('e -> 'a * ('f * 'g) -> 'a * ('f * 'g)) ->
            'a * ('f * 'g) -> 'h * ('f * 'g)) ->
        ('h ->
          ('i -> bool) ->
            (IntInf.int * IntInf.int ->
              ('j * ('k * IntInf.int)) * ('l * IntInf.int) list ->
                ('j * ('k * IntInf.int)) * ('l * IntInf.int) list) ->
              ('j * ('k * IntInf.int)) * ('l * IntInf.int) list ->
                ('j * ('k * IntInf.int)) * ('l * IntInf.int) list) ->
          ('m -> ('n -> bool) -> ('e -> 'k -> 'k) -> 'k -> 'k) ->
            ('e, IntInf.int, 'k, 'o) MapSpec.map_ops_ext ->
              (IntInf.int, (IntInf.int * IntInf.int), 'j, 'p)
                MapSpec.map_ops_ext ->
                (IntInf.int, 'e, 'g, 'q) MapSpec.map_ops_ext ->
                  ('e, IntInf.int, 'f, 'r) MapSpec.map_ops_ext ->
                    ('m ->
                      ('s -> bool) ->
                        ('e ->
                          ('f * 'g) * IntInf.int -> ('f * 'g) * IntInf.int) ->
                          ('f * 'g) * IntInf.int -> ('f * 'g) * IntInf.int) ->
                      ('t, 'm, 'u) SetSpec.set_ops_ext ->
                        'm -> 'm -> 'l list ->
                                      ('l ->
'g -> IntInf.int * IntInf.int -> 'c) ->
('j * ('k * IntInf.int)) * ('f * 'g)
end = struct

fun sm_update pim_ops sm_ops n sm pim p v =
  (if ((v : IntInf.int) = (0 : IntInf.int)) then sm
    else let
           val q = Option.the (MapSpec.map_op_lookup pim_ops p pim);
           val sma = MapSpec.map_op_update sm_ops q n sm;
         in
           sm_update pim_ops sm_ops n sma pim (Arith.suc p)
             (Arith.minus_nat (Arith.suc (Arith.minus_nat v (1 : IntInf.int)))
               (1 : IntInf.int))
         end);

fun l_insert_impl i l [] = l
  | l_insert_impl i l (a :: asa) = l_insert_impl i ((a, i) :: l) asa;

fun hopcroft_code_step_compute_iM_swap_check im_ops sm_ops pm_ops pim_ops iM_ops
  pre_it cm pre =
  (fn (im, (sm, _)) =>
    pre_it pre (fn _ => true)
      (fn q => fn (iM, (pm, pim)) =>
        let
          val i = Option.the (MapSpec.map_op_lookup sm_ops q sm);
          val s =
            (case MapSpec.map_op_lookup iM_ops i iM
              of NONE =>
                let
                  val (l, _) = Option.the (MapSpec.map_op_lookup im_ops i im);
                in
                  l
                end
              | SOME s => s);
          val iq = Option.the (MapSpec.map_op_lookup pm_ops q pm);
          val iMa = MapSpec.map_op_update iM_ops i (Arith.suc s) iM;
        in
          (if ((iq : IntInf.int) = s) then (iMa, (pm, pim))
            else let
                   val qs = Option.the (MapSpec.map_op_lookup pim_ops s pim);
                   val pima =
                     MapSpec.map_op_update pm_ops qs iq
                       (MapSpec.map_op_update pm_ops q s pm);
                   val pma =
                     MapSpec.map_op_update pim_ops iq qs
                       (MapSpec.map_op_update pim_ops s q pim);
                 in
                   (iMa, (pima, pma))
                 end)
        end)
      (MapSpec.map_op_empty iM_ops (), cm));

fun hopcroft_code_step iM_it pre_it iM_ops pim_ops pm_ops sm_ops im_ops aL pre p
  l cm =
  let
    val (iM, cma) =
      hopcroft_code_step_compute_iM_swap_check im_ops sm_ops pm_ops pim_ops
        iM_ops pre_it cm pre p;
    val (pa, la) =
      iM_it iM (fn _ => true)
        (fn (pa, s) => fn (a, b) =>
          let
            val (im, (sm, n)) = a;
          in
            (fn la =>
              let
                val (pt, (pct, (pf, pcf))) =
                  let
                    val (lb, u) =
                      Option.the (MapSpec.map_op_lookup im_ops pa im);
                  in
                    ((lb, Arith.minus_nat s (1 : IntInf.int)),
                      (Arith.minus_nat s lb,
                        ((s, u), Arith.minus_nat (Arith.suc u) s)))
                  end;
              in
                (if ((pcf : IntInf.int) = (0 : IntInf.int))
                  then ((im, (sm, n)), la)
                  else let
                         val (pmin, pmax) =
                           (if IntInf.< (pcf, pct) then (pf, pt) else (pt, pf));
                         val lb = l_insert_impl n la aL;
                         val pb =
                           (MapSpec.map_op_update im_ops n pmin
                              (MapSpec.map_op_update im_ops pa pmax im),
                             (sm_update pim_ops sm_ops n sm
                                (Product_Type.snd cma) (Product_Type.fst pmin)
                                (Arith.minus_nat
                                  (Arith.suc (Product_Type.snd pmin))
                                  (Product_Type.fst pmin)),
                               Arith.suc n));
                       in
                         (pb, lb)
                       end)
              end)
          end
            b)
        (p, l);
  in
    ((pa, la), cma)
  end;

fun class_map_init_pred_code F_ cm_it pm_ops pim_ops qf f =
  let
    val cm0 = (MapSpec.map_op_empty pm_ops (), MapSpec.map_op_empty pim_ops ());
    val (cm1, s) =
      cm_it qf (fn _ => true)
        (fn q => fn (a, b) =>
          let
            val (pm, pim) = a;
          in
            (fn i =>
              ((MapSpec.map_op_update pm_ops q i pm,
                 MapSpec.map_op_update pim_ops i q pim),
                Arith.suc i))
          end
            b)
        (cm0, Arith.zero F_);
    val (cm2, m) =
      cm_it f (fn _ => true)
        (fn q => fn (a, b) =>
          let
            val (pm, pim) = a;
          in
            (fn i =>
              ((MapSpec.map_op_update pm_ops q i pm,
                 MapSpec.map_op_update pim_ops i q pim),
                Arith.suc i))
          end
            b)
        (cm1, s);
  in
    (cm2, (s, m))
  end;

fun hopcroft_code iM_ops pre_it iM_it sm_it sm_ops im_ops pim_ops pm_ops cm_it
  s_ops q f al pre_fun =
  let
    val x = SetSpec.set_op_diff s_ops q f;
    val (a, (aa, ba)) =
      class_map_init_pred_code Arith.zero_nat cm_it pm_ops pim_ops x f;
  in
    (if ((ba : IntInf.int) = (0 : IntInf.int))
      then ((MapSpec.map_op_empty im_ops (),
              (MapSpec.map_op_empty sm_ops (), (0 : IntInf.int))),
             a)
      else (if ((ba : IntInf.int) = aa)
             then ((MapSpec.map_op_sng im_ops (0 : IntInf.int)
                      ((0 : IntInf.int), Arith.minus_nat ba (1 : IntInf.int)),
                     (sm_it q (fn _ => true)
                        (fn qa =>
                          MapSpec.map_op_update sm_ops qa (0 : IntInf.int))
                        (MapSpec.map_op_empty sm_ops ()),
                       (1 : IntInf.int))),
                    a)
             else let
                    val ((ac, _), bb) =
                      While_Combinator.whilea
                        (fn pl =>
                          not (List.null
                                (Product_Type.snd (Product_Type.fst pl))))
                        (fn ((ac, bc), (ad, bd)) =>
                          let
                            val (ae, be) = List.hd bc;
                            val xd =
                              pre_fun ae bd
                                (Option.the
                                  (MapSpec.map_op_lookup im_ops be
                                    (Product_Type.fst ac)));
                            val (ab, b) =
                              hopcroft_code_step iM_it pre_it iM_ops pim_ops
                                pm_ops sm_ops im_ops al xd ac (List.tl bc)
                                (ad, bd);
                          in
                            (ab, b)
                          end)
                        (((if ((aa : IntInf.int) = (0 : IntInf.int))
                            then (MapSpec.map_op_sng im_ops (0 : IntInf.int)
                                    ((0 : IntInf.int),
                                      Arith.minus_nat ba (1 : IntInf.int)),
                                   (sm_it q (fn _ => true)
                                      (fn qa =>
MapSpec.map_op_update sm_ops qa (0 : IntInf.int))
                                      (MapSpec.map_op_empty sm_ops ()),
                                     (1 : IntInf.int)))
                            else (MapSpec.map_op_update im_ops
                                    (Arith.suc (0 : IntInf.int))
                                    ((0 : IntInf.int),
                                      Arith.minus_nat aa (1 : IntInf.int))
                                    (MapSpec.map_op_sng im_ops (0 : IntInf.int)
                                      (aa,
Arith.minus_nat ba (1 : IntInf.int))),
                                   (sm_it f (fn _ => true)
                                      (fn qa =>
MapSpec.map_op_update sm_ops qa (0 : IntInf.int))
                                      (sm_it x (fn _ => true)
 (fn qa => MapSpec.map_op_update sm_ops qa (1 : IntInf.int))
(MapSpec.map_op_empty sm_ops ())),
                                     (2 : IntInf.int)))),
                           l_insert_impl (0 : IntInf.int) [] al),
                          a);
                  in
                    (ac, bb)
                  end))
  end;

end; (*struct Hopcroft_Minimisation*)

structure RBT_NFAImpl : sig
  val rs_nfa_props :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        unit NFAByLTS.nfa_props_ext
  val rs_nfa_accept_dfa :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        'a list -> bool
  val rs_nfa_accept_nfa :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        'a list -> bool
  val rs_nfa_accept :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        'a list -> bool
  val rs_hop_lts_add :
    'a Orderings.linorder ->
      IntInf.int ->
        'a -> IntInf.int ->
                ('a, (((IntInf.int list) option)
                       STArray.IsabelleMapping.ArrayType))
                  RBT.rbt ->
                  ('a, (((IntInf.int list) option)
                         STArray.IsabelleMapping.ArrayType))
                    RBT.rbt
  val rs_nfa_reverse :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_hop_lts_copy : 'a -> 'a
  val rs_hop_lts_get_succs :
    'a Orderings.linorder ->
      ('a, (((IntInf.int list) option) STArray.IsabelleMapping.ArrayType))
        RBT.rbt ->
        IntInf.int list -> 'a -> IntInf.int list
  val rs_nfa_rename_states_dfa :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int -> IntInf.int) ->
          (IntInf.int, unit) RBT.rbt *
            (('a, unit) RBT.rbt *
              (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                 (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                 LTSByLTS_DLTS.lTS_choice *
                ((IntInf.int, unit) RBT.rbt *
                  ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_Hopcroft :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_destruct :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int list *
          ('a list *
            ((IntInf.int * ('a list * IntInf.int)) list *
              (IntInf.int list * IntInf.int list)))
  val rs_nfa_final_no :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int
  val rs_nfa_trans_no :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int
  val rs_nfa_construct_gen :
    'a Orderings.linorder ->
      unit NFAByLTS.nfa_props_ext ->
        IntInf.int list *
          ('a list *
            ((IntInf.int * ('a list * IntInf.int)) list *
              (IntInf.int list * IntInf.int list))) ->
          (IntInf.int, unit) RBT.rbt *
            (('a, unit) RBT.rbt *
              (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                 (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                 LTSByLTS_DLTS.lTS_choice *
                ((IntInf.int, unit) RBT.rbt *
                  ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_dfa_construct :
    'a Orderings.linorder ->
      IntInf.int list *
        ('a list *
          ((IntInf.int * ('a list * IntInf.int)) list *
            (IntInf.int list * IntInf.int list))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_dfa_construct_reachable :
    'b Orderings.linorder -> 'c Orderings.linorder ->
      bool ->
        ('a -> 'b) ->
          'a list ->
            ('c, unit) RBT.rbt ->
              ('a -> bool) ->
                ('a ->
                  ((('b, IntInf.int) RBT.rbt * IntInf.int) *
                     (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                         RBT.rbt,
                        (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                        LTSByLTS_DLTS.lTS_choice *
                       'a list) ->
                    bool) ->
                    ('c * 'a ->
                      (('b, IntInf.int) RBT.rbt * IntInf.int) *
                        (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                            RBT.rbt,
                           (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                           LTSByLTS_DLTS.lTS_choice *
                          'a list) ->
                        (('b, IntInf.int) RBT.rbt * IntInf.int) *
                          (((IntInf.int,
                              ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                              RBT.rbt,
                             (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                             LTSByLTS_DLTS.lTS_choice *
                            'a list)) ->
                      (('b, IntInf.int) RBT.rbt * IntInf.int) *
                        (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                            RBT.rbt,
                           (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                           LTSByLTS_DLTS.lTS_choice *
                          'd list) ->
                        (('b, IntInf.int) RBT.rbt * IntInf.int) *
                          (((IntInf.int,
                              ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                              RBT.rbt,
                             (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                             LTSByLTS_DLTS.lTS_choice *
                            'a list)) ->
                  (IntInf.int, unit) RBT.rbt *
                    (('c, unit) RBT.rbt *
                      (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                          RBT.rbt,
                         (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                         LTSByLTS_DLTS.lTS_choice *
                        ((IntInf.int, unit) RBT.rbt *
                          ((IntInf.int, unit) RBT.rbt *
                            unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_bool_comb_gen :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt ->
        (bool -> bool -> bool) ->
          (IntInf.int, unit) RBT.rbt *
            (('a, unit) RBT.rbt *
              (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                 (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                 LTSByLTS_DLTS.lTS_choice *
                ((IntInf.int, unit) RBT.rbt *
                  ((IntInf.int, unit) RBT.rbt *
                    unit NFAByLTS.nfa_props_ext)))) ->
            (IntInf.int, unit) RBT.rbt *
              (('a, unit) RBT.rbt *
                (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                    RBT.rbt,
                   (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                   LTSByLTS_DLTS.lTS_choice *
                  ((IntInf.int, unit) RBT.rbt *
                    ((IntInf.int, unit) RBT.rbt *
                      unit NFAByLTS.nfa_props_ext)))) ->
              (IntInf.int, unit) RBT.rbt *
                (('a, unit) RBT.rbt *
                  (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                      RBT.rbt,
                     (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                     LTSByLTS_DLTS.lTS_choice *
                    ((IntInf.int, unit) RBT.rbt *
                      ((IntInf.int, unit) RBT.rbt *
                        unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_bool_comb :
    'a Orderings.linorder ->
      (bool -> bool -> bool) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
          (IntInf.int, unit) RBT.rbt *
            (('a, unit) RBT.rbt *
              (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                 (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                 LTSByLTS_DLTS.lTS_choice *
                ((IntInf.int, unit) RBT.rbt *
                  ((IntInf.int, unit) RBT.rbt *
                    unit NFAByLTS.nfa_props_ext)))) ->
            (IntInf.int, unit) RBT.rbt *
              (('a, unit) RBT.rbt *
                (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                    RBT.rbt,
                   (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                   LTSByLTS_DLTS.lTS_choice *
                  ((IntInf.int, unit) RBT.rbt *
                    ((IntInf.int, unit) RBT.rbt *
                      unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_construct :
    'a Orderings.linorder ->
      IntInf.int list *
        ('a list *
          ((IntInf.int * ('a list * IntInf.int)) list *
            (IntInf.int list * IntInf.int list))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_labels_no :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int
  val rs_nfa_normalise :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_states_no :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int
  val rs_dfa_construct_reachable :
    'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a -> 'b) ->
        'a list ->
          ('c, unit) RBT.rbt ->
            ('a -> bool) ->
              ('a ->
                ((('b, IntInf.int) RBT.rbt * IntInf.int) *
                   (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                       RBT.rbt,
                      (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                      LTSByLTS_DLTS.lTS_choice *
                     'a list) ->
                  bool) ->
                  ('c * 'a ->
                    (('b, IntInf.int) RBT.rbt * IntInf.int) *
                      (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                          RBT.rbt,
                         (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                         LTSByLTS_DLTS.lTS_choice *
                        'a list) ->
                      (('b, IntInf.int) RBT.rbt * IntInf.int) *
                        (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                            RBT.rbt,
                           (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                           LTSByLTS_DLTS.lTS_choice *
                          'a list)) ->
                    (('b, IntInf.int) RBT.rbt * IntInf.int) *
                      (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                          RBT.rbt,
                         (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                         LTSByLTS_DLTS.lTS_choice *
                        'd list) ->
                      (('b, IntInf.int) RBT.rbt * IntInf.int) *
                        (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                            RBT.rbt,
                           (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                           LTSByLTS_DLTS.lTS_choice *
                          'a list)) ->
                (IntInf.int, unit) RBT.rbt *
                  (('c, unit) RBT.rbt *
                    (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                        RBT.rbt,
                       (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                       LTSByLTS_DLTS.lTS_choice *
                      ((IntInf.int, unit) RBT.rbt *
                        ((IntInf.int, unit) RBT.rbt *
                          unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_determinise :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_Brzozowski :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_complement :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_initial_no :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int
  val rs_nfa_Hopcroft_NFA :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_rename_labels_gen :
    'a Orderings.linorder ->
      bool ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
          'b -> ('a -> 'a) ->
                  (IntInf.int, unit) RBT.rbt *
                    ('b * (((IntInf.int,
                              ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                              RBT.rbt,
                             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                             LTSByLTS_DLTS.lTS_choice *
                            ((IntInf.int, unit) RBT.rbt *
                              ((IntInf.int, unit) RBT.rbt *
                                unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_rename_labels :
    'a Orderings.linorder ->
      bool ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
          ('a -> 'a) ->
            (IntInf.int, unit) RBT.rbt *
              (('a, unit) RBT.rbt *
                (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                    RBT.rbt,
                   (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                   LTSByLTS_DLTS.lTS_choice *
                  ((IntInf.int, unit) RBT.rbt *
                    ((IntInf.int, unit) RBT.rbt *
                      unit NFAByLTS.nfa_props_ext))))
  val rs_nfa_language_is_empty :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        bool
  val rs_nfa_language_is_subset :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
          bool
  val rs_nfa_language_is_eq :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
          bool
  val rs_nfa_destruct_simple :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        IntInf.int list *
          ('a list *
            ((IntInf.int * ('a * IntInf.int)) list *
              (IntInf.int list * IntInf.int list)))
  val rs_nfa_language_is_univ :
    'a Orderings.linorder ->
      (IntInf.int, unit) RBT.rbt *
        (('a, unit) RBT.rbt *
          (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
             (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
             LTSByLTS_DLTS.lTS_choice *
            ((IntInf.int, unit) RBT.rbt *
              ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
        bool
  val rs_nfa_right_quotient_lists :
    'a Orderings.linorder ->
      ('a -> bool) ->
        (IntInf.int, unit) RBT.rbt *
          (('a, unit) RBT.rbt *
            (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
               (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext)))) ->
          (IntInf.int, unit) RBT.rbt *
            (('a, unit) RBT.rbt *
              (((IntInf.int, ('a, (IntInf.int, unit) RBT.rbt) RBT.rbt) RBT.rbt,
                 (IntInf.int, ('a, IntInf.int) RBT.rbt) RBT.rbt)
                 LTSByLTS_DLTS.lTS_choice *
                ((IntInf.int, unit) RBT.rbt *
                  ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_dfa_construct_reachable_fun :
    'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a -> 'b) ->
        'a -> ('c, unit) RBT.rbt ->
                ('a -> bool) ->
                  ('a -> 'c -> 'a) ->
                    (IntInf.int, unit) RBT.rbt *
                      (('c, unit) RBT.rbt *
                        (((IntInf.int, ('c, (IntInf.int, unit) RBT.rbt) RBT.rbt)
                            RBT.rbt,
                           (IntInf.int, ('c, IntInf.int) RBT.rbt) RBT.rbt)
                           LTSByLTS_DLTS.lTS_choice *
                          ((IntInf.int, unit) RBT.rbt *
                            ((IntInf.int, unit) RBT.rbt *
                              unit NFAByLTS.nfa_props_ext))))
end = struct

fun rs_nfa_props A_ (q, (a, (d, (i, (f, flags))))) = flags;

fun rs_nfa_accept_dfa A_ =
  (fn (_, (_, (d, (i, (f, _))))) => fn w =>
    StdInst.rs_bexists Arith.linorder_nat i
      (fn q =>
        (case ListIterator.foldli w (fn q_opt => not (Option.is_none q_opt))
                (fn sigma => fn q_opt =>
                  RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_succ Arith.linorder_nat A_ d
                    (Option.the q_opt) sigma)
                (SOME q)
          of NONE => false
          | SOME qa => RBTSetImpl.rs_memb Arith.linorder_nat qa f)));

fun rs_nfa_accept_nfa A_ =
  (fn (_, (_, (d, (i, (f, _))))) => fn w =>
    not (StdInst.rr_disjoint Arith.linorder_nat
          (List.foldl
            (fn q => fn a =>
              RBTSetImpl.rs_iteratei Arith.linorder_nat q (fn _ => true)
                (fn qa =>
                  (case d
                    of LTSByLTS_DLTS.Lts aa =>
                      RBT_TripleSetImpl.rs_ts_C_it Arith.linorder_nat A_
                        Arith.linorder_nat aa
                    | LTSByLTS_DLTS.Dlts aa =>
                      RBT_DLTSImpl.rs_dlts_succ_it Arith.linorder_nat A_ aa)
                    qa
                    a
                    (fn _ => true)
                    (RBTSetImpl.rs_ins Arith.linorder_nat))
                (RBTSetImpl.rs_empty Arith.linorder_nat ()))
            i w)
          f));

fun rs_nfa_accept A_ a w =
  (if NFAByLTS.nfa_prop_is_complete_deterministic (rs_nfa_props A_ a)
    then rs_nfa_accept_dfa A_ a w else rs_nfa_accept_nfa A_ a w);

fun rs_hop_lts_add A_ =
  (fn q => fn a => fn v => fn l =>
    (case RBTMapImpl.rm_lookup A_ a l
      of NONE =>
        RBTMapImpl.rm_update A_ a
          (StdInst.iam_sng q (ListSetImpl_Sorted.lss_sng v)) l
      | SOME m2 =>
        (case ArrayMapImpl.iam_lookup q m2
          of NONE =>
            RBTMapImpl.rm_update A_ a
              (ArrayMapImpl.iam_update q (ListSetImpl_Sorted.lss_sng v) m2) l
          | SOME s3 =>
            RBTMapImpl.rm_update A_ a
              (ArrayMapImpl.iam_update q
                (ListSetImpl_Sorted.lss_ins
                  (Arith.equal_nat, Arith.linorder_nat) v s3)
                m2)
              l)));

fun rs_nfa_reverse A_ =
  (fn (q, (a, (d, (i, (f, _))))) =>
    (q, (a, (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_reverse Arith.linorder_nat A_ d,
              (f, (i, NFAByLTS.fields false false))))));

fun rs_hop_lts_copy x = Fun.id x;

fun rs_hop_lts_get_succs A_ =
  (fn l => fn vs => fn a =>
    (case RBTMapImpl.rm_lookup A_ a l of NONE => ListSetImpl_Sorted.lss_empty ()
      | SOME im =>
        ListSetImpl_Sorted.lss_union_list (Arith.equal_nat, Arith.linorder_nat)
          (List.map_filter (fn q => ArrayMapImpl.iam_lookup q im) vs)));

fun rs_nfa_rename_states_dfa A_ (q, (a, (d, (i, (fa, p))))) f =
  (RBTSetImpl.rs_image Arith.linorder_nat Arith.linorder_nat f q,
    (a, (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_image_dlts Arith.linorder_nat A_
           Arith.linorder_nat A_ (fn (qb, (aa, qa)) => (f qb, (aa, f qa))) d,
          (RBTSetImpl.rs_image Arith.linorder_nat Arith.linorder_nat f i,
            (RBTSetImpl.rs_image Arith.linorder_nat Arith.linorder_nat f fa,
              NFAByLTS.fields true
                (NFAByLTS.nfa_prop_is_initially_connected p))))));

fun rs_nfa_Hopcroft A_ (q, (a, (d, (i, (f, p))))) =
  let
    val al = RBTSetImpl.rs_to_list A_ a;
    val rv_D =
      rs_hop_lts_copy
        (LTSGA.ltsga_reverse (RBTMapImpl.rm_empty A_) (rs_hop_lts_add A_)
          (fn aa =>
            (case aa
              of LTSByLTS_DLTS.Lts ab =>
                RBT_TripleSetImpl.rs_ts_it Arith.linorder_nat A_
                  Arith.linorder_nat ab
              | LTSByLTS_DLTS.Dlts ab =>
                RBT_DLTSImpl.rs_dlts_it Arith.linorder_nat A_ ab))
          d);
    val pre_fun =
      (fn aa => fn pim => fn (l, u) =>
        rs_hop_lts_get_succs A_ rv_D
          (NFAByLTS.hopcroft_class_map_alpha_impl
            (fn ia => ArrayMapImpl.iam_lookup ia pim) l u)
          aa);
    val (b, c) =
      Hopcroft_Minimisation.hopcroft_code
        (RecordMapImpl.rm_ops (Arith.equal_nat, Arith.linorder_nat)
          Arith.equal_nat)
        ListSetImpl_Sorted.lss_iteratei
        (RBTMapImpl.rm_iteratei Arith.linorder_nat)
        (RBTSetImpl.rs_iteratei Arith.linorder_nat) RecordMapImpl.iam_ops
        RecordMapImpl.iam_ops RecordMapImpl.iam_ops RecordMapImpl.iam_ops
        (RBTSetImpl.rs_iteratei Arith.linorder_nat)
        (RecordSetImpl.rs_ops (Arith.equal_nat, Arith.linorder_nat)) q f al
        pre_fun;
  in
    let
      val (_, (sm, _)) = b;
    in
      (fn _ =>
        rs_nfa_rename_states_dfa A_ (q, (a, (d, (i, (f, p)))))
          (fn qa =>
            SemiAutomaton.states_enumerate_nat
              (Option.the (ArrayMapImpl.iam_lookup qa sm))))
    end
      c
  end;

fun rs_nfa_destruct A_ (q, (a, (d, (i, (f, p))))) =
  (RBTSetImpl.rs_to_list Arith.linorder_nat q,
    (RBTSetImpl.rs_to_list A_ a,
      (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_to_collect_list
         (Arith.equal_nat, Arith.linorder_nat) A_ d,
        (RBTSetImpl.rs_to_list Arith.linorder_nat i,
          RBTSetImpl.rs_to_list Arith.linorder_nat f))));

fun rs_nfa_final_no A_ (q, (a, (d, (i, (f, p))))) =
  StdInst.rs_size Arith.linorder_nat f;

fun rs_nfa_trans_no A_ (q, (a, (d, (i, (f, p))))) =
  SetIteratorGA.iterate_size
    (case d
      of LTSByLTS_DLTS.Lts aa =>
        RBT_TripleSetImpl.rs_ts_it Arith.linorder_nat A_ Arith.linorder_nat aa
      | LTSByLTS_DLTS.Dlts aa =>
        RBT_DLTSImpl.rs_dlts_it Arith.linorder_nat A_ aa);

fun rs_nfa_construct_gen A_ p (ql, (al, (dl, (il, fl)))) =
  List.foldl
    (fn (q, (a, (d, (i, (f, props))))) => fn (q1, (l, q2)) =>
      (RBTSetImpl.rs_ins Arith.linorder_nat q1
         (RBTSetImpl.rs_ins Arith.linorder_nat q2 q),
        (List.foldl (fn s => fn x => RBTSetImpl.rs_ins A_ x s) a l,
          (List.foldl
             (fn da => fn aa =>
               RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_add_simple Arith.linorder_nat A_
                 q1 aa q2 da)
             d l,
            (i, (f, props))))))
    (RBTSetImpl.list_to_rs Arith.linorder_nat (ql @ il @ fl),
      (RBTSetImpl.list_to_rs A_ al,
        (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_empty_dlts Arith.linorder_nat A_ (),
          (RBTSetImpl.list_to_rs Arith.linorder_nat il,
            (RBTSetImpl.list_to_rs Arith.linorder_nat fl, p)))))
    dl;

fun rs_dfa_construct A_ = rs_nfa_construct_gen A_ (NFAByLTS.fields true false);

fun rs_nfa_dfa_construct_reachable B_ C_ det ff i a fp d_it =
  let
    val (b, c) =
      List.foldl
        (fn (aa, b) =>
          let
            val (qm, n) = aa;
          in
            (fn is => fn q =>
              ((RBTMapImpl.rm_update_dj B_ (ff q)
                  (SemiAutomaton.states_enumerate_nat n) qm,
                 Arith.suc n),
                RBTSetImpl.rs_ins_dj Arith.linorder_nat
                  (SemiAutomaton.states_enumerate_nat n) is))
          end
            b)
        ((RBTMapImpl.rm_empty B_ (), (0 : IntInf.int)),
          RBTSetImpl.rs_empty Arith.linorder_nat ())
        i;
  in
    let
      val (qm, n) = b;
    in
      (fn is =>
        let
          val (aa, ba) =
            Workset.worklist (fn _ => true)
              (fn (aa, ba) =>
                let
                  val (qma, na) = aa;
                in
                  (fn (qs, (asa, (dd, (isa, (fs, p))))) => fn q =>
                    let
                      val r = Option.the (RBTMapImpl.rm_lookup B_ (ff q) qma);
                    in
                      (if RBTSetImpl.rs_memb Arith.linorder_nat r qs
                        then (((qma, na), (qs, (asa, (dd, (isa, (fs, p)))))),
                               [])
                        else let
                               val (ab, bb) =
                                 d_it q (fn _ => true)
                                   (fn (ab, qa) => fn (bb, ca) =>
                                     let
                                       val (qmb, nb) = bb;
                                     in
                                       (fn (dda, naa) =>
 let
   val r_opt = RBTMapImpl.rm_lookup B_ (ff qa) qmb;
   val (bc, cb) =
     (if Option.is_none r_opt
       then let
              val ra = SemiAutomaton.states_enumerate_nat nb;
            in
              ((RBTMapImpl.rm_update_dj B_ (ff qa) ra qmb, Arith.suc nb), ra)
            end
       else ((qmb, nb), Option.the r_opt));
 in
   let
     val (qmc, nc) = bc;
   in
     (fn ra =>
       ((qmc, nc),
         (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_add_choice Arith.linorder_nat C_ det
            r ab ra dda,
           qa :: naa)))
   end
     cb
 end)
                                     end
                                       ca)
                                   ((qma, na), (dd, []));
                             in
                               let
                                 val (qmb, nb) = ab;
                               in
                                 (fn (dda, ac) =>
                                   (((qmb, nb),
                                      (RBTSetImpl.rs_ins_dj Arith.linorder_nat r
 qs,
(asa, (dda, (isa, ((if fp q then RBTSetImpl.rs_ins_dj Arith.linorder_nat r fs
                     else fs),
                    p)))))),
                                     ac))
                               end
                                 bb
                             end)
                    end)
                end
                  ba)
              (((qm, n),
                 (RBTSetImpl.rs_empty Arith.linorder_nat (),
                   (a, (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_empty_dlts
                          Arith.linorder_nat C_ (),
                         (is, (RBTSetImpl.rs_empty Arith.linorder_nat (),
                                NFAByLTS.fields det true)))))),
                i);
        in
          let
            val (_, aaa) = aa;
          in
            (fn _ => aaa)
          end
            ba
        end)
    end
      c
  end;

fun rs_nfa_bool_comb_gen A_ a bc (q1, (a1, (d1, (i1, (f1, p1)))))
  (q2, (a2, (d2, (i2, (f2, p2))))) =
  rs_nfa_dfa_construct_reachable
    (Misc.linorder_prod (Arith.equal_nat, Arith.linorder_nat)
      (Arith.equal_nat, Arith.linorder_nat))
    A_ (NFAByLTS.nfa_prop_is_complete_deterministic p1 andalso
         NFAByLTS.nfa_prop_is_complete_deterministic p2)
    rs_hop_lts_copy
    (Enum.product (RBTSetImpl.rs_to_list Arith.linorder_nat i1)
      (RBTSetImpl.rs_to_list Arith.linorder_nat i2))
    a (fn (q1a, q2a) =>
        bc (RBTSetImpl.rs_memb Arith.linorder_nat q1a f1)
          (RBTSetImpl.rs_memb Arith.linorder_nat q2a f2))
    (fn (q1a, q2a) => fn c => fn f =>
      (case d1
        of LTSByLTS_DLTS.Lts aa =>
          RBT_TripleSetImpl.rs_ts_BC_it Arith.linorder_nat A_ Arith.linorder_nat
            aa
        | LTSByLTS_DLTS.Dlts aa =>
          RBT_DLTSImpl.rs_dlts_succ_label_it Arith.linorder_nat A_ aa)
        q1a
        c
        (fn (aa, q1b) =>
          (case d2
            of LTSByLTS_DLTS.Lts ab =>
              RBT_TripleSetImpl.rs_ts_C_it Arith.linorder_nat A_
                Arith.linorder_nat ab
            | LTSByLTS_DLTS.Dlts ab =>
              RBT_DLTSImpl.rs_dlts_succ_it Arith.linorder_nat A_ ab)
            q2a
            aa
            c
            (fn q2b => f (aa, (q1b, q2b)))));

fun rs_nfa_bool_comb A_ bc (q1, (a1, (d1, (i1, (f1, p1)))))
  (q2, (a2, (d2, (i2, (f2, p2))))) =
  rs_nfa_bool_comb_gen A_ a1 bc (q1, (a1, (d1, (i1, (f1, p1)))))
    (q2, (a2, (d2, (i2, (f2, p2)))));

fun rs_nfa_construct A_ = rs_nfa_construct_gen A_ (NFAByLTS.fields false false);

fun rs_nfa_labels_no A_ (q, (a, (d, (i, (f, p))))) = StdInst.rs_size A_ a;

fun rs_nfa_normalise A_ =
  (fn (q, (a, (d, (i, (f, p))))) =>
    (if NFAByLTS.nfa_prop_is_initially_connected p
      then (q, (a, (d, (i, (f, p)))))
      else rs_nfa_dfa_construct_reachable Arith.linorder_nat A_
             (NFAByLTS.nfa_prop_is_complete_deterministic p) rs_hop_lts_copy
             (RBTSetImpl.rs_to_list Arith.linorder_nat i) a
             (fn qa => RBTSetImpl.rs_memb Arith.linorder_nat qa f)
             (case d
               of LTSByLTS_DLTS.Lts aa =>
                 RBT_TripleSetImpl.rs_ts_BC_it Arith.linorder_nat A_
                   Arith.linorder_nat aa
               | LTSByLTS_DLTS.Dlts aa =>
                 RBT_DLTSImpl.rs_dlts_succ_label_it Arith.linorder_nat A_ aa)));

fun rs_nfa_states_no A_ (q, (a, (d, (i, (f, p))))) =
  StdInst.rs_size Arith.linorder_nat q;

fun rs_dfa_construct_reachable B_ C_ =
  rs_nfa_dfa_construct_reachable B_ C_ true;

fun rs_nfa_determinise A_ (q1, (a1, (d1, (i1, (f1, p1))))) =
  (if NFAByLTS.nfa_prop_is_initially_connected p1 andalso
        NFAByLTS.nfa_prop_is_complete_deterministic p1
    then (q1, (a1, (d1, (i1, (f1, p1)))))
    else let
           val re_map =
             Product_Type.fst
               (RBTSetImpl.rs_iteratei Arith.linorder_nat q1 (fn _ => true)
                 (fn q => fn (m, n) =>
                   (RBTMapImpl.rm_update_dj Arith.linorder_nat q n m,
                     IntInf.* ((2 : IntInf.int), n)))
                 (RBTMapImpl.rm_empty Arith.linorder_nat (), (1 : IntInf.int)));
         in
           rs_dfa_construct_reachable Arith.linorder_nat A_
             (fn q =>
               RBTSetImpl.rs_iteratei Arith.linorder_nat q (fn _ => true)
                 (fn qa => fn n =>
                   IntInf.+ (n, Option.the
                                  (RBTMapImpl.rm_lookup Arith.linorder_nat qa
                                    re_map)))
                 (0 : IntInf.int))
             [i1] a1 (fn q => not (StdInst.rr_disjoint Arith.linorder_nat q f1))
             (fn s => fn c => fn f =>
               RBTSetImpl.rs_iteratei A_ a1 c
                 (fn x =>
                   f (x, RBTSetImpl.rs_iteratei Arith.linorder_nat s
                           (fn _ => true)
                           (fn a =>
                             (case d1
                               of LTSByLTS_DLTS.Lts aa =>
                                 RBT_TripleSetImpl.rs_ts_C_it Arith.linorder_nat
                                   A_ Arith.linorder_nat aa
                               | LTSByLTS_DLTS.Dlts aa =>
                                 RBT_DLTSImpl.rs_dlts_succ_it Arith.linorder_nat
                                   A_ aa)
                               a
                               x
                               (fn _ => true)
                               (RBTSetImpl.rs_ins Arith.linorder_nat))
                           (RBTSetImpl.rs_empty Arith.linorder_nat ()))))
         end);

fun rs_nfa_Brzozowski A_ a =
  rs_nfa_determinise A_
    (rs_nfa_reverse A_ (rs_nfa_determinise A_ (rs_nfa_reverse A_ a)));

fun rs_nfa_complement A_ =
  (fn (q, (a, (d, (i, (f, p))))) =>
    (q, (a, (d, (i, (StdInst.rr_diff Arith.linorder_nat q f, p))))));

fun rs_nfa_initial_no A_ (q, (a, (d, (i, (f, p))))) =
  StdInst.rs_size Arith.linorder_nat i;

fun rs_nfa_Hopcroft_NFA A_ =
  (fn a => rs_nfa_Hopcroft A_ (rs_nfa_determinise A_ a));

fun rs_nfa_rename_labels_gen A_ det (q, (aa, (d, (i, (fa, p))))) a f =
  (q, (a, (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_image Arith.linorder_nat A_
             Arith.linorder_nat A_ (fn (qb, (ab, qa)) => (qb, (f ab, qa))) d,
            (i, (fa, NFAByLTS.fields det
                       (NFAByLTS.nfa_prop_is_initially_connected p))))));

fun rs_nfa_rename_labels A_ det =
  (fn (q, (a, (d, (i, f)))) => fn fa =>
    rs_nfa_rename_labels_gen A_ det (q, (a, (d, (i, f))))
      (RBTSetImpl.rs_image A_ A_ fa a) fa);

fun rs_nfa_language_is_empty A_ n =
  let
    val (_, (_, (_, (_, (f, _))))) = rs_nfa_normalise A_ n;
  in
    RBTSetImpl.rs_isEmpty (Arith.equal_nat, Arith.linorder_nat) f
  end;

fun rs_nfa_language_is_subset A_ a1 a2 =
  rs_nfa_language_is_empty A_
    (rs_nfa_bool_comb A_ (fn a => fn b => a andalso b) a1
      (rs_nfa_complement A_ (rs_nfa_determinise A_ a2)));

fun rs_nfa_language_is_eq A_ a1 a2 =
  rs_nfa_language_is_subset A_ a1 a2 andalso rs_nfa_language_is_subset A_ a2 a1;

fun rs_nfa_destruct_simple A_ (q, (a, (d, (i, (f, p))))) =
  (RBTSetImpl.rs_to_list Arith.linorder_nat q,
    (RBTSetImpl.rs_to_list A_ a,
      (RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_to_list Arith.linorder_nat A_ d,
        (RBTSetImpl.rs_to_list Arith.linorder_nat i,
          RBTSetImpl.rs_to_list Arith.linorder_nat f))));

fun rs_nfa_language_is_univ A_ a =
  rs_nfa_language_is_empty A_ (rs_nfa_complement A_ (rs_nfa_determinise A_ a));

fun rs_nfa_right_quotient_lists A_ ap (q, (a, (d, (i, (f, p))))) =
  let
    val m =
      RBT_LTS_DLTS_LTSImpl.rs_lts_dlts_filter_it Arith.linorder_nat A_
        (fn _ => true) ap (fn _ => true) (fn _ => true) d (fn _ => true)
        (fn (qb, (_, qa)) => fn m =>
          let
            val s =
              (case RBTMapImpl.rm_lookup Arith.linorder_nat qa m
                of NONE => RBTSetImpl.rs_empty Arith.linorder_nat ()
                | SOME s => s);
          in
            RBTMapImpl.rm_update Arith.linorder_nat qa
              (RBTSetImpl.rs_ins Arith.linorder_nat qb s) m
          end)
        (RBTMapImpl.rm_empty Arith.linorder_nat ());
    val fa =
      Product_Type.fst
        (Workset.worklist (fn _ => true)
          (fn s => fn e =>
            (if RBTSetImpl.rs_memb Arith.linorder_nat e s then (s, [])
              else (RBTSetImpl.rs_ins Arith.linorder_nat e s,
                     (case RBTMapImpl.rm_lookup Arith.linorder_nat e m
                       of NONE => []
                       | SOME aa =>
                         RBTSetImpl.rs_to_list Arith.linorder_nat aa))))
          (RBTSetImpl.rs_empty Arith.linorder_nat (),
            RBTSetImpl.rs_to_list Arith.linorder_nat f));
  in
    (q, (a, (d, (i, (fa, p)))))
  end;

fun rs_dfa_construct_reachable_fun B_ C_ ff i a fp d_fun =
  rs_dfa_construct_reachable B_ C_ ff [i] a fp
    (fn q => fn c => fn f =>
      RBTSetImpl.rs_iteratei C_ a c (fn x => f (x, d_fun q x)));

end; (*struct RBT_NFAImpl*)

structure Nat_Bijection : sig
  val triangle : IntInf.int -> IntInf.int
  val sum_encode : (IntInf.int, IntInf.int) Sum_Type.sum -> IntInf.int
  val int_encode : IntInf.int -> IntInf.int
  val prod_encode : IntInf.int * IntInf.int -> IntInf.int
end = struct

fun triangle n = Arith.div_nat (IntInf.* (n, Arith.suc n)) (2 : IntInf.int);

fun sum_encode x =
  (case x of Sum_Type.Inl a => IntInf.* ((2 : IntInf.int), a)
    | Sum_Type.Inr b => Arith.suc (IntInf.* ((2 : IntInf.int), b)));

fun int_encode i =
  sum_encode
    (if IntInf.<= ((0 : IntInf.int), i) then Sum_Type.Inl (IntInf.max (0, i))
      else Sum_Type.Inr
             (IntInf.max (0, (IntInf.- (IntInf.~ i, (1 : IntInf.int))))));

fun prod_encode x = (fn (m, n) => IntInf.+ (triangle (IntInf.+ (m, n)), m)) x;

end; (*struct Nat_Bijection*)

structure Presburger_Automata : sig
  datatype pf = Eq of IntInf.int list * IntInf.int |
    Le of IntInf.int list * IntInf.int | And of pf * pf | Or of pf * pf |
    Imp of pf * pf | Forall of pf | Exist of pf | Neg of pf
  datatype 'a bdd = Leaf of 'a | Branch of 'a bdd * 'a bdd
  val tr_lookup : (bool list) list -> IntInf.int -> IntInf.int -> bool
  val check_eq : IntInf.int bdd -> IntInf.int bdd -> (bool list) list -> bool
  val fold_map_idx :
    (IntInf.int -> 'a -> 'b -> 'a * 'c) ->
      IntInf.int -> 'a -> 'b list -> 'a * 'c list
  val iter :
    IntInf.int bdd list * bool list ->
      (bool list) list -> bool * (bool list) list
  val bv_or : bool list -> bool list -> bool list
  val fixpt :
    IntInf.int bdd list * bool list -> (bool list) list -> (bool list) list
  val map_index : ('a -> IntInf.int -> 'b) -> 'a list -> IntInf.int -> 'b list
  val rquot_ins : IntInf.int -> bool list -> bool list
  val rquot_empt : IntInf.int bdd list * bool list -> bool list
  val rquot_memb : IntInf.int -> bool list -> bool
  val bdd_lookup : 'a bdd -> bool list -> 'a
  val rquot_succs :
    IntInf.int bdd list * bool list ->
      IntInf.int -> IntInf.int -> IntInf.int list
  val rquot_dfs :
    IntInf.int bdd list * bool list -> IntInf.int -> IntInf.int -> bool list
  val nfa_accepting : bool list -> bool list -> bool
  val rquot :
    IntInf.int bdd list * bool list ->
      IntInf.int -> IntInf.int bdd list * bool list
  val make_bdd :
    (IntInf.int list -> 'a) -> IntInf.int -> IntInf.int list -> 'a bdd
  val dioph_ins :
    IntInf.int ->
      (IntInf.int option) list * IntInf.int list ->
        (IntInf.int option) list * IntInf.int list
  val dioph_empt :
    IntInf.int list -> IntInf.int -> (IntInf.int option) list * IntInf.int list
  val dioph_memb :
    IntInf.int -> (IntInf.int option) list * IntInf.int list -> bool
  val eval_dioph : IntInf.int list -> IntInf.int list -> IntInf.int
  val mk_nat_vecs : IntInf.int -> (IntInf.int list) list
  val dioph_succs :
    IntInf.int -> IntInf.int list -> IntInf.int -> IntInf.int list
  val dioph_dfs :
    IntInf.int ->
      IntInf.int list ->
        IntInf.int -> (IntInf.int option) list * IntInf.int list
  val eq_dfa :
    IntInf.int ->
      IntInf.int list -> IntInf.int -> IntInf.int bdd list * bool list
  val prod_ins :
    IntInf.int * IntInf.int ->
      ((IntInf.int option) list) list * (IntInf.int * IntInf.int) list ->
        ((IntInf.int option) list) list * (IntInf.int * IntInf.int) list
  val prod_empt :
    IntInf.int bdd list * bool list ->
      IntInf.int bdd list * bool list ->
        ((IntInf.int option) list) list * (IntInf.int * IntInf.int) list
  val prod_memb :
    IntInf.int * IntInf.int ->
      ((IntInf.int option) list) list * (IntInf.int * IntInf.int) list -> bool
  val bdd_binop : ('a -> 'b -> 'c) -> 'a bdd -> 'b bdd -> 'c bdd
  val add_leaves : 'a HOL.equal -> 'a bdd -> 'a list -> 'a list
  val prod_succs :
    IntInf.int bdd list * bool list ->
      IntInf.int bdd list * bool list ->
        IntInf.int * IntInf.int -> (IntInf.int * IntInf.int) list
  val prod_dfs :
    IntInf.int bdd list * bool list ->
      IntInf.int bdd list * bool list ->
        IntInf.int * IntInf.int ->
          ((IntInf.int option) list) list * (IntInf.int * IntInf.int) list
  val binop_dfa :
    (bool -> bool -> bool) ->
      IntInf.int bdd list * bool list ->
        IntInf.int bdd list * bool list -> IntInf.int bdd list * bool list
  val or_dfa :
    IntInf.int bdd list * bool list ->
      IntInf.int bdd list * bool list -> IntInf.int bdd list * bool list
  val accepts : ('a -> 'b -> 'a) -> ('a -> 'c) -> 'a -> 'b list -> 'c
  val and_dfa :
    IntInf.int bdd list * bool list ->
      IntInf.int bdd list * bool list -> IntInf.int bdd list * bool list
  val bdd_map : ('a -> 'b) -> 'a bdd -> 'b bdd
  val subsetbdd :
    (bool list) bdd list -> bool list -> (bool list) bdd -> (bool list) bdd
  val bddinsert : 'a bdd -> bool list -> 'a -> 'a bdd
  val subset_ins :
    bool list ->
      (IntInf.int option) bdd * (bool list) list ->
        (IntInf.int option) bdd * (bool list) list
  val subset_empt : (IntInf.int option) bdd * (bool list) list
  val subset_memb :
    bool list -> (IntInf.int option) bdd * (bool list) list -> bool
  val nfa_emptybdd : IntInf.int -> (bool list) bdd
  val subset_succs :
    (bool list) bdd list * bool list -> bool list -> (bool list) list
  val subset_dfs :
    (bool list) bdd list * bool list ->
      bool list -> (IntInf.int option) bdd * (bool list) list
  val nfa_startnode : (bool list) bdd list * bool list -> bool list
  val nfa_acceptinga : (bool list) bdd list * bool list -> bool list -> bool
  val det_nfa :
    (bool list) bdd list * bool list -> IntInf.int bdd list * bool list
  val imp_dfa :
    IntInf.int bdd list * bool list ->
      IntInf.int bdd list * bool list -> IntInf.int bdd list * bool list
  val make_tr : (IntInf.int -> 'a) -> IntInf.int -> IntInf.int -> 'a list
  val init_tr : IntInf.int bdd list * bool list -> (bool list) list
  val mk_eqcla :
    (IntInf.int option) list ->
      IntInf.int ->
        IntInf.int -> IntInf.int -> (bool list) list -> (IntInf.int option) list
  val mk_eqcl :
    (IntInf.int option) list ->
      IntInf.int list ->
        IntInf.int -> (bool list) list -> IntInf.int list * IntInf.int list
  val min_dfa :
    IntInf.int bdd list * bool list -> IntInf.int bdd list * bool list
  val dioph_ineq_succs :
    IntInf.int -> IntInf.int list -> IntInf.int -> IntInf.int list
  val dioph_ineq_dfs :
    IntInf.int ->
      IntInf.int list ->
        IntInf.int -> (IntInf.int option) list * IntInf.int list
  val ineq_dfa :
    IntInf.int ->
      IntInf.int list -> IntInf.int -> IntInf.int bdd list * bool list
  val negate_dfa :
    IntInf.int bdd list * bool list -> IntInf.int bdd list * bool list
  val nfa_of_dfa :
    IntInf.int bdd list * bool list -> (bool list) bdd list * bool list
  val quantify_bdd : IntInf.int -> (bool list) bdd -> (bool list) bdd
  val quantify_nfa :
    IntInf.int ->
      (bool list) bdd list * bool list -> (bool list) bdd list * bool list
  val dfa_of_pf : IntInf.int -> pf -> IntInf.int bdd list * bool list
  val dfa_trans :
    IntInf.int bdd list * bool list -> IntInf.int -> bool list -> IntInf.int
  val nat_of_bool : bool -> IntInf.int
  val dfa_accepting : IntInf.int bdd list * bool list -> IntInf.int -> bool
end = struct

datatype pf = Eq of IntInf.int list * IntInf.int |
  Le of IntInf.int list * IntInf.int | And of pf * pf | Or of pf * pf |
  Imp of pf * pf | Forall of pf | Exist of pf | Neg of pf;

datatype 'a bdd = Leaf of 'a | Branch of 'a bdd * 'a bdd;

fun tr_lookup x =
  (fn t => fn i => fn j =>
    (if ((i : IntInf.int) = j) then false
      else (if IntInf.< (j, i)
             then List.nth (List.nth t (Arith.minus_nat i (1 : IntInf.int))) j
             else List.nth (List.nth t (Arith.minus_nat j (1 : IntInf.int)))
                    i)))
    x;

fun check_eq (Leaf i) (Leaf j) t = not (tr_lookup t i j)
  | check_eq (Branch (l, r)) (Leaf i) t =
    check_eq l (Leaf i) t andalso check_eq r (Leaf i) t
  | check_eq (Leaf i) (Branch (l, r)) t =
    check_eq (Leaf i) l t andalso check_eq (Leaf i) r t
  | check_eq (Branch (l1, r1)) (Branch (l2, r2)) t =
    check_eq l1 l2 t andalso check_eq r1 r2 t;

fun fold_map_idx f i y [] = (y, [])
  | fold_map_idx f i y (x :: xs) =
    let
      val (ya, xa) = f i y x;
      val (yb, xsa) = fold_map_idx f (Arith.suc i) ya xs;
    in
      (yb, xa :: xsa)
    end;

fun iter x =
  (fn (bd, _) => fn t =>
    fold_map_idx
      (fn i =>
        fold_map_idx
          (fn j => fn c => fn b =>
            let
              val ba =
                b orelse not (check_eq (List.nth bd i) (List.nth bd j) t);
            in
              (c orelse not (Product_Type.equal_boola b ba), ba)
            end)
          (0 : IntInf.int))
      (1 : IntInf.int) false t)
    x;

fun bv_or [] [] = []
  | bv_or (x :: xs) (y :: ys) = (x orelse y) :: bv_or xs ys;

fun fixpt m t = (case iter m t of (true, t2) => fixpt m t2 | (false, t2) => t2);

fun map_index f [] n = []
  | map_index f (x :: xs) n = f x n :: map_index f xs (Arith.suc n);

fun rquot_ins x = (fn xa => fn l => List.list_update l xa true) x;

fun rquot_empt m = List.replicate (List.size_list (Product_Type.fst m)) false;

fun rquot_memb x = (fn xa => fn l => List.nth l xa) x;

fun bdd_lookup (Leaf x) bs = x
  | bdd_lookup (Branch (l, r)) (b :: bs) = bdd_lookup (if b then r else l) bs;

fun rquot_succs m =
  (fn n => fn x =>
    [bdd_lookup (List.nth (Product_Type.fst m) x) (List.replicate n false)]);

fun rquot_dfs m n x =
  DFS.gen_dfs (rquot_succs m n) rquot_ins rquot_memb (rquot_empt m) [x];

fun nfa_accepting [] bs = false
  | nfa_accepting (v :: va) [] = false
  | nfa_accepting (a :: asa) (b :: bs) =
    a andalso b orelse nfa_accepting asa bs;

fun rquot x =
  (fn (bd, asa) => fn v =>
    (bd, map_index (fn _ => fn n => nfa_accepting asa (rquot_dfs (bd, asa) v n))
           asa (0 : IntInf.int)))
    x;

fun make_bdd f n xs =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then Leaf (f xs)
    else Branch
           (make_bdd f (Arith.minus_nat n (1 : IntInf.int))
              (xs @ [(0 : IntInf.int)]),
             make_bdd f (Arith.minus_nat n (1 : IntInf.int))
               (xs @ [(1 : IntInf.int)])));

fun dioph_ins m =
  (fn (is, js) =>
    (List.list_update is (Nat_Bijection.int_encode m)
       (SOME (List.size_list js)),
      js @ [m]));

fun dioph_empt ks l =
  (List.replicate
     (IntInf.max (0,
       (IntInf.+ (IntInf.* ((2 : IntInf.int), Orderings.max Arith.ord_int
        (Arith.abs_int l)
        (List.listsum Arith.monoid_add_int
          (List.map Arith.abs_int ks))), (1 : IntInf.int)))))
     NONE,
    []);

fun dioph_memb m =
  (fn (is, _) =>
    not (Option.is_none (List.nth is (Nat_Bijection.int_encode m))));

fun eval_dioph (k :: ks) (x :: xs) =
  IntInf.+ (IntInf.* (k, x), eval_dioph ks xs)
  | eval_dioph [] xs = (0 : IntInf.int)
  | eval_dioph ks [] = (0 : IntInf.int);

fun mk_nat_vecs n =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then [[]]
    else let
           val yss = mk_nat_vecs (Arith.minus_nat n (1 : IntInf.int));
         in
           List.map (fn a => (0 : IntInf.int) :: a) yss @
             List.map (fn a => (1 : IntInf.int) :: a) yss
         end);

fun dioph_succs n ks m =
  List.map_filter
    (fn xs =>
      (if (((Arith.mod_int (eval_dioph ks xs)
              (2 : IntInf.int)) : IntInf.int) = (Arith.mod_int m
          (2 : IntInf.int)))
        then SOME (Arith.div_int (IntInf.- (m, eval_dioph ks xs))
                    (2 : IntInf.int))
        else NONE))
    (mk_nat_vecs n);

fun dioph_dfs n ks l =
  DFS.gen_dfs (dioph_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l];

fun eq_dfa n ks l =
  let
    val (is, js) = dioph_dfs n ks l;
  in
    (List.map
       (fn j =>
         make_bdd
           (fn xs =>
             (if (((Arith.mod_int (eval_dioph ks xs)
                     (2 : IntInf.int)) : IntInf.int) = (Arith.mod_int j
                 (2 : IntInf.int)))
               then Option.the
                      (List.nth is
                        (Nat_Bijection.int_encode
                          (Arith.div_int (IntInf.- (j, eval_dioph ks xs))
                            (2 : IntInf.int))))
               else List.size_list js))
           n [])
       js @
       [Leaf (List.size_list js)],
      List.map (fn j => ((j : IntInf.int) = (0 : IntInf.int))) js @ [false])
  end;

fun prod_ins x =
  (fn (i, j) => fn (tab, ps) =>
    (List.list_update tab i
       (List.list_update (List.nth tab i) j (SOME (List.size_list ps))),
      ps @ [(i, j)]))
    x;

fun prod_empt a b =
  (List.replicate (List.size_list (Product_Type.fst a))
     (List.replicate (List.size_list (Product_Type.fst b)) NONE),
    []);

fun prod_memb x =
  (fn (i, j) => fn (tab, _) =>
    not (Option.is_none (List.nth (List.nth tab i) j)))
    x;

fun bdd_binop f (Leaf x) (Leaf y) = Leaf (f x y)
  | bdd_binop f (Branch (l, r)) (Leaf y) =
    Branch (bdd_binop f l (Leaf y), bdd_binop f r (Leaf y))
  | bdd_binop f (Leaf x) (Branch (l, r)) =
    Branch (bdd_binop f (Leaf x) l, bdd_binop f (Leaf x) r)
  | bdd_binop f (Branch (l_1, r_1)) (Branch (l_2, r_2)) =
    Branch (bdd_binop f l_1 l_2, bdd_binop f r_1 r_2);

fun add_leaves A_ (Leaf x) xs = List.insert A_ x xs
  | add_leaves A_ (Branch (b, c)) xs = add_leaves A_ c (add_leaves A_ b xs);

fun prod_succs a b =
  (fn (i, j) =>
    add_leaves (Product_Type.equal_prod Arith.equal_nat Arith.equal_nat)
      (bdd_binop (fn aa => fn ba => (aa, ba)) (List.nth (Product_Type.fst a) i)
        (List.nth (Product_Type.fst b) j))
      []);

fun prod_dfs a b x =
  DFS.gen_dfs (prod_succs a b) prod_ins prod_memb (prod_empt a b) [x];

fun binop_dfa f a b =
  let
    val (tab, ps) = prod_dfs a b ((0 : IntInf.int), (0 : IntInf.int));
  in
    (List.map
       (fn (i, j) =>
         bdd_binop (fn k => fn l => Option.the (List.nth (List.nth tab k) l))
           (List.nth (Product_Type.fst a) i) (List.nth (Product_Type.fst b) j))
       ps,
      List.map
        (fn (i, j) =>
          f (List.nth (Product_Type.snd a) i) (List.nth (Product_Type.snd b) j))
        ps)
  end;

fun or_dfa x = binop_dfa (fn a => fn b => a orelse b) x;

fun accepts tr p s asa = p (List.foldl tr s asa);

fun and_dfa x = binop_dfa (fn a => fn b => a andalso b) x;

fun bdd_map f (Leaf a) = Leaf (f a)
  | bdd_map f (Branch (l, r)) = Branch (bdd_map f l, bdd_map f r);

fun subsetbdd [] [] bdd = bdd
  | subsetbdd (bdda :: bdds) (b :: bs) bdd =
    (if b then subsetbdd bdds bs (bdd_binop bv_or bdd bdda)
      else subsetbdd bdds bs bdd);

fun bddinsert (Leaf a) [] x = Leaf x
  | bddinsert (Leaf a) (w :: ws) x =
    (if w then Branch (Leaf a, bddinsert (Leaf a) ws x)
      else Branch (bddinsert (Leaf a) ws x, Leaf a))
  | bddinsert (Branch (l, r)) (w :: ws) x =
    (if w then Branch (l, bddinsert r ws x) else Branch (bddinsert l ws x, r));

fun subset_ins qs =
  (fn (bdd, qss) => (bddinsert bdd qs (SOME (List.size_list qss)), qss @ [qs]));

val subset_empt : (IntInf.int option) bdd * (bool list) list = (Leaf NONE, []);

fun subset_memb qs = (fn (bdd, _) => not (Option.is_none (bdd_lookup bdd qs)));

fun nfa_emptybdd n = Leaf (List.replicate n false);

fun subset_succs a qs =
  add_leaves (List.equal_list Product_Type.equal_bool)
    (subsetbdd (Product_Type.fst a) qs (nfa_emptybdd (List.size_list qs))) [];

fun subset_dfs a x =
  DFS.gen_dfs (subset_succs a) subset_ins subset_memb subset_empt [x];

fun nfa_startnode a =
  List.list_update (List.replicate (List.size_list (Product_Type.fst a)) false)
    (0 : IntInf.int) true;

fun nfa_acceptinga a = nfa_accepting (Product_Type.snd a);

fun det_nfa a =
  let
    val (bdd, qss) = subset_dfs a (nfa_startnode a);
  in
    (List.map
       (fn qs =>
         bdd_map (fn qsa => Option.the (bdd_lookup bdd qsa))
           (subsetbdd (Product_Type.fst a) qs
             (nfa_emptybdd (List.size_list qs))))
       qss,
      List.map (nfa_acceptinga a) qss)
  end;

fun imp_dfa x = binop_dfa (fn a => fn b => (if a then b else true)) x;

fun make_tr f n i =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then []
    else f i :: make_tr f (Arith.minus_nat n (1 : IntInf.int)) (Arith.suc i));

fun init_tr x =
  (fn (bd, asa) =>
    make_tr
      (fn i =>
        make_tr
          (fn j =>
            not (Product_Type.equal_boola (List.nth asa i) (List.nth asa j)))
          i (0 : IntInf.int))
      (Arith.minus_nat (List.size_list bd) (1 : IntInf.int)) (1 : IntInf.int))
    x;

fun mk_eqcla [] i j l t = []
  | mk_eqcla (x :: xs) i j l t =
    (if tr_lookup t j i orelse not (Option.is_none x) then x else SOME l) ::
      mk_eqcla xs i (Arith.suc j) l t;

fun mk_eqcl [] zs i t = ([], zs)
  | mk_eqcl (NONE :: xs) zs i t =
    let
      val (xsa, a) =
        mk_eqcl (mk_eqcla xs i (Arith.suc i) (List.size_list zs) t) (zs @ [i])
          (Arith.suc i) t;
    in
      (List.size_list zs :: xsa, a)
    end
  | mk_eqcl (SOME l :: xs) zs i t =
    let
      val (xsa, a) = mk_eqcl xs zs (Arith.suc i) t;
    in
      (l :: xsa, a)
    end;

fun min_dfa x =
  (fn (bd, asa) =>
    let
      val (os, ns) =
        mk_eqcl (List.replicate (List.size_list bd) NONE) [] (0 : IntInf.int)
          (fixpt (bd, asa) (init_tr (bd, asa)));
    in
      (List.map (fn p => bdd_map (List.nth os) (List.nth bd p)) ns,
        List.map (List.nth asa) ns)
    end)
    x;

fun dioph_ineq_succs n ks m =
  List.map
    (fn xs => Arith.div_int (IntInf.- (m, eval_dioph ks xs)) (2 : IntInf.int))
    (mk_nat_vecs n);

fun dioph_ineq_dfs n ks l =
  DFS.gen_dfs (dioph_ineq_succs n ks) dioph_ins dioph_memb (dioph_empt ks l)
    [l];

fun ineq_dfa n ks l =
  let
    val (is, js) = dioph_ineq_dfs n ks l;
  in
    (List.map
       (fn j =>
         make_bdd
           (fn xs =>
             Option.the
               (List.nth is
                 (Nat_Bijection.int_encode
                   (Arith.div_int (IntInf.- (j, eval_dioph ks xs))
                     (2 : IntInf.int)))))
           n [])
       js,
      List.map (fn a => IntInf.<= ((0 : IntInf.int), a)) js)
  end;

fun negate_dfa x = (fn (t, a) => (t, List.map not a)) x;

fun nfa_of_dfa x =
  (fn (bdd, a) =>
    (List.map
       (bdd_map
         (fn q =>
           List.list_update (List.replicate (List.size_list bdd) false) q true))
       bdd,
      a))
    x;

fun quantify_bdd i (Leaf q) = Leaf q
  | quantify_bdd i (Branch (l, r)) =
    (if ((i : IntInf.int) = (0 : IntInf.int)) then bdd_binop bv_or l r
      else Branch
             (quantify_bdd (Arith.minus_nat i (1 : IntInf.int)) l,
               quantify_bdd (Arith.minus_nat i (1 : IntInf.int)) r));

fun quantify_nfa i = (fn (bdds, a) => (List.map (quantify_bdd i) bdds, a));

fun dfa_of_pf n (Eq (ks, l)) = eq_dfa n ks l
  | dfa_of_pf n (Le (ks, l)) = ineq_dfa n ks l
  | dfa_of_pf n (And (p, q)) = and_dfa (dfa_of_pf n p) (dfa_of_pf n q)
  | dfa_of_pf n (Or (p, q)) = or_dfa (dfa_of_pf n p) (dfa_of_pf n q)
  | dfa_of_pf n (Imp (p, q)) = imp_dfa (dfa_of_pf n p) (dfa_of_pf n q)
  | dfa_of_pf n (Exist p) =
    min_dfa
      (rquot
        (det_nfa
          (quantify_nfa (0 : IntInf.int)
            (nfa_of_dfa (dfa_of_pf (Arith.suc n) p))))
        n)
  | dfa_of_pf n (Forall p) = dfa_of_pf n (Neg (Exist (Neg p)))
  | dfa_of_pf n (Neg p) = negate_dfa (dfa_of_pf n p);

fun dfa_trans a q bs = bdd_lookup (List.nth (Product_Type.fst a) q) bs;

fun nat_of_bool false = (0 : IntInf.int)
  | nat_of_bool true = (1 : IntInf.int);

fun dfa_accepting a q = List.nth (Product_Type.snd a) q;

end; (*struct Presburger_Automata*)

structure Presburger_Adapt : sig
  datatype pres_NFA_state = Pres_NFA_state_error |
    Pres_NFA_state_int of IntInf.int
  val pres_NFA_state_to_nat : pres_NFA_state -> IntInf.int
  val pres_DFA_eq_ineq_trans_fun :
    bool -> IntInf.int list -> pres_NFA_state -> bool list -> pres_NFA_state
end = struct

datatype pres_NFA_state = Pres_NFA_state_error |
  Pres_NFA_state_int of IntInf.int;

fun pres_NFA_state_to_nat Pres_NFA_state_error = (0 : IntInf.int)
  | pres_NFA_state_to_nat (Pres_NFA_state_int m) =
    IntInf.+ (Nat_Bijection.int_encode m, (1 : IntInf.int));

fun pres_DFA_eq_ineq_trans_fun ineq ks Pres_NFA_state_error uu =
  Pres_NFA_state_error
  | pres_DFA_eq_ineq_trans_fun ineq ks (Pres_NFA_state_int j) bs =
    (if ineq orelse
          (((Arith.mod_int
              (Presburger_Automata.eval_dioph ks
                (List.map Presburger_Automata.nat_of_bool bs))
              (2 : IntInf.int)) : IntInf.int) = (Arith.mod_int j
          (2 : IntInf.int)))
      then Pres_NFA_state_int
             (Arith.div_int
               (IntInf.- (j, Presburger_Automata.eval_dioph ks
                               (List.map Presburger_Automata.nat_of_bool bs)))
               (2 : IntInf.int))
      else Pres_NFA_state_error);

end; (*struct Presburger_Adapt*)

structure RBT_Presburger_Impl : sig
  val lexord_lexord_less :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> bool
  val less_list :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> bool
  val lexord_lexord_less_eq :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> bool
  val less_eq_list :
    'a HOL.equal * 'a Orderings.linorder -> 'a list -> 'a list -> bool
  val ord_list : 'a HOL.equal * 'a Orderings.linorder -> ('a list) Orderings.ord
  val preorder_list :
    'a HOL.equal * 'a Orderings.linorder -> ('a list) Orderings.preorder
  val order_list :
    'a HOL.equal * 'a Orderings.linorder -> ('a list) Orderings.order
  val linorder_bool : bool Orderings.linorder
  val linorder_list :
    'a HOL.equal * 'a Orderings.linorder -> ('a list) Orderings.linorder
  val rs_DFA_eq_ineq :
    ((bool list), unit) RBT.rbt ->
      bool ->
        'a -> IntInf.int list ->
                IntInf.int ->
                  (IntInf.int, unit) RBT.rbt *
                    (((bool list), unit) RBT.rbt *
                      (((IntInf.int,
                          ((bool list), (IntInf.int, unit) RBT.rbt) RBT.rbt)
                          RBT.rbt,
                         (IntInf.int, ((bool list), IntInf.int) RBT.rbt)
                           RBT.rbt)
                         LTSByLTS_DLTS.lTS_choice *
                        ((IntInf.int, unit) RBT.rbt *
                          ((IntInf.int, unit) RBT.rbt *
                            unit NFAByLTS.nfa_props_ext))))
  val rs_cache_alpha :
    (IntInf.int, ((bool list), unit) RBT.rbt) RBT.rbt ->
      IntInf.int ->
        (IntInf.int, ((bool list), unit) RBT.rbt) RBT.rbt *
          ((bool list), unit) RBT.rbt
  val rs_pres_nfa_of_pf :
    IntInf.int ->
      Presburger_Automata.pf ->
        (IntInf.int, ((bool list), unit) RBT.rbt) RBT.rbt ->
          ((IntInf.int, unit) RBT.rbt *
            (((bool list), unit) RBT.rbt *
              (((IntInf.int, ((bool list), (IntInf.int, unit) RBT.rbt) RBT.rbt)
                  RBT.rbt,
                 (IntInf.int, ((bool list), IntInf.int) RBT.rbt) RBT.rbt)
                 LTSByLTS_DLTS.lTS_choice *
                ((IntInf.int, unit) RBT.rbt *
                  ((IntInf.int, unit) RBT.rbt *
                    unit NFAByLTS.nfa_props_ext))))) *
            (IntInf.int, ((bool list), unit) RBT.rbt) RBT.rbt
  val rs_pres_pf_to_nfa :
    IntInf.int ->
      Presburger_Automata.pf ->
        (IntInf.int, unit) RBT.rbt *
          (((bool list), unit) RBT.rbt *
            (((IntInf.int, ((bool list), (IntInf.int, unit) RBT.rbt) RBT.rbt)
                RBT.rbt,
               (IntInf.int, ((bool list), IntInf.int) RBT.rbt) RBT.rbt)
               LTSByLTS_DLTS.lTS_choice *
              ((IntInf.int, unit) RBT.rbt *
                ((IntInf.int, unit) RBT.rbt * unit NFAByLTS.nfa_props_ext))))
  val rs_eval_pf : Presburger_Automata.pf -> bool
  val eval_pf_dfa : Presburger_Automata.pf -> bool
end = struct

fun lexord_lexord_less (A1_, A2_) (x :: xs) (y :: ys) =
  (if Orderings.less
        ((Orderings.ord_preorder o Orderings.preorder_order o
           Orderings.order_linorder)
          A2_)
        x y
    then true
    else (if HOL.eq A1_ x y then lexord_lexord_less (A1_, A2_) xs ys
           else false))
  | lexord_lexord_less (A1_, A2_) (x :: xs) [] = false
  | lexord_lexord_less (A1_, A2_) [] (y :: ys) = true
  | lexord_lexord_less (A1_, A2_) [] [] = false;

fun less_list (A1_, A2_) l1 l2 = lexord_lexord_less (A1_, A2_) l1 l2;

fun lexord_lexord_less_eq (A1_, A2_) (x :: xs) (y :: ys) =
  (if Orderings.less
        ((Orderings.ord_preorder o Orderings.preorder_order o
           Orderings.order_linorder)
          A2_)
        x y
    then true
    else (if HOL.eq A1_ x y then lexord_lexord_less_eq (A1_, A2_) xs ys
           else false))
  | lexord_lexord_less_eq (A1_, A2_) (x :: xs) [] = false
  | lexord_lexord_less_eq (A1_, A2_) [] (y :: ys) = true
  | lexord_lexord_less_eq (A1_, A2_) [] [] = true;

fun less_eq_list (A1_, A2_) l1 l2 = lexord_lexord_less_eq (A1_, A2_) l1 l2;

fun ord_list (A1_, A2_) =
  {less_eq = less_eq_list (A1_, A2_), less = less_list (A1_, A2_)} :
  ('a list) Orderings.ord;

fun preorder_list (A1_, A2_) = {ord_preorder = ord_list (A1_, A2_)} :
  ('a list) Orderings.preorder;

fun order_list (A1_, A2_) = {preorder_order = preorder_list (A1_, A2_)} :
  ('a list) Orderings.order;

val linorder_bool = {order_linorder = Orderings.order_bool} :
  bool Orderings.linorder;

fun linorder_list (A1_, A2_) = {order_linorder = order_list (A1_, A2_)} :
  ('a list) Orderings.linorder;

fun rs_DFA_eq_ineq a ineq n ks l =
  RBT_NFAImpl.rs_dfa_construct_reachable_fun Arith.linorder_nat
    (linorder_list (Product_Type.equal_bool, linorder_bool))
    Presburger_Adapt.pres_NFA_state_to_nat
    (Presburger_Adapt.Pres_NFA_state_int l) a
    (if ineq
      then (fn aa =>
             (case aa of Presburger_Adapt.Pres_NFA_state_error => false
               | Presburger_Adapt.Pres_NFA_state_int ab =>
                 IntInf.<= ((0 : IntInf.int), ab)))
      else (fn aa =>
             (case aa of Presburger_Adapt.Pres_NFA_state_error => false
               | Presburger_Adapt.Pres_NFA_state_int m =>
                 ((m : IntInf.int) = (0 : IntInf.int)))))
    (Presburger_Adapt.pres_DFA_eq_ineq_trans_fun ineq ks);

fun rs_cache_alpha m n =
  (if ((n : IntInf.int) = (0 : IntInf.int))
    then (m, StdInst.rs_sng
               (linorder_list (Product_Type.equal_bool, linorder_bool)) [])
    else (case RBTMapImpl.rm_lookup Arith.linorder_nat
                 (Arith.suc (Arith.minus_nat n (1 : IntInf.int))) m
           of NONE =>
             let
               val (ma, bl) =
                 rs_cache_alpha m (Arith.minus_nat n (1 : IntInf.int));
               val bla =
                 RBTSetImpl.rs_union
                   (linorder_list (Product_Type.equal_bool, linorder_bool))
                   (RBTSetImpl.rs_image
                     (linorder_list (Product_Type.equal_bool, linorder_bool))
                     (linorder_list (Product_Type.equal_bool, linorder_bool))
                     (fn a => true :: a) bl)
                   (RBTSetImpl.rs_image
                     (linorder_list (Product_Type.equal_bool, linorder_bool))
                     (linorder_list (Product_Type.equal_bool, linorder_bool))
                     (fn a => false :: a) bl);
               val mb =
                 RBTMapImpl.rm_update Arith.linorder_nat
                   (Arith.suc (Arith.minus_nat n (1 : IntInf.int))) bla ma;
             in
               (mb, bla)
             end
           | SOME a => (m, a)));

fun rs_pres_nfa_of_pf n (Presburger_Automata.Neg p) c =
  let
    val (pa, a) = rs_pres_nfa_of_pf n p c;
  in
    (RBT_NFAImpl.rs_nfa_complement
       (linorder_list (Product_Type.equal_bool, linorder_bool)) pa,
      a)
  end
  | rs_pres_nfa_of_pf n (Presburger_Automata.Forall p) c =
    let
      val (ca, a) = rs_cache_alpha c n;
      val (pa, b) = rs_pres_nfa_of_pf (Arith.suc n) p ca;
    in
      (RBT_NFAImpl.rs_nfa_complement
         (linorder_list (Product_Type.equal_bool, linorder_bool))
         (RBT_NFAImpl.rs_nfa_right_quotient_lists
           (linorder_list (Product_Type.equal_bool, linorder_bool))
           (List.list_all not)
           (RBT_NFAImpl.rs_nfa_Hopcroft_NFA
             (linorder_list (Product_Type.equal_bool, linorder_bool))
             (RBT_NFAImpl.rs_nfa_rename_labels_gen
               (linorder_list (Product_Type.equal_bool, linorder_bool)) false
               (RBT_NFAImpl.rs_nfa_complement
                 (linorder_list (Product_Type.equal_bool, linorder_bool)) pa)
               a List.tl))),
        b)
    end
  | rs_pres_nfa_of_pf n (Presburger_Automata.Exist p) c =
    let
      val (ca, a) = rs_cache_alpha c n;
      val (pa, b) = rs_pres_nfa_of_pf (Arith.suc n) p ca;
    in
      (RBT_NFAImpl.rs_nfa_right_quotient_lists
         (linorder_list (Product_Type.equal_bool, linorder_bool))
         (List.list_all not)
         (RBT_NFAImpl.rs_nfa_Hopcroft_NFA
           (linorder_list (Product_Type.equal_bool, linorder_bool))
           (RBT_NFAImpl.rs_nfa_rename_labels_gen
             (linorder_list (Product_Type.equal_bool, linorder_bool)) false pa a
             List.tl)),
        b)
    end
  | rs_pres_nfa_of_pf n (Presburger_Automata.Imp (p, q)) c =
    let
      val (pa, ca) = rs_pres_nfa_of_pf n p c;
      val (qa, a) = rs_pres_nfa_of_pf n q ca;
    in
      (RBT_NFAImpl.rs_nfa_bool_comb
         (linorder_list (Product_Type.equal_bool, linorder_bool))
         (fn aa => fn b => (if aa then b else true)) pa qa,
        a)
    end
  | rs_pres_nfa_of_pf n (Presburger_Automata.Or (p, q)) c =
    let
      val (pa, ca) = rs_pres_nfa_of_pf n p c;
      val (qa, a) = rs_pres_nfa_of_pf n q ca;
    in
      (RBT_NFAImpl.rs_nfa_bool_comb
         (linorder_list (Product_Type.equal_bool, linorder_bool))
         (fn aa => fn b => aa orelse b) pa qa,
        a)
    end
  | rs_pres_nfa_of_pf n (Presburger_Automata.And (p, q)) c =
    let
      val (pa, ca) = rs_pres_nfa_of_pf n p c;
      val (qa, a) = rs_pres_nfa_of_pf n q ca;
    in
      (RBT_NFAImpl.rs_nfa_bool_comb
         (linorder_list (Product_Type.equal_bool, linorder_bool))
         (fn aa => fn b => aa andalso b) pa qa,
        a)
    end
  | rs_pres_nfa_of_pf n (Presburger_Automata.Le (ks, l)) c =
    let
      val (ca, a) = rs_cache_alpha c n;
    in
      (rs_DFA_eq_ineq a true n ks l, ca)
    end
  | rs_pres_nfa_of_pf n (Presburger_Automata.Eq (ks, l)) c =
    let
      val (ca, a) = rs_cache_alpha c n;
    in
      (rs_DFA_eq_ineq a false n ks l, ca)
    end;

fun rs_pres_pf_to_nfa n pf =
  Product_Type.fst
    (rs_pres_nfa_of_pf n pf (RBTMapImpl.rm_empty Arith.linorder_nat ()));

fun rs_eval_pf pf =
  RBT_NFAImpl.rs_nfa_accept
    (linorder_list (Product_Type.equal_bool, linorder_bool))
    (rs_pres_pf_to_nfa (0 : IntInf.int) pf) [];

fun eval_pf_dfa pf =
  Presburger_Automata.accepts
    (Presburger_Automata.dfa_trans
      (Presburger_Automata.dfa_of_pf (0 : IntInf.int) pf))
    (Presburger_Automata.dfa_accepting
      (Presburger_Automata.dfa_of_pf (0 : IntInf.int) pf))
    (0 : IntInf.int) [];

end; (*struct RBT_Presburger_Impl*)
