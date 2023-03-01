
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of 
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
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

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of 
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x) 
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then 
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
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
  datatype 'a itself = Type
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

datatype 'a itself = Type;

end; (*struct HOL*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val maxa : ('a -> 'a -> bool) -> 'a -> 'a -> 'a
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun maxa less_eq a b = (if less_eq a b then b else a);

fun max A_ = maxa (less_eq A_);

end; (*struct Orderings*)

structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val equal_boola : bool -> bool -> bool
  val equal_bool : bool HOL.equal
  val equal_proda : 'a HOL.equal -> 'b HOL.equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
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

end; (*struct Product_Type*)

structure Arith : sig
  val suc : IntInf.int -> IntInf.int
  val ord_int : IntInf.int Orderings.ord
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
  val minus_nat : IntInf.int -> IntInf.int -> IntInf.int
  val divmod_int : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val div_int : IntInf.int -> IntInf.int -> IntInf.int
  val div_nat : IntInf.int -> IntInf.int -> IntInf.int
  val mod_int : IntInf.int -> IntInf.int -> IntInf.int
  val mod_nat : IntInf.int -> IntInf.int -> IntInf.int
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

fun mod_nat m n = Product_Type.snd (IntInf.divMod (m, n));

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
  val filter : ('a -> bool) -> 'a list -> 'a list
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

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

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
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

fun dom m = Set.collect (fn a => not (Option.is_none (m a)));

fun map_of A_ ((l, v) :: ps) k =
  (if HOL.eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

end; (*struct Map*)

structure NFA : sig
  type 'a nFA_states
  val states_enumerate : 'a nFA_states -> IntInf.int -> 'a
  val states_enumerate_nat : IntInf.int -> IntInf.int
  val nFA_states_nat : IntInf.int nFA_states
end = struct

type 'a nFA_states = {states_enumerate : IntInf.int -> 'a};
val states_enumerate = #states_enumerate : 'a nFA_states -> IntInf.int -> 'a;

fun states_enumerate_nat q = q;

val nFA_states_nat = {states_enumerate = states_enumerate_nat} :
  IntInf.int nFA_states;

end; (*struct NFA*)

structure Enum : sig
  val product : 'a list -> 'b list -> ('a * 'b) list
end = struct

fun product [] uu = []
  | product (x :: xs) ys = List.map (fn a => (x, a)) ys @ product xs ys;

end; (*struct Enum*)

structure AList : sig
  val delete : 'a HOL.equal -> 'a -> ('a * 'b) list -> ('a * 'b) list
  val update : 'a HOL.equal -> 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
end = struct

fun delete A_ k = List.filter (fn (ka, _) => not (HOL.eq A_ k ka));

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if HOL.eq A_ (Product_Type.fst p) k then (k, v) :: ps
      else p :: update A_ k v ps);

end; (*struct AList*)

structure LTSGA : sig
  val ltsga_list_to_collect_list :
    'a HOL.equal -> 'c HOL.equal ->
      ('a * ('b * 'c)) list -> ('a * ('b list * 'c)) list
end = struct

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
      (('a -> 'b -> 'c -> 'c) -> 'c -> 'c -> 'c) -> 'c -> 'c -> 'c
  val it_size :
    (('a -> 'b -> IntInf.int -> IntInf.int) ->
      'c -> IntInf.int -> IntInf.int) ->
      'c -> IntInf.int
  val iti_sel :
    (('a option -> bool) ->
      ('b -> 'c -> 'd -> 'e option) -> 'f -> 'g option -> 'e option) ->
      'f -> ('b -> 'c -> 'e option) -> 'e option
  val sel_sel :
    ('a -> ('b -> 'c -> ('b * 'c) option) -> ('b * 'c) option) ->
      'a -> ('b -> 'c -> bool) -> ('b * 'c) option
  val sel_ball :
    ('a -> ('b -> 'c -> unit option) -> unit option) ->
      'a -> ('b -> 'c -> bool) -> bool
  val sza_isSng : (IntInf.int -> 'a -> IntInf.int) -> 'a -> bool
  val iti_isEmpty :
    ((bool -> bool) -> ('a -> 'b -> bool -> bool) -> 'c -> bool -> bool) ->
      'c -> bool
  val iti_iterate :
    (('a -> bool) -> ('b -> 'c -> 'a -> 'a) -> 'd -> 'a -> 'a) ->
      ('b -> 'c -> 'a -> 'a) -> 'd -> 'a -> 'a
  val it_map_to_list :
    (('a -> 'b -> ('a * 'b) list -> ('a * 'b) list) ->
      'c -> ('a * 'b) list -> ('a * 'b) list) ->
      'c -> ('a * 'b) list
  val iti_size_abort :
    ((IntInf.int -> bool) ->
      ('a -> 'b -> IntInf.int -> IntInf.int) ->
        'c -> IntInf.int -> IntInf.int) ->
      IntInf.int -> 'c -> IntInf.int
  val gen_list_to_map_aux : ('a -> 'b -> 'c -> 'c) -> 'c -> ('a * 'b) list -> 'c
  val gen_list_to_map :
    (unit -> 'a) -> ('b -> 'c -> 'a -> 'a) -> ('b * 'c) list -> 'a
  val it_map_image_filter :
    (('a -> 'b -> 'c -> 'c) -> 'd -> 'c -> 'c) ->
      (unit -> 'c) ->
        ('e -> 'f -> 'c -> 'c) -> ('a -> 'b -> ('e * 'f) option) -> 'd -> 'c
  val it_map_restrict :
    (('a -> 'b -> 'c -> 'c) -> 'd -> 'c -> 'c) ->
      (unit -> 'c) -> ('a -> 'b -> 'c -> 'c) -> ('a -> 'b -> bool) -> 'd -> 'c
  val neg_ball_bexists :
    ('a -> ('b -> 'c -> bool) -> bool) -> 'a -> ('b -> 'c -> bool) -> bool
end = struct

fun eu_sng empt update k v = update k v (empt ());

fun it_add update iterate m1 m2 = iterate update m2 m1;

fun it_size iterate s = iterate (fn _ => fn _ => Arith.suc) s (0 : IntInf.int);

fun iti_sel iti m f = iti Option.is_none (fn k => fn v => fn _ => f k v) m NONE;

fun sel_sel sel s p =
  sel s (fn k => fn v => (if p k v then SOME (k, v) else NONE));

fun sel_ball sel s p =
  Option.is_none
    (sel s (fn k => fn v => (if not (p k v) then SOME () else NONE)));

fun sza_isSng sza s =
  (((sza (2 : IntInf.int) s) : IntInf.int) = (1 : IntInf.int));

fun iti_isEmpty iti m = iti Fun.id (fn _ => fn _ => fn _ => false) m true;

fun iti_iterate iti = iti (fn _ => true);

fun it_map_to_list iterate m =
  iterate (fn u => fn v => (fn a => (u, v) :: a)) m [];

fun iti_size_abort it m s =
  it (fn n => IntInf.< (n, m)) (fn _ => fn _ => Arith.suc) s (0 : IntInf.int);

fun gen_list_to_map_aux upd accs [] = accs
  | gen_list_to_map_aux upd accs ((k, v) :: l) =
    gen_list_to_map_aux upd (upd k v accs) l;

fun gen_list_to_map empt upd l = gen_list_to_map_aux upd (empt ()) (List.rev l);

fun it_map_image_filter map_it map_emp map_up_dj f m =
  map_it
    (fn k => fn v => fn sigma =>
      (case f k v of NONE => sigma | SOME (ka, va) => map_up_dj ka va sigma))
    m
    (map_emp ());

fun it_map_restrict map_it map_emp map_up_dj p =
  it_map_image_filter map_it map_emp map_up_dj
    (fn k => fn v => (if p k v then SOME (k, v) else NONE));

fun neg_ball_bexists ball s p = not (ball s (fn k => fn v => not (p k v)));

end; (*struct MapGA*)

structure SetGA : sig
  val ei_sng : (unit -> 'a) -> ('b -> 'a -> 'a) -> 'b -> 'a
  val it_diff :
    (('a -> 'b -> 'b) -> 'c -> 'b -> 'b) -> ('a -> 'b -> 'b) -> 'b -> 'c -> 'b
  val it_size :
    (('a -> IntInf.int -> IntInf.int) -> 'b -> IntInf.int -> IntInf.int) ->
      'b -> IntInf.int
  val sel_sel :
    ('a -> ('b -> 'b option) -> 'b option) -> 'a -> ('b -> bool) -> 'b option
  val it_inter :
    (('a -> 'b -> 'b) -> 'c -> 'b -> 'b) ->
      ('a -> 'd -> bool) -> (unit -> 'b) -> ('a -> 'b -> 'b) -> 'c -> 'd -> 'b
  val iti_ball :
    ((bool -> bool) -> ('a -> bool -> bool) -> 'b -> bool -> bool) ->
      'b -> ('a -> bool) -> bool
  val sza_isSng : (IntInf.int -> 'a -> IntInf.int) -> 'a -> bool
  val iflt_image : (('a -> 'b option) -> 'c -> 'd) -> ('a -> 'b) -> 'c -> 'd
  val ball_subset :
    ('a -> ('b -> bool) -> bool) -> ('b -> 'c -> bool) -> 'a -> 'c -> bool
  val iflt_filter : (('a -> 'a option) -> 'b -> 'c) -> ('a -> bool) -> 'b -> 'c
  val subset_equal :
    ('a -> 'b -> bool) -> ('b -> 'a -> bool) -> 'a -> 'b -> bool
  val ball_disjoint :
    ('a -> ('b -> bool) -> 'c) -> ('b -> 'd -> bool) -> 'a -> 'd -> 'c
  val it_set_to_list :
    (('a -> 'a list -> 'a list) -> 'b -> 'c list -> 'a list) -> 'b -> 'a list
  val iti_size_abort :
    ((IntInf.int -> bool) ->
      ('a -> IntInf.int -> IntInf.int) -> 'b -> IntInf.int -> IntInf.int) ->
      IntInf.int -> 'b -> IntInf.int
  val gen_list_to_set_aux : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val gen_list_to_set : (unit -> 'a) -> ('b -> 'a -> 'a) -> 'b list -> 'a
  val it_image_filter :
    (('a -> 'b -> 'b) -> 'c -> 'b -> 'b) ->
      (unit -> 'b) -> ('d -> 'b -> 'b) -> ('a -> 'd option) -> 'c -> 'b
  val neg_ball_bexists :
    ('a -> ('b -> bool) -> bool) -> 'a -> ('b -> bool) -> bool
  val it_inj_image_filter :
    (('a -> 'b -> 'b) -> 'c -> 'b -> 'b) ->
      (unit -> 'b) -> ('d -> 'b -> 'b) -> ('a -> 'd option) -> 'c -> 'b
  val sel_disjoint_witness :
    ('a -> ('b -> 'b option) -> 'c) -> ('b -> 'd -> bool) -> 'a -> 'd -> 'c
end = struct

fun ei_sng e i x = i x (e ());

fun it_diff iterate1 del2 s2 s1 = iterate1 del2 s1 s2;

fun it_size iterate s = iterate (fn _ => Arith.suc) s (0 : IntInf.int);

fun sel_sel sel s p = sel s (fn x => (if p x then SOME x else NONE));

fun it_inter iterate1 memb2 empt3 insrt3 s1 s2 =
  iterate1 (fn x => fn s => (if memb2 x s2 then insrt3 x s else s)) s1
    (empt3 ());

fun iti_ball it s p = it Fun.id (fn a => fn _ => p a) s true;

fun sza_isSng sza s =
  (((sza (2 : IntInf.int) s) : IntInf.int) = (1 : IntInf.int));

fun iflt_image iflt f s = iflt (fn x => SOME (f x)) s;

fun ball_subset ball1 mem2 s1 s2 = ball1 s1 (fn x => mem2 x s2);

fun iflt_filter iflt p s = iflt (fn x => (if p x then SOME x else NONE)) s;

fun subset_equal ss1 ss2 s1 s2 = ss1 s1 s2 andalso ss2 s2 s1;

fun ball_disjoint ball1 memb2 s1 s2 = ball1 s1 (fn x => not (memb2 x s2));

fun it_set_to_list iterate s = iterate (fn a => fn b => a :: b) s [];

fun iti_size_abort it m s =
  it (fn n => IntInf.< (n, m)) (fn _ => Arith.suc) s (0 : IntInf.int);

fun gen_list_to_set_aux ins accs [] = accs
  | gen_list_to_set_aux ins accs (x :: l) =
    gen_list_to_set_aux ins (ins x accs) l;

fun gen_list_to_set empt ins = gen_list_to_set_aux ins (empt ());

fun it_image_filter iterate1 empty2 ins2 f s =
  iterate1 (fn x => fn res => (case f x of NONE => res | SOME v => ins2 v res))
    s
    (empty2 ());

fun neg_ball_bexists ball s p = not (ball s (fn x => not (p x)));

fun it_inj_image_filter iterate1 empty2 ins2 f s =
  iterate1 (fn x => fn res => (case f x of NONE => res | SOME v => ins2 v res))
    s
    (empty2 ());

fun sel_disjoint_witness sel1 mem2 s1 s2 =
  sel1 s1 (fn x => (if mem2 x s2 then SOME x else NONE));

end; (*struct SetGA*)

structure ListGA : sig
  val idx_iteratei_aux :
    ('a -> IntInf.int -> 'b) ->
      IntInf.int ->
        IntInf.int -> ('c -> bool) -> ('b -> 'c -> 'c) -> 'a -> 'c -> 'c
  val idx_iteratei :
    ('a -> IntInf.int -> 'b) ->
      ('a -> IntInf.int) -> ('c -> bool) -> ('b -> 'c -> 'c) -> 'a -> 'c -> 'c
end = struct

fun idx_iteratei_aux get sz i c f l sigma =
  (if ((i : IntInf.int) = (0 : IntInf.int)) orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (Arith.minus_nat i (1 : IntInf.int)) c f l
           (f (get l (Arith.minus_nat sz i)) sigma));

fun idx_iteratei get sz c f l sigma =
  idx_iteratei_aux get (sz l) (sz l) c f l sigma;

end; (*struct ListGA*)

structure MapSpec : sig
  datatype ('a, 'b, 'c, 'd) map_ops_ext =
    Map_ops_ext of
      ('c -> 'a -> 'b option) * ('c -> bool) * (unit -> 'c) * ('a -> 'b -> 'c) *
        ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c) *
        ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'c) *
        (('a -> 'b -> bool) -> 'c -> 'c) * ('c -> 'c -> 'c) * ('c -> 'c -> 'c) *
        ('c -> bool) * ('c -> bool) * ('c -> ('a -> 'b -> bool) -> bool) *
        ('c -> ('a -> 'b -> bool) -> bool) * ('c -> IntInf.int) *
        (IntInf.int -> 'c -> IntInf.int) *
        ('c -> ('a -> 'b -> bool) -> ('a * 'b) option) *
        ('c -> ('a * 'b) list) * (('a * 'b) list -> 'c) * 'd
  val map_op_sng : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'b -> 'c
  val map_op_empty : ('a, 'b, 'c, 'd) map_ops_ext -> unit -> 'c
  val map_op_lookup : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'c -> 'b option
  val map_op_update : ('a, 'b, 'c, 'd) map_ops_ext -> 'a -> 'b -> 'c -> 'c
end = struct

datatype ('a, 'b, 'c, 'd) map_ops_ext =
  Map_ops_ext of
    ('c -> 'a -> 'b option) * ('c -> bool) * (unit -> 'c) * ('a -> 'b -> 'c) *
      ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c) *
      ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'c) *
      (('a -> 'b -> bool) -> 'c -> 'c) * ('c -> 'c -> 'c) * ('c -> 'c -> 'c) *
      ('c -> bool) * ('c -> bool) * ('c -> ('a -> 'b -> bool) -> bool) *
      ('c -> ('a -> 'b -> bool) -> bool) * ('c -> IntInf.int) *
      (IntInf.int -> 'c -> IntInf.int) *
      ('c -> ('a -> 'b -> bool) -> ('a * 'b) option) * ('c -> ('a * 'b) list) *
      (('a * 'b) list -> 'c) * 'd;

fun map_op_sng
  (Map_ops_ext
    (map_op_alpha, map_op_invar, map_op_empty, map_op_sng, map_op_lookup,
      map_op_update, map_op_update_dj, map_op_delete, map_op_restrict,
      map_op_add, map_op_add_dj, map_op_isEmpty, map_op_isSng, map_op_ball,
      map_op_bexists, map_op_size, map_op_size_abort, map_op_sel,
      map_op_to_list, map_op_to_map, more))
  = map_op_sng;

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
  val set_op_ins : ('a, 'b, 'c) set_ops_ext -> 'a -> 'b -> 'b
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

fun set_op_ins
  (Set_ops_ext
    (set_op_alpha, set_op_invar, set_op_empty, set_op_sng, set_op_memb,
      set_op_ins, set_op_ins_dj, set_op_delete, set_op_isEmpty, set_op_isSng,
      set_op_ball, set_op_bexists, set_op_size, set_op_size_abort, set_op_union,
      set_op_union_dj, set_op_diff, set_op_filter, set_op_inter, set_op_subset,
      set_op_equal, set_op_disjoint, set_op_disjoint_witness, set_op_sel,
      set_op_to_list, set_op_from_list, more))
  = set_op_ins;

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

structure HashCode : sig
  type 'a hashable
  val hashcode : 'a hashable -> 'a -> IntInf.int
  val bounded_hashcode : 'a hashable -> IntInf.int -> 'a -> IntInf.int
  val def_hashmap_size : 'a hashable -> 'a HOL.itself -> IntInf.int
  val hashcode_nat : IntInf.int -> IntInf.int
  val bounded_hashcode_nat : IntInf.int -> IntInf.int -> IntInf.int
  val def_hashmap_size_nat : IntInf.int HOL.itself -> IntInf.int
  val hashable_nat : IntInf.int hashable
  val hashcode_bool : bool -> IntInf.int
  val bounded_hashcode_bool : IntInf.int -> bool -> IntInf.int
  val def_hashmap_size_bool : bool HOL.itself -> IntInf.int
  val hashable_bool : bool hashable
  val hashcode_list : 'a hashable -> 'a list -> IntInf.int
  val bounded_hashcode_list : 'a hashable -> IntInf.int -> 'a list -> IntInf.int
  val def_hashmap_size_list : 'a hashable -> ('a list) HOL.itself -> IntInf.int
  val hashable_list : 'a hashable -> ('a list) hashable
  val hashcode_prod : 'a hashable -> 'b hashable -> 'a * 'b -> IntInf.int
  val bounded_hashcode_prod :
    'a hashable -> 'b hashable -> IntInf.int -> 'a * 'b -> IntInf.int
  val def_hashmap_size_prod :
    'a hashable -> 'b hashable -> ('a * 'b) HOL.itself -> IntInf.int
  val hashable_prod : 'a hashable -> 'b hashable -> ('a * 'b) hashable
end = struct

type 'a hashable =
  {hashcode : 'a -> IntInf.int,
    bounded_hashcode : IntInf.int -> 'a -> IntInf.int,
    def_hashmap_size : 'a HOL.itself -> IntInf.int};
val hashcode = #hashcode : 'a hashable -> 'a -> IntInf.int;
val bounded_hashcode = #bounded_hashcode :
  'a hashable -> IntInf.int -> 'a -> IntInf.int;
val def_hashmap_size = #def_hashmap_size :
  'a hashable -> 'a HOL.itself -> IntInf.int;

fun hashcode_nat n = n;

fun bounded_hashcode_nat na n = Arith.mod_nat n na;

fun def_hashmap_size_nat x = (fn _ => (16 : IntInf.int)) x;

val hashable_nat =
  {hashcode = hashcode_nat, bounded_hashcode = bounded_hashcode_nat,
    def_hashmap_size = def_hashmap_size_nat}
  : IntInf.int hashable;

fun hashcode_bool b = (if b then (1 : IntInf.int) else (0 : IntInf.int));

fun bounded_hashcode_bool n b =
  (if b then (1 : IntInf.int) else (0 : IntInf.int));

fun def_hashmap_size_bool x = (fn _ => (2 : IntInf.int)) x;

val hashable_bool =
  {hashcode = hashcode_bool, bounded_hashcode = bounded_hashcode_bool,
    def_hashmap_size = def_hashmap_size_bool}
  : bool hashable;

fun hashcode_list A_ =
  List.foldl
    (fn h => fn x => IntInf.+ (IntInf.* (h, (33 : IntInf.int)), hashcode A_ x))
    (5381 : IntInf.int);

fun bounded_hashcode_list A_ n =
  List.foldl
    (fn h => fn x =>
      Arith.mod_nat
        (IntInf.+ (IntInf.* (h, (33 : IntInf.int)), bounded_hashcode A_ n x)) n)
    (Arith.mod_nat (5381 : IntInf.int) n);

fun def_hashmap_size_list A_ =
  (fn _ => IntInf.* ((2 : IntInf.int), def_hashmap_size A_ HOL.Type));

fun hashable_list A_ =
  {hashcode = hashcode_list A_, bounded_hashcode = bounded_hashcode_list A_,
    def_hashmap_size = def_hashmap_size_list A_}
  : ('a list) hashable;

fun hashcode_prod A_ B_ x =
  IntInf.+ (IntInf.* (hashcode A_
                        (Product_Type.fst
                          x), (33 : IntInf.int)), hashcode B_
            (Product_Type.snd x));

fun bounded_hashcode_prod A_ B_ n x =
  Arith.mod_nat
    (IntInf.+ (IntInf.* (bounded_hashcode A_ n
                           (Product_Type.fst
                             x), (33 : IntInf.int)), bounded_hashcode B_ n
               (Product_Type.snd x)))
    n;

fun def_hashmap_size_prod A_ B_ =
  (fn _ =>
    IntInf.+ (def_hashmap_size A_ HOL.Type, def_hashmap_size B_ HOL.Type));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    bounded_hashcode = bounded_hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

end; (*struct HashCode*)

structure Assoc_List : sig
  val iteratei_aux :
    ('a -> bool) -> ('b -> 'c -> 'a -> 'a) -> ('b * 'c) list -> 'a -> 'a
end = struct

fun iteratei_aux c f [] sigma = sigma
  | iteratei_aux c f ((k, v) :: l) sigma =
    (if c sigma then iteratei_aux c f l (f k v sigma) else sigma);

end; (*struct Assoc_List*)

structure ArrayHashMap_Impl : sig
  datatype ('a, 'b) hashmap =
    HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * IntInf.int
  val hm_grow : 'a HashCode.hashable -> ('a, 'b) hashmap -> IntInf.int
  val ahm_alpha_aux :
    'a HOL.equal * 'a HashCode.hashable ->
      (('a * 'b) list) FArray.IsabelleMapping.ArrayType -> 'a -> 'b option
  val ahm_alpha :
    'a HOL.equal * 'a HashCode.hashable -> ('a, 'b) hashmap -> 'a -> 'b option
  val new_hashmap_with : 'a HashCode.hashable -> IntInf.int -> ('a, 'b) hashmap
  val ahm_empty : 'a HashCode.hashable -> unit -> ('a, 'b) hashmap
  val ahm_delete :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val load_factor : IntInf.int
  val ahm_filled : 'a HashCode.hashable -> ('a, 'b) hashmap -> bool
  val ahm_lookup :
    'a HOL.equal * 'a HashCode.hashable -> 'a -> ('a, 'b) hashmap -> 'b option
  val ahm_rehash_auxa :
    'a HashCode.hashable ->
      IntInf.int ->
        'a -> 'b -> (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
                      (('a * 'b) list) FArray.IsabelleMapping.ArrayType
  val ahm_iteratei_aux :
    'b HashCode.hashable ->
      ('a -> bool) ->
        ('b -> 'c -> 'a -> 'a) ->
          (('b * 'c) list) FArray.IsabelleMapping.ArrayType -> 'a -> 'a
  val ahm_rehash_aux :
    'a HashCode.hashable ->
      (('a * 'b) list) FArray.IsabelleMapping.ArrayType ->
        IntInf.int -> (('a * 'b) list) FArray.IsabelleMapping.ArrayType
  val ahm_rehash :
    'a HashCode.hashable -> ('a, 'b) hashmap -> IntInf.int -> ('a, 'b) hashmap
  val ahm_update_aux :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, 'b) hashmap -> 'a -> 'b -> ('a, 'b) hashmap
  val ahm_update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val ahm_iteratei :
    'b HashCode.hashable ->
      ('a -> bool) -> ('b -> 'c -> 'a -> 'a) -> ('b, 'c) hashmap -> 'a -> 'a
end = struct

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * IntInf.int;

fun hm_grow A_ (HashMap (a, n)) =
  IntInf.+ (IntInf.* ((2 : IntInf.int), FArray.IsabelleMapping.array_length
  a), (3 : IntInf.int));

fun ahm_alpha_aux (A1_, A2_) a k =
  Map.map_of A1_
    (FArray.IsabelleMapping.array_get a
      (HashCode.bounded_hashcode A2_ (FArray.IsabelleMapping.array_length a) k))
    k;

fun ahm_alpha (A1_, A2_) (HashMap (a, uu)) = ahm_alpha_aux (A1_, A2_) a;

fun new_hashmap_with A_ size =
  HashMap (FArray.IsabelleMapping.new_array [] size, (0 : IntInf.int));

fun ahm_empty A_ =
  (fn _ => new_hashmap_with A_ (HashCode.def_hashmap_size A_ HOL.Type));

fun ahm_delete (A1_, A2_) k (HashMap (a, n)) =
  let
    val h =
      HashCode.bounded_hashcode A2_ (FArray.IsabelleMapping.array_length a) k;
    val m = FArray.IsabelleMapping.array_get a h;
    val deleted = not (Option.is_none (Map.map_of A1_ m k));
  in
    HashMap
      (FArray.IsabelleMapping.array_set a h (AList.delete A1_ k m),
        (if deleted then Arith.minus_nat n (1 : IntInf.int) else n))
  end;

val load_factor : IntInf.int = (75 : IntInf.int);

fun ahm_filled A_ (HashMap (a, n)) =
  IntInf.<= (IntInf.* (FArray.IsabelleMapping.array_length
                         a, load_factor), IntInf.* (n, (100 : IntInf.int)));

fun ahm_lookup (A1_, A2_) k hm = ahm_alpha (A1_, A2_) hm k;

fun ahm_rehash_auxa A_ n k v a =
  let
    val h = HashCode.bounded_hashcode A_ n k;
  in
    FArray.IsabelleMapping.array_set a h
      ((k, v) :: FArray.IsabelleMapping.array_get a h)
  end;

fun ahm_iteratei_aux B_ c f a sigma =
  ListGA.idx_iteratei FArray.IsabelleMapping.array_get
    FArray.IsabelleMapping.array_length c (Assoc_List.iteratei_aux c f) a sigma;

fun ahm_rehash_aux A_ a sz =
  ahm_iteratei_aux A_ (fn _ => true) (ahm_rehash_auxa A_ sz) a
    (FArray.IsabelleMapping.new_array [] sz);

fun ahm_rehash A_ (HashMap (a, n)) sz = HashMap (ahm_rehash_aux A_ a sz, n);

fun ahm_update_aux (A1_, A2_) (HashMap (a, n)) k v =
  let
    val h =
      HashCode.bounded_hashcode A2_ (FArray.IsabelleMapping.array_length a) k;
    val m = FArray.IsabelleMapping.array_get a h;
    val insert = Option.is_none (Map.map_of A1_ m k);
  in
    HashMap
      (FArray.IsabelleMapping.array_set a h (AList.update A1_ k v m),
        (if insert then IntInf.+ (n, (1 : IntInf.int)) else n))
  end;

fun ahm_update (A1_, A2_) k v hm =
  let
    val hma = ahm_update_aux (A1_, A2_) hm k v;
  in
    (if ahm_filled A2_ hma then ahm_rehash A2_ hma (hm_grow A2_ hma) else hma)
  end;

fun ahm_iteratei B_ c f (HashMap (a, n)) = ahm_iteratei_aux B_ c f a;

end; (*struct ArrayHashMap_Impl*)

structure ArrayHashMap : sig
  datatype ('a, 'b) hashmap = HashMap of ('a, 'b) ArrayHashMap_Impl.hashmap
  val impl_of :
    'a HashCode.hashable ->
      ('a, 'b) hashmap -> ('a, 'b) ArrayHashMap_Impl.hashmap
  val ahm_update :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val ahm_iteratei :
    'b HashCode.hashable ->
      ('a -> bool) -> ('b -> 'c -> 'a -> 'a) -> ('b, 'c) hashmap -> 'a -> 'a
  val ahm_iterate :
    'a HashCode.hashable ->
      ('a -> 'b -> 'c -> 'c) -> ('a, 'b) hashmap -> 'c -> 'c
  val ahm_add :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, 'b) hashmap -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val ahm_sel :
    'a HashCode.hashable ->
      ('a, 'b) hashmap -> ('a -> 'b -> 'c option) -> 'c option
  val ahm_sela :
    'a HashCode.hashable ->
      ('a, 'b) hashmap -> ('a -> 'b -> bool) -> ('a * 'b) option
  val ahm_alpha :
    'a HOL.equal * 'a HashCode.hashable -> ('a, 'b) hashmap -> 'a -> 'b option
  val ahm_empty_const : 'a HashCode.hashable -> ('a, 'b) hashmap
  val ahm_empty : 'a HashCode.hashable -> unit -> ('a, 'b) hashmap
  val ahm_add_dj :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, 'b) hashmap -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val ahm_delete :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, 'b) hashmap -> ('a, 'b) hashmap
  val ahm_lookup :
    'a HOL.equal * 'a HashCode.hashable -> 'a -> ('a, 'b) hashmap -> 'b option
  val ahm_isEmpty : 'a HashCode.hashable -> ('a, 'b) hashmap -> bool
  val ahm_to_list : 'a HashCode.hashable -> ('a, 'b) hashmap -> ('a * 'b) list
  val list_to_ahm :
    'a HOL.equal * 'a HashCode.hashable -> ('a * 'b) list -> ('a, 'b) hashmap
  val ahm_update_dj :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) hashmap -> ('a, 'b) hashmap
end = struct

datatype ('a, 'b) hashmap = HashMap of ('a, 'b) ArrayHashMap_Impl.hashmap;

fun impl_of A_ (HashMap x) = x;

fun ahm_update (A1_, A2_) k v hm =
  HashMap (ArrayHashMap_Impl.ahm_update (A1_, A2_) k v (impl_of A2_ hm));

fun ahm_iteratei B_ c f hm =
  ArrayHashMap_Impl.ahm_iteratei B_ c f (impl_of B_ hm);

fun ahm_iterate A_ = MapGA.iti_iterate (ahm_iteratei A_);

fun ahm_add (A1_, A2_) = MapGA.it_add (ahm_update (A1_, A2_)) (ahm_iterate A2_);

fun ahm_sel A_ = MapGA.iti_sel (ahm_iteratei A_);

fun ahm_sela A_ = MapGA.sel_sel (ahm_sel A_);

fun ahm_alpha (A1_, A2_) hm =
  ArrayHashMap_Impl.ahm_alpha (A1_, A2_) (impl_of A2_ hm);

fun ahm_empty_const A_ = HashMap (ArrayHashMap_Impl.ahm_empty A_ ());

fun ahm_empty A_ = (fn _ => ahm_empty_const A_);

fun ahm_add_dj (A1_, A2_) = ahm_add (A1_, A2_);

fun ahm_delete (A1_, A2_) k hm =
  HashMap (ArrayHashMap_Impl.ahm_delete (A1_, A2_) k (impl_of A2_ hm));

fun ahm_lookup (A1_, A2_) k hm =
  ArrayHashMap_Impl.ahm_lookup (A1_, A2_) k (impl_of A2_ hm);

fun ahm_isEmpty A_ = MapGA.iti_isEmpty (ahm_iteratei A_);

fun ahm_to_list A_ = MapGA.it_map_to_list (ahm_iterate A_);

fun list_to_ahm (A1_, A2_) =
  MapGA.gen_list_to_map (ahm_empty A2_) (ahm_update (A1_, A2_));

fun ahm_update_dj (A1_, A2_) = ahm_update (A1_, A2_);

end; (*struct ArrayHashMap*)

structure SetByMap : sig
  val s_ins : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val s_sel :
    ('a -> ('b -> unit -> 'c option) -> 'c option) ->
      'a -> ('b -> 'c option) -> 'c option
  val s_memb : ('a -> 'b -> 'c option) -> 'a -> 'b -> bool
  val s_alpha : ('a -> 'b -> unit option) -> 'a -> 'b -> bool
  val s_empty : 'a -> 'a
  val s_union : 'a -> 'a
  val s_delete : 'a -> 'a
  val s_ins_dj : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val s_isEmpty : 'a -> 'a
  val s_iterate :
    (('a -> unit -> 'b -> 'b) -> 'c -> 'b -> 'b) ->
      ('a -> 'b -> 'b) -> 'c -> 'b -> 'b
  val s_iteratei :
    (('a -> bool) -> ('b -> unit -> 'a -> 'a) -> 'c -> 'a -> 'a) ->
      ('a -> bool) -> ('b -> 'a -> 'a) -> 'c -> 'a -> 'a
  val s_union_dj : 'a -> 'a
end = struct

fun s_ins update x s = update x () s;

fun s_sel sel s f = sel s (fn u => fn _ => f u);

fun s_memb lookup x s = not (Option.is_none (lookup x s));

fun s_alpha alpha m = Map.dom (alpha m);

fun s_empty empt = empt;

fun s_union add = add;

fun s_delete delete = delete;

fun s_ins_dj update_dj x s = update_dj x () s;

fun s_isEmpty isEmpty = isEmpty;

fun s_iterate iterate f s sigma_0 = iterate (fn k => fn _ => f k) s sigma_0;

fun s_iteratei iteratei c f s sigma_0 =
  iteratei c (fn k => fn _ => f k) s sigma_0;

fun s_union_dj add_dj = add_dj;

end; (*struct SetByMap*)

structure ArrayHashSet : sig
  val ahs_ins :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahs_sel :
    'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a -> 'b option) -> 'b option
  val ahs_memb :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> bool
  val ahs_sela :
    'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a -> bool) -> 'a option
  val ahs_alpha :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> 'a -> bool
  val ahs_empty :
    'a HashCode.hashable -> unit -> ('a, unit) ArrayHashMap.hashmap
  val ahs_iterate :
    'a HashCode.hashable ->
      ('a -> 'b -> 'b) -> ('a, unit) ArrayHashMap.hashmap -> 'b -> 'b
  val ahs_image_filter :
    'a HashCode.hashable -> 'b HOL.equal * 'b HashCode.hashable ->
      ('a -> 'b option) ->
        ('a, unit) ArrayHashMap.hashmap -> ('b, unit) ArrayHashMap.hashmap
  val ahs_image :
    'a HashCode.hashable -> 'b HOL.equal * 'b HashCode.hashable ->
      ('a -> 'b) ->
        ('a, unit) ArrayHashMap.hashmap -> ('b, unit) ArrayHashMap.hashmap
  val ahs_ins_dj :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahs_inter :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap ->
        ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahs_union :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap ->
        ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahs_delete :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahs_isEmpty :
    'a HashCode.hashable -> ('a, unit) ArrayHashMap.hashmap -> bool
  val ahs_to_list :
    'a HashCode.hashable -> ('a, unit) ArrayHashMap.hashmap -> 'a list
  val list_to_ahs :
    'a HOL.equal * 'a HashCode.hashable ->
      'a list -> ('a, unit) ArrayHashMap.hashmap
  val ahs_iteratei :
    'b HashCode.hashable ->
      ('a -> bool) ->
        ('b -> 'a -> 'a) -> ('b, unit) ArrayHashMap.hashmap -> 'a -> 'a
  val ahs_union_dj :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap ->
        ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
end = struct

fun ahs_ins (A1_, A2_) = SetByMap.s_ins (ArrayHashMap.ahm_update (A1_, A2_));

fun ahs_sel A_ = SetByMap.s_sel (ArrayHashMap.ahm_sel A_);

fun ahs_memb (A1_, A2_) = SetByMap.s_memb (ArrayHashMap.ahm_lookup (A1_, A2_));

fun ahs_sela A_ = SetGA.sel_sel (ahs_sel A_);

fun ahs_alpha (A1_, A2_) = SetByMap.s_alpha (ArrayHashMap.ahm_alpha (A1_, A2_));

fun ahs_empty A_ = SetByMap.s_empty (ArrayHashMap.ahm_empty A_);

fun ahs_iterate A_ = SetByMap.s_iterate (ArrayHashMap.ahm_iterate A_);

fun ahs_image_filter A_ (B1_, B2_) =
  SetGA.it_image_filter (ahs_iterate A_) (ahs_empty B2_) (ahs_ins (B1_, B2_));

fun ahs_image A_ (B1_, B2_) = SetGA.iflt_image (ahs_image_filter A_ (B1_, B2_));

fun ahs_ins_dj (A1_, A2_) =
  SetByMap.s_ins_dj (ArrayHashMap.ahm_update_dj (A1_, A2_));

fun ahs_inter (A1_, A2_) =
  SetGA.it_inter (ahs_iterate A2_) (ahs_memb (A1_, A2_)) (ahs_empty A2_)
    (ahs_ins_dj (A1_, A2_));

fun ahs_union (A1_, A2_) = SetByMap.s_union (ArrayHashMap.ahm_add (A1_, A2_));

fun ahs_delete (A1_, A2_) =
  SetByMap.s_delete (ArrayHashMap.ahm_delete (A1_, A2_));

fun ahs_isEmpty A_ = SetByMap.s_isEmpty (ArrayHashMap.ahm_isEmpty A_);

fun ahs_to_list A_ = SetGA.it_set_to_list (ahs_iterate A_);

fun list_to_ahs (A1_, A2_) =
  SetGA.gen_list_to_set (ahs_empty A2_) (ahs_ins (A1_, A2_));

fun ahs_iteratei B_ = SetByMap.s_iteratei (ArrayHashMap.ahm_iteratei B_);

fun ahs_union_dj (A1_, A2_) =
  SetByMap.s_union_dj (ArrayHashMap.ahm_add_dj (A1_, A2_));

end; (*struct ArrayHashSet*)

structure StdInst : sig
  val aa_diff :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap ->
        ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahm_sng :
    'a HOL.equal * 'a HashCode.hashable ->
      'a -> 'b -> ('a, 'b) ArrayHashMap.hashmap
  val ahs_sng :
    'a HOL.equal * 'a HashCode.hashable -> 'a -> ('a, unit) ArrayHashMap.hashmap
  val ahs_ball :
    'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a -> bool) -> bool
  val aa_subset :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap -> bool
  val aa_equal :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap -> bool
  val ahm_ball :
    'a HashCode.hashable ->
      ('a, 'b) ArrayHashMap.hashmap -> ('a -> 'b -> bool) -> bool
  val ahm_size :
    'a HashCode.hashable -> ('a, 'b) ArrayHashMap.hashmap -> IntInf.int
  val ahs_size :
    'a HashCode.hashable -> ('a, unit) ArrayHashMap.hashmap -> IntInf.int
  val aa_inj_image_filter :
    'a HashCode.hashable -> 'b HOL.equal * 'b HashCode.hashable ->
      ('a -> 'b option) ->
        ('a, unit) ArrayHashMap.hashmap -> ('b, unit) ArrayHashMap.hashmap
  val aa_filter :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> bool) ->
        ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap
  val ahm_size_abort :
    'a HashCode.hashable ->
      IntInf.int -> ('a, 'b) ArrayHashMap.hashmap -> IntInf.int
  val ahm_isSng : 'a HashCode.hashable -> ('a, 'b) ArrayHashMap.hashmap -> bool
  val ahs_size_abort :
    'a HashCode.hashable ->
      IntInf.int -> ('a, unit) ArrayHashMap.hashmap -> IntInf.int
  val ahs_isSng :
    'a HashCode.hashable -> ('a, unit) ArrayHashMap.hashmap -> bool
  val aa_disjoint :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a, unit) ArrayHashMap.hashmap -> bool
  val aa_restrict :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a -> 'b -> bool) ->
        ('a, 'b) ArrayHashMap.hashmap -> ('a, 'b) ArrayHashMap.hashmap
  val ahm_bexists :
    'a HashCode.hashable ->
      ('a, 'b) ArrayHashMap.hashmap -> ('a -> 'b -> bool) -> bool
  val ahs_bexists :
    'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap -> ('a -> bool) -> bool
  val aa_disjoint_witness :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, unit) ArrayHashMap.hashmap ->
        ('a, unit) ArrayHashMap.hashmap -> 'a option
end = struct

fun aa_diff (A1_, A2_) =
  SetGA.it_diff (ArrayHashSet.ahs_iterate A2_)
    (ArrayHashSet.ahs_delete (A1_, A2_));

fun ahm_sng (A1_, A2_) =
  MapGA.eu_sng (ArrayHashMap.ahm_empty A2_)
    (ArrayHashMap.ahm_update (A1_, A2_));

fun ahs_sng (A1_, A2_) =
  SetGA.ei_sng (ArrayHashSet.ahs_empty A2_) (ArrayHashSet.ahs_ins (A1_, A2_));

fun ahs_ball A_ = SetGA.iti_ball (ArrayHashSet.ahs_iteratei A_);

fun aa_subset (A1_, A2_) =
  SetGA.ball_subset (ahs_ball A2_) (ArrayHashSet.ahs_memb (A1_, A2_));

fun aa_equal (A1_, A2_) =
  SetGA.subset_equal (aa_subset (A1_, A2_)) (aa_subset (A1_, A2_));

fun ahm_ball A_ = MapGA.sel_ball (ArrayHashMap.ahm_sel A_);

fun ahm_size A_ = MapGA.it_size (ArrayHashMap.ahm_iterate A_);

fun ahs_size A_ = SetGA.it_size (ArrayHashSet.ahs_iterate A_);

fun aa_inj_image_filter A_ (B1_, B2_) =
  SetGA.it_inj_image_filter (ArrayHashSet.ahs_iterate A_)
    (ArrayHashSet.ahs_empty B2_) (ArrayHashSet.ahs_ins_dj (B1_, B2_));

fun aa_filter (A1_, A2_) =
  SetGA.iflt_filter (aa_inj_image_filter A2_ (A1_, A2_));

fun ahm_size_abort A_ = MapGA.iti_size_abort (ArrayHashMap.ahm_iteratei A_);

fun ahm_isSng A_ = MapGA.sza_isSng (ahm_size_abort A_);

fun ahs_size_abort A_ = SetGA.iti_size_abort (ArrayHashSet.ahs_iteratei A_);

fun ahs_isSng A_ = SetGA.sza_isSng (ahs_size_abort A_);

fun aa_disjoint (A1_, A2_) =
  SetGA.ball_disjoint (ahs_ball A2_) (ArrayHashSet.ahs_memb (A1_, A2_));

fun aa_restrict (A1_, A2_) =
  MapGA.it_map_restrict (ArrayHashMap.ahm_iterate A2_)
    (ArrayHashMap.ahm_empty A2_) (ArrayHashMap.ahm_update_dj (A1_, A2_));

fun ahm_bexists A_ = MapGA.neg_ball_bexists (ahm_ball A_);

fun ahs_bexists A_ = SetGA.neg_ball_bexists (ahs_ball A_);

fun aa_disjoint_witness (A1_, A2_) =
  SetGA.sel_disjoint_witness (ArrayHashSet.ahs_sel A2_)
    (ArrayHashSet.ahs_memb (A1_, A2_));

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

structure Iterator : sig
  val iterate_size :
    ((IntInf.int -> bool) ->
      ('a -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      IntInf.int
  val set_iterator_emp : ('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a
  val set_iterator_sng : 'a -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
end = struct

fun iterate_size it = it (fn _ => true) (fn _ => Arith.suc) (0 : IntInf.int);

fun set_iterator_emp c f sigma_0 = sigma_0;

fun set_iterator_sng x c f sigma_0 =
  (if c sigma_0 then f x sigma_0 else sigma_0);

end; (*struct Iterator*)

structure NFAByLTS : sig
  datatype ('a, 'b) automaton = Nfa_rep of 'a | Dfa_rep of 'b
  val nfa_trans_no :
    ('a ->
      (IntInf.int -> bool) ->
        ('b -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
      ('c ->
        (IntInf.int -> bool) ->
          ('d -> IntInf.int -> IntInf.int) -> IntInf.int -> IntInf.int) ->
        (('e * ('f * ('a * ('g * 'h)))), ('i * ('j * ('c * ('k * 'l)))))
          automaton ->
          IntInf.int
  val hopcroft_pre_fun_aux :
    ('a -> 'b -> 'c -> ('d -> bool) -> ('e -> 'f -> 'f) -> 'g -> 'g) ->
      ('e, 'f, 'h) SetSpec.set_ops_ext ->
        (IntInf.int -> 'b) -> 'a -> 'c -> 'g -> IntInf.int -> 'g
end = struct

datatype ('a, 'b) automaton = Nfa_rep of 'a | Dfa_rep of 'b;

fun nfa_trans_no it_nfa it_dfa (Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  Iterator.iterate_size (it_dfa d2)
  | nfa_trans_no it_nfa it_dfa (Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    Iterator.iterate_size (it_nfa d1);

fun hopcroft_pre_fun_aux succ_it s_ops pim d e s n =
  (if ((n : IntInf.int) = (0 : IntInf.int)) then s
    else let
           val sa =
             succ_it d (pim (Arith.minus_nat n (1 : IntInf.int))) e
               (fn _ => true)
               (SetSpec.set_op_ins s_ops)
               s;
         in
           hopcroft_pre_fun_aux succ_it s_ops pim d e sa
             (Arith.minus_nat n (1 : IntInf.int))
         end);

end; (*struct NFAByLTS*)

structure Sum_Type : sig
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
end = struct

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

end; (*struct Sum_Type*)

structure AHS_LTSImpl : sig
  val ahs_lts_it :
    'a HashCode.hashable -> 'b HashCode.hashable -> 'c HashCode.hashable ->
      ('a, ('b, ('c, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val ahs_dlts_it :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val ahs_lts_add :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      'a -> 'b -> 'a -> ('a, ('b, ('a, unit) ArrayHashMap.hashmap)
                               ArrayHashMap.hashmap)
                          ArrayHashMap.hashmap ->
                          ('a, ('b, ('a, unit) ArrayHashMap.hashmap)
                                 ArrayHashMap.hashmap)
                            ArrayHashMap.hashmap
  val ahs_dlts_add :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      'a -> 'b -> 'a -> ('a, ('b, 'a) ArrayHashMap.hashmap)
                          ArrayHashMap.hashmap ->
                          ('a, ('b, 'a) ArrayHashMap.hashmap)
                            ArrayHashMap.hashmap
  val ahs_lts_empty :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      unit ->
        ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
          ArrayHashMap.hashmap
  val ahs_lts_filter_it :
    'a HashCode.hashable -> 'b HashCode.hashable -> 'c HashCode.hashable ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('c -> bool) ->
            ('a * ('b * 'c) -> bool) ->
              ('a, ('b, ('c, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap ->
                ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val ahs_lts_image_filter :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                  ArrayHashMap.hashmap ->
                  ('c, ('d, ('c, unit) ArrayHashMap.hashmap)
                         ArrayHashMap.hashmap)
                    ArrayHashMap.hashmap
  val ahs_lts_image :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
          ArrayHashMap.hashmap ->
          ('c, ('d, ('c, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
            ArrayHashMap.hashmap
  val ahs_dlts_empty :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      unit -> ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap
  val ahs_dlts_filter_it :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a -> bool) ->
        ('b -> bool) ->
          ('c -> bool) ->
            ('a * ('b * 'c) -> bool) ->
              ('a, ('b, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
                ('d -> bool) -> ('a * ('b * 'c) -> 'd -> 'd) -> 'd -> 'd
  val ahs_dlts_image_filter :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
                  ('c, ('d, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap
  val ahs_dlts_image :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
          ('c, ('d, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap
  val ahs_lts_reverse :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
          ArrayHashMap.hashmap
  val ahs_lts_succ_it :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        'a -> 'b -> ('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c
  val ahs_lts_to_list :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        ('a * ('b * 'a)) list
  val ahs_dlts_succ_it :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        'a -> 'b -> ('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c
  val ahs_dlts_to_list :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        ('a * ('b * 'a)) list
  val ahs_lts_succ_bex :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        ('a -> bool) -> 'a -> 'b -> bool
  val ahs_dlts_succ_bex :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        ('a -> bool) -> 'a -> 'b -> bool
  val ahs_dlts_lts_image_filter :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                  ArrayHashMap.hashmap ->
                  ('c, ('d, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap
  val ahs_dlts_lts_image :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
          ArrayHashMap.hashmap ->
          ('c, ('d, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap
  val ahs_lts_dlts_image_filter :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a -> bool) ->
          ('b -> bool) ->
            ('a -> bool) ->
              ('a * ('b * 'a) -> bool) ->
                ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
                  ('c, ('d, ('c, unit) ArrayHashMap.hashmap)
                         ArrayHashMap.hashmap)
                    ArrayHashMap.hashmap
  val ahs_lts_dlts_image :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
          ('c, ('d, ('c, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
            ArrayHashMap.hashmap
  val ahs_lts_is_weak_det :
    'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        bool
  val ahs_lts_dlts_reverse :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
          ArrayHashMap.hashmap
  val ahs_lts_is_reachable :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        'a -> 'b list -> ('a -> bool) -> bool
  val ahs_dlts_is_reachable :
    'a HOL.equal * 'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        'a -> 'b list -> ('a -> bool) -> bool
  val ahs_lts_succ_label_it :
    'a HOL.equal * 'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        'a -> ('c -> bool) -> ('b * 'a -> 'c -> 'c) -> 'c -> 'c
  val ahs_dlts_succ_label_it :
    'a HOL.equal * 'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        'a -> ('c -> bool) -> ('b * 'a -> 'c -> 'c) -> 'c -> 'c
  val ahs_lts_to_collect_list :
    'a HOL.equal * 'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
        ArrayHashMap.hashmap ->
        ('a * ('b list * 'a)) list
  val ahs_dlts_to_collect_list :
    'a HOL.equal * 'a HashCode.hashable -> 'b HashCode.hashable ->
      ('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap ->
        ('a * ('b list * 'a)) list
end = struct

fun ahs_lts_it A_ B_ C_ =
  (fn l => fn c => fn f =>
    ArrayHashMap.ahm_iteratei A_ c
      (fn v =>
        ArrayHashMap.ahm_iteratei B_ c
          (fn e => ArrayHashSet.ahs_iteratei C_ c (fn va => f (v, (e, va)))))
      l);

fun ahs_dlts_it A_ B_ =
  (fn l => fn c => fn f =>
    ArrayHashMap.ahm_iteratei A_ c
      (fn v => ArrayHashMap.ahm_iteratei B_ c (fn e => fn va => f (v, (e, va))))
      l);

fun ahs_lts_add (A1_, A2_) (B1_, B2_) =
  (fn v => fn w => fn va => fn l =>
    (case ArrayHashMap.ahm_lookup (A1_, A2_) v l
      of NONE =>
        ArrayHashMap.ahm_update (A1_, A2_) v
          (StdInst.ahm_sng (B1_, B2_) w (StdInst.ahs_sng (A1_, A2_) va)) l
      | SOME m2 =>
        (case ArrayHashMap.ahm_lookup (B1_, B2_) w m2
          of NONE =>
            ArrayHashMap.ahm_update (A1_, A2_) v
              (ArrayHashMap.ahm_update (B1_, B2_) w
                (StdInst.ahs_sng (A1_, A2_) va) m2)
              l
          | SOME s3 =>
            ArrayHashMap.ahm_update (A1_, A2_) v
              (ArrayHashMap.ahm_update (B1_, B2_) w
                (ArrayHashSet.ahs_ins (A1_, A2_) va s3) m2)
              l)));

fun ahs_dlts_add (A1_, A2_) (B1_, B2_) =
  (fn v => fn w => fn va => fn l =>
    (case ArrayHashMap.ahm_lookup (A1_, A2_) v l
      of NONE =>
        ArrayHashMap.ahm_update (A1_, A2_) v (StdInst.ahm_sng (B1_, B2_) w va) l
      | SOME m2 =>
        ArrayHashMap.ahm_update (A1_, A2_) v
          (ArrayHashMap.ahm_update (B1_, B2_) w va m2) l));

fun ahs_lts_empty A_ B_ = ArrayHashMap.ahm_empty A_;

fun ahs_lts_filter_it A_ B_ C_ =
  (fn p_v1 => fn p_e => fn p_v2 => fn p => fn l => fn c => fn f =>
    ArrayHashMap.ahm_iteratei A_ c
      (fn v1 => fn m2 => fn sigma =>
        (if p_v1 v1
          then ArrayHashMap.ahm_iteratei B_ c
                 (fn e => fn s3 => fn sigmaa =>
                   (if p_e e
                     then ArrayHashSet.ahs_iteratei C_ c
                            (fn v2 => fn sigmab =>
                              (if p_v2 v2 andalso p (v1, (e, v2))
                                then f (v1, (e, v2)) sigmab else sigmab))
                            s3 sigmaa
                     else sigmaa))
                 m2 sigma
          else sigma))
      l);

fun ahs_lts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f => fn p_v1 => fn p_e => fn p_v2 => fn p => fn l =>
    ahs_lts_filter_it A_ B_ A_ p_v1 p_e p_v2 p l (fn _ => true)
      (fn vev => fn la =>
        let
          val (v, (e, va)) = f vev;
        in
          ahs_lts_add (C1_, C2_) (D1_, D2_) v e va la
        end)
      (ahs_lts_empty C2_ D2_ ()));

fun ahs_lts_image A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f =>
    ahs_lts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) f (fn _ => true)
      (fn _ => true) (fn _ => true) (fn _ => true));

fun ahs_dlts_empty A_ B_ = ArrayHashMap.ahm_empty A_;

fun ahs_dlts_filter_it A_ B_ =
  (fn p_v1 => fn p_e => fn p_v2 => fn p => fn m1 => fn c => fn f =>
    ArrayHashMap.ahm_iteratei A_ c
      (fn x => fn y => fn sigma =>
        (if p_v1 x
          then ArrayHashMap.ahm_iteratei B_ c
                 (fn xa => fn ya => fn sigmaa =>
                   (if p_v2 ya andalso (p_e xa andalso p (x, (xa, ya)))
                     then f (x, (xa, ya)) sigmaa else sigmaa))
                 y sigma
          else sigma))
      m1);

fun ahs_dlts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f => fn p_v1 => fn p_e => fn p_v2 => fn p => fn l =>
    ahs_dlts_filter_it A_ B_ p_v1 p_e p_v2 p l (fn _ => true)
      (fn vev => fn la =>
        let
          val (v, (e, va)) = f vev;
        in
          ahs_dlts_add (C1_, C2_) (D1_, D2_) v e va la
        end)
      (ahs_dlts_empty C2_ D2_ ()));

fun ahs_dlts_image A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f =>
    ahs_dlts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) f (fn _ => true)
      (fn _ => true) (fn _ => true) (fn _ => true));

fun ahs_lts_reverse (A1_, A2_) (B1_, B2_) =
  (fn l =>
    ahs_lts_it A2_ B2_ A2_ l (fn _ => true)
      (fn (v, (e, va)) => ahs_lts_add (A1_, A2_) (B1_, B2_) va e v)
      (ahs_lts_empty A2_ B2_ ()));

fun ahs_lts_succ_it (A1_, A2_) (B1_, B2_) =
  (fn m1 => fn v => fn e =>
    (case ArrayHashMap.ahm_lookup (A1_, A2_) v m1
      of NONE => Iterator.set_iterator_emp
      | SOME m2 =>
        (case ArrayHashMap.ahm_lookup (B1_, B2_) e m2
          of NONE => Iterator.set_iterator_emp
          | SOME s3 =>
            (fn c => fn f => ArrayHashSet.ahs_iteratei A2_ c f s3))));

fun ahs_lts_to_list A_ B_ =
  (fn x => ahs_lts_it A_ B_ A_ x (fn _ => true) (fn a => fn b => a :: b) []);

fun ahs_dlts_succ_it (A1_, A2_) (B1_, B2_) =
  (fn m1 => fn v => fn e =>
    (case ArrayHashMap.ahm_lookup (A1_, A2_) v m1
      of NONE => Iterator.set_iterator_emp
      | SOME m2 =>
        (case ArrayHashMap.ahm_lookup (B1_, B2_) e m2
          of NONE => Iterator.set_iterator_emp
          | SOME a => Iterator.set_iterator_sng a)));

fun ahs_dlts_to_list A_ B_ =
  (fn x => ahs_dlts_it A_ B_ x (fn _ => true) (fn a => fn b => a :: b) []);

fun ahs_lts_succ_bex (A1_, A2_) (B1_, B2_) =
  (fn l => fn p => fn v => fn e =>
    ahs_lts_succ_it (A1_, A2_) (B1_, B2_) l v e not (fn x => fn _ => p x)
      false);

fun ahs_dlts_succ_bex (A1_, A2_) (B1_, B2_) =
  (fn l => fn p => fn v => fn e =>
    ahs_dlts_succ_it (A1_, A2_) (B1_, B2_) l v e not (fn x => fn _ => p x)
      false);

fun ahs_dlts_lts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f => fn p_v1 => fn p_e => fn p_v2 => fn p => fn l =>
    ahs_lts_filter_it A_ B_ A_ p_v1 p_e p_v2 p l (fn _ => true)
      (fn vev => fn la =>
        let
          val (v, (e, va)) = f vev;
        in
          ahs_dlts_add (C1_, C2_) (D1_, D2_) v e va la
        end)
      (ahs_dlts_empty C2_ D2_ ()));

fun ahs_dlts_lts_image A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f =>
    ahs_dlts_lts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) f (fn _ => true)
      (fn _ => true) (fn _ => true) (fn _ => true));

fun ahs_lts_dlts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f => fn p_v1 => fn p_e => fn p_v2 => fn p => fn l =>
    ahs_dlts_filter_it A_ B_ p_v1 p_e p_v2 p l (fn _ => true)
      (fn vev => fn la =>
        let
          val (v, (e, va)) = f vev;
        in
          ahs_lts_add (C1_, C2_) (D1_, D2_) v e va la
        end)
      (ahs_lts_empty C2_ D2_ ()));

fun ahs_lts_dlts_image A_ B_ (C1_, C2_) (D1_, D2_) =
  (fn f =>
    ahs_lts_dlts_image_filter A_ B_ (C1_, C2_) (D1_, D2_) f (fn _ => true)
      (fn _ => true) (fn _ => true) (fn _ => true));

fun ahs_lts_is_weak_det A_ B_ =
  (fn l =>
    StdInst.ahm_ball A_ l
      (fn _ => fn m2 =>
        StdInst.ahm_ball B_ m2
          (fn _ => fn s3 =>
            IntInf.< (StdInst.ahs_size_abort A_ (2 : IntInf.int)
                        s3, (2 : IntInf.int)))));

fun ahs_lts_dlts_reverse (A1_, A2_) (B1_, B2_) =
  (fn l =>
    ahs_dlts_it A2_ B2_ l (fn _ => true)
      (fn (v, (e, va)) => ahs_lts_add (A1_, A2_) (B1_, B2_) va e v)
      (ahs_lts_empty A2_ B2_ ()));

fun ahs_lts_is_reachable (A1_, A2_) (B1_, B2_) l qa (sigma :: w) q =
  ahs_lts_succ_bex (A1_, A2_) (B1_, B2_) l
    (fn qaa => ahs_lts_is_reachable (A1_, A2_) (B1_, B2_) l qaa w q) qa sigma
  | ahs_lts_is_reachable (A1_, A2_) (B1_, B2_) l qa [] q = q qa;

fun ahs_dlts_is_reachable (A1_, A2_) (B1_, B2_) l qa (sigma :: w) q =
  ahs_dlts_succ_bex (A1_, A2_) (B1_, B2_) l
    (fn qaa => ahs_dlts_is_reachable (A1_, A2_) (B1_, B2_) l qaa w q) qa sigma
  | ahs_dlts_is_reachable (A1_, A2_) (B1_, B2_) l qa [] q = q qa;

fun ahs_lts_succ_label_it (A1_, A2_) B_ =
  (fn m1 => fn v =>
    (case ArrayHashMap.ahm_lookup (A1_, A2_) v m1
      of NONE => (fn _ => fn _ => fn sigma_0 => sigma_0)
      | SOME m2 =>
        (fn c => fn f =>
          ArrayHashMap.ahm_iteratei B_ c
            (fn x => ArrayHashSet.ahs_iteratei A2_ c (fn b => f (x, b))) m2)));

fun ahs_dlts_succ_label_it (A1_, A2_) B_ =
  (fn m1 => fn v =>
    (case ArrayHashMap.ahm_lookup (A1_, A2_) v m1
      of NONE => (fn _ => fn _ => fn sigma_0 => sigma_0)
      | SOME m2 =>
        (fn c => fn f =>
          ArrayHashMap.ahm_iteratei B_ c (fn x => fn y => f (x, y)) m2)));

fun ahs_lts_to_collect_list (A1_, A2_) B_ =
  (fn l => LTSGA.ltsga_list_to_collect_list A1_ A1_ (ahs_lts_to_list A2_ B_ l));

fun ahs_dlts_to_collect_list (A1_, A2_) B_ =
  (fn l =>
    LTSGA.ltsga_list_to_collect_list A1_ A1_ (ahs_dlts_to_list A2_ B_ l));

end; (*struct AHS_LTSImpl*)

structure RecordMapImpl : sig
  val ahm_ops :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, 'b, ('a, 'b) ArrayHashMap.hashmap, unit) MapSpec.map_ops_ext
end = struct

fun ahm_ops (A1_, A2_) =
  MapSpec.Map_ops_ext
    (ArrayHashMap.ahm_alpha (A1_, A2_), (fn _ => true),
      ArrayHashMap.ahm_empty A2_, StdInst.ahm_sng (A1_, A2_),
      ArrayHashMap.ahm_lookup (A1_, A2_), ArrayHashMap.ahm_update (A1_, A2_),
      ArrayHashMap.ahm_update_dj (A1_, A2_), ArrayHashMap.ahm_delete (A1_, A2_),
      StdInst.aa_restrict (A1_, A2_), ArrayHashMap.ahm_add (A1_, A2_),
      ArrayHashMap.ahm_add_dj (A1_, A2_), ArrayHashMap.ahm_isEmpty A2_,
      StdInst.ahm_isSng A2_, StdInst.ahm_ball A2_, StdInst.ahm_bexists A2_,
      StdInst.ahm_size A2_, StdInst.ahm_size_abort A2_,
      ArrayHashMap.ahm_sela A2_, ArrayHashMap.ahm_to_list A2_,
      ArrayHashMap.list_to_ahm (A1_, A2_), ());

end; (*struct RecordMapImpl*)

structure RecordSetImpl : sig
  val ahs_ops :
    'a HOL.equal * 'a HashCode.hashable ->
      ('a, ('a, unit) ArrayHashMap.hashmap, unit) SetSpec.set_ops_ext
end = struct

fun ahs_ops (A1_, A2_) =
  SetSpec.Set_ops_ext
    (ArrayHashSet.ahs_alpha (A1_, A2_), (fn _ => true),
      ArrayHashSet.ahs_empty A2_, StdInst.ahs_sng (A1_, A2_),
      ArrayHashSet.ahs_memb (A1_, A2_), ArrayHashSet.ahs_ins (A1_, A2_),
      ArrayHashSet.ahs_ins_dj (A1_, A2_), ArrayHashSet.ahs_delete (A1_, A2_),
      ArrayHashSet.ahs_isEmpty A2_, StdInst.ahs_isSng A2_, StdInst.ahs_ball A2_,
      StdInst.ahs_bexists A2_, StdInst.ahs_size A2_, StdInst.ahs_size_abort A2_,
      ArrayHashSet.ahs_union (A1_, A2_), ArrayHashSet.ahs_union_dj (A1_, A2_),
      StdInst.aa_diff (A1_, A2_), StdInst.aa_filter (A1_, A2_),
      ArrayHashSet.ahs_inter (A1_, A2_), StdInst.aa_subset (A1_, A2_),
      StdInst.aa_equal (A1_, A2_), StdInst.aa_disjoint (A1_, A2_),
      StdInst.aa_disjoint_witness (A1_, A2_), ArrayHashSet.ahs_sela A2_,
      ArrayHashSet.ahs_to_list A2_, ArrayHashSet.list_to_ahs (A1_, A2_), ());

end; (*struct RecordSetImpl*)

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
              (('n -> bool) ->
                ('e -> 'l * ('h * 'j) -> 'l * ('h * 'j)) ->
                  'o -> 'l * 'p -> 'q) ->
                'p -> 'o -> 'c * ('f * 'r) -> 'q
  val hopcroft_code_step :
    (('a -> bool) ->
      (IntInf.int ->
        IntInf.int ->
          ('b * ('c * IntInf.int)) * ('d * IntInf.int) list ->
            ('b * ('c * IntInf.int)) * ('d * IntInf.int) list) ->
        'e -> ('b * ('c * 'f)) * 'g -> 'h * 'i) ->
      (('j -> bool) ->
        ('k -> 'l * ('m * 'n) -> 'l * ('m * 'n)) ->
          'o -> 'l * 'p -> 'e * ('q * 'n)) ->
        (IntInf.int, IntInf.int, 'l, 'r) MapSpec.map_ops_ext ->
          (IntInf.int, 'k, 'n, 's) MapSpec.map_ops_ext ->
            ('k, IntInf.int, 'm, 't) MapSpec.map_ops_ext ->
              ('k, IntInf.int, 'c, 'u) MapSpec.map_ops_ext ->
                (IntInf.int, (IntInf.int * IntInf.int), 'b, 'v)
                  MapSpec.map_ops_ext ->
                  'd list ->
                    'o -> 'b * ('c * 'f) -> 'g -> 'p -> ('h * 'i) * ('q * 'n)
  val class_map_init_pred_code :
    'f Arith.zero ->
      (('a -> bool) ->
        ('b -> ('c * 'd) * IntInf.int -> ('c * 'd) * IntInf.int) ->
          'e -> ('c * 'd) * 'f -> ('c * 'd) * 'f) ->
        ('b, IntInf.int, 'c, 'g) MapSpec.map_ops_ext ->
          (IntInf.int, 'b, 'd, 'h) MapSpec.map_ops_ext ->
            'e -> 'e -> ('c * 'd) * ('f * 'f)
  val hopcroft_code :
    (IntInf.int, IntInf.int, 'a, 'b) MapSpec.map_ops_ext ->
      (('c -> bool) ->
        ('d -> 'a * ('e * 'f) -> 'a * ('e * 'f)) ->
          'g -> 'a * ('e * 'f) -> 'h * ('e * 'f)) ->
        (('i -> bool) ->
          (IntInf.int ->
            IntInf.int ->
              ('j * ('k * IntInf.int)) * ('l * IntInf.int) list ->
                ('j * ('k * IntInf.int)) * ('l * IntInf.int) list) ->
            'h -> ('j * ('k * IntInf.int)) * ('l * IntInf.int) list ->
                    ('j * ('k * IntInf.int)) * ('l * IntInf.int) list) ->
          (('m -> bool) -> ('d -> 'k -> 'k) -> 'n -> 'k -> 'k) ->
            ('d, IntInf.int, 'k, 'o) MapSpec.map_ops_ext ->
              (IntInf.int, (IntInf.int * IntInf.int), 'j, 'p)
                MapSpec.map_ops_ext ->
                (IntInf.int, 'd, 'f, 'q) MapSpec.map_ops_ext ->
                  ('d, IntInf.int, 'e, 'r) MapSpec.map_ops_ext ->
                    (('s -> bool) ->
                      ('d ->
                        ('e * 'f) * IntInf.int -> ('e * 'f) * IntInf.int) ->
                        'n -> ('e * 'f) * IntInf.int ->
                                ('e * 'f) * IntInf.int) ->
                      ('t, 'n, 'u) SetSpec.set_ops_ext ->
                        'n -> 'n -> 'l list ->
                                      ('l ->
'f -> IntInf.int * IntInf.int -> 'g) ->
('j * ('k * IntInf.int)) * ('e * 'f)
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
  pre_it cm pre (im, (sm, n)) =
  pre_it (fn _ => true)
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
    pre
    (MapSpec.map_op_empty iM_ops (), cm);

fun hopcroft_code_step iM_it pre_it iM_ops pim_ops pm_ops sm_ops im_ops aL pre p
  l cm =
  let
    val (iM, cma) =
      hopcroft_code_step_compute_iM_swap_check im_ops sm_ops pm_ops pim_ops
        iM_ops pre_it cm pre p;
    val (pa, la) =
      iM_it (fn _ => true)
        (fn pa => fn s => fn (a, b) =>
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
        iM
        (p, l);
  in
    ((pa, la), cma)
  end;

fun class_map_init_pred_code F_ cm_it pm_ops pim_ops qf f =
  let
    val cm0 = (MapSpec.map_op_empty pm_ops (), MapSpec.map_op_empty pim_ops ());
    val (cm1, s) =
      cm_it (fn _ => true)
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
        qf
        (cm0, Arith.zero F_);
    val (cm2, m) =
      cm_it (fn _ => true)
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
        f
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
                     (sm_it (fn _ => true)
                        (fn qa =>
                          MapSpec.map_op_update sm_ops qa (0 : IntInf.int))
                        q
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
                                   (sm_it (fn _ => true)
                                      (fn qa =>
MapSpec.map_op_update sm_ops qa (0 : IntInf.int))
                                      q
                                      (MapSpec.map_op_empty sm_ops ()),
                                     (1 : IntInf.int)))
                            else (MapSpec.map_op_update im_ops
                                    (Arith.suc (0 : IntInf.int))
                                    ((0 : IntInf.int),
                                      Arith.minus_nat aa (1 : IntInf.int))
                                    (MapSpec.map_op_sng im_ops (0 : IntInf.int)
                                      (aa,
Arith.minus_nat ba (1 : IntInf.int))),
                                   (sm_it (fn _ => true)
                                      (fn qa =>
MapSpec.map_op_update sm_ops qa (0 : IntInf.int))
                                      f
                                      (sm_it (fn _ => true)
 (fn qa => MapSpec.map_op_update sm_ops qa (1 : IntInf.int))
 x
(MapSpec.map_op_empty sm_ops ())),
                                     (2 : IntInf.int)))),
                           l_insert_impl (0 : IntInf.int) [] al),
                          a);
                  in
                    (ac, bb)
                  end))
  end;

end; (*struct Hopcroft_Minimisation*)

structure AHS_NFAImpl : sig
  val ahs_nfa_accept :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        'b list -> bool
  val ahs_nfa_reverse :
    'c HOL.equal * 'c HashCode.hashable * 'c NFA.nFA_states ->
      'd HOL.equal * 'd HashCode.hashable ->
      (('a * ('b * (('c, ('d, ('c, unit) ArrayHashMap.hashmap)
                           ArrayHashMap.hashmap)
                      ArrayHashMap.hashmap *
                     ('e * 'f)))),
        ('a * ('b * (('c, ('d, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                      ('e * 'f)))))
        NFAByLTS.automaton ->
        (('a * ('b * (('c, ('d, ('c, unit) ArrayHashMap.hashmap)
                             ArrayHashMap.hashmap)
                        ArrayHashMap.hashmap *
                       ('f * 'e)))),
          'g)
          NFAByLTS.automaton
  val ahs_nfa_Hopcroft :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        ((('a, unit) ArrayHashMap.hashmap *
           (('b, unit) ArrayHashMap.hashmap *
             (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('a, unit) ArrayHashMap.hashmap *
                 ('a, unit) ArrayHashMap.hashmap)))),
          (('a, unit) ArrayHashMap.hashmap *
            (('b, unit) ArrayHashMap.hashmap *
              (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                (('a, unit) ArrayHashMap.hashmap *
                  ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_destruct :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        'a list * ('b list * (('a * ('b list * 'a)) list * ('a list * 'a list)))
  val ahs_nfa_final_no :
    'e HashCode.hashable * 'e NFA.nFA_states ->
      (('a * ('b * ('c * ('d * ('e, unit) ArrayHashMap.hashmap)))),
        ('f * ('g * ('h * ('i * ('e, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        IntInf.int
  val ahs_nfa_trans_no :
    'c HashCode.hashable -> 'd HashCode.hashable -> 'e HashCode.hashable ->
      'j HashCode.hashable -> 'k HashCode.hashable ->
      (('a * ('b * (('c, ('d, ('e, unit) ArrayHashMap.hashmap)
                           ArrayHashMap.hashmap)
                      ArrayHashMap.hashmap *
                     ('f * 'g)))),
        ('h * ('i * (('j, ('k, 'l) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                      ('m * 'n)))))
        NFAByLTS.automaton ->
        IntInf.int
  val ahs_dfa_construct :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      'a list *
        ('b list * (('a * ('b list * 'a)) list * ('a list * 'a list))) ->
        ('c, (('a, unit) ArrayHashMap.hashmap *
               (('b, unit) ArrayHashMap.hashmap *
                 (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                   (('a, unit) ArrayHashMap.hashmap *
                     ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_bool_comb :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      (bool -> bool -> bool) ->
        ((('a, unit) ArrayHashMap.hashmap *
           (('b, unit) ArrayHashMap.hashmap *
             (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('a, unit) ArrayHashMap.hashmap *
                 ('a, unit) ArrayHashMap.hashmap)))),
          (('a, unit) ArrayHashMap.hashmap *
            (('b, unit) ArrayHashMap.hashmap *
              (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                (('a, unit) ArrayHashMap.hashmap *
                  ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton ->
          ((('a, unit) ArrayHashMap.hashmap *
             (('b, unit) ArrayHashMap.hashmap *
               (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                  ArrayHashMap.hashmap *
                 (('a, unit) ArrayHashMap.hashmap *
                   ('a, unit) ArrayHashMap.hashmap)))),
            (('a, unit) ArrayHashMap.hashmap *
              (('b, unit) ArrayHashMap.hashmap *
                (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                  (('a, unit) ArrayHashMap.hashmap *
                    ('a, unit) ArrayHashMap.hashmap)))))
            NFAByLTS.automaton ->
            ((('a, unit) ArrayHashMap.hashmap *
               (('b, unit) ArrayHashMap.hashmap *
                 (('a, ('b, ('a, unit) ArrayHashMap.hashmap)
                         ArrayHashMap.hashmap)
                    ArrayHashMap.hashmap *
                   (('a, unit) ArrayHashMap.hashmap *
                     ('a, unit) ArrayHashMap.hashmap)))),
              (('a, unit) ArrayHashMap.hashmap *
                (('b, unit) ArrayHashMap.hashmap *
                  (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                    (('a, unit) ArrayHashMap.hashmap *
                      ('a, unit) ArrayHashMap.hashmap)))))
              NFAByLTS.automaton
  val ahs_nfa_construct :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      'a list *
        ('b list * (('a * ('b list * 'a)) list * ('a list * 'a list))) ->
        ((('a, unit) ArrayHashMap.hashmap *
           (('b, unit) ArrayHashMap.hashmap *
             (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('a, unit) ArrayHashMap.hashmap *
                 ('a, unit) ArrayHashMap.hashmap)))),
          'c)
          NFAByLTS.automaton
  val ahs_nfa_labels_no :
    'b HashCode.hashable ->
      (('a * (('b, unit) ArrayHashMap.hashmap * ('c * ('d * 'e)))),
        ('f * (('b, unit) ArrayHashMap.hashmap * ('g * ('h * 'i)))))
        NFAByLTS.automaton ->
        IntInf.int
  val ahs_nfa_normalise :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        ((('a, unit) ArrayHashMap.hashmap *
           (('b, unit) ArrayHashMap.hashmap *
             (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('a, unit) ArrayHashMap.hashmap *
                 ('a, unit) ArrayHashMap.hashmap)))),
          (('a, unit) ArrayHashMap.hashmap *
            (('b, unit) ArrayHashMap.hashmap *
              (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                (('a, unit) ArrayHashMap.hashmap *
                  ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_states_no :
    'a HashCode.hashable * 'a NFA.nFA_states ->
      ((('a, unit) ArrayHashMap.hashmap * ('b * ('c * ('d * 'e)))),
        (('a, unit) ArrayHashMap.hashmap * ('f * ('g * ('h * 'i)))))
        NFAByLTS.automaton ->
        IntInf.int
  val ahs_nfa_determinise :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        ('c, (('a, unit) ArrayHashMap.hashmap *
               (('b, unit) ArrayHashMap.hashmap *
                 (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                   (('a, unit) ArrayHashMap.hashmap *
                     ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_Brzozowski :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        ((('a, unit) ArrayHashMap.hashmap *
           (('b, unit) ArrayHashMap.hashmap *
             (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('a, unit) ArrayHashMap.hashmap *
                 ('a, unit) ArrayHashMap.hashmap)))),
          (('a, unit) ArrayHashMap.hashmap *
            (('b, unit) ArrayHashMap.hashmap *
              (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                (('a, unit) ArrayHashMap.hashmap *
                  ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_complement :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      ((('a, unit) ArrayHashMap.hashmap *
         ('b * ('c * ('d * ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          ('e * ('f * ('g * ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        ((('a, unit) ArrayHashMap.hashmap *
           ('b * ('c * ('d * ('a, unit) ArrayHashMap.hashmap)))),
          (('a, unit) ArrayHashMap.hashmap *
            ('e * ('f * ('g * ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_initial_no :
    'd HashCode.hashable * 'd NFA.nFA_states ->
      (('a * ('b * ('c * (('d, unit) ArrayHashMap.hashmap * 'e)))),
        ('f * ('g * ('h * (('d, unit) ArrayHashMap.hashmap * 'i)))))
        NFAByLTS.automaton ->
        IntInf.int
  val ahs_nfa_Hopcroft_NFA :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        ((('a, unit) ArrayHashMap.hashmap *
           (('b, unit) ArrayHashMap.hashmap *
             (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('a, unit) ArrayHashMap.hashmap *
                 ('a, unit) ArrayHashMap.hashmap)))),
          (('a, unit) ArrayHashMap.hashmap *
            (('b, unit) ArrayHashMap.hashmap *
              (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                (('a, unit) ArrayHashMap.hashmap *
                  ('a, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_nfa_bool_comb_gen :
    'b HOL.equal * 'b HashCode.hashable * 'b NFA.nFA_states ->
      'c HOL.equal * 'c HashCode.hashable ->
      'a -> (bool -> bool -> bool) ->
              ((('b, unit) ArrayHashMap.hashmap *
                 (('c, unit) ArrayHashMap.hashmap *
                   (('b, ('c, ('b, unit) ArrayHashMap.hashmap)
                           ArrayHashMap.hashmap)
                      ArrayHashMap.hashmap *
                     (('b, unit) ArrayHashMap.hashmap *
                       ('b, unit) ArrayHashMap.hashmap)))),
                (('b, unit) ArrayHashMap.hashmap *
                  (('c, unit) ArrayHashMap.hashmap *
                    (('b, ('c, 'b) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                      (('b, unit) ArrayHashMap.hashmap *
                        ('b, unit) ArrayHashMap.hashmap)))))
                NFAByLTS.automaton ->
                ((('b, unit) ArrayHashMap.hashmap *
                   (('c, unit) ArrayHashMap.hashmap *
                     (('b, ('c, ('b, unit) ArrayHashMap.hashmap)
                             ArrayHashMap.hashmap)
                        ArrayHashMap.hashmap *
                       (('b, unit) ArrayHashMap.hashmap *
                         ('b, unit) ArrayHashMap.hashmap)))),
                  (('b, unit) ArrayHashMap.hashmap *
                    (('c, unit) ArrayHashMap.hashmap *
                      (('b, ('c, 'b) ArrayHashMap.hashmap)
                         ArrayHashMap.hashmap *
                        (('b, unit) ArrayHashMap.hashmap *
                          ('b, unit) ArrayHashMap.hashmap)))))
                  NFAByLTS.automaton ->
                  ((('b, unit) ArrayHashMap.hashmap *
                     ('a * (('b, ('c, ('b, unit) ArrayHashMap.hashmap)
                                   ArrayHashMap.hashmap)
                              ArrayHashMap.hashmap *
                             (('b, unit) ArrayHashMap.hashmap *
                               ('b, unit) ArrayHashMap.hashmap)))),
                    (('b, unit) ArrayHashMap.hashmap *
                      ('a * (('b, ('c, 'b) ArrayHashMap.hashmap)
                               ArrayHashMap.hashmap *
                              (('b, unit) ArrayHashMap.hashmap *
                                ('b, unit) ArrayHashMap.hashmap)))))
                    NFAByLTS.automaton
  val ahs_nfa_rename_labels :
    'b HOL.equal * 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable * 'c NFA.nFA_states ->
      (('a * (('b, unit) ArrayHashMap.hashmap *
               (('c, ('b, ('c, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                  ArrayHashMap.hashmap *
                 ('d * 'e)))),
        ('a * (('b, unit) ArrayHashMap.hashmap *
                (('c, ('b, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                  ('d * 'e)))))
        NFAByLTS.automaton ->
        ('b -> 'b) ->
          (('a * (('b, unit) ArrayHashMap.hashmap *
                   (('c, ('b, ('c, unit) ArrayHashMap.hashmap)
                           ArrayHashMap.hashmap)
                      ArrayHashMap.hashmap *
                     ('d * 'e)))),
            'f)
            NFAByLTS.automaton
  val ahs_nfa_destruct_simple :
    'a HashCode.hashable * 'a NFA.nFA_states -> 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               ('a, unit) ArrayHashMap.hashmap)))),
        (('a, unit) ArrayHashMap.hashmap *
          (('b, unit) ArrayHashMap.hashmap *
            (('a, ('b, 'a) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                ('a, unit) ArrayHashMap.hashmap)))))
        NFAByLTS.automaton ->
        'a list * ('b list * (('a * ('b * 'a)) list * ('a list * 'a list)))
  val ahs_nfa_is_deterministic :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      'b HOL.equal * 'b HashCode.hashable ->
      ((('a, unit) ArrayHashMap.hashmap *
         (('b, unit) ArrayHashMap.hashmap *
           (('a, ('b, ('a, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
              ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap * 'c)))),
        'd)
        NFAByLTS.automaton ->
        bool
  val ahs_nfa_rename_labels_gen :
    'c HOL.equal * 'c HashCode.hashable * 'c NFA.nFA_states ->
      'd HOL.equal * 'd HashCode.hashable ->
      (('a * ('b * (('c, ('d, ('c, unit) ArrayHashMap.hashmap)
                           ArrayHashMap.hashmap)
                      ArrayHashMap.hashmap *
                     ('e * 'f)))),
        ('a * ('g * (('c, ('d, 'c) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                      ('e * 'f)))))
        NFAByLTS.automaton ->
        'h -> ('d -> 'd) ->
                (('a * ('h * (('c, ('d, ('c, unit) ArrayHashMap.hashmap)
                                     ArrayHashMap.hashmap)
                                ArrayHashMap.hashmap *
                               ('e * 'f)))),
                  'i)
                  NFAByLTS.automaton
  val ahs_dfa_construct_reachable :
    'b HOL.equal * 'b HashCode.hashable ->
      'd HOL.equal * 'd HashCode.hashable * 'd NFA.nFA_states ->
      'e HOL.equal * 'e HashCode.hashable ->
      ('a -> 'b) ->
        'a list ->
          'c -> ('a -> bool) ->
                  ('a ->
                    ((('b, 'd) ArrayHashMap.hashmap * IntInf.int) *
                       (('d, ('e, 'd) ArrayHashMap.hashmap)
                          ArrayHashMap.hashmap *
                         'a list) ->
                      bool) ->
                      ('e * 'a ->
                        (('b, 'd) ArrayHashMap.hashmap * IntInf.int) *
                          (('d, ('e, 'd) ArrayHashMap.hashmap)
                             ArrayHashMap.hashmap *
                            'a list) ->
                          (('b, 'd) ArrayHashMap.hashmap * IntInf.int) *
                            (('d, ('e, 'd) ArrayHashMap.hashmap)
                               ArrayHashMap.hashmap *
                              'a list)) ->
                        (('b, 'd) ArrayHashMap.hashmap * IntInf.int) *
                          (('d, ('e, 'd) ArrayHashMap.hashmap)
                             ArrayHashMap.hashmap *
                            'f list) ->
                          (('b, 'd) ArrayHashMap.hashmap * IntInf.int) *
                            (('d, ('e, 'd) ArrayHashMap.hashmap)
                               ArrayHashMap.hashmap *
                              'a list)) ->
                    ('g, (('d, unit) ArrayHashMap.hashmap *
                           ('c * (('d, ('e, 'd) ArrayHashMap.hashmap)
                                    ArrayHashMap.hashmap *
                                   (('d, unit) ArrayHashMap.hashmap *
                                     ('d, unit) ArrayHashMap.hashmap)))))
                      NFAByLTS.automaton
  val ahs_nfa_right_quotient_lists :
    'a HashCode.hashable ->
      'b HOL.equal * 'b HashCode.hashable * 'b NFA.nFA_states ->
      ('a -> bool) ->
        ((('b, unit) ArrayHashMap.hashmap *
           (('a, unit) ArrayHashMap.hashmap *
             (('b, ('a, ('b, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               (('b, unit) ArrayHashMap.hashmap *
                 ('b, unit) ArrayHashMap.hashmap)))),
          (('b, unit) ArrayHashMap.hashmap *
            (('a, unit) ArrayHashMap.hashmap *
              (('b, ('a, 'b) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                (('b, unit) ArrayHashMap.hashmap *
                  ('b, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton ->
          ((('b, unit) ArrayHashMap.hashmap *
             (('a, unit) ArrayHashMap.hashmap *
               (('b, ('a, ('b, unit) ArrayHashMap.hashmap) ArrayHashMap.hashmap)
                  ArrayHashMap.hashmap *
                 (('b, unit) ArrayHashMap.hashmap *
                   ('b, unit) ArrayHashMap.hashmap)))),
            (('b, unit) ArrayHashMap.hashmap *
              (('a, unit) ArrayHashMap.hashmap *
                (('b, ('a, 'b) ArrayHashMap.hashmap) ArrayHashMap.hashmap *
                  (('b, unit) ArrayHashMap.hashmap *
                    ('b, unit) ArrayHashMap.hashmap)))))
            NFAByLTS.automaton
  val ahs_dfa_construct_reachable_fun :
    'b HOL.equal * 'b HashCode.hashable ->
      'c HOL.equal * 'c HashCode.hashable ->
      'e HOL.equal * 'e HashCode.hashable * 'e NFA.nFA_states ->
      ('a -> 'b) ->
        'a -> ('c, unit) ArrayHashMap.hashmap ->
                ('a -> bool) ->
                  ('a -> 'c -> 'a) ->
                    ('d, (('e, unit) ArrayHashMap.hashmap *
                           (('c, unit) ArrayHashMap.hashmap *
                             (('e, ('c, 'e) ArrayHashMap.hashmap)
                                ArrayHashMap.hashmap *
                               (('e, unit) ArrayHashMap.hashmap *
                                 ('e, unit) ArrayHashMap.hashmap)))))
                      NFAByLTS.automaton
end = struct

fun ahs_nfa_accept (A1_, A2_, A3_) (B1_, B2_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  (fn w =>
    StdInst.ahs_bexists A2_ i2
      (fn i =>
        AHS_LTSImpl.ahs_dlts_is_reachable (A1_, A2_) (B1_, B2_) d2 i w
          (fn q => ArrayHashSet.ahs_memb (A1_, A2_) q f2)))
  | ahs_nfa_accept (A1_, A2_, A3_) (B1_, B2_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    (fn w =>
      StdInst.ahs_bexists A2_ i1
        (fn i =>
          AHS_LTSImpl.ahs_lts_is_reachable (A1_, A2_) (B1_, B2_) d1 i w
            (fn q => ArrayHashSet.ahs_memb (A1_, A2_) q f1)));

fun ahs_nfa_reverse (C1_, C2_, C3_) (D1_, D2_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  NFAByLTS.Nfa_rep
    (q2, (a2, (AHS_LTSImpl.ahs_lts_dlts_reverse (C1_, C2_) (D1_, D2_) d2,
                (f2, i2))))
  | ahs_nfa_reverse (C1_, C2_, C3_) (D1_, D2_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    NFAByLTS.Nfa_rep
      (q1, (a1, (AHS_LTSImpl.ahs_lts_reverse (C1_, C2_) (D1_, D2_) d1,
                  (f1, i1))));

fun ahs_nfa_Hopcroft (A1_, A2_, A3_) (B1_, B2_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  NFAByLTS.Dfa_rep
    let
      val al = ArrayHashSet.ahs_to_list B2_ a2;
      val rv_D = AHS_LTSImpl.ahs_lts_dlts_reverse (A1_, A2_) (B1_, B2_) d2;
      val pre_fun =
        (fn a => fn pim => fn (l, u) =>
          NFAByLTS.hopcroft_pre_fun_aux
            (AHS_LTSImpl.ahs_lts_succ_it (A1_, A2_) (B1_, B2_))
            (RecordSetImpl.ahs_ops (A1_, A2_))
            (fn i =>
              Option.the
                (ArrayHashMap.ahm_lookup
                  (Arith.equal_nat, HashCode.hashable_nat) (IntInf.+ (i, l))
                  pim))
            rv_D a (ArrayHashSet.ahs_empty A2_ ())
            (Arith.minus_nat (Arith.suc u) l));
      val (a, b) =
        Hopcroft_Minimisation.hopcroft_code
          (RecordMapImpl.ahm_ops (Arith.equal_nat, HashCode.hashable_nat))
          (ArrayHashSet.ahs_iteratei A2_)
          (ArrayHashMap.ahm_iteratei HashCode.hashable_nat)
          (ArrayHashSet.ahs_iteratei A2_) (RecordMapImpl.ahm_ops (A1_, A2_))
          (RecordMapImpl.ahm_ops (Arith.equal_nat, HashCode.hashable_nat))
          (RecordMapImpl.ahm_ops (Arith.equal_nat, HashCode.hashable_nat))
          (RecordMapImpl.ahm_ops (A1_, A2_)) (ArrayHashSet.ahs_iteratei A2_)
          (RecordSetImpl.ahs_ops (A1_, A2_)) q2 f2 al pre_fun;
    in
      let
        val (_, (sm, _)) = a;
      in
        (fn _ =>
          (ArrayHashSet.ahs_image A2_ (A1_, A2_)
             (fn q =>
               NFA.states_enumerate A3_
                 (Option.the (ArrayHashMap.ahm_lookup (A1_, A2_) q sm)))
             q2,
            (a2, (AHS_LTSImpl.ahs_dlts_image A2_ B2_ (A1_, A2_) (B1_, B2_)
                    (fn qaq =>
                      (NFA.states_enumerate A3_
                         (Option.the
                           (ArrayHashMap.ahm_lookup (A1_, A2_)
                             (Product_Type.fst qaq) sm)),
                        (Product_Type.fst (Product_Type.snd qaq),
                          NFA.states_enumerate A3_
                            (Option.the
                              (ArrayHashMap.ahm_lookup (A1_, A2_)
                                (Product_Type.snd (Product_Type.snd qaq))
                                sm)))))
                    d2,
                   (ArrayHashSet.ahs_image A2_ (A1_, A2_)
                      (fn q =>
                        NFA.states_enumerate A3_
                          (Option.the
                            (ArrayHashMap.ahm_lookup (A1_, A2_) q sm)))
                      i2,
                     ArrayHashSet.ahs_image A2_ (A1_, A2_)
                       (fn q =>
                         NFA.states_enumerate A3_
                           (Option.the
                             (ArrayHashMap.ahm_lookup (A1_, A2_) q sm)))
                       f2)))))
      end
        b
    end
  | ahs_nfa_Hopcroft (A1_, A2_, A3_) (B1_, B2_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    NFAByLTS.Dfa_rep
      let
        val al = ArrayHashSet.ahs_to_list B2_ a1;
        val rv_D = AHS_LTSImpl.ahs_lts_reverse (A1_, A2_) (B1_, B2_) d1;
        val pre_fun =
          (fn a => fn pim => fn (l, u) =>
            NFAByLTS.hopcroft_pre_fun_aux
              (AHS_LTSImpl.ahs_lts_succ_it (A1_, A2_) (B1_, B2_))
              (RecordSetImpl.ahs_ops (A1_, A2_))
              (fn i =>
                Option.the
                  (ArrayHashMap.ahm_lookup
                    (Arith.equal_nat, HashCode.hashable_nat) (IntInf.+ (i, l))
                    pim))
              rv_D a (ArrayHashSet.ahs_empty A2_ ())
              (Arith.minus_nat (Arith.suc u) l));
        val (a, b) =
          Hopcroft_Minimisation.hopcroft_code
            (RecordMapImpl.ahm_ops (Arith.equal_nat, HashCode.hashable_nat))
            (ArrayHashSet.ahs_iteratei A2_)
            (ArrayHashMap.ahm_iteratei HashCode.hashable_nat)
            (ArrayHashSet.ahs_iteratei A2_) (RecordMapImpl.ahm_ops (A1_, A2_))
            (RecordMapImpl.ahm_ops (Arith.equal_nat, HashCode.hashable_nat))
            (RecordMapImpl.ahm_ops (Arith.equal_nat, HashCode.hashable_nat))
            (RecordMapImpl.ahm_ops (A1_, A2_)) (ArrayHashSet.ahs_iteratei A2_)
            (RecordSetImpl.ahs_ops (A1_, A2_)) q1 f1 al pre_fun;
      in
        let
          val (_, (sm, _)) = a;
        in
          (fn _ =>
            (ArrayHashSet.ahs_image A2_ (A1_, A2_)
               (fn q =>
                 NFA.states_enumerate A3_
                   (Option.the (ArrayHashMap.ahm_lookup (A1_, A2_) q sm)))
               q1,
              (a1, (AHS_LTSImpl.ahs_dlts_lts_image A2_ B2_ (A1_, A2_) (B1_, B2_)
                      (fn qaq =>
                        (NFA.states_enumerate A3_
                           (Option.the
                             (ArrayHashMap.ahm_lookup (A1_, A2_)
                               (Product_Type.fst qaq) sm)),
                          (Product_Type.fst (Product_Type.snd qaq),
                            NFA.states_enumerate A3_
                              (Option.the
                                (ArrayHashMap.ahm_lookup (A1_, A2_)
                                  (Product_Type.snd (Product_Type.snd qaq))
                                  sm)))))
                      d1,
                     (ArrayHashSet.ahs_image A2_ (A1_, A2_)
                        (fn q =>
                          NFA.states_enumerate A3_
                            (Option.the
                              (ArrayHashMap.ahm_lookup (A1_, A2_) q sm)))
                        i1,
                       ArrayHashSet.ahs_image A2_ (A1_, A2_)
                         (fn q =>
                           NFA.states_enumerate A3_
                             (Option.the
                               (ArrayHashMap.ahm_lookup (A1_, A2_) q sm)))
                         f1)))))
        end
          b
      end;

fun ahs_nfa_destruct (A1_, A2_, A3_) B_
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  (ArrayHashSet.ahs_to_list A2_ q2,
    (ArrayHashSet.ahs_to_list B_ a2,
      (AHS_LTSImpl.ahs_dlts_to_collect_list (A1_, A2_) B_ d2,
        (ArrayHashSet.ahs_to_list A2_ i2, ArrayHashSet.ahs_to_list A2_ f2))))
  | ahs_nfa_destruct (A1_, A2_, A3_) B_
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    (ArrayHashSet.ahs_to_list A2_ q1,
      (ArrayHashSet.ahs_to_list B_ a1,
        (AHS_LTSImpl.ahs_lts_to_collect_list (A1_, A2_) B_ d1,
          (ArrayHashSet.ahs_to_list A2_ i1, ArrayHashSet.ahs_to_list A2_ f1))));

fun ahs_nfa_final_no (E1_, E2_) (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  StdInst.ahs_size E1_ f2
  | ahs_nfa_final_no (E1_, E2_) (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    StdInst.ahs_size E1_ f1;

fun ahs_nfa_trans_no C_ D_ E_ J_ K_ =
  NFAByLTS.nfa_trans_no (AHS_LTSImpl.ahs_lts_it C_ D_ E_)
    (AHS_LTSImpl.ahs_dlts_it J_ K_);

fun ahs_dfa_construct (A1_, A2_, A3_) (B1_, B2_) (ql, (al, (dl, (il, fl)))) =
  NFAByLTS.Dfa_rep
    (List.foldl
      (fn (q, (a, (d, (i, f)))) => fn (q1, (l, q2)) =>
        (ArrayHashSet.ahs_ins (A1_, A2_) q1
           (ArrayHashSet.ahs_ins (A1_, A2_) q2 q),
          (List.foldl (fn s => fn x => ArrayHashSet.ahs_ins (B1_, B2_) x s) a l,
            (List.foldl
               (fn da => fn aa =>
                 AHS_LTSImpl.ahs_dlts_add (A1_, A2_) (B1_, B2_) q1 aa q2 da)
               d l,
              (i, f)))))
      (ArrayHashSet.list_to_ahs (A1_, A2_) (ql @ il @ fl),
        (ArrayHashSet.list_to_ahs (B1_, B2_) al,
          (AHS_LTSImpl.ahs_dlts_empty A2_ B2_ (),
            (ArrayHashSet.list_to_ahs (A1_, A2_) il,
              ArrayHashSet.list_to_ahs (A1_, A2_) fl))))
      dl);

fun ahs_nfa_bool_comb (A1_, A2_, A3_) (B1_, B2_) bc
  (NFAByLTS.Dfa_rep (q3, (a3, (d3, (i3, f3)))))
  (NFAByLTS.Dfa_rep (q4, (a4, (d4, (i4, f4))))) =
  NFAByLTS.Dfa_rep
    let
      val (a, b) =
        List.foldl
          (fn (a, b) =>
            let
              val (qm, n) = a;
            in
              (fn is => fn q =>
                ((ArrayHashMap.ahm_update_dj
                    (Product_Type.equal_prod A1_ A1_,
                      HashCode.hashable_prod A2_ A2_)
                    (Fun.id q) (NFA.states_enumerate A3_ n) qm,
                   Arith.suc n),
                  ArrayHashSet.ahs_ins_dj (A1_, A2_)
                    (NFA.states_enumerate A3_ n) is))
            end
              b)
          ((ArrayHashMap.ahm_empty (HashCode.hashable_prod A2_ A2_) (),
             (0 : IntInf.int)),
            ArrayHashSet.ahs_empty A2_ ())
          (Enum.product (ArrayHashSet.ahs_to_list A2_ i3)
            (ArrayHashSet.ahs_to_list A2_ i4));
    in
      let
        val (qm, n) = a;
      in
        (fn is =>
          let
            val (aa, ba) =
              Workset.worklist (fn _ => true)
                (fn (aa, ba) =>
                  let
                    val (qma, na) = aa;
                  in
                    (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                      let
                        val r =
                          Option.the
                            (ArrayHashMap.ahm_lookup
                              (Product_Type.equal_prod A1_ A1_,
                                HashCode.hashable_prod A2_ A2_)
                              (Fun.id q) qma);
                      in
                        (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                          then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                          else let
                                 val (ab, bb) =
                                   let
                                     val (q1, q2) = q;
                                   in
                                     (fn c => fn f =>
                                       AHS_LTSImpl.ahs_dlts_succ_label_it
 (A1_, A2_) B2_ d3 q1 c
 (fn (ab, q1a) =>
   AHS_LTSImpl.ahs_dlts_succ_it (A1_, A2_) (B1_, B2_) d4 q2 ab c
     (fn q2a => f (ab, (q1a, q2a)))))
                                   end
                                     (fn _ => true)
                                     (fn (ab, qa) => fn (bb, c) =>
                                       let
 val (qmb, nb) = bb;
                                       in
 (fn (dda, naa) =>
   let
     val r_opt =
       ArrayHashMap.ahm_lookup
         (Product_Type.equal_prod A1_ A1_, HashCode.hashable_prod A2_ A2_)
         (Fun.id qa) qmb;
     val (bd, ca) =
       (if Option.is_none r_opt
         then let
                val ra = NFA.states_enumerate A3_ nb;
              in
                ((ArrayHashMap.ahm_update_dj
                    (Product_Type.equal_prod A1_ A1_,
                      HashCode.hashable_prod A2_ A2_)
                    (Fun.id qa) ra qmb,
                   Arith.suc nb),
                  ra)
              end
         else ((qmb, nb), Option.the r_opt));
   in
     let
       val (qmc, nc) = bd;
     in
       (fn ra =>
         ((qmc, nc),
           (AHS_LTSImpl.ahs_dlts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
             qa :: naa)))
     end
       ca
   end)
                                       end
 c)
                                     ((qma, na), (dd, []));
                               in
                                 let
                                   val (qmb, nb) = ab;
                                 in
                                   (fn (dda, ac) =>
                                     (((qmb, nb),
(ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
  (asa, (dda, (isa, (if let
                          val (q1, q2) = q;
                        in
                          bc (ArrayHashSet.ahs_memb (A1_, A2_) q1 f3)
                            (ArrayHashSet.ahs_memb (A1_, A2_) q2 f4)
                        end
                      then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                      else fs)))))),
                                       ac))
                                 end
                                   bb
                               end)
                      end)
                  end
                    ba)
                (((qm, n),
                   (ArrayHashSet.ahs_empty A2_ (),
                     (a3, (AHS_LTSImpl.ahs_dlts_empty A2_ B2_ (),
                            (is, ArrayHashSet.ahs_empty A2_ ()))))),
                  Enum.product (ArrayHashSet.ahs_to_list A2_ i3)
                    (ArrayHashSet.ahs_to_list A2_ i4));
          in
            let
              val (_, aaa) = aa;
            in
              (fn _ => aaa)
            end
              ba
          end)
      end
        b
    end
  | ahs_nfa_bool_comb (A1_, A2_, A3_) (B1_, B2_) bc
    (NFAByLTS.Dfa_rep (q3, (a3, (d3, (i3, f3)))))
    (NFAByLTS.Nfa_rep (q2, (a2, (d2, (i2, f2))))) =
    NFAByLTS.Nfa_rep
      let
        val (a, b) =
          List.foldl
            (fn (a, b) =>
              let
                val (qm, n) = a;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod A1_ A1_,
                        HashCode.hashable_prod A2_ A2_)
                      (Fun.id q) (NFA.states_enumerate A3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (A1_, A2_)
                      (NFA.states_enumerate A3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty (HashCode.hashable_prod A2_ A2_) (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty A2_ ())
            (Enum.product (ArrayHashSet.ahs_to_list A2_ i3)
              (ArrayHashSet.ahs_to_list A2_ i2));
      in
        let
          val (qm, n) = a;
        in
          (fn is =>
            let
              val (aa, ba) =
                Workset.worklist (fn _ => true)
                  (fn (aa, ba) =>
                    let
                      val (qma, na) = aa;
                    in
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Product_Type.equal_prod A1_ A1_,
                                  HashCode.hashable_prod A2_ A2_)
                                (Fun.id q) qma);
                        in
                          (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     let
                                       val (q1, q2a) = q;
                                     in
                                       (fn c => fn f =>
 AHS_LTSImpl.ahs_dlts_succ_label_it (A1_, A2_) B2_ d3 q1 c
   (fn (ab, q1a) =>
     AHS_LTSImpl.ahs_lts_succ_it (A1_, A2_) (B1_, B2_) d2 q2a ab c
       (fn q2b => f (ab, (q1a, q2b)))))
                                     end
                                       (fn _ => true)
                                       (fn (ab, qa) => fn (bb, c) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt =
         ArrayHashMap.ahm_lookup
           (Product_Type.equal_prod A1_ A1_, HashCode.hashable_prod A2_ A2_)
           (Fun.id qa) qmb;
       val (bd, ca) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate A3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod A1_ A1_,
                        HashCode.hashable_prod A2_ A2_)
                      (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bd;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
               qa :: naa)))
       end
         ca
     end)
 end
   c)
                                       ((qma, na), (dd, []));
                                 in
                                   let
                                     val (qmb, nb) = ab;
                                   in
                                     (fn (dda, ac) =>
                                       (((qmb, nb),
  (ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
    (asa, (dda, (isa, (if let
                            val (q1, q2a) = q;
                          in
                            bc (ArrayHashSet.ahs_memb (A1_, A2_) q1 f3)
                              (ArrayHashSet.ahs_memb (A1_, A2_) q2a f2)
                          end
                        then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty A2_ (),
                       (a3, (AHS_LTSImpl.ahs_lts_empty A2_ B2_ (),
                              (is, ArrayHashSet.ahs_empty A2_ ()))))),
                    Enum.product (ArrayHashSet.ahs_to_list A2_ i3)
                      (ArrayHashSet.ahs_to_list A2_ i2));
            in
              let
                val (_, aaa) = aa;
              in
                (fn _ => aaa)
              end
                ba
            end)
        end
          b
      end
  | ahs_nfa_bool_comb (A1_, A2_, A3_) (B1_, B2_) bc
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1)))))
    (NFAByLTS.Dfa_rep (q4, (a4, (d4, (i4, f4))))) =
    NFAByLTS.Nfa_rep
      let
        val (a, b) =
          List.foldl
            (fn (a, b) =>
              let
                val (qm, n) = a;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod A1_ A1_,
                        HashCode.hashable_prod A2_ A2_)
                      (Fun.id q) (NFA.states_enumerate A3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (A1_, A2_)
                      (NFA.states_enumerate A3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty (HashCode.hashable_prod A2_ A2_) (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty A2_ ())
            (Enum.product (ArrayHashSet.ahs_to_list A2_ i1)
              (ArrayHashSet.ahs_to_list A2_ i4));
      in
        let
          val (qm, n) = a;
        in
          (fn is =>
            let
              val (aa, ba) =
                Workset.worklist (fn _ => true)
                  (fn (aa, ba) =>
                    let
                      val (qma, na) = aa;
                    in
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Product_Type.equal_prod A1_ A1_,
                                  HashCode.hashable_prod A2_ A2_)
                                (Fun.id q) qma);
                        in
                          (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     let
                                       val (q1a, q2) = q;
                                     in
                                       (fn c => fn f =>
 AHS_LTSImpl.ahs_lts_succ_label_it (A1_, A2_) B2_ d1 q1a c
   (fn (ab, q1b) =>
     AHS_LTSImpl.ahs_dlts_succ_it (A1_, A2_) (B1_, B2_) d4 q2 ab c
       (fn q2a => f (ab, (q1b, q2a)))))
                                     end
                                       (fn _ => true)
                                       (fn (ab, qa) => fn (bb, c) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt =
         ArrayHashMap.ahm_lookup
           (Product_Type.equal_prod A1_ A1_, HashCode.hashable_prod A2_ A2_)
           (Fun.id qa) qmb;
       val (bd, ca) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate A3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod A1_ A1_,
                        HashCode.hashable_prod A2_ A2_)
                      (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bd;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
               qa :: naa)))
       end
         ca
     end)
 end
   c)
                                       ((qma, na), (dd, []));
                                 in
                                   let
                                     val (qmb, nb) = ab;
                                   in
                                     (fn (dda, ac) =>
                                       (((qmb, nb),
  (ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
    (asa, (dda, (isa, (if let
                            val (q1a, q2) = q;
                          in
                            bc (ArrayHashSet.ahs_memb (A1_, A2_) q1a f1)
                              (ArrayHashSet.ahs_memb (A1_, A2_) q2 f4)
                          end
                        then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty A2_ (),
                       (a1, (AHS_LTSImpl.ahs_lts_empty A2_ B2_ (),
                              (is, ArrayHashSet.ahs_empty A2_ ()))))),
                    Enum.product (ArrayHashSet.ahs_to_list A2_ i1)
                      (ArrayHashSet.ahs_to_list A2_ i4));
            in
              let
                val (_, aaa) = aa;
              in
                (fn _ => aaa)
              end
                ba
            end)
        end
          b
      end
  | ahs_nfa_bool_comb (A1_, A2_, A3_) (B1_, B2_) bc
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1)))))
    (NFAByLTS.Nfa_rep (q2, (a2, (d2, (i2, f2))))) =
    NFAByLTS.Nfa_rep
      let
        val (a, b) =
          List.foldl
            (fn (a, b) =>
              let
                val (qm, n) = a;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod A1_ A1_,
                        HashCode.hashable_prod A2_ A2_)
                      (Fun.id q) (NFA.states_enumerate A3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (A1_, A2_)
                      (NFA.states_enumerate A3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty (HashCode.hashable_prod A2_ A2_) (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty A2_ ())
            (Enum.product (ArrayHashSet.ahs_to_list A2_ i1)
              (ArrayHashSet.ahs_to_list A2_ i2));
      in
        let
          val (qm, n) = a;
        in
          (fn is =>
            let
              val (aa, ba) =
                Workset.worklist (fn _ => true)
                  (fn (aa, ba) =>
                    let
                      val (qma, na) = aa;
                    in
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Product_Type.equal_prod A1_ A1_,
                                  HashCode.hashable_prod A2_ A2_)
                                (Fun.id q) qma);
                        in
                          (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     let
                                       val (q1a, q2a) = q;
                                     in
                                       (fn c => fn f =>
 AHS_LTSImpl.ahs_lts_succ_label_it (A1_, A2_) B2_ d1 q1a c
   (fn (ab, q1b) =>
     AHS_LTSImpl.ahs_lts_succ_it (A1_, A2_) (B1_, B2_) d2 q2a ab c
       (fn q2b => f (ab, (q1b, q2b)))))
                                     end
                                       (fn _ => true)
                                       (fn (ab, qa) => fn (bb, c) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt =
         ArrayHashMap.ahm_lookup
           (Product_Type.equal_prod A1_ A1_, HashCode.hashable_prod A2_ A2_)
           (Fun.id qa) qmb;
       val (bd, ca) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate A3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod A1_ A1_,
                        HashCode.hashable_prod A2_ A2_)
                      (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bd;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
               qa :: naa)))
       end
         ca
     end)
 end
   c)
                                       ((qma, na), (dd, []));
                                 in
                                   let
                                     val (qmb, nb) = ab;
                                   in
                                     (fn (dda, ac) =>
                                       (((qmb, nb),
  (ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
    (asa, (dda, (isa, (if let
                            val (q1a, q2a) = q;
                          in
                            bc (ArrayHashSet.ahs_memb (A1_, A2_) q1a f1)
                              (ArrayHashSet.ahs_memb (A1_, A2_) q2a f2)
                          end
                        then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty A2_ (),
                       (a1, (AHS_LTSImpl.ahs_lts_empty A2_ B2_ (),
                              (is, ArrayHashSet.ahs_empty A2_ ()))))),
                    Enum.product (ArrayHashSet.ahs_to_list A2_ i1)
                      (ArrayHashSet.ahs_to_list A2_ i2));
            in
              let
                val (_, aaa) = aa;
              in
                (fn _ => aaa)
              end
                ba
            end)
        end
          b
      end;

fun ahs_nfa_construct (A1_, A2_, A3_) (B1_, B2_) (ql, (al, (dl, (il, fl)))) =
  NFAByLTS.Nfa_rep
    (List.foldl
      (fn (q, (a, (d, (i, f)))) => fn (q1, (l, q2)) =>
        (ArrayHashSet.ahs_ins (A1_, A2_) q1
           (ArrayHashSet.ahs_ins (A1_, A2_) q2 q),
          (List.foldl (fn s => fn x => ArrayHashSet.ahs_ins (B1_, B2_) x s) a l,
            (List.foldl
               (fn da => fn aa =>
                 AHS_LTSImpl.ahs_lts_add (A1_, A2_) (B1_, B2_) q1 aa q2 da)
               d l,
              (i, f)))))
      (ArrayHashSet.list_to_ahs (A1_, A2_) (ql @ il @ fl),
        (ArrayHashSet.list_to_ahs (B1_, B2_) al,
          (AHS_LTSImpl.ahs_lts_empty A2_ B2_ (),
            (ArrayHashSet.list_to_ahs (A1_, A2_) il,
              ArrayHashSet.list_to_ahs (A1_, A2_) fl))))
      dl);

fun ahs_nfa_labels_no B_ (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  StdInst.ahs_size B_ a2
  | ahs_nfa_labels_no B_ (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    StdInst.ahs_size B_ a1;

fun ahs_nfa_normalise (A1_, A2_, A3_) (B1_, B2_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  NFAByLTS.Dfa_rep
    let
      val (a, b) =
        List.foldl
          (fn (a, b) =>
            let
              val (qm, n) = a;
            in
              (fn is => fn q =>
                ((ArrayHashMap.ahm_update_dj (A1_, A2_) (Fun.id q)
                    (NFA.states_enumerate A3_ n) qm,
                   Arith.suc n),
                  ArrayHashSet.ahs_ins_dj (A1_, A2_)
                    (NFA.states_enumerate A3_ n) is))
            end
              b)
          ((ArrayHashMap.ahm_empty A2_ (), (0 : IntInf.int)),
            ArrayHashSet.ahs_empty A2_ ())
          (ArrayHashSet.ahs_to_list A2_ i2);
    in
      let
        val (qm, n) = a;
      in
        (fn is =>
          let
            val (aa, ba) =
              Workset.worklist (fn _ => true)
                (fn (aa, ba) =>
                  let
                    val (qma, na) = aa;
                  in
                    (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                      let
                        val r =
                          Option.the
                            (ArrayHashMap.ahm_lookup (A1_, A2_) (Fun.id q) qma);
                      in
                        (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                          then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                          else let
                                 val (ab, bb) =
                                   AHS_LTSImpl.ahs_dlts_succ_label_it (A1_, A2_)
                                     B2_ d2 q (fn _ => true)
                                     (fn (ab, qa) => fn (bb, c) =>
                                       let
 val (qmb, nb) = bb;
                                       in
 (fn (dda, naa) =>
   let
     val r_opt = ArrayHashMap.ahm_lookup (A1_, A2_) (Fun.id qa) qmb;
     val (bc, ca) =
       (if Option.is_none r_opt
         then let
                val ra = NFA.states_enumerate A3_ nb;
              in
                ((ArrayHashMap.ahm_update_dj (A1_, A2_) (Fun.id qa) ra qmb,
                   Arith.suc nb),
                  ra)
              end
         else ((qmb, nb), Option.the r_opt));
   in
     let
       val (qmc, nc) = bc;
     in
       (fn ra =>
         ((qmc, nc),
           (AHS_LTSImpl.ahs_dlts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
             qa :: naa)))
     end
       ca
   end)
                                       end
 c)
                                     ((qma, na), (dd, []));
                               in
                                 let
                                   val (qmb, nb) = ab;
                                 in
                                   (fn (dda, ac) =>
                                     (((qmb, nb),
(ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
  (asa, (dda, (isa, (if ArrayHashSet.ahs_memb (A1_, A2_) q f2
                      then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                      else fs)))))),
                                       ac))
                                 end
                                   bb
                               end)
                      end)
                  end
                    ba)
                (((qm, n),
                   (ArrayHashSet.ahs_empty A2_ (),
                     (a2, (AHS_LTSImpl.ahs_dlts_empty A2_ B2_ (),
                            (is, ArrayHashSet.ahs_empty A2_ ()))))),
                  ArrayHashSet.ahs_to_list A2_ i2);
          in
            let
              val (_, aaa) = aa;
            in
              (fn _ => aaa)
            end
              ba
          end)
      end
        b
    end
  | ahs_nfa_normalise (A1_, A2_, A3_) (B1_, B2_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    NFAByLTS.Nfa_rep
      let
        val (a, b) =
          List.foldl
            (fn (a, b) =>
              let
                val (qm, n) = a;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj (A1_, A2_) (Fun.id q)
                      (NFA.states_enumerate A3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (A1_, A2_)
                      (NFA.states_enumerate A3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty A2_ (), (0 : IntInf.int)),
              ArrayHashSet.ahs_empty A2_ ())
            (ArrayHashSet.ahs_to_list A2_ i1);
      in
        let
          val (qm, n) = a;
        in
          (fn is =>
            let
              val (aa, ba) =
                Workset.worklist (fn _ => true)
                  (fn (aa, ba) =>
                    let
                      val (qma, na) = aa;
                    in
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup (A1_, A2_) (Fun.id q)
                                qma);
                        in
                          (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     AHS_LTSImpl.ahs_lts_succ_label_it
                                       (A1_, A2_) B2_ d1 q (fn _ => true)
                                       (fn (ab, qa) => fn (bb, c) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt = ArrayHashMap.ahm_lookup (A1_, A2_) (Fun.id qa) qmb;
       val (bc, ca) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate A3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj (A1_, A2_) (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bc;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
               qa :: naa)))
       end
         ca
     end)
 end
   c)
                                       ((qma, na), (dd, []));
                                 in
                                   let
                                     val (qmb, nb) = ab;
                                   in
                                     (fn (dda, ac) =>
                                       (((qmb, nb),
  (ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
    (asa, (dda, (isa, (if ArrayHashSet.ahs_memb (A1_, A2_) q f1
                        then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty A2_ (),
                       (a1, (AHS_LTSImpl.ahs_lts_empty A2_ B2_ (),
                              (is, ArrayHashSet.ahs_empty A2_ ()))))),
                    ArrayHashSet.ahs_to_list A2_ i1);
            in
              let
                val (_, aaa) = aa;
              in
                (fn _ => aaa)
              end
                ba
            end)
        end
          b
      end;

fun ahs_nfa_states_no (A1_, A2_) (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  StdInst.ahs_size A1_ q2
  | ahs_nfa_states_no (A1_, A2_) (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    StdInst.ahs_size A1_ q1;

fun ahs_nfa_determinise (A1_, A2_, A3_) (B1_, B2_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  let
    val m =
      Product_Type.fst
        (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
          (fn q => fn (m, n) =>
            (ArrayHashMap.ahm_update_dj (A1_, A2_) q n m,
              IntInf.* ((2 : IntInf.int), n)))
          q2 (ArrayHashMap.ahm_empty A2_ (), (1 : IntInf.int)));
  in
    NFAByLTS.Dfa_rep
      let
        val (a, b) =
          List.foldl
            (fn (a, b) =>
              let
                val (qm, n) = a;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Arith.equal_nat, HashCode.hashable_nat)
                      (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                        (fn qa => fn na =>
                          IntInf.+ (na, Option.the
  (ArrayHashMap.ahm_lookup (A1_, A2_) qa m)))
                        q (0 : IntInf.int))
                      (NFA.states_enumerate A3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (A1_, A2_)
                      (NFA.states_enumerate A3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty HashCode.hashable_nat (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty A2_ ())
            [i2];
      in
        let
          val (qm, n) = a;
        in
          (fn is =>
            let
              val (aa, ba) =
                Workset.worklist (fn _ => true)
                  (fn (aa, ba) =>
                    let
                      val (qma, na) = aa;
                    in
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Arith.equal_nat, HashCode.hashable_nat)
                                (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                                  (fn qa => fn nb =>
                                    IntInf.+ (nb, Option.the
            (ArrayHashMap.ahm_lookup (A1_, A2_) qa m)))
                                  q (0 : IntInf.int))
                                qma);
                        in
                          (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     ArrayHashSet.ahs_iteratei B2_
                                       (fn _ => true)
                                       (fn x =>
 let
   val (ab, qa) =
     (x, ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
           (fn ab =>
             AHS_LTSImpl.ahs_dlts_succ_it (A1_, A2_) (B1_, B2_) d2 ab x
               (fn _ => true) (ArrayHashSet.ahs_ins (A1_, A2_)))
           q (ArrayHashSet.ahs_empty A2_ ()));
 in
   (fn (bb, c) =>
     let
       val (qmb, nb) = bb;
     in
       (fn (dda, naa) =>
         let
           val r_opt =
             ArrayHashMap.ahm_lookup (Arith.equal_nat, HashCode.hashable_nat)
               (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                 (fn qb => fn nc =>
                   IntInf.+ (nc, Option.the
                                   (ArrayHashMap.ahm_lookup (A1_, A2_) qb m)))
                 qa (0 : IntInf.int))
               qmb;
           val (bc, ca) =
             (if Option.is_none r_opt
               then let
                      val ra = NFA.states_enumerate A3_ nb;
                    in
                      ((ArrayHashMap.ahm_update_dj
                          (Arith.equal_nat, HashCode.hashable_nat)
                          (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                            (fn qb => fn nc =>
                              IntInf.+ (nc, Option.the
      (ArrayHashMap.ahm_lookup (A1_, A2_) qb m)))
                            qa (0 : IntInf.int))
                          ra qmb,
                         Arith.suc nb),
                        ra)
                    end
               else ((qmb, nb), Option.the r_opt));
         in
           let
             val (qmc, nc) = bc;
           in
             (fn ra =>
               ((qmc, nc),
                 (AHS_LTSImpl.ahs_dlts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
                   qa :: naa)))
           end
             ca
         end)
     end
       c)
 end)
                                       a2 ((qma, na), (dd, []));
                                 in
                                   let
                                     val (qmb, nb) = ab;
                                   in
                                     (fn (dda, ac) =>
                                       (((qmb, nb),
  (ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
    (asa, (dda, (isa, (if not (StdInst.aa_disjoint (A1_, A2_) q f2)
                        then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty A2_ (),
                       (a2, (AHS_LTSImpl.ahs_dlts_empty A2_ B2_ (),
                              (is, ArrayHashSet.ahs_empty A2_ ()))))),
                    [i2]);
            in
              let
                val (_, aaa) = aa;
              in
                (fn _ => aaa)
              end
                ba
            end)
        end
          b
      end
  end
  | ahs_nfa_determinise (A1_, A2_, A3_) (B1_, B2_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    let
      val m =
        Product_Type.fst
          (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
            (fn q => fn (m, n) =>
              (ArrayHashMap.ahm_update_dj (A1_, A2_) q n m,
                IntInf.* ((2 : IntInf.int), n)))
            q1 (ArrayHashMap.ahm_empty A2_ (), (1 : IntInf.int)));
    in
      NFAByLTS.Dfa_rep
        let
          val (a, b) =
            List.foldl
              (fn (a, b) =>
                let
                  val (qm, n) = a;
                in
                  (fn is => fn q =>
                    ((ArrayHashMap.ahm_update_dj
                        (Arith.equal_nat, HashCode.hashable_nat)
                        (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                          (fn qa => fn na =>
                            IntInf.+ (na, Option.the
    (ArrayHashMap.ahm_lookup (A1_, A2_) qa m)))
                          q (0 : IntInf.int))
                        (NFA.states_enumerate A3_ n) qm,
                       Arith.suc n),
                      ArrayHashSet.ahs_ins_dj (A1_, A2_)
                        (NFA.states_enumerate A3_ n) is))
                end
                  b)
              ((ArrayHashMap.ahm_empty HashCode.hashable_nat (),
                 (0 : IntInf.int)),
                ArrayHashSet.ahs_empty A2_ ())
              [i1];
        in
          let
            val (qm, n) = a;
          in
            (fn is =>
              let
                val (aa, ba) =
                  Workset.worklist (fn _ => true)
                    (fn (aa, ba) =>
                      let
                        val (qma, na) = aa;
                      in
                        (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                          let
                            val r =
                              Option.the
                                (ArrayHashMap.ahm_lookup
                                  (Arith.equal_nat, HashCode.hashable_nat)
                                  (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                                    (fn qa => fn nb =>
                                      IntInf.+ (nb, Option.the
              (ArrayHashMap.ahm_lookup (A1_, A2_) qa m)))
                                    q (0 : IntInf.int))
                                  qma);
                          in
                            (if ArrayHashSet.ahs_memb (A1_, A2_) r qs
                              then (((qma, na), (qs, (asa, (dd, (isa, fs))))),
                                     [])
                              else let
                                     val (ab, bb) =
                                       ArrayHashSet.ahs_iteratei B2_
 (fn _ => true)
 (fn x =>
   let
     val (ab, qa) =
       (x, ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
             (fn ab =>
               AHS_LTSImpl.ahs_lts_succ_it (A1_, A2_) (B1_, B2_) d1 ab x
                 (fn _ => true) (ArrayHashSet.ahs_ins (A1_, A2_)))
             q (ArrayHashSet.ahs_empty A2_ ()));
   in
     (fn (bb, c) =>
       let
         val (qmb, nb) = bb;
       in
         (fn (dda, naa) =>
           let
             val r_opt =
               ArrayHashMap.ahm_lookup (Arith.equal_nat, HashCode.hashable_nat)
                 (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                   (fn qb => fn nc =>
                     IntInf.+ (nc, Option.the
                                     (ArrayHashMap.ahm_lookup (A1_, A2_) qb m)))
                   qa (0 : IntInf.int))
                 qmb;
             val (bc, ca) =
               (if Option.is_none r_opt
                 then let
                        val ra = NFA.states_enumerate A3_ nb;
                      in
                        ((ArrayHashMap.ahm_update_dj
                            (Arith.equal_nat, HashCode.hashable_nat)
                            (ArrayHashSet.ahs_iteratei A2_ (fn _ => true)
                              (fn qb => fn nc =>
                                IntInf.+ (nc, Option.the
        (ArrayHashMap.ahm_lookup (A1_, A2_) qb m)))
                              qa (0 : IntInf.int))
                            ra qmb,
                           Arith.suc nb),
                          ra)
                      end
                 else ((qmb, nb), Option.the r_opt));
           in
             let
               val (qmc, nc) = bc;
             in
               (fn ra =>
                 ((qmc, nc),
                   (AHS_LTSImpl.ahs_dlts_add (A1_, A2_) (B1_, B2_) r ab ra dda,
                     qa :: naa)))
             end
               ca
           end)
       end
         c)
   end)
 a1 ((qma, na), (dd, []));
                                   in
                                     let
                                       val (qmb, nb) = ab;
                                     in
                                       (fn (dda, ac) =>
 (((qmb, nb),
    (ArrayHashSet.ahs_ins_dj (A1_, A2_) r qs,
      (asa, (dda, (isa, (if not (StdInst.aa_disjoint (A1_, A2_) q f1)
                          then ArrayHashSet.ahs_ins_dj (A1_, A2_) r fs
                          else fs)))))),
   ac))
                                     end
                                       bb
                                   end)
                          end)
                      end
                        ba)
                    (((qm, n),
                       (ArrayHashSet.ahs_empty A2_ (),
                         (a1, (AHS_LTSImpl.ahs_dlts_empty A2_ B2_ (),
                                (is, ArrayHashSet.ahs_empty A2_ ()))))),
                      [i1]);
              in
                let
                  val (_, aaa) = aa;
                in
                  (fn _ => aaa)
                end
                  ba
              end)
          end
            b
        end
    end;

fun ahs_nfa_Brzozowski (A1_, A2_, A3_) (B1_, B2_) a =
  ahs_nfa_determinise (A1_, A2_, A3_) (B1_, B2_)
    (ahs_nfa_reverse (A1_, A2_, A3_) (B1_, B2_)
      (ahs_nfa_determinise (A1_, A2_, A3_) (B1_, B2_)
        (ahs_nfa_reverse (A1_, A2_, A3_) (B1_, B2_) a)));

fun ahs_nfa_complement (A1_, A2_, A3_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, StdInst.aa_diff (A1_, A2_) q2 f2))))
  | ahs_nfa_complement (A1_, A2_, A3_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, StdInst.aa_diff (A1_, A2_) q1 f1))));

fun ahs_nfa_initial_no (D1_, D2_) (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2)))))
  = StdInst.ahs_size D1_ i2
  | ahs_nfa_initial_no (D1_, D2_) (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1)))))
    = StdInst.ahs_size D1_ i1;

fun ahs_nfa_Hopcroft_NFA (A1_, A2_, A3_) (B1_, B2_) =
  (fn a =>
    ahs_nfa_Hopcroft (A1_, A2_, A3_) (B1_, B2_)
      (ahs_nfa_determinise (A1_, A2_, A3_) (B1_, B2_) a));

fun ahs_nfa_bool_comb_gen (B1_, B2_, B3_) (C1_, C2_) a bc
  (NFAByLTS.Dfa_rep (q3, (a3, (d3, (i3, f3)))))
  (NFAByLTS.Dfa_rep (q4, (a4, (d4, (i4, f4))))) =
  NFAByLTS.Dfa_rep
    let
      val (b, c) =
        List.foldl
          (fn (aa, b) =>
            let
              val (qm, n) = aa;
            in
              (fn is => fn q =>
                ((ArrayHashMap.ahm_update_dj
                    (Product_Type.equal_prod B1_ B1_,
                      HashCode.hashable_prod B2_ B2_)
                    (Fun.id q) (NFA.states_enumerate B3_ n) qm,
                   Arith.suc n),
                  ArrayHashSet.ahs_ins_dj (B1_, B2_)
                    (NFA.states_enumerate B3_ n) is))
            end
              b)
          ((ArrayHashMap.ahm_empty (HashCode.hashable_prod B2_ B2_) (),
             (0 : IntInf.int)),
            ArrayHashSet.ahs_empty B2_ ())
          (Enum.product (ArrayHashSet.ahs_to_list B2_ i3)
            (ArrayHashSet.ahs_to_list B2_ i4));
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
                    (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                      let
                        val r =
                          Option.the
                            (ArrayHashMap.ahm_lookup
                              (Product_Type.equal_prod B1_ B1_,
                                HashCode.hashable_prod B2_ B2_)
                              (Fun.id q) qma);
                      in
                        (if ArrayHashSet.ahs_memb (B1_, B2_) r qs
                          then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                          else let
                                 val (ab, bb) =
                                   let
                                     val (q1, q2) = q;
                                   in
                                     (fn ca => fn f =>
                                       AHS_LTSImpl.ahs_dlts_succ_label_it
 (B1_, B2_) C2_ d3 q1 ca
 (fn (ab, q1a) =>
   AHS_LTSImpl.ahs_dlts_succ_it (B1_, B2_) (C1_, C2_) d4 q2 ab ca
     (fn q2a => f (ab, (q1a, q2a)))))
                                   end
                                     (fn _ => true)
                                     (fn (ab, qa) => fn (bb, ca) =>
                                       let
 val (qmb, nb) = bb;
                                       in
 (fn (dda, naa) =>
   let
     val r_opt =
       ArrayHashMap.ahm_lookup
         (Product_Type.equal_prod B1_ B1_, HashCode.hashable_prod B2_ B2_)
         (Fun.id qa) qmb;
     val (bd, cb) =
       (if Option.is_none r_opt
         then let
                val ra = NFA.states_enumerate B3_ nb;
              in
                ((ArrayHashMap.ahm_update_dj
                    (Product_Type.equal_prod B1_ B1_,
                      HashCode.hashable_prod B2_ B2_)
                    (Fun.id qa) ra qmb,
                   Arith.suc nb),
                  ra)
              end
         else ((qmb, nb), Option.the r_opt));
   in
     let
       val (qmc, nc) = bd;
     in
       (fn ra =>
         ((qmc, nc),
           (AHS_LTSImpl.ahs_dlts_add (B1_, B2_) (C1_, C2_) r ab ra dda,
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
(ArrayHashSet.ahs_ins_dj (B1_, B2_) r qs,
  (asa, (dda, (isa, (if let
                          val (q1, q2) = q;
                        in
                          bc (ArrayHashSet.ahs_memb (B1_, B2_) q1 f3)
                            (ArrayHashSet.ahs_memb (B1_, B2_) q2 f4)
                        end
                      then ArrayHashSet.ahs_ins_dj (B1_, B2_) r fs
                      else fs)))))),
                                       ac))
                                 end
                                   bb
                               end)
                      end)
                  end
                    ba)
                (((qm, n),
                   (ArrayHashSet.ahs_empty B2_ (),
                     (a, (AHS_LTSImpl.ahs_dlts_empty B2_ C2_ (),
                           (is, ArrayHashSet.ahs_empty B2_ ()))))),
                  Enum.product (ArrayHashSet.ahs_to_list B2_ i3)
                    (ArrayHashSet.ahs_to_list B2_ i4));
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
    end
  | ahs_nfa_bool_comb_gen (B1_, B2_, B3_) (C1_, C2_) a bc
    (NFAByLTS.Dfa_rep (q3, (a3, (d3, (i3, f3)))))
    (NFAByLTS.Nfa_rep (q2, (a2, (d2, (i2, f2))))) =
    NFAByLTS.Nfa_rep
      let
        val (b, c) =
          List.foldl
            (fn (aa, b) =>
              let
                val (qm, n) = aa;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod B1_ B1_,
                        HashCode.hashable_prod B2_ B2_)
                      (Fun.id q) (NFA.states_enumerate B3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (B1_, B2_)
                      (NFA.states_enumerate B3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty (HashCode.hashable_prod B2_ B2_) (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty B2_ ())
            (Enum.product (ArrayHashSet.ahs_to_list B2_ i3)
              (ArrayHashSet.ahs_to_list B2_ i2));
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
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Product_Type.equal_prod B1_ B1_,
                                  HashCode.hashable_prod B2_ B2_)
                                (Fun.id q) qma);
                        in
                          (if ArrayHashSet.ahs_memb (B1_, B2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     let
                                       val (q1, q2a) = q;
                                     in
                                       (fn ca => fn f =>
 AHS_LTSImpl.ahs_dlts_succ_label_it (B1_, B2_) C2_ d3 q1 ca
   (fn (ab, q1a) =>
     AHS_LTSImpl.ahs_lts_succ_it (B1_, B2_) (C1_, C2_) d2 q2a ab ca
       (fn q2b => f (ab, (q1a, q2b)))))
                                     end
                                       (fn _ => true)
                                       (fn (ab, qa) => fn (bb, ca) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt =
         ArrayHashMap.ahm_lookup
           (Product_Type.equal_prod B1_ B1_, HashCode.hashable_prod B2_ B2_)
           (Fun.id qa) qmb;
       val (bd, cb) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate B3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod B1_ B1_,
                        HashCode.hashable_prod B2_ B2_)
                      (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bd;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (B1_, B2_) (C1_, C2_) r ab ra dda,
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
  (ArrayHashSet.ahs_ins_dj (B1_, B2_) r qs,
    (asa, (dda, (isa, (if let
                            val (q1, q2a) = q;
                          in
                            bc (ArrayHashSet.ahs_memb (B1_, B2_) q1 f3)
                              (ArrayHashSet.ahs_memb (B1_, B2_) q2a f2)
                          end
                        then ArrayHashSet.ahs_ins_dj (B1_, B2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty B2_ (),
                       (a, (AHS_LTSImpl.ahs_lts_empty B2_ C2_ (),
                             (is, ArrayHashSet.ahs_empty B2_ ()))))),
                    Enum.product (ArrayHashSet.ahs_to_list B2_ i3)
                      (ArrayHashSet.ahs_to_list B2_ i2));
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
      end
  | ahs_nfa_bool_comb_gen (B1_, B2_, B3_) (C1_, C2_) a bc
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1)))))
    (NFAByLTS.Dfa_rep (q4, (a4, (d4, (i4, f4))))) =
    NFAByLTS.Nfa_rep
      let
        val (b, c) =
          List.foldl
            (fn (aa, b) =>
              let
                val (qm, n) = aa;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod B1_ B1_,
                        HashCode.hashable_prod B2_ B2_)
                      (Fun.id q) (NFA.states_enumerate B3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (B1_, B2_)
                      (NFA.states_enumerate B3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty (HashCode.hashable_prod B2_ B2_) (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty B2_ ())
            (Enum.product (ArrayHashSet.ahs_to_list B2_ i1)
              (ArrayHashSet.ahs_to_list B2_ i4));
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
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Product_Type.equal_prod B1_ B1_,
                                  HashCode.hashable_prod B2_ B2_)
                                (Fun.id q) qma);
                        in
                          (if ArrayHashSet.ahs_memb (B1_, B2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     let
                                       val (q1a, q2) = q;
                                     in
                                       (fn ca => fn f =>
 AHS_LTSImpl.ahs_lts_succ_label_it (B1_, B2_) C2_ d1 q1a ca
   (fn (ab, q1b) =>
     AHS_LTSImpl.ahs_dlts_succ_it (B1_, B2_) (C1_, C2_) d4 q2 ab ca
       (fn q2a => f (ab, (q1b, q2a)))))
                                     end
                                       (fn _ => true)
                                       (fn (ab, qa) => fn (bb, ca) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt =
         ArrayHashMap.ahm_lookup
           (Product_Type.equal_prod B1_ B1_, HashCode.hashable_prod B2_ B2_)
           (Fun.id qa) qmb;
       val (bd, cb) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate B3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod B1_ B1_,
                        HashCode.hashable_prod B2_ B2_)
                      (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bd;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (B1_, B2_) (C1_, C2_) r ab ra dda,
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
  (ArrayHashSet.ahs_ins_dj (B1_, B2_) r qs,
    (asa, (dda, (isa, (if let
                            val (q1a, q2) = q;
                          in
                            bc (ArrayHashSet.ahs_memb (B1_, B2_) q1a f1)
                              (ArrayHashSet.ahs_memb (B1_, B2_) q2 f4)
                          end
                        then ArrayHashSet.ahs_ins_dj (B1_, B2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty B2_ (),
                       (a, (AHS_LTSImpl.ahs_lts_empty B2_ C2_ (),
                             (is, ArrayHashSet.ahs_empty B2_ ()))))),
                    Enum.product (ArrayHashSet.ahs_to_list B2_ i1)
                      (ArrayHashSet.ahs_to_list B2_ i4));
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
      end
  | ahs_nfa_bool_comb_gen (B1_, B2_, B3_) (C1_, C2_) a bc
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1)))))
    (NFAByLTS.Nfa_rep (q2, (a2, (d2, (i2, f2))))) =
    NFAByLTS.Nfa_rep
      let
        val (b, c) =
          List.foldl
            (fn (aa, b) =>
              let
                val (qm, n) = aa;
              in
                (fn is => fn q =>
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod B1_ B1_,
                        HashCode.hashable_prod B2_ B2_)
                      (Fun.id q) (NFA.states_enumerate B3_ n) qm,
                     Arith.suc n),
                    ArrayHashSet.ahs_ins_dj (B1_, B2_)
                      (NFA.states_enumerate B3_ n) is))
              end
                b)
            ((ArrayHashMap.ahm_empty (HashCode.hashable_prod B2_ B2_) (),
               (0 : IntInf.int)),
              ArrayHashSet.ahs_empty B2_ ())
            (Enum.product (ArrayHashSet.ahs_to_list B2_ i1)
              (ArrayHashSet.ahs_to_list B2_ i2));
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
                      (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                        let
                          val r =
                            Option.the
                              (ArrayHashMap.ahm_lookup
                                (Product_Type.equal_prod B1_ B1_,
                                  HashCode.hashable_prod B2_ B2_)
                                (Fun.id q) qma);
                        in
                          (if ArrayHashSet.ahs_memb (B1_, B2_) r qs
                            then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                            else let
                                   val (ab, bb) =
                                     let
                                       val (q1a, q2a) = q;
                                     in
                                       (fn ca => fn f =>
 AHS_LTSImpl.ahs_lts_succ_label_it (B1_, B2_) C2_ d1 q1a ca
   (fn (ab, q1b) =>
     AHS_LTSImpl.ahs_lts_succ_it (B1_, B2_) (C1_, C2_) d2 q2a ab ca
       (fn q2b => f (ab, (q1b, q2b)))))
                                     end
                                       (fn _ => true)
                                       (fn (ab, qa) => fn (bb, ca) =>
 let
   val (qmb, nb) = bb;
 in
   (fn (dda, naa) =>
     let
       val r_opt =
         ArrayHashMap.ahm_lookup
           (Product_Type.equal_prod B1_ B1_, HashCode.hashable_prod B2_ B2_)
           (Fun.id qa) qmb;
       val (bd, cb) =
         (if Option.is_none r_opt
           then let
                  val ra = NFA.states_enumerate B3_ nb;
                in
                  ((ArrayHashMap.ahm_update_dj
                      (Product_Type.equal_prod B1_ B1_,
                        HashCode.hashable_prod B2_ B2_)
                      (Fun.id qa) ra qmb,
                     Arith.suc nb),
                    ra)
                end
           else ((qmb, nb), Option.the r_opt));
     in
       let
         val (qmc, nc) = bd;
       in
         (fn ra =>
           ((qmc, nc),
             (AHS_LTSImpl.ahs_lts_add (B1_, B2_) (C1_, C2_) r ab ra dda,
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
  (ArrayHashSet.ahs_ins_dj (B1_, B2_) r qs,
    (asa, (dda, (isa, (if let
                            val (q1a, q2a) = q;
                          in
                            bc (ArrayHashSet.ahs_memb (B1_, B2_) q1a f1)
                              (ArrayHashSet.ahs_memb (B1_, B2_) q2a f2)
                          end
                        then ArrayHashSet.ahs_ins_dj (B1_, B2_) r fs
                        else fs)))))),
 ac))
                                   end
                                     bb
                                 end)
                        end)
                    end
                      ba)
                  (((qm, n),
                     (ArrayHashSet.ahs_empty B2_ (),
                       (a, (AHS_LTSImpl.ahs_lts_empty B2_ C2_ (),
                             (is, ArrayHashSet.ahs_empty B2_ ()))))),
                    Enum.product (ArrayHashSet.ahs_to_list B2_ i1)
                      (ArrayHashSet.ahs_to_list B2_ i2));
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

fun ahs_nfa_rename_labels (B1_, B2_) (C1_, C2_, C3_)
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2a))))) f2 =
  NFAByLTS.Nfa_rep
    (q2, (ArrayHashSet.ahs_image B2_ (B1_, B2_) f2 a2,
           (AHS_LTSImpl.ahs_lts_dlts_image C2_ B2_ (C1_, C2_) (B1_, B2_)
              (fn qaq =>
                (Product_Type.fst qaq,
                  (f2 (Product_Type.fst (Product_Type.snd qaq)),
                    Product_Type.snd (Product_Type.snd qaq))))
              d2,
             (i2, f2a))))
  | ahs_nfa_rename_labels (B1_, B2_) (C1_, C2_, C3_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1a))))) f1 =
    NFAByLTS.Nfa_rep
      (q1, (ArrayHashSet.ahs_image B2_ (B1_, B2_) f1 a1,
             (AHS_LTSImpl.ahs_lts_image C2_ B2_ (C1_, C2_) (B1_, B2_)
                (fn qaq =>
                  (Product_Type.fst qaq,
                    (f1 (Product_Type.fst (Product_Type.snd qaq)),
                      Product_Type.snd (Product_Type.snd qaq))))
                d1,
               (i1, f1a))));

fun ahs_nfa_destruct_simple (A1_, A2_) B_
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  (ArrayHashSet.ahs_to_list A1_ q2,
    (ArrayHashSet.ahs_to_list B_ a2,
      (AHS_LTSImpl.ahs_dlts_to_list A1_ B_ d2,
        (ArrayHashSet.ahs_to_list A1_ i2, ArrayHashSet.ahs_to_list A1_ f2))))
  | ahs_nfa_destruct_simple (A1_, A2_) B_
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    (ArrayHashSet.ahs_to_list A1_ q1,
      (ArrayHashSet.ahs_to_list B_ a1,
        (AHS_LTSImpl.ahs_lts_to_list A1_ B_ d1,
          (ArrayHashSet.ahs_to_list A1_ i1, ArrayHashSet.ahs_to_list A1_ f1))));

fun ahs_nfa_is_deterministic (A1_, A2_, A3_) (B1_, B2_) (NFAByLTS.Dfa_rep d) =
  true
  | ahs_nfa_is_deterministic (A1_, A2_, A3_) (B1_, B2_)
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    AHS_LTSImpl.ahs_lts_is_weak_det A2_ B2_ d1 andalso
      StdInst.ahs_ball A2_ q1
        (fn q =>
          StdInst.ahs_ball B2_ a1
            (fn a =>
              not (((AHS_LTSImpl.ahs_lts_succ_it (A1_, A2_) (B1_, B2_) d1 q a
                      (fn sigma => IntInf.< (sigma, (1 : IntInf.int)))
                      (fn _ => Arith.suc)
                      (0 : IntInf.int)) : IntInf.int) = (0 : IntInf.int)))) andalso
      StdInst.ahs_isSng A2_ i1;

fun ahs_nfa_rename_labels_gen (C1_, C2_, C3_) (D1_, D2_)
  (NFAByLTS.Dfa_rep (q2, (a2a, (d2, (i2, f2a))))) a2 f2 =
  NFAByLTS.Nfa_rep
    (q2, (a2, (AHS_LTSImpl.ahs_lts_dlts_image C2_ D2_ (C1_, C2_) (D1_, D2_)
                 (fn qaq =>
                   (Product_Type.fst qaq,
                     (f2 (Product_Type.fst (Product_Type.snd qaq)),
                       Product_Type.snd (Product_Type.snd qaq))))
                 d2,
                (i2, f2a))))
  | ahs_nfa_rename_labels_gen (C1_, C2_, C3_) (D1_, D2_)
    (NFAByLTS.Nfa_rep (q1, (a1a, (d1, (i1, f1a))))) a1 f1 =
    NFAByLTS.Nfa_rep
      (q1, (a1, (AHS_LTSImpl.ahs_lts_image C2_ D2_ (C1_, C2_) (D1_, D2_)
                   (fn qaq =>
                     (Product_Type.fst qaq,
                       (f1 (Product_Type.fst (Product_Type.snd qaq)),
                         Product_Type.snd (Product_Type.snd qaq))))
                   d1,
                  (i1, f1a))));

fun ahs_dfa_construct_reachable (B1_, B2_) (D1_, D2_, D3_) (E1_, E2_) f i a fp
  d_it =
  NFAByLTS.Dfa_rep
    let
      val (b, c) =
        List.foldl
          (fn (aa, b) =>
            let
              val (qm, n) = aa;
            in
              (fn is => fn q =>
                ((ArrayHashMap.ahm_update_dj (B1_, B2_) (f q)
                    (NFA.states_enumerate D3_ n) qm,
                   Arith.suc n),
                  ArrayHashSet.ahs_ins_dj (D1_, D2_)
                    (NFA.states_enumerate D3_ n) is))
            end
              b)
          ((ArrayHashMap.ahm_empty B2_ (), (0 : IntInf.int)),
            ArrayHashSet.ahs_empty D2_ ())
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
                    (fn (qs, (asa, (dd, (isa, fs)))) => fn q =>
                      let
                        val r =
                          Option.the
                            (ArrayHashMap.ahm_lookup (B1_, B2_) (f q) qma);
                      in
                        (if ArrayHashSet.ahs_memb (D1_, D2_) r qs
                          then (((qma, na), (qs, (asa, (dd, (isa, fs))))), [])
                          else let
                                 val (ab, bb) =
                                   d_it q (fn _ => true)
                                     (fn (ab, qa) => fn (bb, ca) =>
                                       let
 val (qmb, nb) = bb;
                                       in
 (fn (dda, naa) =>
   let
     val r_opt = ArrayHashMap.ahm_lookup (B1_, B2_) (f qa) qmb;
     val (bc, cb) =
       (if Option.is_none r_opt
         then let
                val ra = NFA.states_enumerate D3_ nb;
              in
                ((ArrayHashMap.ahm_update_dj (B1_, B2_) (f qa) ra qmb,
                   Arith.suc nb),
                  ra)
              end
         else ((qmb, nb), Option.the r_opt));
   in
     let
       val (qmc, nc) = bc;
     in
       (fn ra =>
         ((qmc, nc),
           (AHS_LTSImpl.ahs_dlts_add (D1_, D2_) (E1_, E2_) r ab ra dda,
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
(ArrayHashSet.ahs_ins_dj (D1_, D2_) r qs,
  (asa, (dda, (isa, (if fp q then ArrayHashSet.ahs_ins_dj (D1_, D2_) r fs
                      else fs)))))),
                                       ac))
                                 end
                                   bb
                               end)
                      end)
                  end
                    ba)
                (((qm, n),
                   (ArrayHashSet.ahs_empty D2_ (),
                     (a, (AHS_LTSImpl.ahs_dlts_empty D2_ E2_ (),
                           (is, ArrayHashSet.ahs_empty D2_ ()))))),
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

fun ahs_nfa_right_quotient_lists A_ (B1_, B2_, B3_) ap
  (NFAByLTS.Dfa_rep (q2, (a2, (d2, (i2, f2))))) =
  NFAByLTS.Dfa_rep
    let
      val m =
        AHS_LTSImpl.ahs_dlts_filter_it B2_ A_ (fn _ => true) ap (fn _ => true)
          (fn _ => true) d2 (fn _ => true)
          (fn (q, (_, qa)) => fn m =>
            let
              val s =
                (case ArrayHashMap.ahm_lookup (B1_, B2_) qa m
                  of NONE => ArrayHashSet.ahs_empty B2_ () | SOME s => s);
            in
              ArrayHashMap.ahm_update (B1_, B2_) qa
                (ArrayHashSet.ahs_ins (B1_, B2_) q s) m
            end)
          (ArrayHashMap.ahm_empty B2_ ());
      val f =
        Product_Type.fst
          (Workset.worklist (fn _ => true)
            (fn s => fn e =>
              (if ArrayHashSet.ahs_memb (B1_, B2_) e s then (s, [])
                else (ArrayHashSet.ahs_ins (B1_, B2_) e s,
                       (case ArrayHashMap.ahm_lookup (B1_, B2_) e m
                         of NONE => []
                         | SOME a => ArrayHashSet.ahs_to_list B2_ a))))
            (ArrayHashSet.ahs_empty B2_ (), ArrayHashSet.ahs_to_list B2_ f2));
    in
      (q2, (a2, (d2, (i2, f))))
    end
  | ahs_nfa_right_quotient_lists A_ (B1_, B2_, B3_) ap
    (NFAByLTS.Nfa_rep (q1, (a1, (d1, (i1, f1))))) =
    NFAByLTS.Nfa_rep
      let
        val m =
          AHS_LTSImpl.ahs_lts_filter_it B2_ A_ B2_ (fn _ => true) ap
            (fn _ => true) (fn _ => true) d1 (fn _ => true)
            (fn (q, (_, qa)) => fn m =>
              let
                val s =
                  (case ArrayHashMap.ahm_lookup (B1_, B2_) qa m
                    of NONE => ArrayHashSet.ahs_empty B2_ () | SOME s => s);
              in
                ArrayHashMap.ahm_update (B1_, B2_) qa
                  (ArrayHashSet.ahs_ins (B1_, B2_) q s) m
              end)
            (ArrayHashMap.ahm_empty B2_ ());
        val f =
          Product_Type.fst
            (Workset.worklist (fn _ => true)
              (fn s => fn e =>
                (if ArrayHashSet.ahs_memb (B1_, B2_) e s then (s, [])
                  else (ArrayHashSet.ahs_ins (B1_, B2_) e s,
                         (case ArrayHashMap.ahm_lookup (B1_, B2_) e m
                           of NONE => []
                           | SOME a => ArrayHashSet.ahs_to_list B2_ a))))
              (ArrayHashSet.ahs_empty B2_ (), ArrayHashSet.ahs_to_list B2_ f1));
      in
        (q1, (a1, (d1, (i1, f))))
      end;

fun ahs_dfa_construct_reachable_fun (B1_, B2_) (C1_, C2_) (E1_, E2_, E3_) ff i a
  fp d_fun =
  ahs_dfa_construct_reachable (B1_, B2_) (E1_, E2_, E3_) (C1_, C2_) ff [i] a fp
    (fn q => fn c => fn f =>
      ArrayHashSet.ahs_iteratei C2_ c (fn x => f (x, d_fun q x)) a);

end; (*struct AHS_NFAImpl*)

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

structure AHS_Presburger_Impl : sig
  val ahs_DFA_eq_ineq :
    'b HOL.equal * 'b HashCode.hashable * 'b NFA.nFA_states ->
      ((bool list), unit) ArrayHashMap.hashmap ->
        bool ->
          'a -> IntInf.int list ->
                  IntInf.int ->
                    ((('b, unit) ArrayHashMap.hashmap *
                       (((bool list), unit) ArrayHashMap.hashmap *
                         (('b, ((bool list), ('b, unit) ArrayHashMap.hashmap)
                                 ArrayHashMap.hashmap)
                            ArrayHashMap.hashmap *
                           (('b, unit) ArrayHashMap.hashmap *
                             ('b, unit) ArrayHashMap.hashmap)))),
                      (('b, unit) ArrayHashMap.hashmap *
                        (((bool list), unit) ArrayHashMap.hashmap *
                          (('b, ((bool list), 'b) ArrayHashMap.hashmap)
                             ArrayHashMap.hashmap *
                            (('b, unit) ArrayHashMap.hashmap *
                              ('b, unit) ArrayHashMap.hashmap)))))
                      NFAByLTS.automaton
  val ahs_cache_alpha :
    (IntInf.int, ((bool list), unit) ArrayHashMap.hashmap)
      ArrayHashMap.hashmap ->
      IntInf.int ->
        (IntInf.int, ((bool list), unit) ArrayHashMap.hashmap)
          ArrayHashMap.hashmap *
          ((bool list), unit) ArrayHashMap.hashmap
  val ahs_pres_nfa_of_pf :
    'a HOL.equal * 'a HashCode.hashable * 'a NFA.nFA_states ->
      IntInf.int ->
        Presburger_Automata.pf ->
          (IntInf.int, ((bool list), unit) ArrayHashMap.hashmap)
            ArrayHashMap.hashmap ->
            ((('a, unit) ArrayHashMap.hashmap *
               (((bool list), unit) ArrayHashMap.hashmap *
                 (('a, ((bool list), ('a, unit) ArrayHashMap.hashmap)
                         ArrayHashMap.hashmap)
                    ArrayHashMap.hashmap *
                   (('a, unit) ArrayHashMap.hashmap *
                     ('a, unit) ArrayHashMap.hashmap)))),
              (('a, unit) ArrayHashMap.hashmap *
                (((bool list), unit) ArrayHashMap.hashmap *
                  (('a, ((bool list), 'a) ArrayHashMap.hashmap)
                     ArrayHashMap.hashmap *
                    (('a, unit) ArrayHashMap.hashmap *
                      ('a, unit) ArrayHashMap.hashmap)))))
              NFAByLTS.automaton *
              (IntInf.int, ((bool list), unit) ArrayHashMap.hashmap)
                ArrayHashMap.hashmap
  val ahs_pres_pf_to_nfa :
    IntInf.int ->
      Presburger_Automata.pf ->
        (((IntInf.int, unit) ArrayHashMap.hashmap *
           (((bool list), unit) ArrayHashMap.hashmap *
             ((IntInf.int,
                ((bool list), (IntInf.int, unit) ArrayHashMap.hashmap)
                  ArrayHashMap.hashmap)
                ArrayHashMap.hashmap *
               ((IntInf.int, unit) ArrayHashMap.hashmap *
                 (IntInf.int, unit) ArrayHashMap.hashmap)))),
          ((IntInf.int, unit) ArrayHashMap.hashmap *
            (((bool list), unit) ArrayHashMap.hashmap *
              ((IntInf.int, ((bool list), IntInf.int) ArrayHashMap.hashmap)
                 ArrayHashMap.hashmap *
                ((IntInf.int, unit) ArrayHashMap.hashmap *
                  (IntInf.int, unit) ArrayHashMap.hashmap)))))
          NFAByLTS.automaton
  val ahs_eval_pf : Presburger_Automata.pf -> bool
  val eval_pf_dfa : Presburger_Automata.pf -> bool
end = struct

fun ahs_DFA_eq_ineq (B1_, B2_, B3_) a ineq n ks l =
  AHS_NFAImpl.ahs_dfa_construct_reachable_fun
    (Arith.equal_nat, HashCode.hashable_nat)
    (List.equal_list Product_Type.equal_bool,
      HashCode.hashable_list HashCode.hashable_bool)
    (B1_, B2_, B3_) Presburger_Adapt.pres_NFA_state_to_nat
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

fun ahs_cache_alpha m n =
  (if ((n : IntInf.int) = (0 : IntInf.int))
    then (m, StdInst.ahs_sng
               (List.equal_list Product_Type.equal_bool,
                 HashCode.hashable_list HashCode.hashable_bool)
               [])
    else (case ArrayHashMap.ahm_lookup (Arith.equal_nat, HashCode.hashable_nat)
                 (Arith.suc (Arith.minus_nat n (1 : IntInf.int))) m
           of NONE =>
             let
               val (ma, bl) =
                 ahs_cache_alpha m (Arith.minus_nat n (1 : IntInf.int));
               val bla =
                 ArrayHashSet.ahs_union
                   (List.equal_list Product_Type.equal_bool,
                     HashCode.hashable_list HashCode.hashable_bool)
                   (ArrayHashSet.ahs_image
                     (HashCode.hashable_list HashCode.hashable_bool)
                     (List.equal_list Product_Type.equal_bool,
                       HashCode.hashable_list HashCode.hashable_bool)
                     (fn a => true :: a) bl)
                   (ArrayHashSet.ahs_image
                     (HashCode.hashable_list HashCode.hashable_bool)
                     (List.equal_list Product_Type.equal_bool,
                       HashCode.hashable_list HashCode.hashable_bool)
                     (fn a => false :: a) bl);
               val mb =
                 ArrayHashMap.ahm_update
                   (Arith.equal_nat, HashCode.hashable_nat)
                   (Arith.suc (Arith.minus_nat n (1 : IntInf.int))) bla ma;
             in
               (mb, bla)
             end
           | SOME a => (m, a)));

fun ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Neg p) c =
  let
    val (pa, a) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n p c;
  in
    (AHS_NFAImpl.ahs_nfa_complement (A1_, A2_, A3_) pa, a)
  end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Forall p) c =
    let
      val (ca, a) = ahs_cache_alpha c n;
      val (pa, b) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) (Arith.suc n) p ca;
    in
      (AHS_NFAImpl.ahs_nfa_complement (A1_, A2_, A3_)
         (AHS_NFAImpl.ahs_nfa_right_quotient_lists
           (HashCode.hashable_list HashCode.hashable_bool) (A1_, A2_, A3_)
           (List.list_all not)
           (AHS_NFAImpl.ahs_nfa_Brzozowski (A1_, A2_, A3_)
             (List.equal_list Product_Type.equal_bool,
               HashCode.hashable_list HashCode.hashable_bool)
             (AHS_NFAImpl.ahs_nfa_rename_labels_gen (A1_, A2_, A3_)
               (List.equal_list Product_Type.equal_bool,
                 HashCode.hashable_list HashCode.hashable_bool)
               (AHS_NFAImpl.ahs_nfa_complement (A1_, A2_, A3_) pa) a List.tl))),
        b)
    end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Exist p) c =
    let
      val (ca, a) = ahs_cache_alpha c n;
      val (pa, b) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) (Arith.suc n) p ca;
    in
      (AHS_NFAImpl.ahs_nfa_right_quotient_lists
         (HashCode.hashable_list HashCode.hashable_bool) (A1_, A2_, A3_)
         (List.list_all not)
         (AHS_NFAImpl.ahs_nfa_Brzozowski (A1_, A2_, A3_)
           (List.equal_list Product_Type.equal_bool,
             HashCode.hashable_list HashCode.hashable_bool)
           (AHS_NFAImpl.ahs_nfa_rename_labels_gen (A1_, A2_, A3_)
             (List.equal_list Product_Type.equal_bool,
               HashCode.hashable_list HashCode.hashable_bool)
             pa a List.tl)),
        b)
    end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Imp (p, q)) c =
    let
      val (pa, ca) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n p c;
      val (qa, a) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n q ca;
    in
      (AHS_NFAImpl.ahs_nfa_bool_comb (A1_, A2_, A3_)
         (List.equal_list Product_Type.equal_bool,
           HashCode.hashable_list HashCode.hashable_bool)
         (fn aa => fn b => (if aa then b else true)) pa qa,
        a)
    end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Or (p, q)) c =
    let
      val (pa, ca) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n p c;
      val (qa, a) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n q ca;
    in
      (AHS_NFAImpl.ahs_nfa_bool_comb (A1_, A2_, A3_)
         (List.equal_list Product_Type.equal_bool,
           HashCode.hashable_list HashCode.hashable_bool)
         (fn aa => fn b => aa orelse b) pa qa,
        a)
    end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.And (p, q)) c =
    let
      val (pa, ca) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n p c;
      val (qa, a) = ahs_pres_nfa_of_pf (A1_, A2_, A3_) n q ca;
    in
      (AHS_NFAImpl.ahs_nfa_bool_comb (A1_, A2_, A3_)
         (List.equal_list Product_Type.equal_bool,
           HashCode.hashable_list HashCode.hashable_bool)
         (fn aa => fn b => aa andalso b) pa qa,
        a)
    end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Le (ks, l)) c =
    let
      val (ca, a) = ahs_cache_alpha c n;
    in
      (ahs_DFA_eq_ineq (A1_, A2_, A3_) a true n ks l, ca)
    end
  | ahs_pres_nfa_of_pf (A1_, A2_, A3_) n (Presburger_Automata.Eq (ks, l)) c =
    let
      val (ca, a) = ahs_cache_alpha c n;
    in
      (ahs_DFA_eq_ineq (A1_, A2_, A3_) a false n ks l, ca)
    end;

fun ahs_pres_pf_to_nfa n pf =
  Product_Type.fst
    (ahs_pres_nfa_of_pf
      (Arith.equal_nat, HashCode.hashable_nat, NFA.nFA_states_nat) n pf
      (ArrayHashMap.ahm_empty HashCode.hashable_nat ()));

fun ahs_eval_pf pf =
  AHS_NFAImpl.ahs_nfa_accept
    (Arith.equal_nat, HashCode.hashable_nat, NFA.nFA_states_nat)
    (List.equal_list Product_Type.equal_bool,
      HashCode.hashable_list HashCode.hashable_bool)
    (ahs_pres_pf_to_nfa (0 : IntInf.int) pf) [];

fun eval_pf_dfa pf =
  Presburger_Automata.accepts
    (Presburger_Automata.dfa_trans
      (Presburger_Automata.dfa_of_pf (0 : IntInf.int) pf))
    (Presburger_Automata.dfa_accepting
      (Presburger_Automata.dfa_of_pf (0 : IntInf.int) pf))
    (0 : IntInf.int) [];

end; (*struct AHS_Presburger_Impl*)
