(* Sets as an abstract data type. Not intended for big sets. H.Leiss, 11/98
   Edited:
   - 14.01.99 bigUnion now without accumulator argument (was: bigU)
   - 16.02.00 renamed EmptySet to empty 
                      abstype 'a set to (data)type 'a t
                      bigUnion to Union
*)

signature SET =
  sig
    type 'a t
    val add : ''a -> ''a t -> ''a t
    val Union : ''a t list -> ''a t
    val difference : ''a t -> ''a t -> ''a t
    val drop : ''a -> ''a t -> ''a t
    val empty : 'a t
    val equal : ''a t -> ''a t -> bool
    val intersects : ''a t -> ''a t -> bool
    val list : 'a t -> 'a list
    val map : ('a -> ''b) -> 'a t -> ''b t
    val member : ''a -> ''a t -> bool
    val mk : ''a list -> ''a t
    val select : 'a t -> ('a -> bool) -> 'a t
    val singleton : 'a -> 'a t
    val size : 'a t -> int
    val subset : ''a t -> ''a t -> bool
    val union : ''a t -> ''a t -> ''a t
  end

structure Set :> SET =
    struct
        datatype 'a t = Set of 'a list

        val empty = Set ([]:'a list)

        fun member x (Set []) = false
          | member x (Set (y::ys)) = (x = y) orelse (member x (Set ys))
        and add x (Set S) = 
            let fun addLst x [] = [x]
                  | addLst x (u::U) = if x=u then (u::U) else u::(addLst x U)
            in Set (addLst x S) end
	and intersects (Set []) Q = false
	  | intersects (Set (p::P)) Q = 
            (member p Q) orelse (intersects (Set P) Q)
	and union (Set []) U = U
	  | union (Set (x::Q)) U = (* x is not in Q! *)
            union (Set Q) (add x U)
        and Union sets = 
            let 
                fun bigU [] (Set U) = (Set U)
                  | bigU (Q::Qs) U = bigU Qs (union Q U)
            in 
                bigU sets empty
            end
	and drop e (Set S) =
            let fun subtr [] e = []
                  | subtr (s::S) e = if s=e then S (* s not in S! *)
                                     else (s::(subtr S e))
            in Set (subtr S e) end
	and difference (Set S) (Set T) =
            let fun diff (Set S) [] = S  
                  | diff (Set S) (e::E) = diff (drop e (Set S)) E
            in Set (diff (Set S) T) end

        fun size (Set S) = List.length S 
        and mk L = Union (map (fn x => Set [x]) L) 
        and list (Set S) = S
	and select (Set S) f =
            let fun selct [] f = []
                  | selct (s::S) f = if f s then (s::(selct S f))
                                     else (selct S f)
            in Set (selct S f) end

        fun subset S T = 
            let fun f x = member x T
                val U = select S f
            in size U = size S end
        and equal S T = (size S = size T) andalso (subset S T)

	fun map f (Set S) = mk (List.map f S)
	fun singleton e = (Set [e])  (* don't use mk to avoid equality type *)
    end





