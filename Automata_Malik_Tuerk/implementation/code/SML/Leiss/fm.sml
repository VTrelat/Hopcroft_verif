(* File:    fm.sml
   Content: Finite Automata without epsilon-transitions,  polymorphic in the alphabet.
   Author:  Hans Leiss, CIS, 12/99,  leiss@cis.uni-muenchen.de

   Assumptions for minimization: 
   (i)  the input automaton is (total) deterministic;
   (ii) all states in the input automaton are reachable from the initial state.

   Make M deterministic to remove unreachable states.

  To be done: 
  - allow alphabet to extend the labels occurring in transitions. (cf. kmp-automaton)
  - might remove some states in Times(M::Ms)

 16.12.99 - added: eta-expansion in minimization, to make it polymorphic in the alphabet
 18.12.99 - changed to use SML-Site-Library/set.sml; 
            states and instructions are now sets (which forces eq-type: ''a machine)
          - added showDetermine 
 14.02.00 - renamed instr to trans, bigUnion to Union
 16.02.99 - made structure Fm : FM 
          - changed FM by removing showEquivStates, 
                          addding minimizeWithStateAssoc,
                          addding determineWithStateAssoc,
 24.02.00 - corrected bug in minimization (cf. example 5)
          - added minimizeWithHistory (also in FM)
          - added Debug and debugMsg (not in FM)
 22.01.10 - thinned out the snapshots in MinimizeHistory and indicated initial and final 
            states in the approximations. Corrected a bug in minimization. (fmbug2)
*)

signature FM = 
  sig
    type ''a machine  
    (* nondeterministic finite automata over alphabet ''a *)

    val Atom : ''a -> ''a machine
    (* returns a machine accepting the atom (letter) a *)
    val Plus : ''a machine list -> ''a machine
    (* returns a machine accepting the union of languages accepted by the machines in the list *)
    val Star : ''a machine -> ''a machine
    (* returns a machine accepting the Kleene closure of the language accepted by m *)
    val Times : ''a machine list -> ''a machine
    (* returns a machine accepting the concatenation of the language 
       accepted by the machines in the list *)
    val accept : ''a machine -> ''a list -> bool
    (* returns true if the machines accepts the given sequence, false otherwise. *)

    val make : {final:int list, 
                trans:(int * ''a * int) list, 
                start:int list} -> ''a machine
    (* construct a machine from the lists of (numbers of) start states, final states, and transitions *)
    val show : ''a machine
               -> {final:int list, 
                   trans:(int * ''a * int) list, 
                   start:int list}

    val states : ''a machine -> int         
	(* an upper bound for the number of states of m *)
    val nextstates : ''a machine -> int -> ''a -> int list
        (* a list of all states which m reaches from state i when reading letter a *)
    val reach : ''a machine -> int list -> ''a list -> int list
        (* a list of all states which m reaches from state i when reading a sequence l of letters *)
    val determine : ''a machine -> ''a machine 
        (* given a nondeterministic machine m, returns an equivelent determinstic machine m2. *)
    val determineWithStateAssoc : ''a machine -> ''a machine * (int * int list) list
    val minimize : ''a machine -> ''a machine 
        (* given a (total) deterministic machine m, returns an equivalent minimal (total)
           deterministic machine m2. Raises an exception if the given machine is partial (or nondet??) *)
    val minimizeWithStateAssoc : ''a machine -> ''a machine * (int * int list) list

    val minimizeWithHistory : ''a machine -> ((''a * int list) machine * (int * int list) list) list  
  end;

structure Fm :> FM = 
  struct
    local 
      val incr = fn (n:int) => (fn (x,a,y) => (x+n,a,y+n))
      val addNat  = fn (n:int) => (fn m => m+n)

      fun member x l = List.exists (fn y => y = x) l
      and add q [] = [q]
        | add q (u::U) = if q=u then (u::U) else (u::(add q U))
      and union [] U = U
        | union (q::Q) U = union Q (add q U)
      and intersects [] Q = false
        | intersects (p::P) Q = if member p Q then true 
                                else intersects P Q
      and Union [] = []
        | Union (Q::Qs) = union Q (Union Qs)
      and difference S [] = S  
        | difference S (e::E) = difference (subtract S e) E
      and subtract [] e = []
        | subtract (s::S) e = if s=e then subtract S e 
                              else (s::(subtract S e))


      (* --- Datatypes and functions needed for minimization ----

       ----------------- Doubly linked lists -----------------------
       
       A node contains an element and points to a prev(ious) and a next 
       node. The node represents a doubly linked list if 

       next(pred(node)) = node = pred(next(node)).

       Doubly linked lists are given by any of their representing nodes,
       or empty. *)

      datatype 'a dl = Nil | Node of 'a dl ref * 'a * 'a dl ref

      exception EmptyDL

      fun next Nil = raise EmptyDL
        | next (Node(_,_,R)) = !R
      and prev Nil = raise EmptyDL
        | prev (Node(L,_,_)) = !L

      (* To pop a Node(L,a,R) representing a doubly linked list means to
       form the `restlist' by connecting the next node to the previous one
       and conversely, and to return the pair of a and the new next node. *)

      fun pop Nil = raise EmptyDL  
        | pop (Node(L,a,R)) = 
        ((case (!L) of Node(_,_,R') => R' := (!R) | _ => ());
            (case (!R) of Node(L',_,_) => L' := (!L) | _ => ());
               if Nil = !L andalso Nil = !R then (a,Nil) else (a,!R))

      (* To push a to a node N representing a doubly linked list means to 
       insert a new node Node(_,a,_) between the previous node and N. *)

      fun push (a, Nil) = Node(ref Nil, a, ref Nil)
        | push (a, Node(L,x,R)) = 
        let 
          val r = Node(L,x,R) and l = (!L)
          val n = Node(ref l, a, ref r)
        in 
          (case l of Node(L',x',R') => R' := n | _ => ()); L := n; n
        end

      fun mapDl f Nil = []
        | mapDl f (Node(L,a,R)) = (f a :: (mapDl f (!R)))

      fun appDl f Nil = ()
        | appDl f (Node(L,a,R)) = (f a ; (appDl f (!R)))

      fun element (Node(L,a,R)) = a
        | element Nil = raise EmptyDL

      fun remove (ptNode,ptDlist) = 
        if (!ptNode) = (!ptDlist) 
          then (ptDlist := #2(pop (!ptNode)) ; ptNode := Nil)
        else (pop (!ptNode); ptNode := Nil)

      (* --------- Datatypes to compute equivalence classes ---------------
       
       We use N.Blum's O(|Sigma|*|Q|*log|Q|) algorithm to minimize a total
       deterministic finite automaton. See Information Processing letters 57,
       p. 65-69, 1996. Actually, we need |Final| instead of log|Q|, since 
       we don't have a final-state bits at states, but search through Final. 

       The minimal automaton is constructed by refining approximations to its 
       transition relation. Transitions in the approximations are called (i,a,j),
       where i and j are names of subsetes Q.i and Q.j of Q. Initially, one sets
       Q.0 := Final, Q.1 := Q-Final. We need

       - a list L of transitions (i,a,j), 
       - for transitions, the set L(i,a,j) = {q in Q.i | delta(q,a) in Q.j} sub Q.i
       - a list Delta'(i,a) = {k | L(i,a,k) is nonempty},
       - a list K = {(i,a)| 2 <= |Delta'(i,a)|} containing those (i,a) where
         subset Q.i has to be split, because a leads from Q.i to different Q.k ,Q.k'.
 
       As long as some (i,a) in K indicates that we have to split a state i because 
       a leads to different non-empty sets Q.k, Q.k', we separate the smaller subset 
       as Q.(t+1) = L(t+1,a,k) := L(i,a,j) and then update other lists L(i',b,j') 
       by removing resp. adding q's of Q.(t+1).

       To do these adjustments efficiently, the sets are cross-linked and some 
       arrays are needed to find elements:

       - an array Delta, where Delta(q,b) holds a pointer to the element q in
         the unique L(i,b,k) where it occurs,
       - a (static) array DeltaInv, where DeltaInv(b,q) holds {p in Q|delta(p,b)=q},
       - an array Gamma, where Gamma(b,k) points to the latest transition in
         { (j,b,k) | 0<= j} that is added to L,
       - an array Gamma', where Gamma'(p,b) points to the (k,b,t+1) where p is in 
         L(k,b,t+1), if there is such (k,b,t+1).
       *)
       
      type 'a dref = 'a dl ref

      datatype ('key,'elem) LineD =  
        LD of 'key * ('key,'elem) LineD dref dref
        * (int ref)
        * ('elem * ('key,'elem) LineD dref) dref

      (* LD((i,a),ptK,ref n,ref dl) says that
          - L(i,a,k) is nonempty for at least one k,
          - ptK points to an element on K which points back to LD((i,a),..)
          - n is the number of k's such that L(i,a,k) is nonempty,
          - dl = {[ (ptL,ptD) | each ptL points to one the nonempty L(i,a,k)'s 
                                and ptD points back to LD((i,a),..) ]}
       ....
       *)
            
      datatype ('st,'lab,'elem) LineL =  
        LL of ('st ref * 'lab * 'st) 
        * (('st,'lab,'elem) LineL dref 
           * 
           ('st * 'lab, ('st,'lab,'elem) LineL dref) LineD dref
           ) dref 
        * (int ref) 
        * ('elem * ('st,'lab,'elem) LineL dref) dref

      (* LL((ref i,a,j),ptD,ref n,ref Qs) says that 
          - Qs = {[ (q,pt) | q in Q.i, delta(q,a) in Q.j ]} represents L(i,a,j),
            where {[ . ]} means a doubly linked list, 
          - n is the length of Qs,
          - pt is a pointer pointing back to the very node LL((ref i,a,j),....),
          - ptD is a pointer to an element in Delta' pointing back to LL((ref i,a,j),...) 
       *)
            
      type state = int

      type 'a line   = (state, 'a, state) LineL dl           (* lines of L *)
      type 'a split  = (state * 'a, 'a line ref) LineD dl    (* lines of Delta' *)
      type 'a agenda = 'a split ref dref                     (* K *)

      fun ptHeadNodeL (ptEl : (state * 'a line ref) dl ref) = #2(element(!ptEl))
      and HeadNodeL (ptEl) : 'a line = !(ptHeadNodeL(ptEl))
      and HeadElemL (ptEl) = element(HeadNodeL(ptEl)) 

      fun ptHeadNodeD (ptEl: ('a line ref * (state * 'a,'a line ref) LineD dref) dref) 
        = #2(element(!ptEl))
      and HeadNodeD (ptEl) = !(ptHeadNodeD(ptEl))
      and HeadElemD (ptEl) = element(HeadNodeD(ptEl)) 

      (* Default A*B-arrays, storing for each (a,b) a pointer to an initial value 
         which is updated later. *)

      exception Undefined
      exception nonDeterministic   

      fun makeLookup A B value =
        let 	
          val array = map (fn a => (a,(map (fn b => (b, ref value)) B))) A
          fun find k ((key,datum)::rest) =
            if k=key then datum else find k rest
            | find k [] = raise Undefined
          fun lookup (a,b) = find b (find a array)
        in 
          lookup
        end; (* add handler : not a deterministic automaton *)

      (* eta-expansion to escape from value restriction resp. unresolved weak tyvars *)

      fun makeK ()       = ref Nil : 'a agenda        
      and makeDelta' ()  = ref (Nil : 'a split)  
      and makeLs ()      = ref (Nil : 'a line)       
      and makeDelta Q S  = makeLookup Q S (Nil: (state * ('a line ref)) dl)
      and makeGamma Q S  = makeLookup S Q (Nil:'a line)
      and makeGamma' Q S = makeLookup Q S (Nil:'a line)

      fun makeHistory () = ref [] : ({start : int list, 
                                      trans : (int * 'a * int) list, 
                                      final : int list} * (state * state list) list) list ref


      fun mkSnapshot (Start,Final) (Ls : ''a line) = 
        let 
          fun extract Nil (accTrans,newStart,accFinal) = (accTrans,newStart,accFinal)
            | extract (Node(_,(LL((ref i,a,j),_,_,ptSet)),R)) (accI,newS,accF) =
              let 
                  fun strt [] = 
                      (case Start of 
                           [] => []
                         | [q] => if found (!ptSet) q then [i] else []
                         | _ => raise nonDeterministic)
                    | strt (i :: rest) = (i :: rest)
                  and found Nil q = false
                    | found (Node(_,(p,_),R)) q = 
                      if p = q then true else found (!R) q
              
                  fun isFinal Nil = false
                    | isFinal (Node(_,(p,_),R)) =
                      if member p Final then true else isFinal (!R)
              in
                  extract (!R) ((i,(a,mapDl #1 (!ptSet)),j) :: accI,
                                strt newS, 
                                if isFinal (!ptSet) then add i accF else accF)
              end

          val (newTrans,newStart,newFinal) = extract Ls ([],[],[])

          val stateAssoc = 
            let 
              fun assoc (LL((ref p,a,q),ptr,n,dl)) = (p, mapDl #1 (!dl)) 
              fun collect [] acc = acc
                | collect ((p,P)::qs) acc = collect qs (add (p,P) acc)
              and add (p,P) [] = [(p,P)]
                | add (p,P) ((q,Q)::qs) = if p=q then ((q,union P Q)::qs) 
                                          else (q,Q)::(add (p,P) qs)
            in 
              collect (mapDl assoc Ls) [] 
            end
        in
          ({trans = newTrans, start = newStart, final = newFinal}, stateAssoc)
        end

      (* for debugging *)
 
      val Debug = ref false
      fun debugMsg s = if (!Debug) then print s else ()

    in         
      abstype 'a machine = 
        Ma of {states : int,
               start : int Set.t, 
               trans : (int * 'a * int) Set.t, 
               final : int Set.t}
      with
        type 'a line   = (state, 'a, state) LineL dl        (* lines of L *)

        fun make {trans=I, start=S, final=F} =
          let 
            val maxStart = foldr Int.max 0 S
            val maxFinal = foldr Int.max maxStart F
            val maxState = 
              foldr (fn ((i,a,j),k) => 
                     Int.max (Int.max(i,j),k)) maxFinal I
          in 
            Ma{states = maxState+1, start = Set.mk S, trans = Set.mk I, final = Set.mk F}
          end

        fun show M = {start = start M, trans = trans M, final = final M}
        and start  (Ma{start = S, ...}) = Set.list S
        and final  (Ma{final = F, ...}) = Set.list F
        and trans  (Ma{trans = I, ...}) = Set.list I
        and states (Ma{states = n, ...}) = n
   
        (* Automata constructions *)

        fun Atom a = 
          Ma{states = 2, start = Set.mk[0], trans = Set.mk[(0,a,1)], final = Set.mk[1]}

        fun Plus [] = Ma{states = 0, start = Set.mk[], trans = Set.mk[], final = Set.mk[]}
          | Plus (M :: Ms) = 
          let 
            fun plus 
              (Ma{states = nA, start = sA, trans = inA, final = finA},
               Ma{states = nB, start = sB, trans = inB, final = finB}) 
              = Ma{states = nA+nB, 
                   start = Set.union sA (Set.map (addNat nA) sB), 
                   trans = Set.union inA (Set.map (incr nA) inB), 
                   final = Set.union finA (Set.map (addNat nA) finB)} 
          in 
            plus (M, Plus Ms) 
          end

        fun Times [] = 
            Ma{states = 1, start = Set.mk[0], trans = Set.mk[], final = Set.mk[0]} 
          | Times [M] = M
          | Times (M :: Ms) = (* Without adding empty moves! *)
          let                 (* Might remove finA-inA's with outdegree 0 *)
            fun times 
              (Ma{states = nA, start = sA, trans = inA, final = finA},
               Ma{states = nB, start = sB, trans = inB, final = finB}) 
              = let 
                val sB' = Set.map (addNat nA) sB
                val inB' = Set.map (incr nA) inB
                val finB' = Set.map (addNat nA) finB
                  
                fun between ((p,a,q)::I) NewTrans =
                  if Set.member q finA
                    then Set.union (Set.map (fn s => (p,a,s)) sB') (between I NewTrans)
                  else between I NewTrans
                  | between [] NewTrans = NewTrans
              in 
                Ma{states = nA+nB,   
                   start = if Set.intersects sA finA then Set.union sA sB'
                           else sA,       
		   trans = Set.Union [inA,(between (Set.list inA) Set.empty),inB'],
                   final = finB'} 
              end
          in 
            times (M, Times Ms) 
          end

        fun Star M = 
          let 
            val sA' = map (addNat 1) (start M)
            val inA' = map (incr 1) (trans M)
            val finA' = map (addNat 1) (final M)

            fun after ((p,a,q)::I) NewTrans =
              if member q finA'
                then after I (map (fn s => (p,a,s)) sA') @ NewTrans
              else after I NewTrans
              | after [] NewTrans = NewTrans
          in Ma{states = 1 + (states M),
                start = Set.mk(0 :: sA'),
                trans = Set.mk(inA' @ (after inA' [])), 
                final = Set.mk(0 :: finA')} 
          end

        fun nextstates M q a = 
          let fun g [] acc = acc
                | g ((x,b,p)::r) acc =
            if (x,b) = (q,a) then g r (add p acc) else g r acc
          in g (trans M) []
          end  
        and reach M Q [] = Q
          | reach M Q (a::l) = 
            let val Qs = map (fn q => (nextstates M q a)) Q 
            in reach M (Union Qs) l end
        and accept M w = intersects (reach M (start M) w) (final M)

        and labels M = 
          let fun labls ((x,a,y)::Trans) L = labls Trans (add a L)
                | labls [] L = L
          in labls (trans M) [] end

        and power M = 
          let fun newStateTrans M A =	
            let fun action A (a,(States,Transs)) = 
              let val B = reach M A [a] 
              in (add B States, add (A,a,B) Transs) end
            in foldr (action A) ([],[]) (labels M) 
            end 
              and service ([],Done,Trans) = ([],Done,Trans)
                | service (A::Queue,Done,Trans) =
                let val (nStates,nTrans) = newStateTrans M A 
                in let val Queue' = union (difference nStates Done) Queue
                       and Done'  = add A Done
                       and Trans' = union nTrans Trans
                in service (Queue',Done',Trans') end
                end
              val (_,pStates,pTrans) = service ([start M],[],[]) 
              val pFinal = List.filter (intersects (final M)) pStates 
          in 
            {start = [start M], trans = pTrans, final = pFinal, states= pStates} 
          end

        and determineWithStateAssoc M =
          let 
            val {start = pStart, trans = pTrans, final = pFinal, 
                 states= pStates} = power M
              
            exception renumUndefined

            fun enum X = 
              let fun num [] n = []             
                    | num (x::X) n = (n,x)::(num X (n+1))
              in num X 0 end
            and renum [] y = raise renumUndefined
              | renum ((n,x)::L) y = if y=x then n else renum L y

            val stateAssoc = (enum pStates)
            fun nr S = renum stateAssoc S
          in
            (make {start = map nr pStart,
                   trans = map (fn (p,a,q) => (nr p, a, nr q)) pTrans,
                   final = map nr pFinal},
             stateAssoc)
          end
        and determine M = (#1 (determineWithStateAssoc M))

      end

      fun minimizeWithEquivalentStates M = 
        let val (Ls, _) = minimizeWithSnapshots M false in Ls end

      and minimizeWithHistory M =
        let val (_, MAss) = minimizeWithSnapshots M true
        in 
          map (fn (M,A) => (make M,A)) MAss 
        end
        
      and minimizeWithSnapshots M flag = 
        let       
          val History = makeHistory ()
          fun snapshot Ls = 
            if flag then 
                History := ((mkSnapshot (start M,final M) (!Ls)) :: (!History))
            else ()

          val (delta,Final) = (trans M, final M)

          val (Q:state list) = 
            let 
              val m = states M 
              fun states 0 = [] | states n = (n-1) :: (states (n-1))
            in rev (states m) end

          val S (* alphabet Sigma :''a list *) = 
            let 
              fun labels [] acc = acc
                | labels ((p,a,q)::Is) acc = 
                if member a acc then labels Is acc 
                else labels Is (a::acc)
            in rev(labels delta []) end

          val K      = makeK ()        (* (ref Nil : 'a agenda)  with variable 'a as label, *)
          val Delta' = makeDelta' ()   (* (Nil : 'a split)      would give typing problems: *)
          val Ls     = makeLs ()       (* (Nil : 'a line)      - " - unresolved weak tyvars *)

          val Delta  = makeDelta Q S   (* makeLookup Q S (Nil: (state * ('a line ref)) dl) *)
              handle Undefined => raise nonDeterministic
          val DeltaInv = makeLookup S Q ([]:state list)  
          val Gamma  = makeGamma Q S   (* makeLookup S Q (Nil:'a line) *)
          val Gamma' = makeGamma' Q S  (* makeLookup Q S (Nil:'a line) *)

          fun pushToPtrD (N:'a line, ptrD: 'a split ref, K: 'a agenda) =
            let 
              val LD(_,ptK,n,dl) = element(!ptrD)
              val LL(_,pt,_,_) = element(N)
            in 
              dl := push((ref N,ptrD),!dl) ; 
              n := (!n)+1 ; 
              if !n = 2 then 
                  (debugMsg "\nadding a ptrD to K which needs splitting";
                   K := push(ptrD,!K) ; 
                   ptK := !K)   
              else () ;               (* put ptrD to K and point back from K *)
                pt := !dl           (* point back from N to the new el of dl *)
            end  

          fun pushToLineL(q:state, LL(key as (_:state ref,b:'a,_),ptr,n,dl), Delta) = 
            let
              val pt = ref(!(#1(element(!ptr)))) (* assumes: !ptr points back to LL *)
            in 
              dl := push((q,pt),!dl);  
              n := (!n)+1;
              Delta(q,b) := !dl
            end

          fun removeFromLD (ptEl:(''a line ref * (state * ''a,''a line ref) LineD dref) dref, 
                            K: ''a agenda) (* (ptEl, K) *) =
            let 
              val LD(_,ptK,n,ptSet) = HeadElemD(ptEl)
            in 
              remove(ptEl,ptSet);
              n := (!n)-1;
              if !n = 1 then remove(ptK,K) else ()
            end

          fun removeState(ptEl: (state * ''a line ref) dref, L : ''a line ref, K: ''a agenda) =
            let
              val ptHeadNode = ptHeadNodeL(ptEl)
              val LL(_,ptD,n,ptSet) = HeadElemL(ptEl)
            in
              remove(ptEl,ptSet);   (* falls !ptEl = Delta(q,b), sollte temporaer *)
              n := (!n)-1;          (* Delta(q,b):= Nil werden; danach pushToLineL *)
              if !n = 0 then 
                (removeFromLD (ptD,K); remove(ptHeadNode,L))
              else ()
            end

          fun initializeD (q,a,r) = 
            let 

              (* Takes O(|Q|*|Sigma|*|Final|) steps! To get O(|Q|*|Sigma|), 
               we would need transitions ((q,Final? q),a,(r,Final? r)) *)

              val i = if member q Final then 0 else 1  (* Q0:= final M, Q1 := Q-Q0 *)
              and j = if member r Final then 0 else 1   

              (* 1. Add q to L(ref i,a,j), a set since delta is deterministic.

                 Let nodeD' = Delta'(i,a) resp. a new empty line of Delta'. 
                 Takes O(|S|*|Q|) steps. 
               *)

              val nodeD' as Node(_,LD(_,_,_,dlist'),_) = 
                let 
                  fun find (N as Node(_,(D as LD(key',_,_,_)),R)) key =
                    if key = key' then N else find (!R) key 
                    | find Nil key =
                      let 
                        val newD = LD((i,a),ref Nil,ref 0,ref Nil)
                      in 
                        Delta' := push (newD,!Delta');  !Delta'
                      end
                in 
                  find (!Delta') (i,a)
                end

              (* Let N be line LL((ref i,a,j),ptr,n,dl) of L, resp. a new empty one.
                 Extend Delta'(i,a) by a ref to N (with ref back): *)

              val (nodeL,L) = 
                let 
                  fun find (N as Node(_,(l as LL((ref li,lb,lj),_,_,_)),R)) 
                    (k as (ref ki,kb,kj)) = 
                    if (li,lb,lj) = (ki,kb,kj) 
                      then (pushToLineL (q,l,Delta); (N,l)) 
                    else find (!R) k
                    | find Nil (* :''a line *) _ = 
                      let 
                        val newL = LL((ref i,a,j), ref Nil, ref 0, ref Nil)
                      in 
                        Ls := push(newL,!Ls) ;    
                        pushToPtrD (!Ls, ref nodeD', K) ;
                        pushToLineL (q,newL,Delta) ;
                        (!Ls,newL)
                      end
                in 
                  find (!Ls) (ref i,a,j)
                end

              (* 4. Delta'(i,a) can have at most 2 refs, pointing to LL(i,a,0) and 
               LL(i,a,1). Extend Delta'(i,a) by a (back-) ref to nodeL; adjust K,
               if this makes |Delta'(i,a)| = 2. *)

              val LLs = mapDl (element o ! o #1) (!dlist') (* = { L'| dlist' refs to L'} *)
            in
              DeltaInv(a,r) :=  q :: (!(DeltaInv(a,r))) ;

              if member L LLs then () 
              else pushToPtrD (nodeL, ref nodeD', K)
            end

          val newstate = ref 2 (* state 0 = Final, state 1 = Q-Final *)

          fun nextD () =    

            (* For t+1 = !newstate, there are i in [0,..,t], a in S, and j1,j2 leq t 
             such that Qj1 and Qj2 intersect delta(Qi,a), i.e. !K is nonempty *)
            let 
              val D' as LD((i,a),ptkD',sizeD',dlD') = (element o ! o element)(!K)      

              (* let Q.t+1 = Qnew be the smaller of the two subsets
                  Lj = {q in Qi| delta(Qi,a) in Qj},  j=j1,j2,  of Qi *)

              fun Element' (Nd : (('st,'lab,'elem) LineL dref * 'b) dl) 
                = element (! (#1 (element (Nd))))
              val Lj1 as LL(_,_,n1,_) = Element' (!dlD')
              val Lj2 as LL(_,_,n2,_) = Element' (next(!dlD'))
              val Qnew as LL((iref,a,jm),ptrm,nm,dlm) = 
                if (!n1) <= (!n2) then Lj1 else Lj2

              val Nm = HeadNodeL(dlm)  (* node containing LL(ref i,a,jm) *)
              val Dnew = LD((!newstate,a),ref Nil,ref 0,ref Nil)

              val QnewSet = mapDl (fn x => x) (!dlm) 
                  (* to make appToMovedStates independent of changes by reTarget *)
              fun appToMovedStates h = app (fn b => app (fn N => h (b,#1 N)) QnewSet) S 

            in	
              debugMsg ("\nnextD for t+1 = " ^ Int.toString (!newstate) ^ "\n");

              (* 1. To subtract Ljm from Qi, delete the reference to Ljm from 
               Delta'(i,a) and evtl. remove the pointer to Delta'(i,a) from K *)

              removeFromLD (ptrm,K); 

              (* 2. Let Q(t+1) := LL(ref(!newstate),a,jm), old LL(ref i,a,jm) sub Qi *)

              Delta' := push(Dnew, !Delta'); 
              pushToPtrD (Nm,ref(!Delta'),K); (* ref(!.) for backrefs in Dnew ! *)
              iref := (!newstate) ;           (* keeping the backpointers *)

              (* To change Qi to Qi-Qnew, Delta'(i,.) and the L(i,.,.) it refers to 
               have to be changed; then all the L(k,.,i) referred to by Qk's have 
               to be changed. For each q in Qnew, adjust the data structure: *)

              let 
                (* 1. Since q of Qnew is to be removed from Qi, for each b in S-a, 
                 remove q from the L(i,b,k) containing it and put q to L(t+1,b,k). 
                 Put Delta(q,b):= new node (q,_) of L(t+1,b,k) and define Gamma(b,k) 

                 To mark Qnew for splitting if q in L(i,b,k) and q in L(i,b,k2) for k=/=k2,
                 add a new line LD((Qnew,b),ptrNil,ptr0,ptrNil) to Delta' if there 
                 there is none, and link it to K when needed !
                 *)

                fun reSource (q,b) = 
                  if b = a orelse !(Delta(q,b)) = Nil then () 
                  else 
                    let 
                      val LL((_,_,k),_,_,_) = HeadElemL(Delta(q,b))

                      fun updateSources () =
                        let 
                          val (Lnew as LL(_,ptrNew,_,dlNew)) =
                            LL((ref(!newstate),b,k),ref Nil,ref 0, ref Nil)

                          (* to add a new line for (Qnew,b) to Delta' if necessary: *)

                          val nodeD' = (* as Node(_,LD(_,_,_,dlist'),_) = *)
                              let 
                                  fun find (N as Node(_,(D as LD(key',_,_,_)),R)) key =
                                      if key = key' then N else find (!R) key 
                                    | find Nil key =
                                      let 
                                          val newD = LD(key,ref Nil,ref 0,ref Nil)
                                      in 
                                          Delta' := push (newD,!Delta');  !Delta'
                                      end
                              in 
                                  find (!Delta') (!newstate,b)
                              end
                        in 
                          (debugMsg ("\nfor target k = " ^ Int.toString k ^
                                  ", change sources q in state " ^ Int.toString i 
                                  ^ " to sources newstate " ^ (Int.toString (!newstate)) ^ "\n");
                           Ls  := push (Lnew,!Ls);
                           pushToPtrD(!Ls,ref nodeD',K); (* defines ptrNew! *)
                           pushToLineL (q,Lnew,Delta); 
                           Gamma(b,k) := !Ls
                           )
                        end                                 
                    in 
                      debugMsg ("\nreSource for q = " ^ Int.toString q);

                      removeState(Delta(q,b),Ls,K); 

                      if !(Gamma(b,k)) = Nil then updateSources ()
                      else
                        let val (Last as LL((ref j,_,_),_,_,_)) 
                          = element(!(Gamma(b,k)))
                        in 
                          if j = !newstate then pushToLineL(q,Last,Delta)
                          else updateSources () 
                        end
                    end

              in (* Forall b in S, q in Q(t+1): turn each q--b->p to (t+1)--b->p) *)
                  appToMovedStates (fn (b,q) => reSource (q,b))
              end ;
          
              (*  2. forall b in S and q in Q(t+1), turn each p--b->q to p--b->(t+1):
                  remove each p in DeltaInv(b,q) from the list Li(k,b,i) containing it;
                  insert p into Li(k,b,t+1). Define Gamma'(k,b). *)

              let
                fun reTarget (p,b) = 
                  let 
                    val ptEl = Delta(p,b) (* used only when p in DeltaInv(b,q)! *)
                    val LL((ref k,b,i),ptDkb,_,_) = HeadElemL(ptEl)
                    val ptrDnode = ptHeadNodeD(ptDkb)

                    fun updateTarget () =
                      let 
                        val Lnew = 
                          LL((ref k,b,!newstate),ref Nil,ref 0,ref Nil)
                      in
                        debugMsg ("\nfor source p in state k = " ^ Int.toString k ^ 
                               ", change targets removed from state " ^ Int.toString i 
                               ^ " to target newstate " 
                               ^ Int.toString (!newstate) ^ "\n");
                        Ls := push(Lnew,!Ls) ;
                        pushToPtrD (!Ls, ptrDnode, K) ;
                        pushToLineL (p,Lnew,Delta) ;
                        Gamma'(k,b) := !Ls 
                      end
                  in 
                    debugMsg ("\nreTarget for source p = " ^ Int.toString p);

                    removeState(ptEl,Ls,K); (* may change moved states = L(t+1,b,i) ! *)

                    if !(Gamma'(k,b)) = Nil then updateTarget () 
                    else
                      let 
                        val Last as LL((_,_,j),_,_,_) = element(!(Gamma'(k,b)))
                      in 
                        if j = !newstate then pushToLineL(p,Last,Delta)
                        else updateTarget () 
                      end
                  end
              in  
                (* Forall b in S, q in Q(t+1) and p --b--> q: reTarget(p,b) *)
                (appToMovedStates (fn (b,q) => 
                           (app (fn p => reTarget (p,b)) (!(DeltaInv(b,q))))))
                (* DeltaInv(b,q) may be undefined for partial machines *)
              end ;

            newstate := !newstate + 1

            end
          handle Undefined => print "\n ** input machine must be deterministic ! **\n"

        in 
          app initializeD delta ; 
          debugMsg "\nInitializing of state 0 and 1 is finished.\n";
          snapshot Ls ;
          while not(!K = Nil) do (nextD() ; snapshot Ls) ;
          (Ls,rev (!History))
        end

        (* newFinalStates and newInitialState can be read off from Ls as done here
           only if delta was a *total* function! *)

      fun extract M Nil (accTrans,newStart,accFinal) = (accTrans,newStart,accFinal) 
        | extract M (Node(_,(LL((ref i,a,j),_,_,ptSet)),R)) (accI,newS,accF) =
        let 
          val Start = start M 
          and Final = final M

          fun strt [] = 
            (case Start of 
               [] => []
             | [q] => if found (!ptSet) q then [i] else []
             | _ => (print "\n ** input machine has several initial states! **" ;
                     raise nonDeterministic))
            | strt (i :: rest) = (i :: rest)
          and found Nil q = false
            | found (Node(_,(p,_),R)) q = 
            if p = q then true else found (!R) q
              
          fun isFinal Nil = false
            | isFinal (Node(_,(p,_),R)) =
            if member p Final then true else isFinal (!R)
              
        in
          extract M (!R) ((i,a,j) :: accI, 
                          strt(newS), 
                          if isFinal (!ptSet) then add i accF else accF)
        end
      
      and minimizeWithStateAssoc M = (* Minimize M to M' with Q' subset 2^Q *)
        let 
          val Ls = !(minimizeWithEquivalentStates M)
          val (newTrans,newStart,newFinal) = extract M Ls ([],[],[])
          val stateAssoc = 
            let 
              fun assoc (LL((ref p,a,q),ptr,n,dl)) = (p, mapDl #1 (!dl)) 
              fun removeDuplicates [] acc = acc
                | removeDuplicates ((p,P)::qs) acc = 
                  removeDuplicates qs (add (p,P) acc)
              and add (p,P) [] = [(p,P)]
                | add (p,P) ((q,Q)::qs) = if p=q then ((q,Q)::qs) else (q,Q)::(add (p,P) qs)
            in 
              removeDuplicates (mapDl assoc Ls) []
            end
        in
          (make {trans = newTrans, start = newStart, final = newFinal}, stateAssoc)
        end
      and minimize M = (#1 (minimizeWithStateAssoc M))


    end
  end;


(* Compiler.Control.Print.printDepth := 10;             

Example 0 (Star of a finite automaton)

val M = Fm.make{trans=[(0,"a",1),(1,"b",2),(0,"c",2)],start=[0],final=[2]}
Fm.show (Fm.Star M)
val it =
  {final=[0,3],start=[0,1],
   trans=[(1,"a",2),(2,"b",3),(1,"c",3),(1,"c",1),(2,"b",1)]}
Fm.accept (Fm.Star M) ["a","b","a","b"]
Fm.reach (Fm.Star M) [1] ["a","b","a"]
Fm.determineWithStateAssoc (Fm.Star M)

Example 1: (Non-deterministic machines are not minimized)

val M = Fm.make{start = [0],final = [1], trans = [(0,"a",0),(0,"a",1),(1,"a",1)]};
Fm.minimize M;
 ** input machine must be deterministic ! **
val it = - : string Fm.machine
val it = () : unit

val M = Fm.make{start = [1,3],final = [3], 
                trans = [(1,0,2),(2,0,6),(2,1,3),(3,0,1),(3,1,3)]};
Fm.display M "M";
Fm.minimize M;
uncaught exception nonDeterministic  (* two initial states *)
  raised at: fm.sml:804.27-804.43

Example 2: (Unreachable states are not removed in minimization)

val M = Fm.make{start = [0], final = [0], trans = [(0,0,0),(0,1,0),(1,0,0)]};
Fm.show(Fm.minimize M);
val it = {final=[0],start=[0],trans=[(0,0,0),(0,1,0),(1,0,0)]}

Example 3: Unreachable states are removed in making a machine (partial) deterministic

val M = Fm.make{start = [0], final = [0], trans = [(0,0,0),(0,1,0),(1,0,0)]};
Fm.show(Fm.determine M);
val it = {final=[0],start=[0],trans=[(0,1,0),(0,0,0)]}

Example 4: Partial deterministic machines in minimization: (should always be rejected!!)

val M = Fm.make{start = [0],final = [1], trans = [(0,"a",0),(0,"b",1),(1,"b",1)]};
Fm.minimize M;
Fm.show (Fm.minimize M);


Example 5: Corrected mistake in Minimization: 

val M = Fm.make{final=[1],start=[0],
                trans=[(0,1,1),(0,0,2),(1,1,1),(1,0,3),(2,1,1),
                       (2,0,4),(3,1,3),(3,0,4),(4,1,1),(4,0,4)]};
Fm.show (Fm.minimize M);
val it =
  {final=[0],start=[1],trans=[(1,1,0),(1,0,1),(0,1,0),(2,0,1),(2,1,2),(0,0,2)]}

Previous version had a wrong arc (0,0,1) instead of (0,0,2).

*)




