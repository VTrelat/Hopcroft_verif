\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Heapsort\<close>
theory Sorting_Heapsort
imports Sorting_Setup "../../nrest/NREST_Automation"
  "../../lib/More_Asymptotics"
begin                                       

paragraph \<open>Summary\<close>
text \<open>This theory verifies functional correctness and running time of an implementation of heapsort.\<close>


paragraph \<open>Main Theorems/Definitions\<close>
text \<open>
\<^item> sift_down: abstract algorithm for sift down
\<^item> sift_down_btu_correct/sift_down_restore_correct: sift down is used for two purposes in heap sort.
    There are two correctness theorems for that algorithm.
\<^item> heapify_btu: algorithm to build up a heap from n elements
\<^item> heapsort: the abstract algorithm for heapsort using an initial heapify_btu and repeatedly
    calls sift_down.
\<^item> heapsort_correct: correctness theorem for high level heapsort algorithm 
\<^item> heapsort_impl: the synthesized LLVM program for heapsort
\<^item> heapsort_final_hoare_triple:  the final Hoare triple showing correctness and running time of heapsort
\<^item> heapsort3_allcost_simplified: the projected costs, for inspecting the constants
\<^item> heapsort3_allcost_nlogn: heapsorts running time bound is in O(n log n)
\<close>


paragraph \<open>TODOs\<close>
text \<open>
\<^item> heapify_btu actually is O(n). we only prove O(n * log n), as that suffices to prove that
   heapsort is in O(n*log n)
\<close>

subsection "Preparations"
subsubsection "stuff to move"



method_setup all_par =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i)

   in SIMPLE_METHOD (PARALLEL_ALLGOALS tac) facts end)
\<close>
(* TODO: Move *)


(*declare less_eq_option_Some_None[simp]*)
lemma ifSome_iff: "(if b then Some T else None) = Some T' \<longleftrightarrow> T=T' \<and> b"
  by (auto split: if_splits)


lemma ifSome_None: "(if P then Some x else None) = Some y \<longleftrightarrow> P \<and> x=y"
  by (auto split: if_splits)

lemma prod3: "m\<le> f x y z \<Longrightarrow> m \<le> (case (x,y,z) of (a,b,c) \<Rightarrow> f a b c)"
  by auto



subsubsection "Heap range context"

locale heap_range_context = 
  fixes l h :: nat
  assumes ran_not_empty[arith,simp]: "l\<le>h"
begin  

  (*lemma l_le_h[arith,simp]: "l\<le>h" by simp*)

  definition "in_heap i \<equiv> i\<in>{l..<h}"

  definition parent where "parent i \<equiv> (i-1-l) div 2 + l"
  definition lchild where "lchild i \<equiv> 2*(i-l) + 1 + l"
  definition rchild where "rchild i \<equiv> 2*(i-l) + 2+ l"  
  
  definition has_parent where "has_parent i \<equiv> in_heap i \<and> i>l"
  definition has_lchild where "has_lchild i \<equiv> in_heap i \<and> in_heap (lchild i)"
  definition has_rchild where "has_rchild i \<equiv> in_heap i \<and> in_heap (rchild i)"
  
  context begin
    private method prove = (
      unfold in_heap_def parent_def has_parent_def lchild_def rchild_def has_lchild_def has_rchild_def, 
      auto)

    text \<open>Optimized checks, normalize to i-l, for index shift\<close>
    lemma has_rchild_ihs: "in_heap i \<Longrightarrow> has_rchild i \<longleftrightarrow> i-l<(h-l-1) div 2"
      by prove

    lemma has_lchild_ihs: "in_heap i \<Longrightarrow> has_lchild i \<longleftrightarrow> (i-l) < (h-l) div 2"  
      by prove
      
    lemma has_parent_ihs: "in_heap i \<Longrightarrow> has_parent i \<longleftrightarrow> i-l > 0"
      by prove
      
    lemma lchild_ihs: "lchild i - l = 2*(i-l)+1"  
      by prove
      
    lemma rchild_ihs: "rchild i - l = 2*(i-l)+2"  
      by prove
      
    lemma parent_ihs: "parent i - l = (i-l-1) div 2"
      by prove
      
    lemma in_heapI: "\<lbrakk> l\<le>i; i<h \<rbrakk> \<Longrightarrow> in_heap i" by prove
      
    lemma in_heap_bounds[simp]: 
      assumes "in_heap i" 
      shows "l\<le>i" and "i<h"
      using assms by prove

    lemma in_heap_triv[simp]: 
      "has_parent i \<Longrightarrow> in_heap i"
      "has_lchild i \<Longrightarrow> in_heap i"
      "has_rchild i \<Longrightarrow> in_heap i"        
      by prove
            
    lemma parent_in_heap[simp]: 
      "has_parent i \<Longrightarrow> in_heap (parent i)"
      "has_parent i \<Longrightarrow> has_lchild (parent i)" 
      by prove
    
    lemma children_in_heap[simp]: 
      "has_lchild i \<Longrightarrow> in_heap (lchild i)"
      "has_rchild i \<Longrightarrow> in_heap (rchild i)"
      by prove

    lemmas in_heap_simps = in_heap_triv parent_in_heap children_in_heap
            

    lemma parent_of_child[simp]:
      "has_lchild i \<Longrightarrow> parent (lchild i) = i"
      "has_rchild i \<Longrightarrow> parent (rchild i) = i"
      by prove

    lemma children_differ[simp]:
      "lchild i \<noteq> rchild i" 
      "rchild i \<noteq> lchild i" 
      by prove

    lemma parent_less[simp]: "has_parent i \<Longrightarrow> parent i < i" by prove

    lemma children_greater[simp]: 
      "lchild i > i" 
      "rchild i > i"
      by prove

      
    lemma children_diff_add_simps[iff]:
      "lchild i \<noteq> i"  
      "i \<noteq> lchild i"  
      "rchild i \<noteq> i"  
      "i \<noteq> rchild i"  
      by prove
      
    lemma parent_diff_add_simps[simp]: 
      assumes "has_parent i" shows "i \<noteq> parent i" and "parent i \<noteq> i"
      using assms by prove
      
    lemma rchild_imp_lchild[simp, intro]: "has_rchild i \<Longrightarrow> has_lchild i" by prove

    lemma no_parent_is_root: "in_heap i \<Longrightarrow> \<not>has_parent i \<longleftrightarrow> i=l" by prove
    
    lemma root_no_parent[iff]: "\<not>has_parent l" by prove
    
    
    lemma root_in_heap: "in_heap l\<longleftrightarrow>l<h" using ran_not_empty by prove
    
                      
    lemma child_of_parent: "has_parent i \<Longrightarrow> lchild (parent i) = i \<or>
                     has_rchild (parent i) \<and> rchild (parent i) = i" by prove
                
    lemma children_of_parent_cases[consumes 1]:
      assumes "has_parent i"
      obtains (left) "has_parent i" "lchild (parent i) = i" 
            | (right) "has_parent i" "has_rchild (parent i)" "rchild (parent i) = i"
      using assms child_of_parent by blast            

    lemma lchild_of_no_rchild_term: "\<lbrakk>\<not>has_rchild i; has_lchild i\<rbrakk> \<Longrightarrow> \<not>has_lchild (lchild i)" by prove 
      
      
          
  end

  lemmas heap_context_defs[no_atp] = in_heap_def parent_def lchild_def rchild_def has_parent_def has_lchild_def has_rchild_def
end  
  
locale heap_context = weak_ordering + heap_range_context begin
  
  definition is_heap :: "'a list \<Rightarrow> bool" 
    where "is_heap xs \<equiv> (h\<le>length xs) \<and> (\<forall>i. has_parent i \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)"

    
  subsubsection \<open>Heap Property implies Minimal Element at Top\<close>
  context
    fixes xs
    assumes H: "is_heap xs"
  begin  

    lemma parent_el_greater[simp]: "has_parent i \<Longrightarrow> xs!i \<^bold>\<le> xs!parent i"
      using H
      unfolding is_heap_def 
      by simp
    
    lemma root_greatest:
      assumes "in_heap i"
      shows "xs!i \<^bold>\<le> xs!l"
      using assms 
    proof (induction i rule: less_induct)
      case (less i)
      note [simp] = \<open>in_heap i\<close>
      
      show ?case proof cases
        assume [simp]: "has_parent i"
        have "xs!i \<^bold>\<le> xs!parent i" by simp
        also from less.IH[of "parent i"] have "xs!parent i \<^bold>\<le> xs!l" by simp
        finally show ?case .
      next
        assume "\<not>has_parent i" 
        hence "i=l" by (simp add: no_parent_is_root)
        thus ?case by simp
      qed  
    qed
  
  end  

    
  subsubsection \<open>Sift-Up Lemmas\<close>    
  definition is_heap_except_up :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" 
    where "is_heap_except_up j xs \<equiv> 
      (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> i\<noteq>j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (has_parent j \<and> has_lchild j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!lchild j)
      \<and> (has_parent j \<and> has_rchild j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!rchild j)"

  lemma is_heap_except_up_len_bound[simp, intro]:
    assumes "is_heap_except_up i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_up_def
    by auto
        
  lemma sift_up_lemma:
    assumes HP: "has_parent i"
    assumes IHE: "is_heap_except_up i xs"
    assumes GE: "xs!i \<^bold>\<ge> xs!parent i"
    shows "is_heap_except_up (parent i) (swap xs i (parent i))"
  proof -
    from assms(2) have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_up_def by auto
  
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp

    have HPROP: "xs!j \<^bold>\<le> xs!parent j" if "has_parent j" "j\<noteq>i" for j
      using that IHE unfolding is_heap_except_up_def by simp
      
      
    show ?thesis using HP
      unfolding is_heap_except_up_def
      apply (clarsimp; safe)
      subgoal
        apply (clarsimp simp: swap_nth HPROP GE; safe)
        subgoal by (metis GE HPROP trans)
        by (metis IHE child_of_parent is_heap_except_up_def parent_in_heap(2))

      subgoal
        by (smt HPROP X children_greater(1) has_lchild_def in_heap_bounds(1) parent_of_child(1)
                trans nat_less_le no_parent_is_root parent_in_heap(2) parent_less less_le_trans   
                swap_indep swap_nth)
      subgoal 
        by (smt HPROP X children_greater(2) has_parent_def has_rchild_def parent_less 
                parent_of_child(2) less_le trans less_trans swap_nth)
        
      done
      
  qed

  text \<open>Terminate when reached root\<close>
  lemma sift_up_term1: "is_heap_except_up l xs \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  text \<open>Terminate when parent is greater or equal\<close>  
  lemma sift_up_term2: "\<lbrakk>is_heap_except_up i xs; xs!i\<^bold>\<le>xs!parent i\<rbrakk> \<Longrightarrow> is_heap xs"
    unfolding is_heap_def is_heap_except_up_def by auto
  
  lemma grow_heap_context: "heap_range_context l (Suc h)" 
    apply unfold_locales using ran_not_empty by linarith 
    
  text \<open>Initializes a sift-up cycle by extending the heap by one element to the right\<close>  
  lemma sift_up_init:
    assumes "is_heap xs"
    assumes "h<length xs"
    shows "heap_context.is_heap_except_up (\<^bold>\<le>) l (Suc h) h xs"
  proof -
    interpret N: heap_range_context l "Suc h" using grow_heap_context .
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "Suc h" by unfold_locales
  
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_up_def N.is_heap_except_up_def
      unfolding N.heap_context_defs heap_context_defs
      by auto
      
  qed
  
  subsubsection \<open>Sift-Down Lemmas\<close>    

  definition is_heap_except_down :: "nat \<Rightarrow> 'a list \<Rightarrow> bool"
    where "is_heap_except_down j xs \<equiv>
        (h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent i = j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!i)"

  lemma is_heap_except_down_len_bound[simp, intro]: 
    assumes "is_heap_except_down i xs"
    shows "h\<le>length xs"     
    using assms unfolding is_heap_except_down_def
    by auto
          
  lemma sift_down_lemma_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<ge> xs!rchild i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(1) children_in_heap(1) dual_order.trans 
            has_parent_def parent_diff_add_simps(1) in_heap_bounds(2) leD order_less_le
            parent_of_child(1) rchild_imp_lchild swap_indep swap_nth1 swap_nth2)
      
  qed

  lemma sift_down_lemma_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!rchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<le> xs!rchild i"
    shows "is_heap_except_down (rchild i) (swap xs i (rchild i))"
  proof -  
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply (clarsimp)
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.trans eq_iff 
              heap_range_context.has_parent_def heap_range_context_axioms in_heap_bounds(2)
              less_le parent_less parent_of_child(2) swap_nth)
      
  qed
  
    
  lemma sift_down_lemma_left_no_right_child:
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i"
    shows "is_heap_except_down (lchild i) (swap xs i (lchild i))"
  proof -  
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
      
    show ?thesis 
      using IHE HRC GE
      unfolding is_heap_except_down_def
      apply clarsimp
      by (smt X child_of_parent children_greater(1) children_in_heap(1)
              heap_range_context.has_parent_def heap_range_context.parent_of_child(1)
              heap_range_context_axioms le_less_trans less_imp_le_nat parent_in_heap(1) swap_nth)
      
  qed

  
  lemma sift_down_term1: "\<not>has_lchild j \<Longrightarrow> is_heap_except_down j xs \<longleftrightarrow> is_heap xs"
    unfolding is_heap_except_down_def is_heap_def
    by auto
  
  lemma sift_down_term2: 
    assumes "is_heap_except_down j xs" "has_rchild j" "xs!j\<^bold>\<ge>xs!lchild j" "xs!j\<^bold>\<ge>xs!rchild j"
    shows "is_heap xs"
    using assms
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
  
  lemma sift_down_term3:
    assumes "is_heap_except_down j xs" "has_lchild j" "\<not>has_rchild j" "xs!j\<^bold>\<ge>xs!lchild j"
    shows "is_heap xs"
    using assms
    unfolding is_heap_except_down_def is_heap_def
    apply (clarsimp)
    by (metis children_of_parent_cases)
     
  lemma shrink_heap_context: "Suc l<h \<Longrightarrow> heap_range_context l (h-Suc 0)" 
    apply unfold_locales using ran_not_empty by linarith 
  
  text \<open>Initializes a sift-down cycle by swapping the first and last element, 
        and then shrinking the heap by one element\<close>
  lemma sift_down_init:  
    assumes "is_heap xs"
    assumes LT: "Suc l < h"
    shows "heap_context.is_heap_except_down (\<^bold>\<le>) l (h-Suc 0) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0"
      apply intro_locales
      using shrink_heap_context[OF LT] .
    
    show ?thesis
      using assms
      unfolding is_heap_def is_heap_except_down_def N.is_heap_except_down_def
      unfolding N.heap_context_defs heap_context_defs
      by (auto simp: swap_nth)
      
  qed    
        
    
  subsubsection \<open>Bottom-up Heapify\<close>

  text \<open>The nodes from index \<open>l'\<close> upwards satisfy the heap criterion\<close>
  definition is_heap_btu :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" where "is_heap_btu l' xs \<equiv> 
        (l'\<le>h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)"

  text \<open>Bottom-up heapify starts with only the last element being a heap\<close>
  lemma btu_heapify_init: "h\<le>length xs \<Longrightarrow> is_heap_btu (h-Suc 0) xs"  
    unfolding is_heap_btu_def
    apply auto
    by (meson dual_order.trans in_heap_bounds(2) in_heap_triv(1) nat_le_Suc_less_imp not_le
              parent_less)
        
  text \<open>When we have reached the lower index, we have a complete heap\<close>    
  lemma btu_heapify_term: "is_heap_btu l xs \<longleftrightarrow> is_heap xs"
    unfolding is_heap_btu_def is_heap_def
    by (auto simp: less_imp_le_nat)
      
      
  text \<open>All nodes in between l' and h form a valid heap, with downwards-hole at j\<close>
  definition is_heap_except_down_btu :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
    where "is_heap_except_down_btu l' j xs \<equiv>
        (l'\<le>j \<and> j<h \<and> h\<le>length xs) 
      \<and> (\<forall>i. has_parent i \<and> parent i \<ge> l' \<and> parent i \<noteq> j \<longrightarrow> xs!parent i \<^bold>\<ge> xs!i)
      \<and> (\<forall>i. has_parent i \<and> has_parent j \<and> parent j \<ge>l' \<and> parent i = j \<longrightarrow> xs!parent j \<^bold>\<ge> xs!i)"

  lemma is_heap_except_down_btu_lenD: "is_heap_except_down_btu l' j xs \<Longrightarrow> h\<le>length xs"    
    unfolding is_heap_except_down_btu_def by auto
      
  text \<open>A sift-down round starts by including one more left element, and marking it as a hole\<close>
  lemma btu_sift_down_init: "\<lbrakk>is_heap_btu l' xs; l'>l\<rbrakk> \<Longrightarrow> is_heap_except_down_btu (l'-1) (l'-1) xs"  
    unfolding is_heap_except_down_btu_def is_heap_btu_def 
    apply auto
    using leD parent_less by blast
  
      
  text \<open>Sift-down completed, we have a complete heap from \<open>l'\<close> upwards\<close>
  lemma btu_sift_down_term1: "\<not>has_lchild j \<Longrightarrow> is_heap_except_down_btu l' j xs \<Longrightarrow> is_heap_btu l' xs"
    unfolding is_heap_except_down_btu_def is_heap_btu_def 
    by auto
      
  lemma btu_sift_down_term2: 
    assumes "is_heap_except_down_btu l' j xs" "has_rchild j" "xs!j\<^bold>\<ge>xs!lchild j" "xs!j\<^bold>\<ge>xs!rchild j"
    shows "is_heap_btu l' xs"
    using assms
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (smt dual_order.trans child_of_parent in_heap_bounds(2) in_heap_triv(3) le_cases not_le)
  
  lemma btu_sift_down_term3:
    assumes "is_heap_except_down_btu l' j xs" "has_lchild j" "\<not>has_rchild j" "xs!j\<^bold>\<ge>xs!lchild j"
    shows "is_heap_btu l' xs"
    using assms
    unfolding is_heap_except_down_btu_def is_heap_btu_def
    apply (clarsimp)
    by (metis child_of_parent dual_order.trans in_heap_bounds(2) in_heap_triv(2) less_imp_le)
  

  

  lemma btu_heapify_down_left:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<ge> xs!rchild i"
    shows "is_heap_except_down_btu l' (lchild i) (swap xs i (lchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(1) children_in_heap(1) 
              heap_range_context.has_parent_def heap_range_context_axioms leD le_cases 
              less_le_trans parent_of_child(1) rchild_imp_lchild)
      
  qed  
        
  lemma btu_heapify_down_right:
    assumes HRC: "has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!rchild i \<^bold>\<ge> xs!i" "xs!lchild i \<^bold>\<le> xs!rchild i"
    shows "is_heap_except_down_btu l' (rchild i) (swap xs i (rchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(2) children_in_heap(2) dual_order.strict_trans2 
              heap_range_context.has_parent_def heap_range_context_axioms less_imp_le_nat
              parent_of_child(2))
      
  qed  
    
  lemma btu_heapify_down_left_no_right_child:
    assumes HRC: "has_lchild i" "\<not>has_rchild i"
    assumes IHE: "is_heap_except_down_btu l' i xs"
    assumes GE: "xs!lchild i \<^bold>\<ge> xs!i"
    shows "is_heap_except_down_btu l' (lchild i) (swap xs i (lchild i))"
  proof -
    from IHE have [simp, arith]: "h\<le>length xs" unfolding is_heap_except_down_btu_def by auto
    
    have X[simp]: "i<length xs" if "in_heap i" for i
      using in_heap_bounds(2)[OF that] by simp
    
    show ?thesis
      using HRC IHE GE
      unfolding is_heap_except_down_btu_def
      apply (clarsimp simp: swap_nth)
      by (smt child_of_parent children_greater(1) children_in_heap(1) 
              heap_range_context.has_parent_def heap_range_context_axioms leD le_cases 
              less_le_trans parent_of_child(1))
      
  qed  
    
  definition "sift_up_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_up i xs"  
    
  lemma sift_up_invar_init: 
    assumes "is_heap xs" "slice_eq_mset l h xs xs\<^sub>0" "h<length xs" 
    shows "heap_context.sift_up_invar (\<^bold>\<le>) l (Suc h) xs\<^sub>0 h xs"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "Suc h" by intro_locales (simp add: grow_heap_context)
    
    show ?thesis 
      using assms
      by (meson N.sift_up_invar_def le_eq_less_or_eq nat_in_between_eq(1) ran_not_empty
                sift_up_init slice_eq_mset_subslice)
      
  qed    
      
  lemma sift_up_invar_step: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; has_parent i; xs!i\<^bold>\<ge>xs!parent i \<rbrakk> 
    \<Longrightarrow> sift_up_invar xs\<^sub>0 (parent i) (swap xs i (parent i))"
    unfolding sift_up_invar_def
    by (auto simp: sift_up_lemma)
    
  lemma sift_up_invar_term1: "\<lbrakk>sift_up_invar xs\<^sub>0 l xs\<rbrakk> \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term1 by blast
    
  lemma sift_up_invar_term2: "\<lbrakk>sift_up_invar xs\<^sub>0 i xs; xs!i\<^bold>\<le>xs!parent i\<rbrakk> 
    \<Longrightarrow> is_heap xs \<and> slice_eq_mset l h xs xs\<^sub>0"
    unfolding sift_up_invar_def
    using sift_up_term2 by blast

  definition "sift_down_invar xs\<^sub>0 i xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down i xs"  

  lemma sift_down_invar_step:
    assumes "sift_down_invar xs\<^sub>0 i xs"
    shows "\<lbrakk>has_rchild i; xs!i\<^bold>\<le>xs!lchild i; xs!lchild i \<^bold>\<ge> xs!rchild i\<rbrakk>
               \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
      and "\<lbrakk>has_rchild i; xs!i\<^bold>\<le>xs!rchild i; xs!lchild i \<^bold>\<le> xs!rchild i\<rbrakk>
               \<Longrightarrow> sift_down_invar xs\<^sub>0 (rchild i) (swap xs i (rchild i))"
      and "\<lbrakk>has_lchild i; \<not>has_rchild i; xs!i\<^bold>\<le>xs!lchild i\<rbrakk>
               \<Longrightarrow> sift_down_invar xs\<^sub>0 (lchild i) (swap xs i (lchild i))" 
    using assms unfolding sift_down_invar_def
    by (auto simp: sift_down_lemma_left sift_down_lemma_right sift_down_lemma_left_no_right_child)

  thm sift_down_init (*xxx, ctd here: we need to initialize from heapsort loop invariant*)
  lemma sift_down_invar_init: 
    assumes "is_heap xs" "Suc l < h" 
    shows "heap_context.sift_down_invar (\<^bold>\<le>) l (h-Suc 0) (swap xs l (h-Suc 0)) l (swap xs l (h-Suc 0))"
  proof -
    interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0"
      apply intro_locales using assms shrink_heap_context by auto
    show ?thesis using sift_down_init assms unfolding N.sift_down_invar_def 
      by (auto simp: sift_down_init)
      
  qed  

  
  definition "heapify_btu_invar xs\<^sub>0 l' xs \<equiv>
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_btu l' xs"
  
  definition "sift_down_btu_invar xs\<^sub>0 l' i xs \<equiv> 
      slice_eq_mset l h xs xs\<^sub>0      
    \<and> is_heap_except_down_btu l' i xs"
    
    
          
end  

context weak_ordering begin

  sublocale singleton_heap_context: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "(Suc l)"
    by unfold_locales auto

  lemma singleton_no_relatives[simp, intro!]:
    "\<not>singleton_heap_context.has_parent l i"  
    "\<not>singleton_heap_context.has_lchild l i"  
    "\<not>singleton_heap_context.has_rchild l i"  
    unfolding singleton_heap_context.heap_context_defs 
    by auto
    
  lemma singleton_heap: "l<length xs \<Longrightarrow> singleton_heap_context.is_heap l xs"  
    unfolding singleton_heap_context.is_heap_def
    by auto

end  

    
context heap_context begin  

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_has_lchild  :: "nat \<Rightarrow> (bool, _) nrest"
    where [simp]: "mop_has_lchild i \<equiv> do { consume (RETURNT (has_lchild i)) (T (i)) }"
  sepref_register "mop_has_lchild"
end

lemma mop_has_lchild:
  "(mop_has_lchild T, mop_has_lchild T) \<in> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_has_lchild_def 
  by (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_has_rchild  :: "nat \<Rightarrow> (bool, _) nrest"
    where [simp]: "mop_has_rchild i \<equiv> do { consume (RETURNT (has_rchild i)) (T (i)) }"
  sepref_register "mop_has_rchild"
end

lemma mop_has_rchild:
  "(mop_has_rchild T, mop_has_rchild T) \<in> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_has_rchild_def 
  by (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_lchild  :: "nat \<Rightarrow> (nat, _) nrest"
    where [simp]: "mop_lchild i \<equiv> do { consume (RETURNT (lchild i)) (T (i)) }"
  sepref_register "mop_lchild"
end

lemma mop_lchild:
  "(mop_lchild T, mop_lchild T) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_lchild_def 
  by (auto simp: pw_acost_le_iff refine_pw_simps)

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_rchild  :: "nat \<Rightarrow> (nat, _) nrest"
    where [simp]: "mop_rchild i \<equiv> do { consume (RETURNT (rchild i)) (T (i)) }"
  sepref_register "mop_rchild"
end

lemma mop_rchild:
  "(mop_rchild T, mop_rchild T) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI) 
  by (auto simp: pw_acost_le_iff refine_pw_simps)
 



abbreviation "mop_has_lchildF \<equiv> mop_has_lchild (\<lambda>_. top)"
abbreviation "mop_has_rchildF \<equiv> mop_has_rchild (\<lambda>_. top)"
abbreviation "mop_lchildF \<equiv> mop_lchild (\<lambda>_. top)"
abbreviation "mop_rchildF \<equiv> mop_rchild (\<lambda>_. top)"

abbreviation "mop_has_lchildN \<equiv> mop_has_lchild (\<lambda>_. cost ''has_lchild'' 1)"
abbreviation "mop_has_rchildN \<equiv> mop_has_rchild (\<lambda>_. cost ''has_rchild'' 1)"
abbreviation "mop_lchildN \<equiv> mop_lchild (\<lambda>_. cost ''lchild'' 1)"
abbreviation "mop_rchildN \<equiv> mop_rchild (\<lambda>_. cost ''rchild'' 1)"

subsection \<open>Verification of sift_down (infinite cost)\<close>

  definition sift_down :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list,_) nrest" where "sift_down i\<^sub>0 xs \<equiv> doN {
    ASSERT (in_heap i\<^sub>0 \<and> i\<^sub>0<length xs);
    _ \<leftarrow> consumea top;
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). in_heap i \<and> i\<ge>i\<^sub>0) 
      (\<lambda>(xs,i,ctd). doN {
                          hrc \<leftarrow> mop_has_rchildF i;
                          SPECc2F  (\<and>)  hrc ctd
                        }) 
      (\<lambda>(xs,i,ctd). doN {
        lci \<leftarrow> mop_lchildF i;
        lc \<leftarrow> mop_list_getF xs lci;
        rci \<leftarrow> mop_rchildF i;
        rc \<leftarrow> mop_list_getF xs rci;
        v \<leftarrow> mop_list_getF xs i;
      
        if\<^sub>N  SPECc2F (\<^bold><)  lc rc then
          if\<^sub>N SPECc2F  (\<^bold><)  v rc then
            doN {
              xs \<leftarrow> mop_list_swapF xs i rci;
              RETURN (xs,rci,True)
            }
          else
           RETURN (xs,i,False)
        else if\<^sub>N  SPECc2F  (\<^bold><)  v lc then
          doN {
            xs \<leftarrow> mop_list_swapF xs i lci;
            RETURN (xs,lci,True)
          }
        else
          RETURN (xs,i,False)
       }) 
    (xs,i\<^sub>0,True);
  
    ASSERT (in_heap i \<and> i\<ge>i\<^sub>0);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    if\<^sub>N mop_has_lchildF i then
      doN {
        lci \<leftarrow> mop_lchildF i;
        if\<^sub>N mop_cmp_idxs top xs i lci then
          mop_list_swapF xs i lci
        else
          (doN { _ \<leftarrow> consumea top; RETURN xs })
      }
    else
      ( doN {_ \<leftarrow> consumea top; RETURN xs })      
  }"

  lemma in_heap_len_bound: "in_heap i \<Longrightarrow> h\<le>length xs \<Longrightarrow> i<length xs"
    using in_heap_bounds(2) less_le_trans by blast

 
subsubsection \<open>Bottom Up Correct\<close>

  lemma sift_down_btu_correct:
    assumes "heapify_btu_invar xs\<^sub>0 l' xs" "l<l'"
    shows "sift_down (l'-Suc 0) xs \<le> SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 (l'-Suc 0) xs') (\<lambda>_. top)" 
    unfolding sift_down_def
    unfolding SPEC_def
    apply(rule gwp_specifies_I)

    supply wr = monadic_WHILE_rule_real[OF refl, where 
      I="\<lambda>(xs,i,ctd). if (in_heap i \<and> i\<ge>(l'-Suc 0) \<and>
          sift_down_btu_invar xs\<^sub>0 (l'-Suc 0) i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<^bold>\<ge>xs!lchild i \<and> xs!i\<^bold>\<ge>xs!rchild i)) then Some top else None"
      and
      R = "Wellfounded.measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ]
    unfolding mop_has_rchild_def mop_has_lchild_def mop_lchild_def mop_rchild_def
          mop_cmp_idxs_def SPECc2_def mop_list_get_def mop_list_swap_def consumea_def
    apply (refine_vcg \<open>-\<close> rules: wr If_le_Some_rule2 If_le_rule prod3) 
    using assms    
    unfolding heapify_btu_invar_def sift_down_btu_invar_def
    apply (simp_all add: ifSome_iff del: in_heap_simps)
    (* apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 wo_leI; fail)?\<close>) (** Takes loooong *)*)
    subgoal by (force simp:  asym wo_leI simp: btu_heapify_down_right)  

    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal by simp (metis wo_leI wo_less_trans)
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal by (force simp add: btu_heapify_down_left asym wo_leI)
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal apply simp using local.trans wo_leI by blast
    subgoal by (simp add: diff_less_mono less_imp_le)
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 wo_leI)
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 wo_leI)
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 wo_leI)
    subgoal 
      apply clarsimp
      using btu_heapify_down_left_no_right_child btu_sift_down_term1 connex lchild_of_no_rchild_term wo_leD by blast
    subgoal 
      apply clarsimp
      using btu_sift_down_term1 btu_sift_down_term2 btu_sift_down_term3 wo_leI by blast
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 wo_leI)
    subgoal 
      apply clarsimp
      using btu_sift_down_term1 btu_sift_down_term2 btu_sift_down_term3 wo_leI by blast
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 wo_leI)

    subgoal using btu_sift_down_init apply (auto simp: top_acost_absorbs)  
      using is_heap_btu_def by blast
    subgoal by (auto split: prod.splits simp: ifSome_iff)
    subgoal unfolding is_heap_btu_def by (auto intro!: in_heapI)
    done


subsubsection \<open>Restore Correct\<close>

  lemma sift_down_restore_correct: 
    assumes A: "l<h" "sift_down_invar xs\<^sub>0 l xs"
    shows "sift_down l xs \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs') (\<lambda>_. top)"
    unfolding sift_down_def
    unfolding SPEC_def
    apply(rule gwp_specifies_I)
    unfolding mop_has_rchild_def mop_has_lchild_def mop_lchild_def mop_rchild_def
          mop_cmp_idxs_def SPECc2_def mop_list_get_def mop_list_swap_def consumea_def
    apply (refine_vcg \<open>-\<close> rules: monadic_WHILE_rule_real[OF refl, where 
      I="\<lambda>(xs,i,ctd). if (in_heap i \<and> i\<ge>l \<and>
          sift_down_invar xs\<^sub>0 i xs 
          \<and> h\<le>length xs
          \<and> (\<not>ctd \<longrightarrow> has_rchild i \<and> xs!i\<^bold>\<ge>xs!lchild i \<and> xs!i\<^bold>\<ge>xs!rchild i)) then Some top else None"
      and
      R = "Wellfounded.measure (\<lambda>(xs,i,ctd). (if ctd then 1 else 0) + h - i)"    
    ] If_le_Some_rule2 If_le_rule prod3)
    apply (all_par \<open>(clarsimp simp add: ifSome_iff)?\<close>)
    (*apply (all \<open>(auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap; fail)?\<close>)*)
    subgoal using asym sift_down_invar_step(2) wo_leI by blast
    subgoal by (simp add: diff_less_mono2 less_SucI)
    subgoal using wo_less_trans wo_not_le_imp_less by blast
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal using asym sift_down_invar_step(1) wo_leI by blast
    subgoal by (simp add: diff_less_mono2 less_Suc_eq)
    subgoal using itrans wo_leI by blast 
    subgoal by (simp add: Suc_diff_le less_imp_le)
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap)
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap)
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap)
    subgoal apply rule
      subgoal unfolding sift_down_invar_def by simp    
      subgoal by (meson lchild_of_no_rchild_term sift_down_invar_def sift_down_invar_step(3) sift_down_term1 wo_leD wo_leI wo_less_not_sym)
      done
    subgoal apply rule   
      subgoal unfolding sift_down_invar_def by simp     
      subgoal unfolding sift_down_invar_def by (meson wo_leI sift_down_term1 sift_down_term2 sift_down_term3)
      done
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap)
    subgoal apply rule
      subgoal unfolding sift_down_invar_def by simp    
      subgoal by (meson lchild_of_no_rchild_term less_imp_le not_le sift_down_invar_def sift_down_lemma_left_no_right_child sift_down_term1)
      done
    subgoal by (auto simp: in_heap_len_bound diff_less_mono2 A sift_down_invar_step wo_leI root_in_heap)
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def by (auto simp: top_acost_absorbs)
    subgoal using A unfolding sift_down_invar_def is_heap_except_down_def root_in_heap by auto
    done
    
    

subsection \<open>verification of sift_down1 (infinite cost)\<close>
    
  text \<open>Deferred swap optimization\<close>

  definition sift_down1 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list,_) nrest" where "sift_down1 i\<^sub>0 xs \<equiv> doN {
    ASSERT (in_heap i\<^sub>0);
    v \<leftarrow> mop_list_getF xs i\<^sub>0;
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). in_heap i \<and> i\<ge>i\<^sub>0) 
      (\<lambda>(xs,i,ctd). doN {                
                          hrc \<leftarrow> mop_has_rchildF i;
                          SPECc2F  (\<and>)  hrc ctd
                        })
    (\<lambda>(xs,i,ctd). doN {
        lci \<leftarrow> mop_lchildF i;
        rci \<leftarrow> mop_rchildF i;
        lc \<leftarrow> mop_list_getF xs lci;
        rc \<leftarrow> mop_list_getF xs rci;
        _ \<leftarrow> consumea 0;
    
      if\<^sub>N SPECc2F  (\<^bold><)  lc rc then
        if\<^sub>N SPECc2F  (\<^bold><)  v rc then
          doN {
            t \<leftarrow> mop_list_getF xs rci;
            xs \<leftarrow> mop_list_setF xs i t;
            RETURN (xs,rci,True)
          }
        else
           (RETURN (xs,i,False))
      else if\<^sub>N SPECc2F  (\<^bold><)  v lc then
        doN {
          t \<leftarrow> mop_list_getF xs lci;
          xs \<leftarrow> mop_list_setF xs i t;
          RETURN (xs,lci,True)
        }
      else 
        (RETURN (xs,i,False))
      } 
    ) (xs,i\<^sub>0,True);

    ASSERT (in_heap i \<and> i\<ge>i\<^sub>0);
    ASSERT (has_lchild i \<longrightarrow> lchild i < length xs);
    
    if\<^sub>N mop_has_lchildF i then
      (doN {
        lci \<leftarrow> mop_lchildF i;
        if\<^sub>N mop_cmp_v_idx top xs v lci then
          (doN {
            t \<leftarrow> mop_list_getF xs lci;
            xs \<leftarrow> mop_list_setF xs i t;
            xs \<leftarrow> mop_list_setF xs lci v;
            RETURN xs })
        else
          (doN {
            xs \<leftarrow> mop_list_setF xs i v;
            RETURN xs}
          )
        })
    else
      (doN {
        xs \<leftarrow> mop_list_setF xs i v;
        RETURN xs})
  }" 


  definition "swap_opt_rel v \<equiv> {((xs,i,ctd),(xs',i',ctd')). xs' = xs[i:=v] \<and> i<length xs \<and> i'=i \<and> ctd'=ctd }"

  subsubsection \<open>Refinement Lemma\<close>

 lemma sift_down1_refine_functional_aux: "sift_down1 i\<^sub>0 xs \<le> \<Down> Id (timerefine TId (sift_down i\<^sub>0 xs))" 
    unfolding sift_down1_def sift_down_def
    unfolding mop_list_get_def mop_list_swap_def mop_list_set_def 
              mop_lchild_def mop_rchild_def mop_has_rchild_def mop_has_lchild_def
              SPECc2_alt mop_cmp_idxs_def mop_cmp_v_idx_def
    apply normalize_blocks
    apply (refine_rcg consumea_Id_refine bindT_refine_easy
            monadic_WHILEIT_refine_t[where R="swap_opt_rel (xs ! i\<^sub>0)"]
            MIf_refine
          )
    supply [simp del] = conc_Id  
    apply(auto simp: swap_opt_rel_def top_acost_absorbs swap_def)
    done


    
  text \<open>Index shift optimization\<close>
  
  definition "ihs_opt_rel \<equiv> {((xs,i,ctd),(xs',i',ctd')). xs' = xs \<and> i' = i+l \<and> ctd'=ctd }"
  
  lemma ihs_opt_rel_alt: "((xs,i,ctd), (xs',i',ctd'))\<in>ihs_opt_rel \<longleftrightarrow> xs'=xs \<and> (i',i)\<in>idx_shift_rel l \<and> ctd'=ctd"
    unfolding ihs_opt_rel_def idx_shift_rel_def by auto

    
  definition [simp]: "mop_lchild2 i \<equiv> doN { ASSERT (2*i+1<h); consume (RETURN (2*i+1))  ( cost ''lchild'' 1) }"
  definition [simp]: "mop_rchild2 i \<equiv> doN { ASSERT (2*i+2<h); consume (RETURN (2*i+2))  ( cost ''rchild'' 1) }"
  definition [simp]: "has_rchild2 i \<equiv> i<(h-l-1) div 2"
  definition [simp]: "has_lchild2 i \<equiv> i<(h-l) div 2"
  definition [simp]: "mop_has_lchild2  i \<equiv> do { consume (RETURNT (has_lchild2 i)) (cost ''has_lchild'' 1) }"
  definition [simp]: "mop_has_rchild2  i \<equiv> do { consume (RETURNT (has_rchild2 i)) (cost ''has_rchild'' 1) }"

  definition [simp]: "mop_lchild2F i \<equiv> doN { ASSERT (2*i+1<h); consume (RETURN (2*i+1))  top }"
  definition [simp]: "mop_rchild2F i \<equiv> doN { ASSERT (2*i+2<h); consume (RETURN (2*i+2))  top }"
  definition [simp]: "mop_has_lchild2F  i \<equiv> do { consume (RETURNT (has_lchild2 i)) top }"
  definition [simp]: "mop_has_rchild2F  i \<equiv> do { consume (RETURNT (has_rchild2 i)) top }"


  definition [simp]: "mop_lchild_l' i \<equiv> doN { ASSERT (2*i+1<h); i'\<leftarrow>SPECc2 ''mul'' (*) i 2; SPECc2 ''add'' (+) i' 1 }"
  definition [simp]: "mop_rchild_l' i \<equiv> doN { ASSERT (2*i+2<h); i'\<leftarrow>SPECc2 ''mul'' (*) i 2; SPECc2 ''add'' (+) i' 2 }"
  definition [simp]: "mop_has_lchild_l'  i \<equiv> do { hl \<leftarrow> SPECc2 ''sub'' (-) h l; hld2 \<leftarrow> SPECc2 ''udiv'' (div) hl 2; SPECc2 ''icmp_slt'' (<) i hld2 }"
  definition [simp]: "mop_has_rchild_l'  i \<equiv> do { hl \<leftarrow> SPECc2 ''sub'' (-) h l; hl1 \<leftarrow> SPECc2 ''sub'' (-) hl 1; hld2 \<leftarrow> SPECc2 ''udiv'' (div) hl1 2; SPECc2 ''icmp_slt'' (<) i hld2 }"

      
end  
  
concrete_definition mop_lchild3 is heap_context.mop_lchild_l'_def
concrete_definition mop_rchild3 is heap_context.mop_rchild_l'_def
concrete_definition has_rchild3 is heap_context.has_rchild2_def
concrete_definition has_lchild3 is heap_context.has_lchild2_def
concrete_definition mop_has_lchild3 is heap_context.mop_has_lchild_l'_def
concrete_definition mop_has_rchild3 is heap_context.mop_has_rchild_l'_def

concrete_definition mop_lchild3F is heap_context.mop_lchild2F_def
concrete_definition mop_rchild3F is heap_context.mop_rchild2F_def
concrete_definition mop_has_lchild3F is heap_context.mop_has_lchild2F_def
concrete_definition mop_has_rchild3F is heap_context.mop_has_rchild2F_def
  
lemmas h_aux_refines = mop_lchild3.refine mop_rchild3.refine has_rchild3.refine 
  has_lchild3.refine  mop_has_lchild3.refine
  mop_lchild3F.refine mop_rchild3F.refine mop_has_lchild3F.refine mop_has_rchild3F.refine

context heap_context begin  


subsection \<open>Verification of sift_down2 (infinite cost)\<close>

  definition sift_down2 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list,_) nrest" where "sift_down2 i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    let i\<^sub>1 = i\<^sub>0 - l;
    
    v \<leftarrow> mop_list_getF xs (i\<^sub>1+l);
    
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1)
       (\<lambda>(xs,i,ctd). do { hrc \<leftarrow> mop_has_rchild3F l h i;
                          SPECc2F (\<and>) hrc ctd })
       (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3F h i;
      rci \<leftarrow> mop_rchild3F h i;
      ASSERT (lci+l<h \<and> rci+l<h);
      ASSERT (lci\<noteq>i \<and> rci\<noteq>i \<and> lci\<noteq>rci);
      lc \<leftarrow> mop_list_getF xs (lci+l);
      rc \<leftarrow> mop_list_getF xs (rci+l);
    
      ASSERT (i+l<h);
      
      if\<^sub>N SPECc2F (\<^bold><)  lc rc then
        if\<^sub>N SPECc2F  (\<^bold><)  v rc then
          (doN {
            xs \<leftarrow> mop_list_setF xs (i+l) rc;
            RETURN (xs,rci,True)
          })
        else ( RETURN (xs,i,False) )
      else if\<^sub>N SPECc2F  (\<^bold><)  v lc then
        (doN {
          xs \<leftarrow> mop_list_setF xs (i+l) lc;
          RETURN (xs,lci,True)
        })
      else
       ( RETURN (xs,i,False) ) }
    ) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1 \<and> i+l<h);
    
    if\<^sub>N mop_has_lchild3F l h i then
      (doN {
      lci \<leftarrow> mop_lchild3F h i;
      ASSERT (lci+l<h);
      ASSERT (lci\<noteq>i);
      lc \<leftarrow> mop_list_getF xs (lci+l);
      if\<^sub>N SPECc2F  (\<^bold><)  v lc then
        (doN {
          xs \<leftarrow> mop_list_setF xs (i+l) lc;
          xs \<leftarrow> mop_list_setF xs (lci+l) v;
          RETURN xs
        })
      else 
        (doN {
          xs \<leftarrow> mop_list_setF xs (i+l) v;
          RETURN xs
        })
      })
    else
      doN {
        xs \<leftarrow> mop_list_setF xs (i+l) v;
        RETURN xs
      }
  }"

    
  lemma idx_shift_adjust:
    assumes "(i',i)\<in>idx_shift_rel l"
    shows 
      "in_heap i' \<longleftrightarrow> i<h-l"
      "has_lchild i' \<longleftrightarrow> i<(h-l) div 2"
      "has_rchild i' \<longleftrightarrow> i<(h-l-1) div 2"
      "lchild i' = 2*i+1+l"
      "rchild i' = 2*i+2+l"
      "i+l = i'"
      "i'<x \<longleftrightarrow> i<x-l"
      "i'\<le>h \<longleftrightarrow> i\<le>h-l"
      "x\<le>i' \<longleftrightarrow> x-l\<le>i"
    using assms
    thm lchild_ihs
    unfolding idx_shift_rel_def 
      in_heap_def 
      has_rchild_def rchild_def
      has_lchild_def lchild_def
    by auto


subsubsection \<open>Refinement Lemma\<close>

 lemma sift_down2_refine: "sift_down2 i xs \<le> \<Down>Id (timerefine TId (sift_down1 i xs))"
    unfolding sift_down1_def sift_down2_def 
    unfolding h_aux_refines[OF heap_context_axioms, symmetric]
    supply [simp del] = conc_Id
    apply (simp cong: if_cong)
    apply (rewrite at "let i=i-l in _" Let_def) 
    unfolding SPECc2_alt
    apply normalize_blocks

    apply (intro refine0)
      apply (all \<open>unfold in_heap_def; simp_all; fail \<close>) [2]
    apply(rule bindT_refine_easy)
    subgoal by simp
     apply(rule consumea_Id_refine)
    subgoal by simp
    apply(rule bindT_refine_easy)
    subgoal by simp
    focus
      apply (refine_rcg bindT_refine_easy monadic_WHILEIT_refine' MIf_refine consumea_Id_refine)
      supply [refine_dref_RELATES] = RELATESI[of ihs_opt_rel]  
      apply refine_dref_type
      apply(simp_all only: wfR''_TId sp_TId top_acost_absorbs )
      apply (simp_all add: ihs_opt_rel_alt ) (** Takes loooong *)
      apply (all \<open>(determ \<open>elim conjE\<close>)?; simp?\<close>)
      apply (clarsimp_all simp: idx_shift_adjust ihs_opt_rel_alt simp del: in_heap_simps) (** Takes loooong *)
      unfolding in_heap_def idx_shift_rel_def ihs_opt_rel_alt
      apply (auto simp: algebra_simps)  
      solved
    subgoal for _ _ s s'
      supply [split del] = if_split
      apply (cases s; simp)
      apply (cases s'; simp)
      apply (intro refine0 )
      subgoal by (clarsimp simp: idx_shift_adjust ihs_opt_rel_alt)

      apply(rule bindT_refine_easy)
      subgoal by simp
       apply(rule consumea_Id_refine)
      subgoal by simp
    
      apply (refine_rcg bindT_refine_easy MIf_refine consumea_Id_refine)
      apply(simp_all only: wfR''_TId sp_TId top_acost_absorbs)  
        apply (simp_all add: ihs_opt_rel_alt)
        apply (all \<open>determ \<open>elim conjE\<close>; simp?\<close>)
        apply (auto simp: algebra_simps idx_shift_adjust)
        done 
     done
       
  
  
  (* Auxiliary definitions to reduce proof complexity in sepref-step.
    TODO: Without these, the sepref step gets really slow, which is another indication that we
      should separate the bound-proofs from the actual transfer step!
  *)
  definition [simp]: "mop_geth2 xs i \<equiv> doN { ASSERT(l+i\<le>h); lpi \<leftarrow> SPECc2 ''add'' (+) l i;  mop_eo_extract (\<lambda>_. lift_acost mop_array_nth_cost) xs lpi }"
  definition [simp]: "mop_seth2 xs i x \<equiv> doN { ASSERT(l+i\<le>h); lpi \<leftarrow> SPECc2 ''add'' (+) l i;  mop_eo_set (\<lambda>_. lift_acost mop_array_upd_cost) xs lpi x }"

  thm mop_oarray_extract_def

end  
  
concrete_definition mop_geth3 is heap_context.mop_geth2_def
concrete_definition mop_seth3 is heap_context.mop_seth2_def
  
lemmas h_aux_refines2 = mop_geth3.refine mop_seth3.refine  


subsection \<open>Verification of sift_down3 (add timing)\<close>

context heap_context begin  
  
  term mop_geth3
  definition sift_down3 :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list, _) nrest" where "sift_down3 i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    i\<^sub>1 \<leftarrow> SPECc2 ''sub'' (-) i\<^sub>0 l;
    xs \<leftarrow> mop_to_eo_conv xs;
    (v,xs) \<leftarrow> mop_geth3 l h xs i\<^sub>1;
    
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1)
       (\<lambda>(xs,i,ctd). do { hrc \<leftarrow> mop_has_rchild3 l h i;
                          SPECc2 ''and'' (\<and>) hrc ctd }) (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3 h i;
      rci \<leftarrow> mop_rchild3 h i;

      ASSERT (l+lci<h \<and> l+rci<h \<and> l+lci \<noteq> l+rci);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      lprci \<leftarrow> SPECc2 ''add'' (+) l rci;
      ASSERT(lplci\<noteq>lprci);

      if\<^sub>N  mop_cmpo_idxs (cost ''cmpo_idxs'' 1) xs lplci lprci then
        doN {
        if\<^sub>N mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) xs v lprci then \<comment> \<open>this is actually one more list_get then in sift_down2 !\<close>
          doN {
            (rc,xs) \<leftarrow> mop_geth3 l h xs rci;
            xs \<leftarrow> mop_seth3 l h xs i rc;
            RETURN (xs,rci,True)
          }
        else
          RETURN (xs,i,False)
        }
      else if\<^sub>N mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) xs v lplci then
        doN {
          (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
          xs \<leftarrow> mop_seth3 l h xs i lc;
          RETURN (xs,lci,True)
        }
      else
        RETURN (xs,i,False)
    }) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1);
    
    if\<^sub>N mop_has_lchild3 l h i then
      doN {
      lci \<leftarrow> mop_lchild3 h i;
      ASSERT (l+lci<h);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      if\<^sub>N mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) xs v lplci then
        doN {
          (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
          xs \<leftarrow> mop_seth3 l h xs i lc;
          xs \<leftarrow> mop_seth3 l h xs lci v;
          xs \<leftarrow> mop_to_wo_conv xs;
          RETURN xs
        }
      else
        doN {
          xs \<leftarrow> mop_seth3 l h xs i v;
          xs \<leftarrow> mop_to_wo_conv xs;
          RETURN xs
        }
      }
    else
      doN {
        xs \<leftarrow> mop_seth3 l h xs i v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      }
  }" 
    
  
  (* TODO: Move. Use also in insort. Maybe generalize to index set? *)
  definition "woe_eq_except i xs' xs \<equiv> length xs' = length xs \<and> xs'!i=None \<and> (\<forall>j\<in>{0..<length xs}-{i}. xs'!j = Some (xs!j))"
  
  lemma woe_eq_except_init: "i<length xs \<Longrightarrow> woe_eq_except i ((map Some xs)[i := None]) xs"
    unfolding woe_eq_except_def by auto
  
  lemma woe_eq_except_length[simp]: "woe_eq_except i xs' xs \<Longrightarrow> length xs'=length xs"
    unfolding woe_eq_except_def by auto
    
  lemma woe_eq_except_nth_eq_Some: "\<lbrakk>woe_eq_except i xs' xs; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = Some v \<longleftrightarrow> (j\<noteq>i \<and> v = xs!j)"  
    unfolding woe_eq_except_def 
    by force
    
  lemma woe_eq_except_nth: "\<lbrakk>woe_eq_except i xs' xs; j<length xs; j\<noteq>i\<rbrakk> \<Longrightarrow> xs'!j = Some (xs!j)"  
    unfolding woe_eq_except_def 
    by force
    
  lemma woe_eq_except_ith[simp]: "\<lbrakk>woe_eq_except i xs' xs\<rbrakk> \<Longrightarrow> xs'!i = None"  
    unfolding woe_eq_except_def 
    by force
    
  lemma woe_eq_except_upd:
    assumes "woe_eq_except i xs' xs" "i'<length xs" "i<length xs" "i\<noteq>i'"
    shows "woe_eq_except i' (xs'[i':=None,i:=Some v]) (xs[i:=v])"
    using assms unfolding woe_eq_except_def by (auto simp: nth_list_update)
    
    
  
  definition "sd23_rel \<equiv> {((xs',i',ctd'),(xs,i,ctd)). i'=i \<and> ctd'=ctd \<and> i+l<length xs \<and> woe_eq_except (i+l) xs' xs }"
  
  lemma in_sd23_rel_conv: "((xs',i',ctd'),(xs,i,ctd))\<in>sd23_rel \<longleftrightarrow> i'=i \<and> ctd'=ctd \<and> i+l<length xs \<and> woe_eq_except (i+l) xs' xs"
    by (auto simp: sd23_rel_def)

(* TODO: Move *)
  lemma introR: "(a,a')\<in>R \<Longrightarrow> (a,a')\<in>R" .

  lemma mop_has_lchild3_refine: "(a,a')\<in>Id \<Longrightarrow> (mop_has_lchild3 l h a :: (_, (_, enat) acost) nrest) \<le> \<Down> bool_rel (timerefine TId (mop_has_lchild3F l h a'))"
    apply(auto simp: mop_has_lchild3_def SPECc2_alt mop_has_lchild3F_def simp del: conc_Id) 
    apply normalize_blocks
    apply(intro refine0 bindT_refine_easy RETURNT_refine_t consumea_refine) by auto 


  lemma mop_has_rchild3_refine: "(a,a')\<in>Id \<Longrightarrow> (mop_has_rchild3 l h a :: (_, (_, enat) acost) nrest) \<le> \<Down> bool_rel (timerefine TId (mop_has_rchild3F l h a'))"
    apply(auto simp: mop_has_rchild3_def SPECc2_alt mop_has_rchild3F_def simp del: conc_Id) 
    apply normalize_blocks
    apply(intro refine0 bindT_refine_easy RETURNT_refine_t consumea_refine) by auto 

  
  lemma mop_lchild3_refine: "(a,a')\<in>Id \<Longrightarrow> (mop_lchild3 h a:: (_, (_, enat) acost) nrest) \<le> \<Down> Id (timerefine TId (mop_lchild3F h a'))"
    apply(auto simp: mop_lchild3_def SPECc2_alt mop_lchild3F_def simp del: conc_Id) 
    apply normalize_blocks
    apply(intro refine0 bindT_refine_easy  RETURNT_refine_t consumea_refine) by auto 




  lemma inres_mop_has_lchild3F: "inres (mop_has_lchild3F l h a) t \<longleftrightarrow> (has_lchild2 a \<longleftrightarrow> t)"
    unfolding mop_has_lchild3F_def by(simp add: inres_consume_conv)
  
  lemma inres_mop_lchild3F: "inres (mop_lchild3F h a) a' \<longleftrightarrow> Suc (2 * a) < h \<and> Suc (2 * a) = a'"
    unfolding mop_lchild3F_def by (simp add: inres_consume_conv)


subsubsection \<open>Functional Refinement Lemma\<close>

  lemma sift_down3_refine_funct: "sift_down3 i xs \<le>\<Down>Id (timerefine TId (sift_down2 i xs))"
    unfolding sift_down3_def sift_down2_def
    supply [simp del] = conc_Id
    supply [simp] = mop_to_eo_conv_alt
    apply (simp add: Let_def mop_geth3_def  cong: if_cong)
    unfolding SPECc2_alt
    apply normalize_blocks
    
    apply (intro refine0)
    apply clarsimp_all [3]
    apply (rule bindT_refine_easy)
    subgoal by simp
    focus
      apply (auto intro!: consumea_refine timerefineA_TId RETURNT_refine_t)
      solved
    subgoal
      for s s'
      apply(cases s; simp)
    apply (rule bindT_refine_easy)
    subgoal by simp
     apply (rule monadic_WHILEIT_refine')
    subgoal by simp
    subgoal by simp
    apply (rule introR[where R=sd23_rel])
    apply (auto simp: sd23_rel_def woe_eq_except_init) []
    apply (auto simp: sd23_rel_def) []
    subgoal 
      unfolding  SPECc2_alt
      apply (refine_rcg bindT_refine_conc_time_my_inres consumea_refine mop_has_rchild3_refine)
      apply refine_dref_type
      by (auto simp: sd23_rel_def ) 
    subgoal
      unfolding mop_has_rchild3F_def
      apply clarsimp
      unfolding mop_lchild3_def mop_rchild3_def mop_cmpo_idxs_def mop_lchild3F_def mop_rchild3F_def SPECc2_alt
      apply normalize_blocks
      apply (intro refine0 bindT_refine_easy)
            apply refine_dref_type
            apply (use [[put_named_ss Main_ss]] in \<open>auto simp: conc_Id in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth\<close>) [4]
            subgoal supply [[put_named_ss Main_ss]] by (auto simp: conc_Id in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth)
            subgoal supply [[put_named_ss Main_ss]] apply (auto simp: conc_Id in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth)
            using \<open>\<lbrakk>i < length xs; l \<le> i; i < h\<rbrakk> \<Longrightarrow> wfR'' TId\<close> by fastforce
        
      subgoal apply(rule consumea_Id_refine) by (simp only: top_acost_absorbs timerefineA_TId_eq top_greatest)

      unfolding mop_seth3_def SPECc2_alt
      apply (simp (no_asm_use))
      apply (simp (no_asm_simp))
      apply normalize_blocks
      apply(refine_rcg MIf_refine bindT_refine_easy)
                         apply refine_dref_type
      apply (auto simp only: sp_TId wfR''_TId timerefineA_TId_eq top_greatest intro!: consumea_refine)
      apply (clarsimp_all simp only: in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth
                woe_eq_except_ith woe_eq_except_upd)
      apply (simp_all (no_asm_use) add: algebra_simps)
      apply (simp_all (no_asm_simp) add: algebra_simps woe_eq_except_upd)
      done
    subgoal
      unfolding mop_to_wo_conv_def 
      apply (clarsimp split: prod.split split del: if_split cong: if_cong simp: mop_seth3_def SPECc2_alt ) 
      apply normalize_blocks
      apply (clarsimp split: prod.split)
      apply (refine_rcg MIf_refine bindT_refine_easy mop_has_lchild3_refine mop_lchild3_refine consume_refine)
      apply refine_dref_type
      apply (auto simp only: inres_mop_has_lchild3F inres_mop_lchild3F sp_TId wfR''_TId
                        timerefineA_TId_eq top_acost_absorbs top_greatest intro!: consumea_refine)
      unfolding has_lchild2_def
      supply [[put_named_ss Main_ss]]
      apply (auto simp: conc_Id in_sd23_rel_conv woe_eq_except_length woe_eq_except_nth algebra_simps woe_eq_except_ith woe_eq_except_upd in_set_conv_nth nth_list_update list_eq_iff_nth_eq)
      subgoal by (smt length_list_update nth_list_update_eq nth_list_update_neq ifSome_iff woe_eq_except_length woe_eq_except_nth_eq_Some)
      subgoal by (metis woe_eq_except_init woe_eq_except_ith woe_eq_except_nth_eq_Some)   
      subgoal by (metis option.simps(3) woe_eq_except_nth) 
      done
    done
  done

subsubsection \<open>Adding Timing Result\<close>

abbreviation "cost_lchild p \<equiv> cost ''mul'' p + cost ''add'' p"
abbreviation "cost_rchild p \<equiv> cost ''mul'' p + cost ''add'' p"
abbreviation "cost_has_lchild p \<equiv> cost ''sub'' p + cost ''udiv'' p + cost ''icmp_slt'' p"
abbreviation "cost_has_rchild p \<equiv> cost ''sub'' (2*p) + cost ''udiv'' p + cost ''icmp_slt'' p"

definition E_sd3_l :: "_ \<Rightarrow> _ \<Rightarrow> (char list, nat) acost" where
  "E_sd3_l i ctd \<equiv> 
      (let p=(if ctd then 1+i else i) in
            cost ''add'' (4*p) +
            ( p *m mop_array_nth_cost) +
           ( p *m mop_array_upd_cost ) +
            (cost ''if'' p + (cost ''cmpo_idxs'' p + (cost ''if'' p + (cost ''cmpo_v_idx'' p
           + (cost_rchild p + (cost_lchild (2*p) + (cost ''call'' p + (cost_has_rchild (2*p)
             + cost ''and'' p + cost ''if'' p)))))))))"

definition sift_down3_cost :: "_ \<Rightarrow> ecost" where
  "sift_down3_cost i =
            cost ''sub'' 1
      + cost ''add'' 5 
      + lift_acost mop_array_upd_cost + lift_acost mop_array_nth_cost + lift_acost mop_array_upd_cost
      + cost ''if'' 1 + cost ''cmpo_v_idx'' 1 + cost_lchild 1 + cost ''if'' 1 
      + cost_has_lchild 2 +
      lift_acost (E_sd3_l i True) 
      + cost_has_rchild 2 + cost ''and'' 1 + cost ''if'' 1 + lift_acost mop_array_nth_cost
      + lift_acost mop_array_upd_cost + lift_acost mop_array_nth_cost
      + cost ''call'' 1"

lemma E_sd3_l_True_mono: "x\<le>y \<Longrightarrow> lift_acost (E_sd3_l x True) \<le> lift_acost (E_sd3_l y True)"
  unfolding E_sd3_l_def
  unfolding Let_def
  apply (auto simp: norm_cost)
  apply sc_solve apply safe apply auto
  done
    
lemma E_sd3_l_dontknow_mono: "x\<le>y \<Longrightarrow> lift_acost (E_sd3_l x t) \<le> lift_acost (E_sd3_l y True)"
  unfolding E_sd3_l_def
  apply(cases t) 
  unfolding Let_def
   apply (auto simp: the_acost_propagate costmult_add_distrib costmult_cost)
  subgoal apply sc_solve apply safe by auto
  subgoal apply sc_solve apply safe by auto
  done
 
lemma lift_acost_leq_conv: "lift_acost x \<le> lift_acost y \<longleftrightarrow> x \<le> y"
  by(auto simp: less_eq_acost_def lift_acost_def)



lemma log_aux: "Discrete.log (Suc (2*(Suc x))) = Discrete.log (2*(Suc x))" 
  by (metis dvd_triv_left even_Suc_div_two le_Suc_eq le_add1 log_rec mult_Suc_right)  

lemma sift_down3_refine_time_aux1':
  assumes "Suc (Suc (i' * 2)) \<le> s "
  shows "Suc (Discrete.log (s) - Discrete.log (Suc (Suc ( (i' * 2)))))
     = Discrete.log (s) - Discrete.log (Suc i')"
proof -
  have ***: "Discrete.log (Suc (Suc (i' * 2))) 
        = Suc (Discrete.log (Suc i'))"
    by (metis One_nat_def add_Suc log_twice mult.commute mult_Suc_right nat.simps(3) numeral_2_eq_2 plus_1_eq_Suc)

  have **: "Suc i' < s" 
    using assms by auto
  then have "Suc i' \<le> s" by auto
  then have **: "Discrete.log (Suc i') \<le> Discrete.log s"
    by(rule log_mono[THEN monoD]) 

  from log_mono[THEN monoD, OF assms]
  have **: "Suc (Discrete.log (Suc i')) \<le> Discrete.log s"
    unfolding *** by simp

  have "Suc (Discrete.log (s) - Discrete.log (Suc (Suc ( (i' * 2)))))
      = Suc (Discrete.log (s) - Suc (Discrete.log (Suc i')))"
    unfolding *** by simp
  also have "...   =  (Discrete.log (s) -  (Discrete.log (Suc i')))"
    using ** by auto 
  finally show ?thesis by simp
qed

lemma sift_down3_refine_time_aux1:
  assumes \<open>Suc (Suc (l + i' * 2)) < h\<close>
  shows "Suc (Discrete.log (h-l) - Discrete.log (Suc (Suc ( (i' * 2)))))
     = Discrete.log (h-l) - Discrete.log (Suc i')"
  apply(rule sift_down3_refine_time_aux1')
  using assms by auto

lemma sift_down3_refine_time_aux2':
  assumes "Suc (Suc (i' * 2)) \<le> s "
  shows "Suc (Discrete.log (s) - Discrete.log (Suc (Suc (Suc (i' * 2)))))
     = Discrete.log (s) - Discrete.log (Suc i')"
proof -
  have ***: "Discrete.log (Suc (Suc (i' * 2))) 
        = Suc (Discrete.log (Suc i'))"
    by (metis One_nat_def add_Suc log_twice mult.commute mult_Suc_right nat.simps(3) numeral_2_eq_2 plus_1_eq_Suc)

  have *: "Discrete.log (Suc (Suc (Suc (i' * 2)))) 
        = Suc (Discrete.log (Suc i'))"
    apply(subst log_twice[symmetric]) apply simp
    apply(subst log_aux[symmetric]) by (simp add: mult.commute)
     
     (* by (metis One_nat_def add_Suc log_twice mult.commute mult_Suc_right nat.simps(3) numeral_2_eq_2 plus_1_eq_Suc)
 *)
  have **: "Suc i' < s" 
    using assms by auto
  then have "Suc i' \<le> s" by auto
  then have **: "Discrete.log (Suc i') \<le> Discrete.log s"
    by(rule log_mono[THEN monoD]) 

  from log_mono[THEN monoD, OF assms]
  have **: "Suc (Discrete.log (Suc i')) \<le> Discrete.log s"
    unfolding *** by simp

  have "Suc (Discrete.log (s) - Discrete.log (Suc (Suc (Suc (i' * 2)))))
      = Suc (Discrete.log (s) - Suc (Discrete.log (Suc i')))"
    unfolding * by simp
  also have "...   =  (Discrete.log (s) -  (Discrete.log (Suc i')))"
    using ** by auto 
  finally show ?thesis by simp
qed

lemma sift_down3_refine_time_aux2:
  assumes \<open>l + (i' * 2 + 2) \<le> h\<close>
  shows "Suc (Discrete.log (h-l) - Discrete.log (Suc (Suc (Suc (i' * 2)))))
     = Discrete.log (h-l) - Discrete.log (Suc i')"
  apply(rule sift_down3_refine_time_aux2')
  using assms by auto


lemma sift_down3_refine_time: "sift_down3 i (xs:: 'a list) \<le>\<^sub>n (SPEC (\<lambda>_. True) (%_. sift_down3_cost (Discrete.log (h-l))))"
  unfolding sift_down3_def SPEC_def
    apply(rule gwpn_specifies_I)


  apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>(_,i,ctd). E_sd3_l (Discrete.log (h-l) - Discrete.log (Suc i)) ctd"])
                         
  unfolding Let_def mop_to_eo_conv_def mop_geth3_def mop_eo_extract_def
  unfolding mop_has_rchild3_def mop_lchild3_def mop_rchild3_def 
            mop_cmpo_idxs_def mop_cmpo_v_idx_def mop_seth3_def mop_eo_set_def
            SPECc2_def

    apply(refine_vcg \<open>-\<close> rules:  gwpn_bindT_I gwpn_ASSERT_bind_I  gwpn_ASSERT_I gwpn_MIf_I
                      gwpn_consume gwpn_RETURNT_I gwpn_SPECT_I 
                      prod3 If_le_Some_rule2 If_le_rule) 
  apply(rule gwpn_monadic_WHILEIET)
  subgoal unfolding wfR2_def E_sd3_l_def zero_acost_def cost_def Let_def costmult_def by auto
  subgoal for e xs s
    apply(refine_vcg \<open>-\<close> rules: gwpn_bindT_I gwpn_consume gwpn_RETURNT_I gwpn_SPECT_I If_le_rule gwpn_ASSERT_I gwpn_MIf_I)
        prefer 5
    subgoal (* exiting loop because of wrong guard *)
      apply(rule loop_exit_conditionI)
      unfolding mop_has_lchild3_def mop_to_wo_conv_def SPECc2_alt
      apply (refine_vcg \<open>-\<close> rules: gwpn_bindT_I gwpn_consume gwpn_RETURNT_I gwpn_SPECT_I If_le_rule gwpn_ASSERT_I gwpn_MIf_I)
      subgoal
        unfolding Let_def   sift_down3_cost_def
        apply clarsimp
        apply(simp add: add.assoc lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        apply(simp only: add.commute add.left_commute)
        apply(rule add_mono) 
        subgoal premises prems apply (rule E_sd3_l_True_mono)  by simp
        subgoal premises prems
          apply sc_solve_debug apply safe   by (all \<open>(auto simp: one_enat_def numeral_eq_enat sc_solve_debug_def;fail)?\<close>)
        done
      subgoal by simp
      subgoal premises p1
        unfolding Let_def   sift_down3_cost_def
        apply clarsimp
        apply(simp add: add.assoc the_acost_costs_distrib lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        
        apply(subst lift_acost_diff_to_the_right) 
        subgoal apply(rule E_sd3_l_dontknow_mono[unfolded lift_acost_leq_conv]) apply(rule diff_le_mono2)
            apply(rule log_mono[THEN monoD]) using p1(5) by simp
        subgoal premises prems
          apply(simp only: add.commute add.left_commute)
          apply(simp add: add.assoc)
          apply(rule add_mono)
          subgoal apply (rule E_sd3_l_True_mono) by simp  
          apply sc_solve by auto
        done
      subgoal by simp
      subgoal
        unfolding Let_def   sift_down3_cost_def
        apply(simp add: add.assoc lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        apply(simp only: add.commute add.left_commute)
        apply(rule add_mono)
        subgoal apply (rule E_sd3_l_True_mono) by simp
        apply sc_solve by auto
      subgoal by simp
      done 
    subgoal for xs' i' ctd (* first if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        subgoal premises prems
        unfolding E_sd3_l_def Let_def
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc costmult_add_distrib costmult_cost)
          apply sc_solve
        apply safe  
                    apply (auto simp only: one_enat_def numeral_eq_enat plus_enat_simps zero_enat_def lift_ord)
        apply auto
         apply(all \<open>intro log_mono[THEN monoD] diff_le_mono2 add_mono; auto\<close>)
        done
      done
      subgoal premises prems (* diff pays *)
        apply simp
        unfolding E_sd3_l_def Let_def
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate costmult_add_distrib costmult_cost acostC_the_acost_cost add.assoc)
        apply sc_solve_debug apply safe 
                    apply(auto simp: sc_solve_debug_def one_enat_def numeral_eq_enat )
        by(auto simp: sift_down3_refine_time_aux2[OF \<open>l + (i' * 2 + 2) \<le> h\<close>, symmetric])    
         
      subgoal 
        apply simp done
      done
    subgoal for xs' i' ctd (* second if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        subgoal premises prems
        unfolding E_sd3_l_def Let_def
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc  costmult_add_distrib costmult_cost)
        apply sc_solve
        apply safe apply (auto simp: numeral_eq_enat one_enat_def) done  
        done
      subgoal (* diff pays *)
        apply simp apply safe
        subgoal premises prems
        unfolding E_sd3_l_def Let_def 
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc costmult_add_distrib costmult_cost)
        apply sc_solve 
          apply safe by (auto simp: numeral_eq_enat one_enat_def) 
        done
      subgoal 
        apply simp done
      done
    subgoal for xs' i' ctd (* third if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc costmult_add_distrib costmult_cost)
          apply sc_solve apply safe apply (auto simp: numeral_eq_enat one_enat_def)
           
         apply(all \<open>intro log_mono[THEN monoD] diff_le_mono2 add_mono; auto\<close>)
          done
        done
      subgoal (* diff pays *)
        apply simp apply safe
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate lift_acost_propagate lift_acost_cost acostC_the_acost_cost add.assoc costmult_add_distrib costmult_cost)        
        apply sc_solve 
          apply safe  apply (auto simp: one_enat_def numeral_eq_enat) 

          by(auto simp: sift_down3_refine_time_aux1[OF \<open>Suc (Suc (l + i' * 2)) < h\<close>, symmetric])    
        done
      subgoal 
        by auto
      done
    subgoal for xs' i' ctd (* fourth if branch *)
      apply(rule loop_body_conditionI) 
      subgoal (*  \<le> *)
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
          apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc costmult_add_distrib costmult_cost) 
          apply sc_solve apply safe apply (auto simp: one_enat_def) done 
        done
      subgoal (* diff pays *)
        apply simp apply safe
        unfolding E_sd3_l_def Let_def
        subgoal premises prems
        apply (clarsimp simp add: the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc costmult_add_distrib costmult_cost)
        apply sc_solve 
          apply safe by (auto simp: one_enat_def) 
        done
      subgoal 
        by auto
      done
    done
  subgoal apply auto done
  done

subsubsection \<open>Bottom Up - Correctness and Timing\<close>

lemma sift_down_btu_correct':
  assumes "heapify_btu_invar xs\<^sub>0 l' xs" "l<l'"
  shows "sift_down3 (l'-Suc 0) xs \<le> SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 (l'-Suc 0) xs') (%_. sift_down3_cost (Discrete.log (h-l)))"
  apply(rule separate_correct_and_time)
  subgoal 
    apply(rule order.trans) 
     apply(rule sift_down3_refine_funct) apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down2_refine)  apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down1_refine_functional_aux)  apply (simp add: timerefine_id)
    apply(rule  sift_down_btu_correct) using assms by auto 
  by (rule sift_down3_refine_time)

definition "sift_down3_t1 i\<^sub>0 xs = sup (sift_down3 i\<^sub>0 xs) (SPEC (\<lambda>_. True) (%_. cost ''sift_down'' 1))"


definition heapify_btu_step 
  where "heapify_btu_step l' xs\<^sub>0 xs  = do { ASSERT (heapify_btu_invar xs\<^sub>0 (Suc l') xs \<and> l<Suc l');
                                SPEC (\<lambda>xs'. heapify_btu_invar xs\<^sub>0 l' xs') (%_. cost ''sift_down'' 1) }"


definition sift_down_restore 
  where "sift_down_restore xs\<^sub>0 xs  = do { ASSERT (l<h \<and> sift_down_invar xs\<^sub>0 l xs);
                                SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs') (%_. cost ''sift_down'' 1) }"



definition Rsd where "Rsd i = TId(''sift_down'':=sift_down3_cost (Discrete.log i))"

lemma sift_down3_refines_heapify_btu_step:
    shows "sift_down3  l' xs \<le> \<Down>Id( timerefine (Rsd (h-l)) (heapify_btu_step l' xs\<^sub>0 xs))"
  unfolding heapify_btu_step_def
  apply(rule ASSERT_D3_leI)
  apply simp  
  apply(rule order.trans[OF sift_down_btu_correct'[of xs\<^sub>0 "Suc l'", simplified]])
    apply simp
   apply simp
  apply(rule SPEC_timerefine)
  subgoal by simp
  subgoal by (auto simp: Rsd_def  timerefineA_upd)
  done


subsubsection \<open>Restore - Correctness and Timing\<close>


lemma sift_down_restore_correct':
  assumes "l < h" "sift_down_invar xs\<^sub>0 l xs"
  shows "sift_down3 l xs \<le> SPEC (\<lambda>xs'. slice_eq_mset l h xs' xs\<^sub>0 \<and> is_heap xs') (%_. sift_down3_cost (Discrete.log (h-l)))"
  apply(rule separate_correct_and_time)
  subgoal 
    apply(rule order.trans) 
     apply(rule sift_down3_refine_funct) apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down2_refine)  apply (simp add: timerefine_id)
    apply(rule order.trans)
     apply(rule sift_down1_refine_functional_aux)  apply (simp add: timerefine_id)
    apply(rule  sift_down_restore_correct) using assms by auto
  by (rule sift_down3_refine_time) 

lemma sift_down3_refines_sift_down_restore:
  shows "sift_down3 l xs \<le>  \<Down>Id( timerefine (Rsd (h-l)) ( sift_down_restore xs\<^sub>0 xs))"
  unfolding sift_down_restore_def
  apply(rule ASSERT_D3_leI)
  apply simp  
  apply(rule order.trans[OF sift_down_restore_correct'[of xs\<^sub>0]])
    apply simp
   apply simp
  apply(rule SPEC_timerefine)
  subgoal by simp
  subgoal by(auto simp: Rsd_def  timerefineA_upd)
  done







end


subsection \<open>Verification of Heapify Bottom up - heapify_btu\<close>

concrete_definition sift_down4 is heap_context.sift_down3_def
concrete_definition sift_down_ab is heap_context.heapify_btu_step_def
concrete_definition sift_down_restore_a for less_eq l h xs\<^sub>0 xs is heap_context.sift_down_restore_def
                                                                              
context heap_context begin  

  (*
  lemma sift_down4_full_refine: "sift_down4 (\<^bold><) l h i xs \<le> sift_down i xs"
  proof -
    note sift_down4.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down3_refine 
    also note sift_down2_refine 
    also note sift_down1_refine 
    finally show ?thesis by simp
  qed *)

  lemmas sift_down_ab_refine = sift_down_ab.refine[OF heap_context_axioms, symmetric, unfolded heapify_btu_step_def]
  lemma sift_down4_refine: "sift_down4 (\<^bold><) l h l' xs \<le> \<Down>Id( timerefine (Rsd (h-l)) (sift_down_ab (\<^bold>\<le>) l h l' xs\<^sub>0 xs))"
  proof -
    note sift_down4.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down3_refines_heapify_btu_step
    finally show ?thesis unfolding sift_down_ab.refine[OF heap_context_axioms] .
  qed

  lemma sift_down4_refine_restore: "sift_down4 (\<^bold><) l h l xs \<le> \<Down>Id( timerefine (Rsd (h-l)) (sift_down_restore_a (\<^bold>\<le>) l h xs\<^sub>0 xs))"
  proof -
    note sift_down4.refine[OF heap_context_axioms, symmetric, THEN meta_eq_to_obj_eq]
    also note sift_down3_refines_sift_down_restore
    finally show ?thesis unfolding sift_down_restore_a.refine[OF heap_context_axioms] .
  qed


  lemma sift_down3_cost_mono:
    "x\<le>y \<Longrightarrow> sift_down3_cost x \<le> sift_down3_cost y"
    unfolding sift_down3_cost_def E_sd3_l_def Let_def
    apply(simp add: lift_acost_propagate lift_acost_cost)
        apply (clarsimp simp add: costmult_add_distrib costmult_cost the_acost_costs_distrib the_acost_cost_mult acostC_the_acost_cost)
        apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
    apply sc_solve by auto


  lemma sift_down4_refine_u: "(la,la')\<in>nat_rel \<Longrightarrow> (xs,xs')\<in> (\<langle>Id\<rangle>list_rel) \<Longrightarrow> sift_down4 (\<^bold><) l h la xs \<le> \<Down>(\<langle>Id\<rangle>list_rel) ( timerefine (Rsd (h-l)) (sift_down_ab (\<^bold>\<le>) l h la' xs\<^sub>0 xs'))"
    apply (simp del: conc_Id)
    apply(rule order.trans[OF sift_down4_refine, of _  xs\<^sub>0])
    unfolding sift_down_ab_def
    apply(rule ASSERT_D5_leI)
    apply simp done (*
    apply(rule timerefine_R_mono_wfR'')
    subgoal by(auto simp: Rsd_def wfR''_TId intro: wfR''_upd)
    unfolding Rsd_def
    apply(simp add: le_fun_def) 
    apply(rule sift_down3_cost_mono)
    by auto *)

  definition "heapify_btu xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
    (xs,l') \<leftarrow> monadic_WHILEIT (\<lambda>(xs,l'). heapify_btu_invar xs\<^sub>0 l' xs \<and> l'\<ge>l)
      (\<lambda>(xs,l'). SPECc2 ''icmp_slt'' (<) l l') 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        l' \<leftarrow> SPECc2 ''sub'' (-) l' 1;
        xs \<leftarrow> sift_down_ab (\<^bold>\<le>) l h l' xs\<^sub>0 xs ;
        RETURN (xs,l')
      })
      (xs\<^sub>0,h');
    RETURN xs
  }"    

definition heapify_btu_cost :: "_ \<Rightarrow> ecost" 
  where "heapify_btu_cost xs\<^sub>0 = cost ''call'' (enat (h - Suc l) + 1) + cost ''icmp_slt'' (enat (h - Suc l) + 1)
       + cost ''if'' (enat (h - Suc l) + 1) + cost ''sub'' (enat (h - Suc l) +1) 
      + cost ''sift_down'' (enat (h - Suc l))"

\<comment> \<open>TODO: heapify_btu actually is O(n), not O(n * log n) ! but we don't need it for heapsort in O(n*log n)\<close> 

definition heapify_btu_lbc :: "_ \<Rightarrow> (char list, nat) acost" where
  "heapify_btu_lbc = (\<lambda>(xs,l'). (cost ''call'' (l'-l) + (cost ''icmp_slt'' (l'-l) + cost ''if'' (l'-l)) + cost ''sub'' (l'-l) + cost ''sift_down'' (l'-l)))"


subsubsection \<open>Correctness Lemma\<close>

  lemma heapify_btu_correct: "\<lbrakk> l<h; h\<le>length xs\<^sub>0 \<rbrakk> \<Longrightarrow> heapify_btu xs\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h xs xs\<^sub>0 \<and> is_heap xs) (\<lambda>_. heapify_btu_cost xs\<^sub>0)"
    unfolding heapify_btu_def
    apply simp
    apply(subst monadic_WHILEIET_def[symmetric, where E=heapify_btu_lbc]) 
    unfolding SPEC_def SPECc2_def 
    unfolding sift_down_ab_refine SPEC_REST_emb'_conv
    apply(rule gwp_specifies_I)
    apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET)
    apply(rule gwp_monadic_WHILEIET)
    subgoal unfolding wfR2_def heapify_btu_lbc_def zero_acost_def cost_def by auto
    subgoal for s
      apply clarsimp
      apply (refine_vcg \<open>-\<close>)
      apply simp_all
      apply safe
      subgoal
        apply (refine_vcg \<open>-\<close>) (* loop body *)
        subgoal apply(rule loop_body_conditionI) 
          subgoal unfolding heapify_btu_lbc_def apply sc_solve by auto
          subgoal unfolding heapify_btu_lbc_def apply sc_solve_debug apply(all \<open>(auto simp: one_enat_def sc_solve_debug_def; fail)?\<close>) done 
          subgoal by auto 
          done
        subgoal by simp
        done
    subgoal (* exiting loop because of wrong guard *)
      apply(rule loop_exit_conditionI)
      apply (refine_vcg \<open>-\<close>)
      unfolding heapify_btu_invar_def
      unfolding heapify_btu_lbc_def heapify_btu_cost_def
      apply auto
      subgoal using btu_heapify_term by blast
      subgoal 
        apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
       apply(sc_solve)
        by auto    
      done
    done      
    subgoal by (simp add: heapify_btu_invar_def btu_heapify_init) 
    done


  
subsection \<open>Verification of heapify_btu2\<close>

  definition "heapify_btu2 xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
    (xs,l') \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
      (\<lambda>(xs,l'). SPECc2 ''icmp_slt'' (<) l l') 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        l'' \<leftarrow> SPECc2 ''sub'' (-) l' 1;
        xs \<leftarrow> sift_down4 (\<^bold><) l h l'' xs;
        RETURN (xs,l'')
      })
      (xs\<^sub>0,h');
    RETURN xs
  }"   


subsubsection \<open>Refinement Lemma\<close>

  lemma heapify_btu2_refine: "heapify_btu2 xs\<^sub>0 \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine (Rsd (h-l)) (heapify_btu xs\<^sub>0))"
    unfolding heapify_btu2_def heapify_btu_def
    supply monadic_WHILEIT_refine'[refine]
    supply bindT_refine_easy[refine]
    supply sift_down4_refine_u[refine]                           
    apply(refine_rcg SPECc2_refine)
    apply refine_dref_type   
    by  (auto simp: cost_n_leq_TId_n Rsd_def SPECc2_def inres_SPECT)
  
  lemma heapify_btu2_correct:
    "\<lbrakk>l < h; h \<le> length xs\<^sub>0\<rbrakk>
    \<Longrightarrow> heapify_btu2 xs\<^sub>0 \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine (Rsd (h-l)) (SPEC (\<lambda>xs. slice_eq_mset l h xs xs\<^sub>0 \<and> is_heap xs) (\<lambda>_. heapify_btu_cost xs\<^sub>0)))"
    apply(rule order.trans)
     apply(rule heapify_btu2_refine)
    apply simp
    apply(rule timerefine_mono2)
    by(auto simp: Rsd_def intro: heapify_btu_correct)
    
  
  thm heap_context.heapify_btu2_def
     
end

concrete_definition heapify_btu1 for less_eq  l h xs\<^sub>0 is heap_context.heapify_btu_def
concrete_definition heapify_btu2 for less l h xs\<^sub>0 is heap_context.heapify_btu2_def
concrete_definition Rsd_a for i is heap_context.Rsd_def


subsection \<open>Verification of Heapsort\<close>

context heap_context begin  

    lemmas heapify_btu1_correct = heapify_btu_correct[unfolded heapify_btu1.refine[OF heap_context_axioms]]
end

context weak_ordering begin

  (* TODO: We keep \<le> out of the definition (although it occurs in invariants). 
    Otherwise, getting rid of the \<le> ghost parameter is difficult!
  *)


  (* abstraction level with currency sift_down *)
  definition heapsort :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "heapsort xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    hl \<leftarrow> SPECc2 ''sub'' (-) h\<^sub>0 l;
    if\<^sub>N SPECc2 ''icmp_slt'' (<) 1 hl then
      doN {
        xs \<leftarrow> heapify_btu1 (\<^bold>\<le>) l h\<^sub>0 xs\<^sub>0;
        
        (xs,h)\<leftarrow> monadic_WHILEIT (\<lambda>(xs,h). 
            l<h \<and> h\<le>h\<^sub>0 
          \<and> heap_context.is_heap (le_by_lt (\<^bold><)) l h xs
          \<and> slice_eq_mset l h\<^sub>0 xs xs\<^sub>0
          \<and> sorted_wrt_lt (\<^bold><) (slice h h\<^sub>0 xs)
          \<and> (\<forall>a\<in>set (slice l h xs). \<forall>b\<in>set (slice h h\<^sub>0 xs). (le_by_lt (\<^bold><)) a b)
        )
          (\<lambda>(xs,h). doN { l' \<leftarrow> SPECc2 ''add'' (+) l 1;
                          SPECc2 ''icmp_slt'' (<) l' h }) 
          (\<lambda>(xs,h). doN {
            ASSERT (h>0 \<and> l\<noteq>h-1);
            h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
            xs \<leftarrow> mop_list_swapN xs l h';
            xs \<leftarrow> sift_down_restore_a (\<^bold>\<le>) l h' xs xs;
            RETURN (xs,h')
          })
          (xs,h\<^sub>0);
        
        RETURN xs
      }
    else
      RETURN xs\<^sub>0
  }"


text \<open>heapsort loop body cost\<close> 
definition heapsort_lbc :: "nat \<Rightarrow> (char list, nat) acost" where
  "heapsort_lbc = (\<lambda>p.  
                 cost ''list_swap'' p + cost ''call'' p +  cost ''add'' p + cost ''icmp_slt'' p
               + cost ''if'' p + cost ''sub'' p + cost ''sift_down'' p )"

  definition heapsort_time :: "_ \<Rightarrow> _ \<Rightarrow> ecost" where
    "heapsort_time l h\<^sub>0 = lift_acost (heapsort_lbc (h\<^sub>0-l)) 
          + cost ''add'' 1 + cost ''call'' (enat (h\<^sub>0 - Suc l) + 2)
          + cost ''icmp_slt'' (enat (h\<^sub>0 - Suc l) + 1 + 1 + 1) + cost ''if'' (enat (h\<^sub>0 - Suc l) + 1 + 3)
          + cost ''sub'' (enat (h\<^sub>0 - Suc l) + 2) + cost ''sift_down'' (enat (h\<^sub>0 - Suc l))"

subsubsection \<open>Correctness Lemma\<close>
  
lemma heapsort_correct:
  fixes xs\<^sub>0 :: "'a list"
    assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
    shows "heapsort xs\<^sub>0 l h\<^sub>0 \<le> SPEC (\<lambda>xs. slice_eq_mset l h\<^sub>0 xs xs\<^sub>0 \<and> sorted_wrt_lt (\<^bold><) (slice l h\<^sub>0 xs)) (\<lambda>_. heapsort_time l h\<^sub>0)"
  proof -
    interpret initial: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h\<^sub>0 by unfold_locales fact

    note F = initial.heapify_btu1_correct[unfolded SPEC_def, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
    note G = initial.sift_down_ab_refine 

    show ?thesis  
      using assms unfolding heapsort_def le_by_lt (* NOTE: not yet used here le_by_lt *)
      apply(subst monadic_WHILEIET_def[symmetric, where E="(\<lambda>(xs,h). heapsort_lbc (h-l) )::(('a list * nat) \<Rightarrow>  (char list, nat) acost)"]) 
      unfolding SPEC_def SPECc2_def mop_list_swap_def 
      apply(rule gwp_specifies_I)
      apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET F If_le_rule)

                apply (all \<open>(auto dest: slice_eq_mset_eq_length;fail)?\<close>)    
      subgoal unfolding wfR2_def apply (auto simp: handy_if_lemma zero_acost_def)
          unfolding heapsort_lbc_def Let_def cost_def zero_acost_def by auto
      apply (clarsimp_all simp add: handy_if_lemma)
      subgoal premises prems for xs\<^sub>1 M xs h y proof -
        (* TODO: This is the argument that swapping the max-element to the end will preserve the
            sortedness criteria. Though apparently simple, the reasoning seems to be much too complex here.
            Try to improve on that!
        *)
        interpret heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h using prems by (unfold_locales) auto
        interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" using prems by (unfold_locales) auto
        
        from prems have 
          [simp]: "length xs = length xs\<^sub>0" 
          and [simp, arith]: "h\<^sub>0 \<le> length xs\<^sub>0"
        by (auto simp: slice_eq_mset_eq_length)
        
        {
          fix xs'
          assume A: "slice_eq_mset l (h - Suc 0) xs' (swap xs l (h - Suc 0))"  
          hence "slice_eq_mset l h\<^sub>0 xs' (swap xs l (h - Suc 0))"
            apply (rule slice_eq_mset_subslice)
            using prems by auto
          from this[symmetric] have "slice_eq_mset l h\<^sub>0 xs' xs"  
            apply -
            apply (drule slice_eq_mset_swap(2)[THEN iffD1, rotated -1])
            using prems by (auto dest: slice_eq_mset_sym)
          also note \<open>slice_eq_mset l h\<^sub>0 xs xs\<^sub>0\<close>   
          finally have G1: "slice_eq_mset l h\<^sub>0 xs' xs\<^sub>0" .
  
          note [simp] = slice_eq_mset_eq_length[OF G1]
          
          have [simp]: "slice (h - Suc 0) h\<^sub>0 xs' = (xs'!(h-Suc 0))#slice h h\<^sub>0 xs'"
            apply (rule slice_extend1_left)
            using prems by (auto)
          
            
          have "slice h h\<^sub>0 xs' = slice h h\<^sub>0 (swap xs l (h - Suc 0))"
            apply (rule slice_eq_mset_eq_outside(2)[OF A]) using prems by auto
          also have "\<dots> = slice h h\<^sub>0 xs" 
            by (metis Suc_lessD atLeastLessThan_iff leI le_antisym le_zero_eq nat_less_le nz_le_conv_less \<open>Suc l < h\<close> slice_swap_outside)
          finally have [simp]: "slice h h\<^sub>0 xs' = slice h h\<^sub>0 xs" .
            
          have [arith,simp]: "h - Suc 0 < length xs\<^sub>0" "l<length xs\<^sub>0" using prems by (auto)
          have [simp]: "xs' ! (h - Suc 0) = xs!l" 
            using slice_eq_mset_nth_outside[OF A, of "h-Suc 0"] 
            by auto
            
          have "xs!l \<in> set (slice l h xs)" using prems by (auto simp: set_slice_conv)
          then have G2: "sorted_wrt (\<^bold>\<le>) (slice (h - Suc 0) h\<^sub>0 xs')" 
            using prems 
            by (auto)
  
          have [simp]: "slice l (h - Suc 0) (swap xs l (h - Suc 0)) = xs!(h-Suc 0)#(slice (Suc l) (h-Suc 0) xs)"
            apply (rule nth_equalityI)
            apply (auto simp: nth_list_update slice_nth swap_nth Suc_diff_Suc \<open>Suc l < h\<close>)
            done
            
          have "in_heap (h - Suc 0)"
            unfolding in_heap_def apply simp
            using \<open>Suc l < h\<close> by linarith
          
          have G3: "\<forall>a \<in> set (slice l (h - Suc 0) xs'). \<forall>b \<in> set (slice (h - Suc 0) h\<^sub>0 xs'). a\<^bold>\<le>b" 
            thm slice_eq_mset_set_inside[OF A]
            apply (simp add: slice_eq_mset_set_inside[OF A])
            using \<open>\<forall>x\<in>set (slice l h xs). \<forall>_\<in>_. _\<close>
            apply (auto simp: set_slice_conv root_greatest[OF \<open>is_heap xs\<close> \<open>in_heap (h-Suc 0)\<close>])
            subgoal using N.ran_not_empty \<open>in_heap (h - Suc 0)\<close> in_heap_bounds(2) by blast  
            subgoal for j 
              apply (subgoal_tac "in_heap j")
              using root_greatest[OF \<open>is_heap xs\<close>, of j] apply blast
              unfolding in_heap_def by simp
            subgoal by (metis Suc_le_lessD diff_le_self less_imp_le less_le_trans)
            done
            
          note G1 G2 G3
        } note aux=this
        thm sift_down_invar_init[OF \<open>is_heap xs\<close> \<open>Suc l < h\<close>]

        have " l < h - Suc 0" using \<open>Suc l < h\<close>
          using N.ran_not_empty le_eq_less_or_eq prems(5) by blast

        show ?thesis
          unfolding sift_down_restore_a_def SPEC_REST_emb'_conv
          apply (refine_vcg \<open>-\<close> )
          subgoal for x
            apply(rule loop_body_conditionI)
            subgoal unfolding heapsort_lbc_def Let_def apply sc_solve by simp
            subgoal unfolding heapsort_lbc_def Let_def apply simp
              apply sc_solve by (auto simp: one_enat_def)
            subgoal  
              apply safe
              using \<open>Suc l < h\<close> \<open>h\<le>h\<^sub>0\<close>
              by (auto simp: aux)
            done
          subgoal using sift_down_invar_init[OF \<open>is_heap xs\<close> \<open>Suc l < h\<close>] \<open>l < h - Suc 0\<close> by simp
          done
          
      qed
      subgoal for xs\<^sub>1 M xs h y
        apply(rule loop_exit_conditionI)
        apply (refine_vcg \<open>-\<close> rules: If_le_Some_rule2)
        subgoal 
          unfolding initial.heapify_btu_cost_def heapsort_time_def
          apply(simp add: lift_acost_zero lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)

          apply(simp only: add.assoc)
          apply(rule add_left_mono)  
          apply sc_solve_debug apply safe by (all \<open>(auto simp: sc_solve_debug_def numeral_eq_enat one_enat_def;fail)?\<close>)
        subgoal 
          
      
      apply clarsimp
      subgoal premises prems
      proof -
        have [simp]: "h=l+1" using prems by auto
      
        from prems have [simp]: "length xs = length xs\<^sub>0"
          and [simp, arith]: "l<length xs\<^sub>0" "h<length xs\<^sub>0"
          by (auto dest: slice_eq_mset_eq_length)
        
        have "set (slice l (Suc l) xs) = {xs!l}" by simp
        
        show ?thesis using prems
          by (auto simp: slice_split_hd le_by_lt)
      qed
      done
    done
    prefer 3
  subgoal
    by (simp add: sorted_wrt01)
  subgoal by auto
  subgoal unfolding heapsort_time_def apply sc_solve by (auto simp: numeral_eq_enat one_enat_def)
  done
                                                                                      
qed

subsection \<open>Verification of heapsort2\<close>


  definition heapsort2 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "heapsort2 xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    hl \<leftarrow> SPECc2 ''sub'' (-) h\<^sub>0 l;
    b \<leftarrow> SPECc2 ''icmp_slt'' (<) 1 hl;
    MIf b (doN {
      xs \<leftarrow> heapify_btu2 (\<^bold><) l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow> monadic_WHILEIT (\<lambda>(xs,h).  True )
        (\<lambda>(xs,h). doN { l' \<leftarrow> SPECc2 ''add'' (+) l 1;
                        SPECc2 ''icmp_slt'' (<) l' h }) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0 \<and> l\<noteq>h-1);
          h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
          xs \<leftarrow> mop_list_swapN xs l h';
          xs \<leftarrow> sift_down4 (\<^bold><) l h' l xs;
          RETURN (xs,h')
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } ) (
      RETURN xs\<^sub>0 )
  }"



subsection \<open>Refinement Lemma\<close>

lemma heapsort2_refine:
  fixes xs\<^sub>0 :: "'a list"
  assumes "l\<le>h\<^sub>0" "h\<^sub>0\<le>length xs\<^sub>0"
  shows "heapsort2  xs\<^sub>0 l h\<^sub>0 \<le> \<Down>Id (timerefine (Rsd_a (h\<^sub>0-l)) (heapsort xs\<^sub>0 l h\<^sub>0))"
proof -
    interpret initial: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l h\<^sub>0 by unfold_locales fact

    

    show ?thesis
      unfolding heapsort_def heapsort2_def 
      supply bindT_refine_conc_time_my_inres[refine]
      apply(refine_rcg SPECc2_refine MIf_refine monadic_WHILEIT_refine' )
      apply refine_dref_type
      prefer 10
      subgoal
        apply(rule  initial.heapify_btu2_refine[unfolded heapify_btu1.refine[OF initial.heap_context_axioms]
                                                Rsd_a.refine[OF initial.heap_context_axioms]
                                                heapify_btu2.refine[OF initial.heap_context_axioms]
                    ])
        done
      apply(auto simp: Rsd_a_def wfR''_TId sp_TId simp del: conc_Id 
                intro!: wfR''_upd cost_n_leq_TId_n struct_preserving_upd_I )
      subgoal 
        apply(refine_rcg)
        by (auto simp: timerefineA_upd)
      unfolding SPECc2_def apply (simp del: conc_Id)
      subgoal premises prems for d _ _ _ xs\<^sub>1 h h' proof -
        interpret N: heap_context "(\<^bold>\<le>)" "(\<^bold><)" l "h-Suc 0" using prems by (unfold_locales) auto

        from prems have *: "h' \<le> h\<^sub>0" by simp

        show ?thesis
          unfolding Rsd_a_def[symmetric]
          using N.sift_down4_refine_restore[of "swap xs\<^sub>1 l h'" "swap xs\<^sub>1 l h'"]
          unfolding Rsd_a.refine[OF N.heap_context_axioms]
          unfolding Rsd_a_def  N.sift_down3_cost_def initial.sift_down3_cost_def
          unfolding prems(8)
          apply(rule order.trans)
          apply simp
          apply(rule timerefine_R_mono_wfR'')
          subgoal by(auto simp: wfR''_TId intro: wfR''_upd)
          subgoal apply(auto simp: le_fun_def)
            unfolding N.E_sd3_l_def Let_def prems(1)[symmetric]
            apply simp
            apply (clarsimp simp add: the_acost_costs_distrib costmult_add_distrib costmult_cost the_acost_cost_mult acostC_the_acost_cost)
            apply(simp add: the_acost_propagate  acostC_the_acost_cost add.assoc)
            apply sc_solve_debug apply safe using \<open>h' \<le> h\<^sub>0\<close>  apply (all \<open>(auto intro: log_mono[THEN monoD] simp: sc_solve_debug_def numeral_eq_enat one_enat_def;fail)?\<close>)
            apply (auto intro: log_mono[THEN monoD] intro!: add_mono simp: sc_solve_debug_def numeral_eq_enat one_enat_def)
            done
          done
      qed
      done        
qed

definition heapsort_TR
  where "heapsort_TR l h = pp (Rsd_a (h-l)) (TId(''slice_sort'':=heapsort_time l h))"

lemma wfR''_Rsd_a[simp]: "wfR'' (Rsd_a x)"
  unfolding Rsd_a_def by auto

lemma wfR''_heapsort_TR[simp]: " wfR'' (heapsort_TR l h)"
  unfolding heapsort_TR_def
  by (auto intro!: wfR''_ppI)

lemma Sum_any_cost: "Sum_any (the_acost (cost n x)) = x"
  unfolding cost_def by (simp add: zero_acost_def)

lemma finite_sum_nonzero_cost_enat:
  "finite {a. the_acost (cost n m) a \<noteq> 0}"
  unfolding cost_def by (auto simp: zero_acost_def)

lemma finite_sum_nonzero_if_summands_finite_nonzero_enat:
  "finite {a. f a \<noteq> 0} \<Longrightarrow> finite {a. g a \<noteq> 0} \<Longrightarrow> finite {a. (f a ::enat) + g a \<noteq> 0}"
  apply(rule finite_subset[where B="{a. f a \<noteq> 0} \<union> {a. g a \<noteq> 0}"])
  by auto


subsubsection \<open>Complexity Bound for Heapsort\<close>

text \<open>Heap sort is in O(n log n)\<close>

lemma "Sum_any (the_acost (timerefineA (heapsort_TR l h) (cost ''slice_sort'' 1))) = 
      enat (73 * (h - Suc l) + 75 * (h - l) + 12 + 29 * (Discrete.log (h - l) * (h - Suc l)) + 29 * ((h - l) * Discrete.log (h - l))) "
  unfolding heapsort_TR_def  singleton_heap_context.sift_down3_cost_def heapsort_time_def
  unfolding pp_fun_upd pp_TId_absorbs_right 
  apply(auto simp add: timerefineA_propagate)
  unfolding Rsd_a_def heapsort_lbc_def 
  apply(auto simp:   timerefineA_update_apply_same_cost' lift_acost_cost costmult_cost
                lift_acost_propagate timerefineA_update_cost wfR''_TId intro!: wfR''_upd)
  apply(subst timerefineA_propagate, auto)+
  unfolding singleton_heap_context.sift_down3_cost_def  singleton_heap_context.E_sd3_l_def
  apply(auto simp: costmult_cost costmult_add_distrib lift_acost_propagate lift_acost_cost)
  apply(simp only: add.left_commute add.assoc cost_same_curr_left_add plus_enat_simps)
  apply(simp add: timerefineA_update_apply_same_cost' costmult_cost costmult_add_distrib)
  apply(simp only: the_acost_propagate )
  apply(subst  Sum_any.distrib; auto  simp only: Sum_any_cost intro!: finite_sum_nonzero_if_summands_finite_nonzero_enat finite_sum_nonzero_cost)+
  apply (simp add: plus_enat_simps one_enat_def numeral_eq_enat add_mult_distrib2 add_mult_distrib)
  done


subsubsection \<open>Correctness Theorem\<close>

lemma heapsort_correct': 
  "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> \<Longrightarrow> heapsort2 xs l h \<le>
      \<Down>Id (timerefine (heapsort_TR l h) (slice_sort_spec (\<^bold><) xs' l' h'))"
    unfolding slice_sort_spec_alt              
    apply (rule refine0)
    apply(rule order.trans)
     apply(rule heapsort2_refine) apply simp apply simp
    apply simp
    unfolding heapsort_TR_def
    apply(subst timerefine_iter2[symmetric])
    subgoal by(auto simp: Rsd_a_def wfR''_TId intro: wfR''_upd) 
    subgoal by(auto simp: wfR''_TId intro: wfR''_upd) 
    apply(rule timerefine_mono2) 
    subgoal by(auto simp: Rsd_a_def wfR''_TId intro: wfR''_upd) 
    subgoal 
      apply(rule order.trans[OF heapsort_correct])
      apply simp apply simp
      apply(rule SPEC_timerefine)
      subgoal by (auto simp: slice_eq_mset_alt)
      subgoal by(simp add: timerefineA_update_apply_same_cost)
      done
    done
  
end


subsection \<open>Synthesis of LLVM Code\<close>

concrete_definition heapsort1 for less xs\<^sub>0 l h\<^sub>0 is weak_ordering.heapsort_def


context weak_ordering begin  
  lemmas heapsort1_correct = heapsort_correct'[unfolded heapsort1.refine[OF weak_ordering_axioms]]
end

context heap_context begin

end

context size_t_context begin

sepref_register mop_lchild3 mop_rchild3 mop_has_rchild3 mop_has_lchild3 mop_geth3  mop_seth3  
sepref_def mop_lchild_impl [llvm_inline] is "uncurry mop_lchild3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mop_lchild3_def apply (annot_snat_const "TYPE ('size_t)")
  by sepref

sepref_def mop_rchild_impl [llvm_inline] is "uncurry mop_rchild3" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding mop_rchild3_def apply (annot_snat_const "TYPE ('size_t)")
  by sepref

sepref_def has_lchild_impl [llvm_inline] is "uncurry2 mop_has_lchild3" :: "[\<lambda>((l,h),i). l\<le>h]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding mop_has_lchild3_def apply (annot_snat_const "TYPE ('size_t)") by sepref

sepref_def has_rchild_impl [llvm_inline] is "uncurry2 mop_has_rchild3" :: "[\<lambda>((l,h),i). l<h]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding mop_has_rchild3_def apply (annot_snat_const "TYPE ('size_t)") by sepref 

sepref_def mop_geth_impl [llvm_inline] is "uncurry3 mop_geth3" 
  (*:: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (eoarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a eoarray_assn elem_assn" *)
  :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (eoarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ((_,ai),_). elem_assn \<times>\<^sub>a cnc_assn (\<lambda>x. x=ai) (eoarray_assn elem_assn))"
  unfolding mop_geth3_def
  unfolding mop_oarray_extract_def[symmetric]
  by sepref
  
sepref_def mop_seth_impl [llvm_inline] is "uncurry4 mop_seth3" 
  :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (eoarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ (((_,ai),_),_). cnc_assn (\<lambda>x. x=ai) (eoarray_assn elem_assn))"
  unfolding mop_seth3_def  
  unfolding mop_oarray_upd_def[symmetric] thm mop_oarray_extract_def[symmetric]
  by sepref
   
end

context sort_impl_context begin

subsubsection \<open>sift_down5\<close>

  definition sift_down5 :: " _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list, _) nrest" where "sift_down5 l h i\<^sub>0 xs \<equiv> doN {
    ASSERT (l\<le>i\<^sub>0 \<and> i\<^sub>0<h);
    i\<^sub>1 \<leftarrow> SPECc2 ''sub'' (-) i\<^sub>0 l;
    xs \<leftarrow> mop_to_eo_conv xs;
    (v,xs) \<leftarrow> mop_geth3 l h xs i\<^sub>1;
    
    (xs,i,_) \<leftarrow> monadic_WHILEIT (\<lambda>(xs,i,ctd). i<h-l \<and> i\<ge>i\<^sub>1)
       (\<lambda>(xs,i,ctd). do { hrc \<leftarrow> mop_has_rchild3 l h i;
                          SPECc2 ''and'' (\<and>) hrc ctd }) (\<lambda>(xs,i,ctd). doN {
      lci \<leftarrow> mop_lchild3 h i;
      rci \<leftarrow> mop_rchild3 h i;

      ASSERT (l+lci<h \<and> l+rci<h \<and> l+lci \<noteq> l+rci);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      lprci \<leftarrow> SPECc2 ''add'' (+) l rci;
      ASSERT (lplci \<noteq> lprci);
      b \<leftarrow> cmpo_idxs2' xs lplci lprci;
      
      MIf b (doN {
        b \<leftarrow> cmpo_v_idx2' xs v lprci;
        MIf b ( doN {
          (rc,xs) \<leftarrow> mop_geth3 l h xs rci;
          xs \<leftarrow> mop_seth3 l h xs i rc;
          RETURN (xs,rci,True)
        } ) (  RETURN (xs,i,False) )
      } ) ( doN {
        b \<leftarrow> cmpo_v_idx2' xs v lplci;
        MIf b ( doN {
          (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
          xs \<leftarrow> mop_seth3 l h xs i lc;
          RETURN (xs,lci,True)
        } ) ( RETURN (xs,i,False) )
      } )
    }) (xs,i\<^sub>1,True);
    
    ASSERT (i\<ge>i\<^sub>1);
    
    hlc \<leftarrow> mop_has_lchild3 l h i;
    MIf hlc ( doN {
      lci \<leftarrow> mop_lchild3 h i;
      ASSERT (l+lci<h);
      lplci \<leftarrow> SPECc2 ''add'' (+) l lci;
      b \<leftarrow> cmpo_v_idx2' xs v lplci;
      MIf b ( doN {
        (lc,xs) \<leftarrow> mop_geth3 l h xs lci;
        xs \<leftarrow> mop_seth3 l h xs i lc;
        xs \<leftarrow> mop_seth3 l h xs lci v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      } )( doN {
        xs \<leftarrow> mop_seth3 l h xs i v;
        xs \<leftarrow> mop_to_wo_conv xs;
        RETURN xs
      }  )
    } )( doN {
      xs \<leftarrow> mop_seth3 l h xs i v;
      xs \<leftarrow> mop_to_wo_conv xs;
      RETURN xs
    }  )
  }" 


lemma mop_geth3_refine_aux1: "enat (Suc 0) = 1" by (simp add: one_enat_def)

lemma mop_geth3_refine:
  assumes 
     "preserves_curr TR ''add''"
   and "preserves_curr TR ''load''"
   and "preserves_curr TR ''ofs_ptr''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id  \<Longrightarrow> (h,h')\<in>Id  \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_geth3 h l a b \<le> \<Down> Id (timerefine TR (mop_geth3 h' l' a' b'))"
  unfolding mop_geth3_def mop_eo_extract_def
  apply(intro refine0 bindT_refine_easy SPECc2_refine)
  apply refine_dref_type
  using assms    
  by (auto simp: mop_geth3_refine_aux1 norm_cost preserves_curr_def)

lemma  mop_seth3_refine:
  fixes TR :: "_ \<Rightarrow> (_, enat) acost"
  assumes 
     "preserves_curr TR ''add''"
   and "preserves_curr TR ''store''"
   and "preserves_curr TR ''ofs_ptr''"
  shows "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> wfR'' TR \<Longrightarrow> mop_seth3 h l a b c \<le> \<Down> Id (timerefine TR (mop_seth3 h' l' a' b' c'))"
    
  unfolding mop_seth3_def mop_eo_set_def
  apply(intro refine0 bindT_refine_easy SPECc2_refine)
  apply refine_dref_type
  using assms   
  by (auto simp: norm_cost preserves_curr_def ) 



lemma mop_has_rchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''sub''"
  assumes "preserves_curr TR ''udiv''"
  assumes "preserves_curr TR ''icmp_slt''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id   \<Longrightarrow> (h,h')\<in>Id  \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_has_rchild3 h l a \<le> \<Down> bool_rel (timerefine TR (mop_has_rchild3 h' l' a'))"
  unfolding mop_has_rchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  by (auto simp: norm_cost preserves_curr_def ) 

lemma mop_lchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''mul''"
  assumes "preserves_curr TR ''add''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_lchild3 l a \<le> \<Down> Id (timerefine TR (mop_lchild3 l' a'))"
  unfolding mop_lchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  by (auto simp: norm_cost preserves_curr_def ) 

lemma mop_rchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''mul''"
  assumes "preserves_curr TR ''add''"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> mop_rchild3 l a \<le> \<Down> Id (timerefine TR (mop_rchild3 l' a'))"
  unfolding mop_rchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  by (auto simp: norm_cost preserves_curr_def ) 

lemma mop_has_lchild3_refine:
  fixes TR :: "_ \<Rightarrow> ecost"
  assumes "preserves_curr TR ''sub''"
  assumes "preserves_curr TR ''udiv''"
  assumes "preserves_curr TR ''icmp_slt''"
  assumes "(h,h')\<in>Id" "(l,l')\<in>Id"
  shows "wfR'' TR \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> mop_has_lchild3 h l a \<le> \<Down> bool_rel (timerefine TR (mop_has_lchild3 h' l' a'))"
  unfolding mop_has_lchild3_def SPECc2_alt
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  apply refine_dref_type
  using assms    
  by (auto simp: norm_cost preserves_curr_def ) 



lemma cmpo_idxs2'_refines_mop_cmpo_idxs_with_E':
  "b'\<noteq>c' \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
    cmpo_idxs2' a b c \<le> \<Down> bool_rel (timerefine TR_cmp_swap (mop_cmpo_idxs (cost ''cmpo_idxs'' 1) a' b' c'))"
  apply(rule cmpo_idxs2'_refines_mop_cmpo_idxs_with_E)
  by (auto simp: timerefineA_update_apply_same_cost')
  

lemma  cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E':
 "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id
     \<Longrightarrow> cmpo_v_idx2' a b c \<le> \<Down> bool_rel (timerefine TR_cmp_swap (mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) a' b' c'))"
  apply(rule cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E)
  by (auto simp: timerefineA_update_apply_same_cost')
  

lemma sift_down5_refine_flexible: 
  assumes "(l,l')\<in>Id" "(h,h')\<in>Id" "(i\<^sub>0,i\<^sub>0')\<in>Id" "(xs,xs')\<in>Id"
  shows " sift_down5 l h i\<^sub>0 xs \<le> \<Down>Id (timerefine TR_cmp_swap (sift_down4 (\<^bold><) l' h' i\<^sub>0' xs'))"
  using assms
  supply conc_Id[simp del] mop_cmpo_v_idx_def[simp del]
  unfolding sift_down5_def sift_down4_def
  supply [refine] =
    mop_to_eo_conv_refine
    mop_geth3_refine
    mop_seth3_refine
    mop_has_rchild3_refine
    mop_has_lchild3_refine
    mop_lchild3_refine
    mop_rchild3_refine
    mop_to_wo_conv_refines
    cmpo_idxs2'_refines_mop_cmpo_idxs_with_E'
    cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E'
  apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
  apply refine_dref_type
  apply(all \<open>(intro  preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  apply (simp_all (no_asm))
  apply auto
  done


subsubsection \<open>heapify_btu3\<close>

  definition "heapify_btu3 l h xs\<^sub>0 \<equiv> doN {
    ASSERT(h>0);
    h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
    (xs,l') \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
      (\<lambda>(xs,l'). SPECc2 ''icmp_slt'' (<) l l') 
      (\<lambda>(xs,l'). doN {
        ASSERT (l'>0);
        l'' \<leftarrow> SPECc2 ''sub'' (-) l' 1;
        xs \<leftarrow> sift_down5 l h l'' xs;
        RETURN (xs,l'')
      })
      (xs\<^sub>0,h');
    RETURN xs
  }"   


lemma heapify_btu3_refine: "(l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id \<Longrightarrow> (xs\<^sub>0,xs\<^sub>0')\<in>Id \<Longrightarrow> heapify_btu3 l h xs\<^sub>0 \<le> \<Down> Id (timerefine TR_cmp_swap (heapify_btu2 (\<^bold><) l' h' xs\<^sub>0'))"
  supply conc_Id[simp del] 
  unfolding heapify_btu3_def heapify_btu2_def
  supply SPECc2_refine'[refine]
  supply sift_down5_refine_flexible[refine]
  apply(refine_rcg bindT_refine_easy monadic_WHILEIT_refine')
  apply refine_dref_type 
  apply(all \<open>(intro preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  by auto


subsubsection \<open>heapsort3\<close>

  definition heapsort3 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "heapsort3 xs\<^sub>0 l h\<^sub>0 \<equiv> doN {
    ASSERT (l\<le>h\<^sub>0);
    hl \<leftarrow> SPECc2 ''sub'' (-) h\<^sub>0 l;
    b \<leftarrow> SPECc2 ''icmp_slt'' (<) 1 hl;
    MIf b (doN {
      xs \<leftarrow> heapify_btu3 l h\<^sub>0 xs\<^sub>0;
      
      (xs,h)\<leftarrow> monadic_WHILEIT (\<lambda>(xs,h).  True )
        (\<lambda>(xs,h). doN { l' \<leftarrow> SPECc2 ''add'' (+) l 1;
                        SPECc2 ''icmp_slt'' (<) l' h }) 
        (\<lambda>(xs,h). doN {
          ASSERT (h>0 \<and> l\<noteq>h-1);
          h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
          xs \<leftarrow> myswap xs l h';
          xs \<leftarrow> sift_down5 l h' l xs;
          RETURN (xs,h')
        })
        (xs,h\<^sub>0);
      
      RETURN xs
    } ) (
      RETURN xs\<^sub>0 )
  }"



lemma heapsort3_refine:
  fixes xs\<^sub>0 :: "'a list" 
  shows "(xs\<^sub>0,xs\<^sub>0')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h\<^sub>0,h\<^sub>0')\<in>Id \<Longrightarrow> heapsort3  xs\<^sub>0 l h\<^sub>0 \<le> \<Down>Id (timerefine TR_cmp_swap (heapsort2 xs\<^sub>0' l' h\<^sub>0'))" 
  unfolding heapsort3_def heapsort2_def
  supply conc_Id[simp del] 
  supply SPECc2_refine'[refine]
  supply heapify_btu3_refine[refine]
  supply sift_down5_refine_flexible[refine]
  supply myswap_TR_cmp_swap_refine[refine]
  apply(refine_rcg bindT_refine_conc_time_my_inres MIf_refine monadic_WHILEIT_refine')
  apply refine_dref_type 
  apply(all \<open>(intro preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
  by (auto simp: SPECc2_def)


subsubsection \<open>synthesize with Sepref\<close>

sepref_register "sift_down5"
sepref_def sift_down_impl [llvm_inline] is "uncurry3 (PR_CONST sift_down5)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a (array_assn elem_assn)"
  unfolding sift_down5_def PR_CONST_def
  supply [[goals_limit = 1]]
  apply sepref_dbg_preproc
     apply sepref_dbg_cons_init
    apply sepref_dbg_id  
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
      apply sepref_dbg_trans (* Takes loooong! *)

  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints 
  done


  

sepref_register "heapify_btu3"
sepref_def heapify_btu_impl [llvm_inline] is "uncurry2 (PR_CONST (heapify_btu3))" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (array_assn elem_assn)\<^sup>d \<rightarrow>\<^sub>a (array_assn elem_assn)"
  unfolding heapify_btu3_def PR_CONST_def
  apply (annot_snat_const "TYPE ('size_t)")
  supply [[goals_limit = 1]]
  apply sepref
  done
  
sepref_register "heapsort3"
sepref_def heapsort_impl is "uncurry2 (PR_CONST (heapsort3))" :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a (array_assn elem_assn)"
  unfolding heapsort3_def unfolding myswap_def PR_CONST_def
  apply (rewrite at "sift_down5 _ _ \<hole> _" fold_COPY)
  apply (annot_snat_const "TYPE ('size_t)")
  by sepref

lemmas heapsort_hnr[sepref_fr_rules] = heapsort_impl.refine[unfolded heapsort1.refine[OF weak_ordering_axioms,symmetric]]  


subsection \<open>Final Correctness Lemma\<close>

schematic_goal heapsort3_correct:
  "heapsort3 xs l h \<le> \<Down> Id (timerefine ?E (slice_sort_spec (\<^bold><) xs l h))"
  unfolding slice_sort_spec_def
  apply(cases "l \<le> h \<and> h \<le> length xs")
   prefer 2 
  subgoal by auto
  apply simp

  apply(rule order.trans)
   apply(rule heapsort3_refine[of xs xs l l h h])
     apply simp_all

  apply(rule order.trans)
   apply(rule timerefine_mono2) apply simp
   apply(rule heapsort_correct'[of xs xs l l h h])
    apply simp
    apply simp
   apply simp

  unfolding slice_sort_spec_def apply simp
  apply (subst timerefine_iter2)  
    apply simp
   apply simp
  apply(rule order.refl)
  done

  
concrete_definition heapsort3_TR is heapsort3_correct uses "_ \<le> \<Down> Id (timerefine \<hole> _) "
                                              
  


lemmas heapsort_correct_hnr = hn_refine_result[OF heapsort_impl.refine[to_hnr],
                                              unfolded PR_CONST_def APP_def,
                                              OF heapsort3_TR.refine ]

lemma pull_heapsort3_TR_into_spec: "(timerefine (heapsort3_TR l h) (slice_sort_spec (\<^bold><) xs l h))
    = slice_sort_specT (heapsort3_TR l h ''slice_sort'') (\<^bold><) xs l h"
  unfolding slice_sort_spec_def slice_sort_specT_def
  apply(cases "l \<le> h \<and> h \<le> length xs")
   apply(auto simp: SPEC_timerefine_conv)
  apply(rule SPEC_cong) apply simp
  by (auto simp: timerefineA_cost)

lemma heapsort_impl_correct:
 "hn_refine (hn_ctxt arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi)
       (heapsort_impl ai bia bi)
 (hn_invalid arr_assn a ai \<and>* hn_val snat_rel ba bia \<and>* hn_val snat_rel b bi) (hr_comp arr_assn Id)
  (timerefine (heapsort3_TR ba b) (slice_sort_spec (\<^bold><) a ba b))"
  apply(rule heapsort_correct_hnr)
  apply(rule attains_sup_sv) by simp

text \<open>extract Hoare Triple\<close>

lemmas heapsort_ht = heapsort_impl_correct[unfolded slice_sort_spec_def SPEC_REST_emb'_conv,
                                          THEN ht_from_hnr]


lemma ub_heapsort3_yx: "y - Suc x = (y - x) - 1"
  by auto
  

find_theorems "_+(_*_) = _*_ + _*_"

find_theorems "_ *m cost _ _"


find_theorems "_ *m _ + _ *m _"

find_theorems timerefineA cost


thm timerefineA_propagate

find_theorems "_ ?a ?b \<equiv> ?a=?b"

definition "EQ_TAG a b \<equiv> a=b"
lemma EQ_TAG_refl: "EQ_TAG a a" unfolding EQ_TAG_def by auto
lemma EQ_TAG_cong[cong]: "a=a' \<Longrightarrow> EQ_TAG a b = EQ_TAG a' b" by simp


lemma timerefine_apply1: "wfR'' TR \<Longrightarrow> EQ_TAG (TR n) TRn \<Longrightarrow> EQ_TAG (t *m TRn) (tt')  \<Longrightarrow> timerefineA TR (cost n t + x) = tt' + timerefineA TR x" 
  for TR :: "string \<Rightarrow> (string, enat) acost"
  unfolding EQ_TAG_def
  by (simp add: timerefineA_propagate timerefineA_cost_apply_costmult)
  
lemma timerefine_apply2: "EQ_TAG (TR n) TRn \<Longrightarrow> EQ_TAG (t *m TRn) (tt')  \<Longrightarrow> timerefineA TR (cost n t) = tt'" 
  for TR :: "string \<Rightarrow> (string, enat) acost"
  unfolding EQ_TAG_def
  by (simp add: timerefineA_propagate timerefineA_cost_apply_costmult)
  
method apply_timerefine = 
  ((subst timerefine_apply1, (intro wfR''_upd wfR''_TId; fail)) | subst timerefine_apply2),
  (simp named_ss Main_ss: TId_apply; rule EQ_TAG_refl),
  ((simp named_ss Main_ss: costmult_add_distrib costmult_cost)?; rule EQ_TAG_refl)

method summarize_and_apply_tr =
  summarize_same_cost, (apply_timerefine+,summarize_same_cost)+  
  
  
find_theorems "_ *m (_+_)"  
find_theorems "_ *m cost _ _"  
  
thm numeral_One

lemma "1+enat n = enat (1+n)" 
  by (metis one_enat_def plus_enat_simps(1))

lemma "numeral k + enat n = enat (numeral k+n)" 
  using numeral_eq_enat plus_enat_simps(1) by presburger
  
find_theorems "_*?a+_*?a = _*_"  
  
context
  fixes l h :: nat and hml hmsl
  defines "hml \<equiv> h-l"
  defines "hmsl \<equiv> h-Suc l"
begin
schematic_goal ub_heapsort3': "timerefineA (heapsort3_TR l h) (cost ''slice_sort'' 1) \<le> ?x"
  unfolding heapsort3_TR_def heapsort_TR_def singleton_heap_context.sift_down3_cost_def
      Rsd_a_def heapsort_time_def  heapsort_lbc_def
  unfolding singleton_heap_context.E_sd3_l_def
  unfolding myswap_cost_def cmpo_idxs2'_cost_def cmpo_v_idx2'_cost_def cmp_idxs2'_cost_def
  apply (fold hml_def hmsl_def)
  apply(simp add: norm_pp norm_cost)
  apply summarize_and_apply_tr
  
  apply (simp add: add_ac numeral_eq_enat one_enat_def left_add_twice)
  by (rule order_refl)
  
end

text \<open>and give it a name\<close>
concrete_definition heapsort3_acost' is ub_heapsort3' uses "_ \<le> \<hole>"

thm heapsort3_acost'_def

lemma enat_mono: "x\<le>y \<Longrightarrow> enat x \<le> enat y"
  by simp

lemma approx_aux: "h - Suc l \<le> h - l"
  by auto

lemma Suc_le_monoI: "x\<le>y \<Longrightarrow> Suc x \<le> Suc y" by blast 
lemma costmult_le_monoI: "n\<le>n' \<Longrightarrow> n *m c \<le> n' *m c" for n n' :: enat 
  apply (cases c)
  apply (auto simp add: costmult_def less_eq_acost_def ) 
  by (simp add: mult_right_mono)


text \<open>estimate "h-(l+1)" with "h-l"\<close>
schematic_goal aprox: "heapsort3_acost' l h \<le> ?x"
  unfolding heapsort3_acost'_def
  (* TODO: This is an excellent example for setoid rewriting! *)
  supply mono_rls = cost_mono add_mono enat_mono  mult_le_mono log_mono[THEN monoD] Suc_le_monoI costmult_le_monoI
  supply refl_rules = order_refl
  apply (rule order_trans)
  apply (repeat_all_new \<open>determ \<open>rule approx_aux mono_rls\<close>\<close>; rule refl_rules)
  apply (simp add: add_ac left_add_twice flip: mult_2 )
  apply (rule order_refl)
  done

thm order.trans[OF heapsort3_acost'.refine aprox]


concrete_definition heapsort_impl_cost is order.trans[OF heapsort3_acost'.refine aprox]  uses "_ \<le> \<hole>"

lemma lift_acost_push_mult: "enat n *m lift_acost c = lift_acost (n *m c)"
  apply (cases c)
  apply (auto simp: lift_acost_def costmult_def)
  done



find_theorems "lift_acost" "(*m)"

text \<open>we pull the lifting to the outer most:\<close>
schematic_goal lift_heapsort3_acost: "heapsort_impl_cost x y = lift_acost ?y"
  unfolding heapsort_impl_cost_def
  unfolding lift_acost_cost[symmetric]  lift_acost_propagate[symmetric] lift_acost_push_mult
  unfolding ub_heapsort3_yx[where x=x and y=y]
  apply(rule refl)
  done

text \<open>We define the finite part of the cost expression:\<close>
concrete_definition heapsort3_cost is lift_heapsort3_acost uses "_ = lift_acost \<hole>"

abbreviation "slice_sort_aux xs\<^sub>0 xs l h \<equiv> (length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0
                    \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice l h xs\<^sub>0) (slice l h xs))"

lemma heapsort_final_hoare_triple_aux:
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($heapsort_impl_cost l h \<and>* hn_ctxt arr_assn xs\<^sub>0 p
           \<and>* hn_val snat_rel l l' \<and>* hn_val snat_rel h h')
        (heapsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
           \<and>* hn_invalid arr_assn xs\<^sub>0 p \<and>* hn_val snat_rel l l' \<and>* hn_val snat_rel h h')"
  using assms    
  by(rule  llvm_htriple_more_time[OF heapsort_impl_cost.refine heapsort_ht,
                unfolded  hr_comp_Id2  ])

(* TODO: Move *)
lemma sep_conj_pred_lift: "(A \<and>* (pred_lift B)) s = (A s \<and> B)"
  apply(cases B) by (auto simp: pure_true_conv)

lemma heapsort_final_hoare_triple:
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($heapsort_impl_cost l h \<and>* arr_assn xs\<^sub>0 p
           \<and>* snat_assn l l' \<and>* snat_assn h h')
        (heapsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
            \<and>* snat_assn l l' \<and>* snat_assn h h')"
  apply(rule cons_post_rule) (* TODO: very ugly proof to get rid of the invalid_assn! *)
   apply (rule heapsort_final_hoare_triple_aux[OF assms, unfolded hn_ctxt_def])
  apply(simp add: pred_lift_extract_simps  invalid_assn_def pure_part_def)
  apply(subst (asm) (2) sep_conj_commute)
  apply(subst (asm) (1) sep_conj_assoc[symmetric])
  apply(subst (asm) sep_conj_pred_lift) by simp



  
  
lemma sum_any_push_costmul: "Sum_any (the_acost (n *m c)) = n * (Sum_any (the_acost c))" for n :: nat 
  apply (cases c) subgoal for x
  apply (auto simp: costmult_def algebra_simps) 
  apply (cases "finite {a. x a \<noteq> 0}"; cases "n=0")
  apply (simp_all add: Sum_any_right_distrib)
  done done
  

text \<open>Calculate the cost for all currencies:\<close>
schematic_goal heapsort3_cost_Sum_any_calc: 
  shows "project_all (heapsort_impl_cost l h) = ?x"
  unfolding norm_cost_tag_def[symmetric]
  apply(subst project_all_is_Sumany_if_lifted[OF heapsort3_cost.refine])
  unfolding heapsort3_cost_def
  apply(simp add: the_acost_propagate add.assoc) 
  supply acost_finiteIs = finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero finite_the_acost_mult_nonzeroI lt_acost_finite
  
  apply (subst Sum_any.distrib, (intro acost_finiteIs;fail), (intro acost_finiteIs;fail))+
  apply (simp only: Sum_any_cost sum_any_push_costmul)
  apply (simp add: add_ac)
  
  apply(rule norm_cost_tagI)
  done

text \<open>Give the result a name:\<close>
concrete_definition (in -) heapsort3_allcost' is sort_impl_context.heapsort3_cost_Sum_any_calc
    uses "_ = \<hole>"

thm heapsort3_allcost'_def      
    
lemma heapsort3_allcost'_Sum_any: 
  shows "heapsort3_allcost' lt_acost l h = project_all (heapsort_impl_cost l h)"  
  apply(subst heapsort3_allcost'.refine[OF sort_impl_context_axioms, symmetric])
  by simp

end  

lemma heapsort3_allcost'_simplified:
  "heapsort3_allcost' lt_acost l h = 
    12 
    + 181 * (h - l)  
    + 6 * (h - l) * Sum_any (the_acost lt_acost)
    + 78 * (h - l) * Discrete.log (h - l)
    + 4 * (h - l) * Sum_any (the_acost lt_acost) * (Discrete.log (h - l))
    "
  unfolding heapsort3_allcost'_def
  apply (simp add: algebra_simps del: algebra_simps(19,20) )
  done

(*
lemma heapsort3_allcost'_simplified:
  "heapsort3_allcost' lt_acost l h = 12 + 187 * (h - l)  + 82 * (h - l) * Discrete.log (h - l)"
  unfolding heapsort3_allcost'_def
  apply (simp add: algebra_simps del: algebra_simps(19,20) )
  done
*)  

definition "heapsort3_allcost n = 12 + 187 * n  + 82 * (n * Discrete.log n)"


lemma heapsort3_allcost_simplified:
  "heapsort3_allcost n = 12 + 187 * n  + 82 * n * Discrete.log n"
  unfolding heapsort3_allcost_def
  by simp

(* TODO: Show under assumption on lt_acost!    
lemma heapsort3_allcost_is_heapsort3_allcost': 
  "heapsort3_allcost (h-l) = heapsort3_allcost' l h"
  unfolding heapsort3_allcost_def heapsort3_allcost'_simplified by auto
*)

lemma heapsort3_allcost_nlogn:
  "(\<lambda>x. real (heapsort3_allcost x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  unfolding heapsort3_allcost_def
  by auto2




end
