(* authors:
    Vincent Trélat <vincent.trelat@depinfonancy.net>
    Peter Lammich  <lammich@in.tum.de>
*)

section \<open>Running-time analysis of Hopcroft's algorithm\<close>

theory Hopcroft_Time
  imports
    "Isabelle_LLVM_Time.NREST_Main"
    Hopcroft_Thms
    "HOL-Library.Discrete"
begin



(* TODO: Add type constraint to definition *)  
abbreviation monadic_WHILEIET :: 
  "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> (char list, nat) acost) \<Rightarrow>
   ('b \<Rightarrow> (bool, (char list, enat) acost) nrest) \<Rightarrow>
   ('b \<Rightarrow> ('b, (char list, enat) acost) nrest) \<Rightarrow> 'b \<Rightarrow> ('b, (char list, enat) acost) nrest"
  where "monadic_WHILEIET I E b f s \<equiv> NREST.monadic_WHILEIET I E b f s"


text
\<open>
  Abstract level I
    def: Hopcroft_abstract
\<close>

definition "preds \<A> a C \<equiv> {q. \<exists>q'. (q,a,q')\<in>\<Delta> \<A> \<and> q'\<in>C }"

definition "pick_splitter_spec \<equiv> \<lambda>(P,L). do {
  ASSERT (L \<noteq> {});
  SPEC (\<lambda>(a,p). (a,p) \<in> L) (\<lambda>_. cost ''pick_splitter'' 1)
}"

definition "update_split_spec \<A> \<equiv> \<lambda>(P,L) a p. 
  SPEC (\<lambda>(P', L'). Hopcroft_update_splitters_pred \<A> p a P L L' 
                \<and> P' = Hopcroft_split \<A> p a {} P)
    (\<lambda>_. cost ''update_split'' (enat (card (\<Sigma> \<A>) * card (preds \<A> a p))))"


definition Hopcroft_abstract_f where
"Hopcroft_abstract_f \<A> = 
 (\<lambda>PL. do {
     ASSERT (Hopcroft_abstract_invar \<A> PL);                             
     (a,p) \<leftarrow> pick_splitter_spec PL;
     PL' \<leftarrow> update_split_spec \<A> PL a p;
     RETURNT PL'
   })"


definition "check_b_spec \<equiv> \<lambda>PL. consume (RETURNT (Hopcroft_abstract_b PL)) (cost ''check_l_empty'' 1)"   
   
definition "init_spec \<A> \<equiv> consume (RETURNT (Hopcroft_abstract_init \<A>)) (cost ''init_state'' 1)"

definition "check_states_empty_spec \<A> \<equiv> consume (RETURNT (\<Q> \<A> = {})) (cost ''check_states_empty'' 1)"

definition "check_final_states_empty_spec \<A> \<equiv> consume (RETURNT (\<F> \<A> = {})) (cost ''check_final_states_empty'' 1)"



definition mop_partition_empty :: "('a set set, _) nrest" where
  [simp]: "mop_partition_empty \<equiv> consume (RETURNT {}) (cost ''part_empty'' 1)"

definition mop_partition_singleton :: "'a set \<Rightarrow> ('a set set, _) nrest" where
  [simp]: "mop_partition_singleton s \<equiv> consume (RETURNT {s}) (cost ''part_singleton'' 1)"


text
\<open>
Formula in the paper proof:
For \<A>, (P, L),
\<Sum>{card (preds \<A> a C) * \<lfloor>log (real (card C))\<rfloor>. (a, C) \<in> L} + \<Sum>{card (preds \<A> a B) * \<lfloor>log (real (card B) / 2)\<rfloor>. (a, B) \<in> ((\<Sigma> \<A>)\<times>P) - L)}
\<close>

definition "estimate1 \<A> \<equiv> \<lambda>(P,L).
  \<Sum>{(card (preds \<A> (fst s) (snd s))) * (Discrete.log (card (snd s))) | s. s \<in> L} +
  \<Sum>{(card (preds \<A> (fst s) (snd s))) * (Discrete.log (card (snd s) div 2)) | s. s \<in> \<Sigma> \<A> \<times> P - L}"\<comment>\<open>@{term s} is a splitter (a, C).}\<close>
  
definition "cost_1_iteration \<equiv> 
  cost ''call'' 1 +
  cost ''check_l_empty'' 1 +
  cost ''if'' 1 +
  cost ''pick_splitter'' 1 +
  cost ''update_split'' 1"
  
definition estimate_iteration where
  "estimate_iteration \<A> PL \<equiv> estimate1 \<A> PL *m cost_1_iteration"

definition Hopcroft_abstractT where
  "Hopcroft_abstractT \<A> \<equiv>
   (if\<^sub>N (check_states_empty_spec \<A>) then mop_partition_empty else (
    if\<^sub>N (check_final_states_empty_spec \<A>) then mop_partition_singleton (\<Q> \<A>) else (
       do {
         PL \<leftarrow> init_spec \<A>;
         (P, _) \<leftarrow> monadic_WHILEIET (Hopcroft_abstract_invar \<A>) (\<lambda>s. estimate_iteration \<A> s)
                     check_b_spec
                     (Hopcroft_abstract_f \<A>) PL;
         RETURNT P
       })))"
       
       
lemma costmult_right_mono_nat:
  fixes a :: nat
  shows "a \<le> a' \<Longrightarrow> a *m c \<le> a' *m c"
  unfolding costmult_def less_eq_acost_def
  by (auto simp add: mult_right_mono)  


definition split_pred where
\<comment>\<open>@{term "(a, C)"} is a splitter of B and the result of the split is @{term "{B', B''}"}\<close>
  "split_pred \<A> P B a C B' B'' \<equiv>
    B \<in> P \<and>
    (\<exists> q1 q2. q1 \<in> B \<and> q2 \<in> B \<and>
      (\<exists> q1'. (q1, a, q1') \<in> \<Delta> \<A> \<and> q1' \<in> C) \<and>
      (\<exists> q2'. (q2, a, q2') \<in> \<Delta> \<A> \<and> q2' \<notin> C)) \<and>
    (B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P"

find_theorems "Hopcroft_splitted" "Hopcroft_split"

lemma (in DFA) split_block_in_partition_prop1:
  assumes "P' = Hopcroft_split \<A> C a {} P" "is_partition (\<Q> \<A>) P"
  shows "(B, B', B'') \<in> Hopcroft_splitted \<A> C a {} P \<Longrightarrow> B' \<in> P' \<and> B'' \<in> P' \<and> B \<notin> P'"
  apply (simp add: assms(1))
  unfolding Hopcroft_splitted_def Hopcroft_split_def split_language_equiv_partition_set_def
  apply (simp, intro conjI)
    apply fastforce+
  unfolding split_language_equiv_partition_def split_set_def
  by blast

lemma (in DFA) split_block_in_partition_prop2:
  assumes "split_pred \<A> P B a C B' B''" "Hopcroft_abstract_invar \<A> (P, L)"
  defines "P' \<equiv> Hopcroft_split \<A> C a {} P"
  shows "B' \<in> P' \<and> B'' \<in> P' \<and> B \<notin> P'"
  apply (rule split_block_in_partition_prop1[of P' C a P B B' B''])
    apply (simp add: P'_def)
    apply (simp add: case_prodD[OF assms(2)[simplified Hopcroft_abstract_invar_def is_weak_language_equiv_partition_def]])
    apply (simp add: assms(1)[simplified split_pred_def])
  done

lemma (in DFA) split_block_not_in_workset:
  assumes "(b, C) \<in> L" "split_pred \<A> P B b C B' B''" "(a, B) \<in> L" "a \<in> \<Sigma> \<A>"
          "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_update_splitters_pred \<A> C b P L L'"
        shows "(a, B) \<notin> L' \<and> (a, B') \<in> L' \<and> (a, B'') \<in> L'"
proof (cases "(b, C) = (a, B)")
  case True
  then show ?thesis sorry
next
  case False
  show ?thesis
  apply (rule conjI)
  subgoal sorry
  subgoal
    apply (rule Hopcroft_update_splitters_pred___in_splitted_in_L[of \<A> C b P L L' a B])
       apply (simp add: assms(6))
      apply (simp add: assms(4))
     apply (simp add: assms(2)[simplified split_pred_def])
    using False assms(3)
    apply blast
    done
  done
qed


lemma estimate1_decrease:
  assumes (* "\<Q> \<A> \<noteq> {}" "\<F> \<A> \<noteq> {}" *) 
  "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_abstract_b (P, L)"
  "Hopcroft_update_splitters_pred \<A> p a P L L'"
  shows "estimate1 \<A> (Hopcroft_split \<A> p a {} P, L') \<le> estimate1 \<A> (P,L)"
    (is "estimate1 \<A> (?P', L') \<le> estimate1 \<A> (P, L)")
  unfolding estimate1_def preds_def
  apply simp
  sorry

lemma estimate1_progress:
  assumes (* "\<Q> \<A> \<noteq> {}" "\<F> \<A> \<noteq> {}" *) 
  "Hopcroft_abstract_invar \<A> (P, L)" "Hopcroft_abstract_b (P, L)"
  "Hopcroft_update_splitters_pred \<A> p a P L L'"
  shows "estimate1 \<A> (Hopcroft_split \<A> p a {} P, L')
          + card (\<Sigma> \<A>) * card (preds \<A> a p) < estimate1 \<A> (P,L)" 
  unfolding estimate1_def preds_def
  apply simp
proof -
  show "\<Sum> {card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * Discrete.log (card b) |a b. (a, b) \<in> L'} +
    \<Sum> {card {q. \<exists>q'. (q, aa, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * (Discrete.log (card b) - Suc 0) |aa b. aa \<in> \<Sigma> \<A> \<and> b \<in> Hopcroft_split \<A> p a {} P \<and> (aa, b) \<notin> L'} +
    card (\<Sigma> \<A>) * card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> p}
    < \<Sum> {card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * Discrete.log (card b) |a b. (a, b) \<in> L} +
      \<Sum> {card {q. \<exists>q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> b} * (Discrete.log (card b) - Suc 0) |a b. a \<in> \<Sigma> \<A> \<and> b \<in> P \<and> (a, b) \<notin> L}"
    sorry
qed
  
lemma estimate1_progress_decrease:
  assumes "estimate1 \<A> (Hopcroft_split \<A> ba aa {} a, bb) + f aa ba < estimate1 \<A> (a, b)"
  shows
    "lift_acost c1 + cost ''update_split'' (enat (f aa ba)) +
      lift_acost (estimate1 \<A> (Hopcroft_split \<A> ba aa {} a, bb) *m (c1 + cost ''update_split'' 1)) 
    \<le> lift_acost (estimate1 \<A> (a, b) *m (c1 + cost ''update_split'' 1))"
proof -
  find_theorems lift_acost "(*m)"
  show ?thesis sorry
qed

lemma finite_sum_positive_cost:"finite {a. the_acost (cost n m) a > (0::nat)}"
  using finite_sum_nonzero_cost[of n m]
  by simp

lemma (in DFA) Hopcroft_abstract_correct :
  fixes t
  assumes [simp]: " cost ''part_empty'' 1 + (cost ''if'' 1 + cost ''check_states_empty'' 1) \<le> t"
  assumes [simp]: " cost ''part_singleton'' 1 +
        (cost ''if'' 1 +
         (cost ''check_final_states_empty'' 1 + (cost ''if'' 1 + cost ''check_states_empty'' 1)))
        \<le> t"
  
  shows "Hopcroft_abstractT \<A> \<le> SPEC (\<lambda>P. P = Myhill_Nerode_partition \<A>) (\<lambda>_. t)"
proof (cases "\<Q> \<A> = {} \<or> \<F> \<A> = {}")
  case True thus ?thesis    
    unfolding SPEC_def
    apply -
    apply(rule gwp_specifies_I)
    
    unfolding Hopcroft_abstractT_def check_states_empty_spec_def check_final_states_empty_spec_def
    apply simp
    supply [simp] = \<Q>_not_Emp Myhill_Nerode_partition___\<F>_emp
    apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET If_le_rule)
    done
next
  case False thus ?thesis
    unfolding SPEC_def
    apply -
    apply(rule gwp_specifies_I)

    unfolding Hopcroft_abstractT_def check_states_empty_spec_def check_final_states_empty_spec_def
      init_spec_def check_b_spec_def    
    
    apply (refine_vcg \<open>simp\<close> rules: gwp_monadic_WHILEIET If_le_rule)
    subgoal
      apply (rule wfR2_If_if_wfR2)
      apply (simp add: wfR2_def estimate_iteration_def cost_1_iteration_def
          costmult_def the_acost_propagate Collect_conj_eq)
      apply (intro impI conjI)
      apply (rule finite_sum_positive_cost)+
      done

    subgoal
      unfolding Hopcroft_abstract_f_def pick_splitter_spec_def
        SPEC_REST_emb'_conv update_split_spec_def
      apply (refine_vcg \<open>simp\<close> rules: gwp_ASSERT_bind_I)
      apply (rule loop_body_conditionI)
      subgoal
        apply clarsimp
        apply (rule lift_acost_mono)
        unfolding estimate_iteration_def
        apply (rule costmult_right_mono_nat)
        sorry
      apply clarsimp
      unfolding estimate_iteration_def cost_1_iteration_def
      apply (drule (4) estimate1_progress_decrease)
      
      apply (rule lift_acost_mono)
      
      oops
      apply sc_solve
      apply auto []
      
      
      oops
(*       ci(state) \<ge> const1 + const2*cpreds(splitter) + ci(split(splitter,state)) *)
      
      
(*       estimate1(state) > estimate1(split(splitter,state)) + cpreds(splitter) *)
      
      
      
      unfolding cost_iteration_def cost_1_iteration_def
      
      apply sc_solve
      apply simp
        
      subgoal  
        
        
    apply clarsimp  
    subgoal for P L
        
      
      find_theorems "_ *m _" "(\<le>)"
      
      term lift_acost
      
      find_theorems "SPEC _ (\<lambda>_. ?a)"
      
      subgoal
        apply (simp add: SPEC_def loop_body_condition_def)
        
        
        sorry
      subgoal
        apply (simp add: Hopcroft_abstract_b_def)
        done
      done

  subgoal
    unfolding loop_exit_condition_def
    apply simp
    sorry

  subgoal by (simp add: Hopcroft_abstract_invar_init)

qed

text
\<open>
  Abstract level II
  Refinement of the specification for acquiring next state toward an inner loop.
    def: Hopcroft_set_f
\<close>
(* thm Hopcroft_set_f_def *)

text
\<open>
  Abstract level III
  Precomputation of the set of predecessors of the currently chosen set.
    def: Hopcroft_precompute_step
\<close>
(* thm Hopcroft_precompute_step_def *)

text
\<open>
  First data refinement
  Refinement towards efficient data structures. Partition of \<Q> \<rightarrow> maps
    def: Hopcroft_map
\<close>
(* thm Hopcroft_map_def *)

text
\<open>
  Second data refinement
  Classes as sets \<rightarrow> maps (bijection with natural numbers).
    def: Hopcroft_map2
\<close>
(* thm Hopcroft_map2_def *)

text
\<open>
  Implementation
  Instantiation of the locales
\<close>
(* thm hopcroft_impl_def *)
(* thm hop_impl.Hopcroft_code_def *)


end