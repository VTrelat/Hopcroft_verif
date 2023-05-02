\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Quicksort Partition\<close>
theory Sorting_Quicksort_Partition
imports Sorting_Quicksort_Scheme
begin
hide_const pi
context weak_ordering begin

paragraph \<open>Summary\<close>
text \<open>This theory implements @{term partition3_spec} with the Hoare Partitioning Scheme.\<close>

  
subsection \<open>Find Median\<close>


definition "move_median_to_first ri ai bi ci (xs::'a list) \<equiv> doN {
    ASSERT (ai\<noteq>bi \<and> ai\<noteq>ci \<and> bi\<noteq>ci \<and> ri\<noteq>ai \<and> ri\<noteq>bi \<and> ri\<noteq>ci);
    
    if\<^sub>N mop_cmp_idxs (cost ''cmp_idxs'' 1) xs ai bi then
      if\<^sub>N mop_cmp_idxs (cost ''cmp_idxs'' 1) xs bi ci then
        mop_list_swapN xs ri bi
      else if\<^sub>N mop_cmp_idxs (cost ''cmp_idxs'' 1) xs ai ci then
        mop_list_swapN xs ri ci
      else
        mop_list_swapN xs ri ai
    else  
      if\<^sub>N mop_cmp_idxs (cost ''cmp_idxs'' 1) xs ai ci then
        mop_list_swapN xs ri ai
      else if\<^sub>N mop_cmp_idxs (cost ''cmp_idxs'' 1) xs bi ci then
        mop_list_swapN xs ri ci
      else 
        mop_list_swapN xs ri bi
  }"

definition "move_median_to_first_cost =  cost ''cmp_idxs'' 3 + cost ''if'' 3 + cost ''list_swap'' 1"

lemma move_median_to_first_correct:
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. \<exists>i\<in>{ai,bi,ci}. 
        xs' = swap xs ri i
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<le>xs!j)   
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<ge>xs!j)   
      ) (\<lambda>_. move_median_to_first_cost)"
  unfolding move_median_to_first_def move_median_to_first_cost_def
  unfolding SPEC_def mop_cmp_idxs_def SPECc2_def mop_list_swap_def
  apply(rule gwp_specifies_I)
  apply (refine_vcg \<open>-\<close> rules: If_le_Some_rule2) 
  apply (all \<open>(sc_solve,simp;fail)?\<close>)
  supply aux = bexI[where P="\<lambda>x. _=_ x \<and> _ x", OF conjI[OF refl]]
  apply ((rule aux)?; insert connex,auto simp: unfold_lt_to_le)+
  done
  
    
lemma move_median_to_first_correct':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai,bi,ci}. xs'!i\<^bold>\<ge>xs'!ri)
      ) (\<lambda>_. move_median_to_first_cost)"
  apply (rule order_trans[OF move_median_to_first_correct])    
  by (auto simp: SPEC_def le_fun_def)
  
(* TODO: Clean up prove below, to use more concise aux-lemma! *)  
lemma move_median_to_first_correct'':
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. slice_eq_mset ri (ci+1) xs' xs 
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<le>xs'!ri)
      \<and> (\<exists>i\<in>{ai..ci}. xs'!i\<^bold>\<ge>xs'!ri)
      ) (\<lambda>_. move_median_to_first_cost)"
  apply (rule order_trans[OF move_median_to_first_correct'])  
  by (auto simp: SPEC_def le_fun_def)
  
end

context sort_impl_context begin 

definition "move_median_to_first2 ri ai bi ci (xs::'a list) \<equiv> doN {
    ASSERT (ai\<noteq>bi \<and> ai\<noteq>ci \<and> bi\<noteq>ci \<and> ri\<noteq>ai \<and> ri\<noteq>bi \<and> ri\<noteq>ci);
    
    if\<^sub>N cmp_idxs2' xs ai bi then doN {    
      if\<^sub>N cmp_idxs2' xs bi ci then
        myswap xs ri bi
      else if\<^sub>N cmp_idxs2' xs ai ci then 
        myswap xs ri ci
      else 
        myswap xs ri ai        
    }
    else if\<^sub>N cmp_idxs2' xs ai ci then
      myswap xs ri ai
    else if\<^sub>N cmp_idxs2' xs bi ci then
      myswap xs ri ci
    else
      myswap xs ri bi
  }" 

lemma cmp_idxs2'_refines_mop_cmp_idxs_with_E':
  "b'\<noteq>c' \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
    cmp_idxs2' a b c \<le> \<Down> bool_rel (timerefine TR_cmp_swap (mop_cmp_idxs (cost ''cmp_idxs'' 1) a' b' c'))"
  apply(rule cmp_idxs2'_refines_mop_cmp_idxs_with_E)
  by(auto simp: timerefineA_update_apply_same_cost')

lemma move_median_to_first2_refine':
  assumes "(ri,ri')\<in>Id" "(ai,ai')\<in>Id" "(bi,bi')\<in>Id" "(ci,ci')\<in>Id" "(xs,xs')\<in>Id"
  shows "move_median_to_first2 ri ai bi ci xs \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine TR_cmp_swap (move_median_to_first ri' ai' bi' ci' xs'))"
  using assms
  unfolding move_median_to_first2_def move_median_to_first_def
  supply cmp_idxs2'_refines_mop_cmp_idxs_with_E'[refine]
  supply SPECc2_refine[refine]
  supply myswap_TR_cmp_swap_refine[refine]
  apply(refine_rcg bindT_refine_conc_time_my_inres MIf_refine)
  by(auto intro: struct_preservingI)

definition "move_median_to_first2_cost = 3 *m cmp_idxs2'_cost + myswap_cost + cost ''if'' 3"

lemma move_median_to_first2_correct: 
  "\<lbrakk> ri<ai; ai<bi; bi<ci; ci<length xs \<rbrakk> \<Longrightarrow> 
  move_median_to_first2 ri ai bi ci xs 
    \<le> SPEC (\<lambda>xs'. \<exists>i\<in>{ai,bi,ci}. 
        xs' = swap xs ri i
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<le>xs!j)   
      \<and> (\<exists>j\<in>{ai,bi,ci}-{i}. xs!i\<^bold>\<ge>xs!j)   
      ) (\<lambda>_. move_median_to_first2_cost)"
  apply(rule order.trans[OF move_median_to_first2_refine'])
  apply simp_all [6] 
  apply(rule order.trans)
   apply(rule timerefine_mono2[OF _ move_median_to_first_correct])
       prefer 6
  subgoal apply(simp add: SPEC_timerefine_conv)
    apply(rule SPEC_leq_SPEC_I) apply simp
    by(auto simp: move_median_to_first_cost_def move_median_to_first2_cost_def
            timerefineA_update_apply_same_cost' timerefineA_propagate add.assoc add.commute) 
  by auto  


sepref_register move_median_to_first2

sepref_def move_median_to_first_impl [llvm_inline] is "uncurry4 (PR_CONST move_median_to_first2)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn"
  unfolding move_median_to_first2_def PR_CONST_def
  unfolding myswap_def
  by sepref 
                    
end

context weak_ordering begin  
  
subsection \<open>Hoare Partitioning Scheme\<close>  


definition "ungrd_qsp_next_l_spec T xs pi li hi0 \<equiv> 
  doN {
    ASSERT (pi<li \<and> pi<hi0 \<and> hi0\<le>length xs);
    ASSERT (\<exists>i\<in>{li..<hi0}. xs!i \<^bold>\<ge> xs!pi); 
    SPEC (\<lambda>li'. li\<le>li' \<and> li'<hi0 \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi) \<and> xs!li'\<^bold>\<ge>xs!pi) (\<lambda>li'. T li li')
  }"

definition "ungrd_qsp_next_h_spec T xs pi li0 hi \<equiv> 
  doN {
    ASSERT (pi<li0 \<and> pi<length xs \<and> hi\<le>length xs \<and> (\<exists>i\<in>{li0..<hi}. (xs!i) \<^bold>\<le> xs!pi)); 
    SPEC (\<lambda>hi'. li0\<le>hi' \<and> hi'<hi \<and> (\<forall>i\<in>{hi'<..<hi}. xs!i\<^bold>>xs!pi) \<and> xs!hi'\<^bold>\<le>xs!pi) (\<lambda>hi'. T hi hi')
  }"

text \<open>This is a major insight, limiting the resulting hi' of ungrd_qsp_next_h_spec
      to not surpass the lower limit li0. Similar argument works for the lower pointer being
      limited by hi0.\<close>
lemma "\<lbrakk>\<exists>i\<in>{li0..<hi}. xs ! i \<^bold>\<le> xs!pi; (\<forall>i\<in>{hi'<..<hi}. xs ! pi \<^bold>< xs! i) \<rbrakk> \<Longrightarrow> li0 \<le> hi'" 
    by (meson atLeastLessThan_iff greaterThanLessThan_iff leI less_le_trans wo_leD)
  
  
definition qsp_next_l :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, ecost) nrest" where            
  "qsp_next_l xs pi li hi \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. (\<exists>i\<in>{li'..<hi}. xs!i\<^bold>\<ge>xs!pi) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi)) 
      (\<lambda>li. doN {ASSERT (li\<noteq>pi); mop_cmp_idxs (cost ''cmp_idxs'' 1) xs li pi}) (\<lambda>li. SPECc2 ''add'' (+) li 1) li
  }"  

definition uqnl_body 
  where "uqnl_body \<equiv> (cost ''if'' (1) + cost ''call'' 1
                                                            + cost ''cmp_idxs'' 1)"
definition "ungrd_qsp_next_l_cost li li' = (enat(li'-li+1)) *m uqnl_body + cost ''add'' (enat(li'-li))"

lemma qsp_next_l_refine: "(qsp_next_l,PR_CONST (ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost))\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nrest_rel"
  unfolding qsp_next_l_def ungrd_qsp_next_l_spec_def ungrd_qsp_next_l_cost_def PR_CONST_def
  apply (intro fun_relI nrest_relI; clarsimp)
  apply(rule le_acost_ASSERTI)+
  unfolding SPEC_def mop_cmp_idxs_def SPECc2_def
  subgoal for xs p li hi
    apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>li'. (hi-li') *m (uqnl_body + cost ''add'' 1)"])
    apply(rule gwp_specifies_I) 
    apply (refine_vcg \<open>-\<close>  rules: gwp_monadic_WHILEIET If_le_rule)
    subgoal 
      unfolding wfR2_def apply (auto simp: uqnl_body_def costmult_add_distrib costmult_cost the_acost_propagate zero_acost_def)
      by(auto simp: cost_def zero_acost_def) 
    subgoal for li'
      apply(rule loop_body_conditionI)
      subgoal apply(simp add: uqnl_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        by auto
      subgoal apply(simp add: uqnl_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        apply safe
        subgoal apply auto  
          by (metis Suc_eq_plus1 Suc_n_not_le_n add.commute le_diff_iff' le_trans lift_ord lt_by_le_def lt_by_linorder not_less_eq_eq one_enat_def plus_enat_simps(1))  
        subgoal apply auto  
          by (simp add: one_enat_def)  
        subgoal apply auto  
          by (simp add: one_enat_def)  
        subgoal apply (auto simp add: one_enat_def)
          done
        done
      subgoal 
        by (metis One_nat_def add.commute atLeastLessThan_iff less_Suc_eq less_Suc_eq_le linorder_not_le plus_1_eq_Suc wo_leD)
      done
    subgoal for li'
      apply(rule loop_exit_conditionI)
      apply(rule If_le_Some_rule2)
      subgoal apply(subst costmult_minus_distrib) apply simp
        unfolding uqnl_body_def apply(simp add: costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve
        apply safe
        subgoal apply auto
          by (metis Suc_diff_le add.commute eq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1))
        subgoal apply auto
          by (metis Suc_diff_le eq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1))
        subgoal apply auto
          by (metis Suc_diff_le add.commute eq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1))
        subgoal by auto
        done
      subgoal by (auto simp: unfold_le_to_lt)
      done
    subgoal apply auto done
    subgoal apply auto done
    subgoal apply auto done
    done
  done


definition qsp_next_h :: "'a list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, ecost) nrest" where
  "qsp_next_h xs pi li0 hi \<equiv> doN {
    ASSERT (hi>0);
    hi \<leftarrow> SPECc2 ''sub'' (-) hi 1;
    ASSERT (hi<length xs);
    monadic_WHILEIT (\<lambda>hi'. hi'\<le>hi \<and> (\<exists>i\<le>hi'. xs!i\<^bold>\<le>xs!pi) \<and> (\<forall>i\<in>{hi'<..hi}. xs!i\<^bold>>xs!pi))
      (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); mop_cmp_idxs (cost ''cmp_idxs'' 1) xs pi hi})
      (\<lambda>hi. doN { ASSERT(hi>0); SPECc2 ''sub'' (-) hi 1}) hi
  }"  

definition uqnr_body 
  where "uqnr_body \<equiv> (cost ''if'' (1) + cost ''call'' 1
                                                           + cost ''sub'' 1 + cost ''cmp_idxs'' 1)"
definition "ungrd_qsp_next_r_cost hi hi' =  (enat(hi-hi')) *m uqnr_body"
  
lemma qsp_next_h_refine_aux1: "hi>0 \<Longrightarrow> {hi'<..hi - Suc 0} = {hi'<..<hi}" by auto

lemma qsp_next_h_refine: "(qsp_next_h,PR_CONST (ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost)) \<in> Id  \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
  unfolding qsp_next_h_def ungrd_qsp_next_h_spec_def ungrd_qsp_next_r_cost_def PR_CONST_def 
  apply (intro fun_relI nrest_relI; clarsimp)
  apply(rule le_acost_ASSERTI)+
  unfolding SPEC_def SPECc2_def mop_cmp_idxs_def
  subgoal for xs pi li0 hi
    apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>hi'. (hi'-li0) *m uqnr_body"])
    apply(rule gwp_specifies_I) 
    apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET If_le_rule split_ifI)
    subgoal
      unfolding wfR2_def apply (auto simp: uqnr_body_def costmult_add_distrib costmult_cost the_acost_propagate zero_acost_def)
      by(auto simp: cost_def zero_acost_def) 
    subgoal 
      apply(rule loop_body_conditionI)
      subgoal 
        apply(simp add: uqnr_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        apply safe by auto
      subgoal apply(simp add: uqnr_body_def costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve 
        apply safe
        subgoal apply auto
          by (metis Suc_diff_Suc eq_iff greaterThanAtMost_iff less_le_trans nat_le_Suc_less_imp nat_neq_iff one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD) 
        subgoal apply auto 
          by (metis Suc_diff_Suc add.commute diff_is_0_eq eq_iff greaterThanAtMost_iff le_less_trans nat_le_Suc_less_imp not_gr_zero one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD zero_less_diff)
        subgoal apply auto 
          by (metis Suc_diff_Suc diff_is_0_eq eq_iff greaterThanAtMost_iff le_less_trans nat_le_Suc_less_imp not_gr_zero one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD zero_less_diff)
        subgoal apply auto 
          by (metis Suc_diff_Suc add.commute diff_is_0_eq eq_iff greaterThanAtMost_iff le_less_trans nat_le_Suc_less_imp not_gr_zero one_enat_def plus_1_eq_Suc plus_enat_simps(1) wo_leD zero_less_diff)
        done
      subgoal apply auto 
        subgoal by (metis One_nat_def le_step_down_nat wo_leD)
        subgoal by (metis Suc_lessI Suc_pred greaterThanAtMost_iff)  
        done
      done
    subgoal apply auto  
      by (metis gr0I leD wo_leD)  
    subgoal for hi'
      apply(rule loop_exit_conditionI)
      apply(rule If_le_Some_rule2)
      subgoal  apply(subst costmult_minus_distrib) apply simp
        unfolding uqnr_body_def apply(simp add:  costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost)
        apply sc_solve
        apply(simp add: zero_enat_def one_enat_def) (*
        apply safe
        subgoal by linarith
        subgoal by linarith 
        subgoal
          using \<open>\<And>ia i. \<lbrakk>hi - Suc 0 < length xs; pi \<noteq> hi'; pi < length xs; \<not> xs ! pi \<^bold>< xs ! hi'; cost ''if'' (hi' - pi) + (cost ''call'' (hi' - pi) + (cost ''sub'' (hi' - pi) + cost ''cmp_idxs'' (hi' - pi))) \<le> cost ''if'' (hi - Suc pi) + (cost ''call'' (hi - Suc pi) + (cost ''sub'' (hi - Suc pi) + cost ''cmp_idxs'' (hi - Suc pi))); hi \<le> length xs; i \<in> {pi<..<hi}; xs ! i \<^bold>\<le> xs ! pi; hi' \<le> hi - Suc 0; hi' < hi; \<forall>i\<in>{hi'<..hi - Suc 0}. xs ! pi \<^bold>< xs ! i; \<forall>i\<in>{hi'<..<hi}. xs ! pi \<^bold>< xs ! i; xs ! hi' \<^bold>\<le> xs ! pi; ia \<le> hi'; xs ! ia \<^bold>\<le> xs ! pi\<rbrakk> \<Longrightarrow> Suc (hi - Suc (pi + (hi' - pi))) \<le> hi - hi'\<close> by blast
        *) done
      subgoal
        apply (intro conjI) 
        subgoal unfolding qsp_next_h_refine_aux1  by (meson atLeastLessThan_iff greaterThanLessThan_iff leI less_le_trans wo_leD)  
        subgoal using nat_le_Suc_less by blast
        subgoal by (simp add: nat_le_Suc_less_imp)
        subgoal using wo_leI by blast
        done
      done
    subgoal by auto 
    subgoal by (meson atLeastLessThan_iff dual_order.strict_trans1 greaterThanAtMost_iff nat_le_Suc_less_imp wo_leD) 
    subgoal apply auto
      using nat_le_Suc_less_imp by blast  
    subgoal          
      using nz_le_conv_less by blast  
    subgoal  
      by auto  
    done
  done

definition "qs_partition li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
  ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
  hi \<leftarrow> ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
  
  ASSERT (li\<^sub>0\<le>hi);
  
  (xs,li,hi) \<leftarrow> monadic_WHILEIT 
    (\<lambda>(xs,li,hi). 
        li\<^sub>0\<le>li \<and> hi<hi\<^sub>0
      \<and> li<hi\<^sub>0 \<and> hi\<ge>li\<^sub>0  
      \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
      \<and> xs!pi = xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> xs\<^sub>0!pi)
      \<and> xs!li \<^bold>\<ge> xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. xs!i \<^bold>\<ge> xs\<^sub>0!pi)
      \<and> xs!hi \<^bold>\<le> xs\<^sub>0!pi  
    )
    (\<lambda>(xs,li,hi). SPECc2 ''icmp_slt'' (<) li hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
      xs \<leftarrow> mop_list_swapN xs li hi;
      li \<leftarrow> SPECc2 ''add'' (+) li 1;
      li \<leftarrow> ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost xs pi li hi\<^sub>0;
      hi \<leftarrow> ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost xs pi li\<^sub>0 hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"  

abbreviation "qs_body_cost \<equiv> (cost ''add'' (1::enat) + cost ''sub'' 1
      + cost ''list_swap'' 1 + cost ''if'' 3 + cost ''call'' 3 + cost ''icmp_slt'' 1 + cost ''cmp_idxs'' 2)"
definition "qs_partition_cost xs\<^sub>0 li hi = (enat (hi-li)) *m qs_body_cost"

(* Found useful for ATPs *)
lemma strict_itrans: "a < c \<Longrightarrow> a < b \<or> b < c" for a b c :: "_::linorder"
  by auto
 
lemma qs_partition_correct:
  fixes xs\<^sub>0 :: "'a list"
  shows 
  "\<lbrakk> pi<li; li<hi; hi\<le>length xs\<^sub>0; \<exists>i\<in>{li..<hi}. xs\<^sub>0!pi\<^bold>\<le>xs\<^sub>0!i; \<exists>i\<in>{li..<hi}. xs\<^sub>0!i\<^bold>\<le>xs\<^sub>0!pi \<rbrakk> \<Longrightarrow> qs_partition li hi pi xs\<^sub>0 
  \<le> SPEC (\<lambda>(xs,i). slice_eq_mset li hi xs xs\<^sub>0 \<and> li\<le>i \<and> i<hi \<and> (\<forall>i\<in>{li..<i}. xs!i\<^bold>\<le>xs\<^sub>0!pi) \<and> (\<forall>i\<in>{i..<hi}. xs!i\<^bold>\<ge>xs\<^sub>0!pi) ) (\<lambda>_. qs_partition_cost xs\<^sub>0 li hi )"  
  unfolding qs_partition_def ungrd_qsp_next_l_spec_def ungrd_qsp_next_h_spec_def
  unfolding SPEC_REST_emb'_conv  SPECc2_def mop_list_swap_def
  
  apply(rule gwp_specifies_I)

  apply(subst monadic_WHILEIET_def[symmetric, where E="\<lambda>(xs::'a list,li'::nat,hi'::nat).
             (hi-li') *m (uqnl_body+ cost ''add'' 1) + (hi'-li) *m uqnr_body + (hi'-li') *m (cost ''list_swap'' 1 + cost ''call'' 1 + cost ''icmp_slt'' 1 + cost ''if'' 1) "])
  apply (refine_vcg \<open>-\<close> rules: gwp_RETURNT_I gwp_monadic_WHILEIET If_le_rule split_ifI)  
 
  subgoal unfolding wfR2_def 
    apply safe
    apply (auto simp add: uqnl_body_def uqnr_body_def costmult_add_distrib costmult_cost   the_acost_propagate)
    apply (simp_all add: cost_def zero_acost_def)
    done  
  subgoal  for _ _ _ xs li' hi' li'' hi'' 
    apply(rule loop_body_conditionI)
    subgoal 
      unfolding ungrd_qsp_next_l_cost_def ungrd_qsp_next_r_cost_def uqnl_body_def uqnr_body_def
      apply(simp add: costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      apply sc_solve  by auto   
    subgoal apply simp
      unfolding ungrd_qsp_next_l_cost_def ungrd_qsp_next_r_cost_def uqnl_body_def uqnr_body_def
      apply(simp add: costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      apply sc_solve_debug
      apply safe
      subgoal (* ''list_swap'' *) unfolding sc_solve_debug_def by (simp add: zero_enat_def one_enat_def)
      subgoal (* ''if'' *) unfolding sc_solve_debug_def
        apply(simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) done
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def)
      subgoal (* ''add'' *) unfolding sc_solve_debug_def 
        by(simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) 
      subgoal (* ''cmp_idxs'' *) unfolding sc_solve_debug_def 
        by(simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) 
      subgoal (* ''sub'' *) unfolding sc_solve_debug_def 
        by (simp only: zero_enat_def one_enat_def plus_enat_simps lift_ord) 
      done
    subgoal 
      apply safe
      subgoal by linarith
      subgoal by linarith
      subgoal by (metis atLeastLessThan_iff slice_eq_mset_swap(2) swap_length)
      subgoal by (metis leD swap_indep)
      subgoal apply(simp only: unfold_lt_to_le) apply clarsimp
        apply (smt Suc_leI atLeastLessThan_iff le_def less_le_trans less_Suc_eq swap_indep swap_length swap_nth1)
        done
      subgoal by (metis (full_types) linorder_not_le swap_indep)
      subgoal
          (* this proof is even more crazy *)
        apply(use [[put_named_ss HOL_ss]] in \<open>clarsimp\<close>) 
        apply(use [[put_named_ss Main_ss]] in \<open>simp_all add: slice_eq_mset_eq_length unfold_lt_to_le\<close>)   
        apply clarsimp 
        by (metis greaterThanLessThan_iff less_le_trans linorder_neqE_nat swap_indep swap_nth2) 
      subgoal by (metis (full_types) linorder_not_le swap_indep)
      done
    done
  subgoal apply safe
    subgoal by linarith
    subgoal by linarith
    subgoal by (metis atLeastLessThan_iff linwo swap_indep swap_nth1 weak_ordering.unfold_lt_to_le)
    done
  subgoal by (metis atLeastLessThan_iff discrete less_not_refl linwo swap_indep swap_nth2 weak_ordering.wo_less_le_trans)
  subgoal apply safe
    subgoal by linarith
    subgoal by (simp add: slice_eq_mset_eq_length) 
    done
  subgoal by safe
  subgoal apply safe
    subgoal by (metis (full_types) less_le_trans slice_eq_mset_eq_length)
    subgoal by (metis (full_types) less_le_trans slice_eq_mset_eq_length)
    done
  subgoal
    apply(rule loop_exit_conditionI)
    apply(rule gwp_RETURNT_I)
    unfolding emb'_def
    apply(rule If_le_Some_rule2)
    subgoal 
      apply simp
      apply(subst lift_acost_diff_to_the_right) subgoal 
        by(simp add: cost_zero costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      unfolding ungrd_qsp_next_r_cost_def ungrd_qsp_next_l_cost_def
      unfolding uqnl_body_def uqnr_body_def
      apply simp
      unfolding qs_partition_cost_def
      apply(simp add: cost_zero costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate)
      apply sc_solve_debug
      apply safe
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal (* ''cmp_idxs'' *) unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      subgoal unfolding sc_solve_debug_def by (simp add: one_enat_def numeral_eq_enat)
      done
    subgoal 
      apply safe
      by (metis atLeastLessThan_iff greaterThanLessThan_iff le_eq_less_or_eq strict_itrans)
    done
  subgoal apply simp
    apply safe
    subgoal using unfold_lt_to_le by blast
    subgoal using unfold_lt_to_le by blast
    done

  subgoal (* this one is a central argument, I didn't see this in the beginning - nice one *)
    by (meson atLeastLessThan_iff greaterThanLessThan_iff leI less_le_trans wo_leD)
  subgoal
    apply safe 
    subgoal by linarith
    subgoal by auto
    done
  subgoal by blast
  subgoal 
        using less_trans by blast    
  subgoal apply simp done
  done


definition "partition_pivot xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  hl \<leftarrow> SPECc2 ''sub'' (-) h l;
  d \<leftarrow> SPECc2 ''udiv'' (div) hl 2;
  m \<leftarrow> SPECc2 ''add'' (+) l d;
  l' \<leftarrow> SPECc2 ''add'' (+) l 1;
  h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
  xs\<^sub>1 \<leftarrow> move_median_to_first l l' m h' xs\<^sub>0;
  ASSERT (l<length xs\<^sub>1 \<and> length xs\<^sub>1 = length xs\<^sub>0);
  (xs,m) \<leftarrow> mop_call (qs_partition l' h l xs\<^sub>1);

  \<comment> \<open>TODO: Use an auxiliary lemma, instead of this assertion chain! \<close>
  ASSERT (l<m \<and> m<h);
  ASSERT ((\<forall>i\<in>{l+1..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l) \<and> xs!l\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{m..<h}. xs\<^sub>1!l\<^bold>\<le>xs!i);
  
  
  RETURN (xs,m)
}"

lemma slice_LT_I_aux:
  assumes B: "l<m" "m<h" "h\<le>length xs"
  assumes BND: "\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>p" "\<forall>i\<in>{m..<h}. p\<^bold>\<le>xs!i"
  shows "slice_LT (\<^bold>\<le>) (slice l m xs) (slice m h xs)"
  unfolding slice_LT_def
  using B apply (clarsimp simp: in_set_conv_nth slice_nth)
  subgoal for i j
    apply (rule trans[OF BND(1)[THEN bspec, of "l+i"] BND(2)[THEN bspec, of "m+j"]])
    by auto
  done
  


lemma partition_pivot_correct_aux1: "hi>0 \<Longrightarrow> {hi'..hi - Suc 0} = {hi'..<hi}" by auto

abbreviation "TR_pp \<equiv> (TId(''partition_c'':=qs_body_cost + move_median_to_first_cost + cost ''sub'' 2 + cost ''call'' 2 + cost ''add'' 2 + cost ''udiv'' 1))"

lemma partition_pivot_correct: "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> 
  \<Longrightarrow> partition_pivot xs l h \<le> \<Down>Id (timerefine TR_pp (partition3_spec xs' l' h'))"
  unfolding partition_pivot_def partition3_spec_def
  apply(intro ASSERT_D3_leI)
  apply(subst SPEC_timerefine_conv)
  unfolding SPEC_def SPECc2_def
  apply simp
  apply(rule gwp_specifies_I)
  supply mmtf = move_median_to_first_correct''[unfolded SPEC_def, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
  supply qsp = qs_partition_correct[unfolded SPEC_def, THEN gwp_specifies_rev_I, THEN gwp_conseq_0]
  apply (refine_vcg \<open>-\<close> rules: mmtf qsp If_le_Some_rule2)

  apply(simp_all only: handy_if_lemma)

  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply clarsimp
  subgoal by auto
  subgoal by (metis le_less_trans less_imp_diff_less linorder_not_less partition_pivot_correct_aux1 zero_less_numeral)
  subgoal apply auto
    unfolding move_median_to_first_cost_def qs_partition_cost_def
      apply(auto simp: timerefineA_update_apply_same_cost' costmult_add_distrib costmult_cost lift_acost_cost lift_acost_propagate) 
    apply sc_solve
    apply safe
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    subgoal by (simp add: one_enat_def numeral_eq_enat)
    done
  subgoal
    apply safe
    subgoal 
      apply simp
      by (metis Suc_le_eq le_add2 le_refl order.strict_trans plus_1_eq_Suc slice_eq_mset_subslice slice_eq_mset_trans)
    subgoal by (auto dest: slice_eq_mset_eq_length intro!: slice_LT_I_aux)
    done
  subgoal 
    by clarsimp
  subgoal apply clarsimp by (metis (full_types) Suc_leI atLeastLessThan_iff le_neq_implies_less)
  subgoal 
    apply clarsimp 
    apply (subst slice_eq_mset_nth_outside, assumption)
      apply (auto dest: slice_eq_mset_eq_length)
    done 
  subgoal by auto
  subgoal by (metis diff_is_0_eq' le_trans nat_less_le not_numeral_le_zero slice_eq_mset_eq_length)
  subgoal by auto
  done


lemma TR_pp_important:
  assumes "TR ''partition_c'' =  TR_pp ''partition_c''"
  shows "timerefine TR (partition3_spec xs' l' h') = timerefine TR_pp (partition3_spec xs' l' h')"
    unfolding partition3_spec_def
  apply(cases "4 \<le> h' - l' \<and> h' \<le> length xs'"; auto)
  apply(simp only: SPEC_timerefine_conv)
  apply(rule SPEC_cong, simp)
  apply(rule ext)
  apply(simp add: norm_cost timerefineA_cost_apply_costmult)
  apply(subst assms(1))
  apply (simp add: norm_cost)
  done


lemma partition_pivot_correct_flexible: 
  assumes "TR ''partition_c'' =  TR_pp ''partition_c''"
  shows "\<lbrakk>(xs,xs')\<in>Id; (l,l')\<in>Id; (h,h')\<in>Id\<rbrakk> 
  \<Longrightarrow> partition_pivot xs l h \<le> \<Down>Id (timerefine TR (partition3_spec xs' l' h'))"
  apply(subst TR_pp_important[where TR=TR, OF assms])
  apply(rule partition_pivot_correct)
  apply auto
  done

    
end  
  
context sort_impl_context begin


  
definition qsp_next_l2 :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, ecost) nrest" where            
  "qsp_next_l2 xs pi li hi \<equiv> doN {
    monadic_WHILEIT (\<lambda>li'. (\<exists>i\<in>{li'..<hi}. xs!i\<^bold>\<ge>xs!pi) \<and> li\<le>li' \<and> (\<forall>i\<in>{li..<li'}. xs!i\<^bold><xs!pi)) 
      (\<lambda>li. doN {ASSERT (li\<noteq>pi); cmp_idxs2' xs li pi}) (\<lambda>li. SPECc2 ''add'' (+) li 1) li
  }"  
 

definition qsp_next_h2 :: "'a list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, ecost) nrest" where
  "qsp_next_h2 xs pi li0 hi \<equiv> doN {
    ASSERT (hi>0);
    hi \<leftarrow> SPECc2 ''sub'' (-) hi 1;
    ASSERT (hi<length xs);
    monadic_WHILEIT (\<lambda>hi'. hi'\<le>hi \<and> (\<exists>i\<le>hi'. xs!i\<^bold>\<le>xs!pi) \<and> (\<forall>i\<in>{hi'<..hi}. xs!i\<^bold>>xs!pi))
      (\<lambda>hi. doN {ASSERT(pi\<noteq>hi); cmp_idxs2' xs pi hi})
      (\<lambda>hi. doN { ASSERT(hi>0); SPECc2 ''sub'' (-) hi 1}) hi
  }"  

sepref_register ungrd_qsp_next_l_spec ungrd_qsp_next_h_spec  qsp_next_h2 qsp_next_l2

(* TODO: We can get rid of the length xs restriction: the stopper element will always lie within <h, which is size_t representable! *)
sepref_definition qsp_next_l_impl [llvm_inline] is "uncurry3 (PR_CONST qsp_next_l2)" :: "(arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_l2_def PR_CONST_def                            
  apply (annot_snat_const "TYPE('size_t)")
  apply sepref 
  done

declare  qsp_next_l_impl.refine[sepref_fr_rules]
 
(* TODO: lemmas [sepref_fr_rules] = qsp_next_l_impl.refine[FCOMP qsp_next_l_refine]  *)
  
sepref_definition qsp_next_h_impl [llvm_inline] is "uncurry3 (PR_CONST qsp_next_h2)" :: "(arr_assn)\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding qsp_next_h2_def PR_CONST_def
  apply (annot_snat_const "TYPE('size_t)")
  by sepref

declare qsp_next_h_impl.refine[sepref_fr_rules]
  
(* TODO: lemmas [sepref_fr_rules] = qsp_next_h_impl.refine[FCOMP qsp_next_h_refine]  *)
  

lemma qsp_next_l2_refines:
  "(xs\<^sub>0,xs\<^sub>0')\<in>Id \<Longrightarrow> (pi,pi')\<in>Id \<Longrightarrow> (li\<^sub>0,li\<^sub>0')\<in>Id \<Longrightarrow> (hi\<^sub>0,hi\<^sub>0')\<in>Id
     \<Longrightarrow> qsp_next_l2 xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0 \<le> \<Down> Id (timerefine TR_cmp_swap (ungrd_qsp_next_l_spec ungrd_qsp_next_l_cost xs\<^sub>0' pi' li\<^sub>0' hi\<^sub>0'))"
  apply(rule order.trans)
   defer
  apply(rule nrest_Rel_mono)  apply(rule timerefine_mono2)
  subgoal by simp
  apply(rule qsp_next_l_refine[to_foparam, THEN nrest_relD, simplified])
  apply simp_all [4]
  unfolding qsp_next_l2_def qsp_next_l_def
  apply(refine_rcg SPECc2_refine cmp_idxs2'_refines_mop_cmp_idxs_with_E')
  supply conc_Id[simp del]
  by (auto intro: struct_preservingI simp: cost_n_leq_TId_n)

lemma qsp_next_h2_refines:
  "(xs\<^sub>0,xs\<^sub>0')\<in>Id \<Longrightarrow> (pi,pi')\<in>Id \<Longrightarrow> (li\<^sub>0,li\<^sub>0')\<in>Id \<Longrightarrow> (hi\<^sub>0,hi\<^sub>0')\<in>Id
     \<Longrightarrow> qsp_next_h2 xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0 \<le> \<Down> Id (timerefine TR_cmp_swap (ungrd_qsp_next_h_spec ungrd_qsp_next_r_cost xs\<^sub>0' pi' li\<^sub>0' hi\<^sub>0'))"
  apply(rule order.trans)
   defer
  apply(rule nrest_Rel_mono)  apply(rule timerefine_mono2)
  subgoal by simp
  apply(rule qsp_next_h_refine[to_foparam, THEN nrest_relD, simplified])
  apply simp_all [4]
  unfolding qsp_next_h2_def qsp_next_h_def
  apply(refine_rcg bindT_refine_easy SPECc2_refine cmp_idxs2'_refines_mop_cmp_idxs_with_E')
  apply refine_dref_type
  supply conc_Id[simp del]
  by (auto intro: struct_preservingI simp: cost_n_leq_TId_n)

definition "qs_partition2 li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<equiv> doN {
  ASSERT (pi < li\<^sub>0 \<and> li\<^sub>0<hi\<^sub>0 \<and> hi\<^sub>0\<le>length xs\<^sub>0);
  
  \<comment> \<open>Initialize\<close>
  li \<leftarrow> qsp_next_l2 xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
  hi \<leftarrow> qsp_next_h2 xs\<^sub>0 pi li\<^sub>0 hi\<^sub>0;
  
  ASSERT (li\<^sub>0\<le>hi);
  
  (xs,li,hi) \<leftarrow> monadic_WHILEIT 
    (\<lambda>(xs,li,hi). 
        li\<^sub>0\<le>li \<and> hi<hi\<^sub>0
      \<and> li<hi\<^sub>0 \<and> hi\<ge>li\<^sub>0  
      \<and> slice_eq_mset li\<^sub>0 hi\<^sub>0 xs xs\<^sub>0
      \<and> xs!pi = xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{li\<^sub>0..<li}. xs!i \<^bold>\<le> xs\<^sub>0!pi)
      \<and> xs!li \<^bold>\<ge> xs\<^sub>0!pi
      \<and> (\<forall>i\<in>{hi<..<hi\<^sub>0}. xs!i \<^bold>\<ge> xs\<^sub>0!pi)
      \<and> xs!hi \<^bold>\<le> xs\<^sub>0!pi  
    )
    (\<lambda>(xs,li,hi). SPECc2 ''icmp_slt'' (<) li hi) 
    (\<lambda>(xs,li,hi). doN {
      ASSERT(li<hi \<and> li<length xs \<and> hi<length xs \<and> li\<noteq>hi);
      xs \<leftarrow> myswap xs li hi;
      li \<leftarrow> SPECc2 ''add'' (+) li 1;
      li \<leftarrow> qsp_next_l2 xs pi li hi\<^sub>0;
      hi \<leftarrow> qsp_next_h2 xs pi li\<^sub>0 hi;
      RETURN (xs,li,hi)
    }) 
    (xs\<^sub>0,li,hi);
  
  RETURN (xs,li)
}"   

lemma qs_partition2_refines:
  "(xs\<^sub>0,xs\<^sub>0')\<in>Id \<Longrightarrow> (pi,pi')\<in>Id \<Longrightarrow> (li\<^sub>0,li\<^sub>0')\<in>Id \<Longrightarrow> (hi\<^sub>0,hi\<^sub>0')\<in>Id
   \<Longrightarrow> qs_partition2 li\<^sub>0 hi\<^sub>0 pi xs\<^sub>0 \<le> \<Down> Id (timerefine TR_cmp_swap (qs_partition li\<^sub>0' hi\<^sub>0' pi' xs\<^sub>0'))"
  unfolding qs_partition2_def qs_partition_def
  supply qsp_next_l2_refines[refine]
  supply qsp_next_h2_refines[refine]
  apply(refine_rcg bindT_refine_easy SPECc2_refine myswap_TR_cmp_swap_refine)
  apply refine_dref_type

  supply conc_Id[simp del]
  apply (auto simp: cost_n_leq_TId_n intro: struct_preservingI) 
   
  done


sepref_register qs_partition2 
sepref_def qs_partition_impl (*[llvm_inline]*) is "uncurry3 (PR_CONST qs_partition2)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a (arr_assn)\<^sup>d \<rightarrow>\<^sub>a arr_assn \<times>\<^sub>a size_assn"
  unfolding qs_partition2_def myswap_def PR_CONST_def
  apply (annot_snat_const "TYPE('size_t)")
  supply [dest] = slice_eq_mset_eq_length 
  apply sepref 
  done



definition "partition_pivot2 xs\<^sub>0 l h \<equiv> doN {
  ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0 \<and> h-l\<ge>4);
  hl \<leftarrow> SPECc2 ''sub'' (-) h l;
  d \<leftarrow> SPECc2 ''udiv'' (div) hl 2;
  m \<leftarrow> SPECc2 ''add'' (+) l d;
  l' \<leftarrow> SPECc2 ''add'' (+) l 1;
  h' \<leftarrow> SPECc2 ''sub'' (-) h 1;
  xs\<^sub>1 \<leftarrow> move_median_to_first2 l l' m h' xs\<^sub>0;
  ASSERT (l<length xs\<^sub>1 \<and> length xs\<^sub>1 = length xs\<^sub>0);
  (xs,m) \<leftarrow> mop_call (qs_partition2 l' h l xs\<^sub>1);

  \<comment> \<open>TODO: Use an auxiliary lemma, instead of this assertion chain! \<close>
  ASSERT (l<m \<and> m<h);
  ASSERT ((\<forall>i\<in>{l+1..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l) \<and> xs!l\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{l..<m}. xs!i\<^bold>\<le>xs\<^sub>1!l);
  ASSERT (\<forall>i\<in>{m..<h}. xs\<^sub>1!l\<^bold>\<le>xs!i);
  
  
  RETURN (xs,m)
}"

lemma partition_pivot2_refines:
  "(xs\<^sub>0,xs\<^sub>0')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id
    \<Longrightarrow> partition_pivot2 xs\<^sub>0 l h \<le> \<Down> Id (timerefine TR_cmp_swap (partition_pivot xs\<^sub>0' l' h'))"
  unfolding partition_pivot2_def partition_pivot_def
  supply move_median_to_first2_refine'[refine]
  supply qs_partition2_refines[refine]
  supply mop_call_refine[refine]
  apply(refine_rcg bindT_refine_easy SPECc2_refine myswap_TR_cmp_swap_refine)
  apply refine_dref_type

  supply conc_Id[simp del]
  apply (auto simp: cost_n_leq_TId_n intro: struct_preservingI)
  done

lemma partition_pivot_bounds_aux1: "\<lbrakk>\<not> b < ba; \<forall>d. b = ba + d \<longrightarrow> 4 \<le> d;
        (ac, ba + (b - ba) div 2) \<in> snat_rel' TYPE('size_t) \<rbrakk>
       \<Longrightarrow> Suc ba < max_snat LENGTH('size_t)"  
  apply sepref_dbg_side_bounds
  by presburger
      
lemma partition_pivot_bounds_aux2: "\<lbrakk> \<not> b < ba; \<forall>d. b = ba + d \<longrightarrow> 4 \<le> d \<rbrakk> \<Longrightarrow> Suc 0 \<le> b"  
  by presburger
       
  

sepref_register partition_pivot2  
sepref_def partition_pivot_impl [llvm_inline] is "uncurry2 (PR_CONST partition_pivot2)" :: "arr_assn\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a arr_assn \<times>\<^sub>a size_assn"
  unfolding partition_pivot2_def PR_CONST_def    
  supply [simp] = nat_diff_split_asm partition_pivot_bounds_aux1 partition_pivot_bounds_aux2
  apply (annot_snat_const "TYPE('size_t)")
  apply sepref
  done



text \<open>A way to synthesize the final Timerefinement Relation, without ever touching the constants.\<close>

schematic_goal partition_pivot2_correct: "(xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id        
   \<Longrightarrow> partition_pivot2 xs l h \<le> \<Down> Id (timerefine ?E (partition3_spec xs' l' h'))"
  apply(rule order.trans)
   apply(rule partition_pivot2_refines)
     apply simp_all [3]
  apply simp 
  apply(rule order.trans)
   apply(rule timerefine_mono2)
    apply simp
   apply(rule partition_pivot_correct[simplified])
     apply simp_all [3]
  apply(subst timerefine_iter2) 
    apply auto [2]  
  unfolding move_median_to_first_cost_def
  apply(simp only: pp_fun_upd pp_TId_absorbs_right timerefineA_propagate[OF wfR''E])
      (* TODO rename wfR''E *)
  apply (simp add:  cmp_idxs2'_cost_def myswap_cost_def
        lift_acost_cost lift_acost_propagate timerefineA_update_cost add.assoc
         timerefineA_update_apply_same_cost' costmult_add_distrib costmult_cost)
  apply(simp add: add.commute add.left_commute ) 
  apply(simp add: cost_same_curr_left_add plus_enat_simps times_enat_simps numeral_eq_enat)
  apply auto done

concrete_definition partition_pivot2_TR is partition_pivot2_correct uses "_ \<le> \<Down> Id (timerefine \<hole> _) "


end

end                           

