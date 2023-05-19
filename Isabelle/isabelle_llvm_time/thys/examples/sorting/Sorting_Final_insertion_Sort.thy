\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Final Insertion Sort\<close>
theory Sorting_Final_insertion_Sort
imports Sorting_Quicksort_Scheme Sorting_Unguarded_Insertion_Sort
begin

paragraph \<open>Summary\<close>
text \<open>This theory implements an algorithm final insertion sort, that
  assumes a list that is almost-sorted @{term part_sorted_wrt} and returns
  a sorted list in linear time.\<close>

paragraph \<open>Main Theorems/Definitions\<close>
text \<open>
\<^item> final_insertion_sort: the abstract algorithm that models final insertion sort
\<^item> final_insertion_sort_correct: final insertion sort, sorts an almost-sorted list
      in time fi_cost, which is linear in the length of the list
\<^item> final_insertion_sort_impl: the synthesized algorithm
\<close>

context weak_ordering begin

subsection \<open>final_insertion_sort\<close>

  definition "final_insertion_sort xs \<equiv> doN {
    ASSERT (1 < length xs);
    lxs \<leftarrow> SPECT [length xs \<mapsto> cost ''sub'' 1];
    if\<^sub>N SPECc2 ''icmp_sle'' (\<le>) lxs is_threshold then doN {
      SPECT [() \<mapsto> cost ''add'' 1];
      insertion_sort_guarded 1 lxs xs
    }
    else doN {
      SPECT [() \<mapsto> cost ''add'' 2];
      xs \<leftarrow> insertion_sort_guarded 1 is_threshold xs;
      insertion_sort_unguarded is_threshold is_threshold lxs xs
    }
  }"  


subsubsection \<open>reasoning about stopper elements\<close>

  lemma has_stopperI:
    assumes "i<length xs" "j'<i" "i-j'\<le>N" "\<forall>j\<le>j'. \<not>xs!i\<^bold><xs!j"
    shows "has_stopper N xs i"
    using assms unfolding has_stopper_def by blast
  
  
  lemma part_sorted_guardedI:
    assumes S: "part_sorted_wrt (le_by_lt (\<^bold><)) N xs" and B: "N\<le>i" "i<length xs"  
    shows "has_stopper N xs i"  
  proof -  
    from S have "N\<noteq>0" \<open>i\<noteq>0\<close> using B by (cases N; auto)+
    
    
    from S obtain ss where SL: "is_slicing N xs ss" and SORTED: "sorted_wrt (slice_LT (le_by_lt (\<^bold><))) ss" unfolding part_sorted_wrt_def by auto

    have XS_EQ: "xs = concat ss" using SL unfolding is_slicing_def by auto
    
    define xi where "xi = xs!i"
    
    obtain xs1 xs2 where XSEQ2: "xs=xs1@xi#xs2" and LEN_XS1: "length xs1 = i"
      unfolding xi_def using id_take_nth_drop[OF \<open>i<length xs\<close>] B by simp
    
    have [simp]: "ss\<noteq>[]"
      using XS_EQ assms(3) by auto
    have "concat ss = xs1@xi#xs2" by (simp add: XS_EQ[symmetric] XSEQ2)
    then obtain ss1 ssi1 ssi2 ss2 where 1: "ss = ss1 @ (ssi1 @ ssi2) # ss2" "xs1 = concat ss1 @ ssi1" "xi # xs2 = ssi2 @ concat ss2"
      by (auto dest: concat_eq_appendD)

    have SS1_NGT: "\<forall>x\<in>set (concat ss1). \<forall>y\<in>set (ssi1@ssi2). \<not>x \<^bold>> y"  
      using SORTED by (auto simp add: "1"(1) sorted_wrt_append slice_LT_def le_by_lt_def)
      
    have XS1_NGT: "\<forall>x\<in>set xs1. \<forall>y\<in>set (concat ss2). \<not>x \<^bold>> y"  
      using SORTED by (auto simp add: "1" sorted_wrt_append slice_LT_def le_by_lt_def)
      
      
    from SL 1 have SLI_BND: "length (ssi1@ssi2) \<le> N" unfolding is_slicing_def by auto
          
    show ?thesis proof (cases ssi2)  
      case [simp]: Nil 
      
      obtain ssi2' ss2' where [simp]: "ss2 = (xi#ssi2') # ss2'" using 1 
        apply simp
        apply (cases ss2; simp)
        subgoal for ss2_1 ss2_r 
          using SL unfolding is_slicing_def
          apply (cases ss2_1; simp)
          done
        done
      
      show ?thesis 
        apply (rule has_stopperI[where j'="length xs1 - 1"])
        subgoal by fact
        subgoal using \<open>i \<noteq> 0\<close> \<open>length xs1 = i\<close> by auto
        subgoal
          using LEN_XS1 \<open>N \<noteq> 0\<close> by linarith
        subgoal
          apply (auto simp add: XS_EQ 1 simp flip: LEN_XS1)
          apply (simp add: nth_append split: if_splits)
          subgoal for j using XS1_NGT nth_mem unfolding 1(2) by fastforce
          subgoal for j using XS1_NGT nth_mem unfolding 1(2) by fastforce
          done
        done
        
    next
      case (Cons _ ssi2') hence [simp]: "ssi2 = xi#ssi2'" using 1 by auto
      
      have "ss1\<noteq>[]" proof
        assume [simp]: "ss1=[]" 
        from 1 have "xs1 = ssi1" by simp
        hence "length ssi1 = i" using \<open>length xs1 = i\<close> by simp
        hence "length (ssi1@ssi2) > i" by simp
        moreover note SLI_BND
        ultimately show False using \<open>N\<le>i\<close> by auto
      qed
      
      have 11: "length (concat ss1) \<le> i" using \<open>length xs1 = i\<close> by (simp add: 1)
      
      have 12: "i < N + length (concat ss1)"
        by (metis "1"(2) "11" SLI_BND \<open>length xs1 = i\<close> add_diff_cancel_left' add_lessD1 le_eq_less_or_eq length_append length_greater_0_conv less_add_same_cancel1 less_diff_conv2 list.simps(3) local.Cons)
      
      show ?thesis 
        apply (rule has_stopperI[where j'="length (concat ss1) - 1"])  
        subgoal using assms(3) by auto
        subgoal using "1"(2) \<open>i \<noteq> 0\<close> \<open>length xs1 = i\<close> by auto
        subgoal using 12 by linarith
        subgoal 
          apply (auto simp add: XS_EQ 1 simp flip: LEN_XS1)
          apply (simp add: nth_append split: if_splits)
          subgoal for j using SS1_NGT using nth_mem by fastforce
          subgoal using "12" assms(2) by linarith
          done
        done
    qed
  qed        
      
  lemma mset_slice_eq_xform_aux:
    assumes "mset (slice 0 N xs') = mset (slice 0 N xs)"
    assumes "j < N" "N < length xs" "length xs' = length xs"
    obtains jj where "jj<N" "xs'!j = xs!jj"
    using assms by (auto simp: list_eq_iff_nth_eq set_slice_conv dest!: mset_eq_setD; auto)       
  
  lemma filter_mset_eq_empty_conv: "filter_mset P m = {#} \<longleftrightarrow> (\<forall>x\<in>#m. \<not>P x)"
    by (auto simp: filter_mset_eq_conv)
  
  lemma filter_mset_eq_same_conv: "filter_mset P m = m \<longleftrightarrow> (\<forall>x\<in>#m. P x)"
    by (auto simp: filter_mset_eq_conv)    
    
  lemma sorted_pos_aux:
    assumes "size (filter_mset (\<lambda>x. x \<^bold>\<le> a) (mset xs)) \<ge> n" "sorted_wrt (\<^bold>\<le>) xs"
    shows "\<forall>i<n. xs!i \<^bold>\<le> a"
  proof -
  
    from assms(1) have NL: "n\<le>length xs" 
      by (metis le_trans size_filter_mset_lesseq size_mset)
  
      
    show ?thesis proof (rule ccontr, simp add: unfold_le_to_lt, clarify)
      fix i
      assume "i<n" "a \<^bold>< xs!i"
      hence 1: "\<forall>j\<in>{i..<length xs}. a \<^bold>< xs!j"
        by (metis antisym_conv2 assms(2) atLeastLessThan_iff itrans sorted_wrt_nth_less wo_leD)
      
      define xs\<^sub>1 where "xs\<^sub>1 = take i xs" 
      define xs\<^sub>2 where "xs\<^sub>2 = drop i xs"
      
      have "xs = xs\<^sub>1@xs\<^sub>2" "\<forall>x\<in>set xs\<^sub>2. \<not>x\<^bold>\<le>a"
        unfolding xs\<^sub>1_def xs\<^sub>2_def using 1
        by (auto simp: in_set_conv_nth unfold_le_to_lt)
      
      hence "filter_mset (\<lambda>x. x \<^bold>\<le> a) (mset xs) = filter_mset (\<lambda>x. x \<^bold>\<le> a) (mset xs\<^sub>1)"
        by (auto simp: filter_mset_eq_empty_conv)
        
      hence "size (filter_mset (\<lambda>x. x \<^bold>\<le> a) (mset xs)) \<le> length xs\<^sub>1"  
        apply auto
        by (metis size_filter_mset_lesseq size_mset)
      also have "length xs\<^sub>1 < n" unfolding xs\<^sub>1_def using \<open>i<n\<close> NL by auto
      finally show False using assms(1) by simp
    qed
  qed

  lemma filter_mset_eq_sameI: 
    "(\<forall>x\<in>#m. P x) \<Longrightarrow> filter_mset P m = m" by (simp add: filter_mset_eq_same_conv)
  
  lemma xfer_stopper_leN_aux:
    assumes "length xs' = length xs"
    assumes I: "N \<le> i" "i < length xs"
    assumes DEQ: "drop N xs' = drop N xs" 
    assumes S: "mset (slice 0 N xs') = mset (slice 0 N xs)" "sorted_wrt_lt (\<^bold><) (slice 0 N xs')"
    assumes LE: "\<forall>j\<le>j'. \<not> xs ! i \<^bold>< xs ! j" "j' < N" "j \<le> j'"
    shows "\<not> (xs' ! i \<^bold>< xs' ! j)"
  proof -

    define xs\<^sub>1 where "xs\<^sub>1 = take (Suc j') (slice 0 N xs)" 
    define xs\<^sub>2 where "xs\<^sub>2 = drop (Suc j') (slice 0 N xs)"
    
    have S0NXS_EQ: "(slice 0 N xs) = xs\<^sub>1@xs\<^sub>2"
      unfolding xs\<^sub>1_def xs\<^sub>2_def by (auto)
  
    have "\<forall>x\<in>set (take (Suc j') xs). x \<^bold>\<le> xs!i"
      unfolding unfold_le_to_lt using LE
      by (auto simp: in_set_conv_nth)
    also have "take (Suc j') xs = xs\<^sub>1" 
      using LE
      apply (auto simp: take_slice xs\<^sub>1_def)
      by (simp add: Misc.slice_def)
    finally have 1: "\<forall>x\<in>set xs\<^sub>1. x \<^bold>\<le> xs ! i" .
    
    have [simp]: "xs!i = xs'!i"
      by (metis DEQ assms(1) assms(2) assms(3) drop_eq_mono hd_drop_conv_nth)
    
    have "Suc j' = length xs\<^sub>1" unfolding xs\<^sub>1_def using LE I by auto 
    also from 1 have "length xs\<^sub>1 \<le> size (filter_mset (\<lambda>x. x \<^bold>\<le> xs!i) (mset (slice 0 N xs)))"
      by (simp add: S0NXS_EQ filter_mset_eq_sameI)
    also have "mset (slice 0 N xs) = mset (slice 0 N xs')" using S by simp
    finally have "\<forall>ia<Suc j'. slice 0 N xs' ! ia \<^bold>\<le> xs ! i"
      using S(2)
      apply -
      apply (erule sorted_pos_aux)
      using le_by_lt by blast
    hence "\<forall>ia<Suc j'. xs' ! ia \<^bold>\<le> xs ! i"
      using LE by (simp add: Misc.slice_def)
    thus ?thesis using LE by (auto simp: unfold_le_to_lt)
  qed    

  lemma transfer_stopper_over_initial_sorting:
    assumes "has_stopper N xs i"
    assumes B: "length xs' = length xs" "0<N" "N \<le> i" "i < length xs"
    assumes DEQ: "drop N xs' = drop N xs" 
    assumes SORTED: "sort_spec (\<^bold><) (slice 0 N xs) (slice 0 N xs')" 
    shows "has_stopper N xs' i"
    using assms[unfolded sort_spec_def has_stopper_def]
    apply clarify
    subgoal for j'
      apply (cases "j'<N")
      subgoal
        apply (rule has_stopperI[where j'=j'])
        using xfer_stopper_leN_aux
        apply auto
        done
      subgoal
        apply (rule has_stopperI[where j'=j'])
        apply auto
        subgoal for j
          apply (subgoal_tac "xs'!i = xs!i")
          subgoal
            apply (cases "j<N")
            subgoal by (erule (1) mset_slice_eq_xform_aux[where j=j]; simp)
            subgoal by (smt assms(6) drop_eq_mono hd_drop_conv_nth leI le_eq_less_or_eq le_less_trans)
            done 
          subgoal by (metis assms(4) drop_eq_mono hd_drop_conv_nth)
          done
        done
      done
    done  
  
  lemma transfer_guard_over_initial_sorting:
    assumes PS: "part_sorted_wrt (le_by_lt (\<^bold><)) N xs"
    assumes B: "length xs' = length xs" "0<N" "N \<le> i" "i < length xs"
    assumes DEQ: "drop N xs' = drop N xs" 
    assumes SORTED: "sort_spec (\<^bold><) (slice 0 N xs) (slice 0 N xs')" 
    shows "has_stopper N xs' i"
    using assms transfer_stopper_over_initial_sorting part_sorted_guardedI by blast


  lemma pull_refinement_into_slice_sort_specT:
    "slice_sort_specT (enat (h-i\<^sub>0+1) *m insort_guarded_step_cost) (\<^bold><) xs 0 h
      = \<Down>Id (timerefine (TId(''slice_sort'' := enat (h-i\<^sub>0+1) *m insort_guarded_step_cost)) (
            slice_sort_spec (\<^bold><) xs 0 h))"
    unfolding slice_sort_spec_def slice_sort_specT_def
    apply(cases "h \<le> length xs"; auto)
    apply(simp add: SPEC_timerefine_conv) 
    apply(rule SPEC_cong, simp)
    by(simp add: timerefineA_cost) 
  

  abbreviation "guarded_insort_cost lxs \<equiv> enat (lxs+1) *m insort_guarded_step_cost"

  lemma insertion_sort_guarded_correct_fl: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs); h\<le>length xs ; i\<^sub>0<h; h\<le>length xs \<rbrakk> 
      \<Longrightarrow> insertion_sort_guarded i\<^sub>0 h xs 
        \<le> slice_sort_specT (guarded_insort_cost (h-i\<^sub>0)) (\<^bold><) xs 0 h"
    apply(subst pull_refinement_into_slice_sort_specT)
    apply(rule insertion_sort_guarded_correct)                    
       apply auto
    done




  lemma insertion_sort_guarded_correct_threshold: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs); h\<le>length xs ; i\<^sub>0<h; h\<le>length xs; (h-i\<^sub>0)\<le>is_threshold \<rbrakk> 
      \<Longrightarrow> insertion_sort_guarded i\<^sub>0 h xs 
        \<le> slice_sort_specT (guarded_insort_cost is_threshold) (\<^bold><) xs 0 h"
    apply(rule order_trans)
     apply(rule insertion_sort_guarded_correct_fl)
        apply auto [4]
    unfolding slice_sort_specT_def
    apply(rule nrest_le_formatI)
    apply(intro refine0 SPEC_both_refine)
    apply clarsimp
    apply(rule costmult_right_mono)
    by auto

  lemma final_insertion_sort_correct_aux:
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs\<^sub>0); h \<le> length xs\<^sub>0; i\<^sub>0 < h; h \<le> length xs\<^sub>0; h - i\<^sub>0 \<le> is_threshold;
          0 \<le> h \<and> h \<le> length xs\<^sub>0\<rbrakk>
    \<Longrightarrow> insertion_sort_guarded i\<^sub>0 h xs\<^sub>0 \<le> 
        SPECT
         (emb (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take 0 xs = take 0 xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice 0 h xs\<^sub>0) (slice 0 h xs))
           (guarded_insort_cost is_threshold))
      "
  using insertion_sort_guarded_correct_threshold[of i\<^sub>0 xs\<^sub>0 h]
  unfolding slice_sort_specT_def SPEC_REST_emb'_conv
  by(cases "0 \<le> h \<and> h \<le> length xs\<^sub>0", auto)


  abbreviation "unguarded_insort_cost lxs \<equiv> enat (lxs+1) *m insort_step_cost"

  thm insertion_sort_unguarded_correct

  lemma pull_refinement_into_slice_sort_specT_guarded:
    "slice_sort_specT (enat (h-i\<^sub>0+1) *m insort_step_cost) (\<^bold><) xs 0 h
    = \<Down>Id (timerefine (TId(''slice_sort'' := enat (h-i\<^sub>0+1) *m insort_step_cost)) (
            slice_sort_spec (\<^bold><) xs 0 h))"
    unfolding slice_sort_spec_def slice_sort_specT_def
    apply(cases "h \<le> length xs"; auto)
    apply(simp add: SPEC_timerefine_conv) 
    apply(rule SPEC_cong, simp)
    by(simp add: timerefineA_cost) 

  lemma insertion_sort_unguarded_correct_prepared: 
    "\<lbrakk>sorted_wrt_lt (\<^bold><) (take i\<^sub>0 xs\<^sub>0); (\<forall>i\<in>{i\<^sub>0..<h}. has_stopper N xs\<^sub>0 i) \<and> h\<le>length xs\<^sub>0 ; i\<^sub>0<h; h\<le>length xs\<^sub>0 \<rbrakk> 
      \<Longrightarrow> insertion_sort_unguarded N i\<^sub>0 h xs\<^sub>0 
        \<le> SPECT
         (emb (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take 0 xs = take 0 xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice 0 h xs\<^sub>0) (slice 0 h xs))
 (unguarded_insort_cost (h)))"
    apply(rule order.trans)
     apply(rule insertion_sort_unguarded_correct)
        apply auto [4]
    unfolding slice_sort_spec_def slice_sort_specT_def
    apply auto
    unfolding SPEC_timerefine_conv SPEC_REST_emb'_conv[symmetric]
    apply(rule SPEC_leq_SPEC_I, simp)
    apply(simp add: timerefineA_cost)
    apply(rule costmult_right_mono)
    apply simp
    done


  
  abbreviation "fi_cost lxs == guarded_insort_cost (is_threshold)
         + cost ''add'' 1 + cost ''add'' 1
        + cost ''if'' 1 +  cost ''sub'' 1 + cost ''icmp_sle'' 1
        + unguarded_insort_cost lxs
      "

subsubsection \<open>Correctness Theorem\<close>

  lemma final_insertion_sort_correct: 
    "\<lbrakk>part_sorted_wrt (le_by_lt (\<^bold><)) is_threshold xs; 1 < length xs; lxs=length xs\<rbrakk> 
      \<Longrightarrow> final_insertion_sort xs
       \<le> \<Down>Id (timerefine (TId(''sort_spec'':=fi_cost lxs))
               (SPEC (sort_spec (\<^bold><) xs) (\<lambda>_. cost ''sort_spec'' 1)))"
    unfolding final_insertion_sort_def SPEC_timerefine_conv
    apply simp
    unfolding SPEC_def
    unfolding SPECc2_def
    apply(rule gwp_specifies_I)
    apply (refine_vcg \<open>-\<close>)

    subgoal (* if branch *)
      apply(rule final_insertion_sort_correct_aux[THEN gwp_specifies_rev_I, THEN gwp_conseq_0 ])

    apply simp_all
      subgoal apply (rule sorted_wrt01) by auto  
      apply safe
      apply(simp_all add: emb_eq_Some_conv)
      subgoal apply auto  using slice_complete by metis
      apply(simp add: norm_cost add.assoc )
      apply sc_solve by (auto simp: one_enat_def)

    subgoal (* else branch *)
      apply(rule final_insertion_sort_correct_aux[THEN gwp_specifies_rev_I, THEN gwp_conseq_0 ])
      apply simp_all
      subgoal apply (rule sorted_wrt01) by auto  
      apply(rule insertion_sort_unguarded_correct_prepared[THEN gwp_specifies_rev_I, THEN gwp_conseq_0 ])
      apply(simp_all add: emb_eq_Some_conv)
      subgoal by (simp add: Misc.slice_def sort_spec_def) 
      subgoal for xs' M (* transfer guard over initial sorting *)
        apply safe
        apply(rule transfer_guard_over_initial_sorting[where xs=xs])
        by auto
      subgoal 
        apply rule
        subgoal 
          apply (auto simp: sort_spec_def)
           apply (metis Misc.slice_def append_take_drop_id drop0 drop_take slice_complete union_code)
          by (metis slice_complete)
        subgoal 
          apply(simp add: norm_cost add.assoc)
          apply sc_solve
          by (auto simp: one_enat_def numeral_eq_enat)
      done                
    done    
  done

subsection \<open>final_insertion_sort2\<close>

  definition "final_insertion_sort2 xs l h \<equiv> doN {
    ASSERT (l<h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l;
    if\<^sub>N SPECc2 ''icmp_sle'' (\<le>) lxs is_threshold then do {
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      insertion_sort_guarded2 l l' h xs
    }
    else doN {
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      l'' \<leftarrow> SPECc2 ''add'' (+) l is_threshold;
      xs \<leftarrow> insertion_sort_guarded2 l l' l'' xs;
      insertion_sort_unguarded2 is_threshold l'' h xs
    }
  }"  

abbreviation "TR_fi2 N == (TR_is_insert3 N)"


lemma wfR''_TR_fi2[simp]: "wfR'' (TR_fi2 N)"
  by (auto simp: pp_TId_absorbs_right pp_fun_upd intro!: wfR''_upd)

lemma sp_TR_fi2[simp]: "struct_preserving (TR_fi2 N)" 
  unfolding TR_is_insert3_def   
  by (auto simp: pp_TId_absorbs_right pp_fun_upd intro!: struct_preserving_upd_I)

  
  (* TODO: make these refinement steps use the correct TimeRefine *)

  thm insertion_sort_guarded2_refine
  lemma insertion_sort_guarded2_refine_prepared: 
    "\<lbrakk> (xsi,xs) \<in> slicep_rel l h; (ii,i)\<in>idx_shift_rel l; (ji,j)\<in>idx_shift_rel l; j\<le>N \<rbrakk> 
      \<Longrightarrow> insertion_sort_guarded2 l ii ji xsi \<le>\<Down>(slice_rel xsi l h) (timerefine (TR_fi2 N) (insertion_sort_guarded i j xs))"
    apply(rule insertion_sort_guarded2_refine)
    apply auto done

  lemma insertion_sort_unguarded2_refine_prepared: 
    "\<lbrakk> (xsi,xs) \<in> slicep_rel l h; (ii,i)\<in>idx_shift_rel l; (ji,j)\<in>idx_shift_rel l \<rbrakk> 
      \<Longrightarrow> insertion_sort_unguarded2 N ii ji xsi \<le>\<Down>(slice_rel xsi l h) (timerefine (TR_fi2 N) (insertion_sort_unguarded N i j xs))"
    apply(rule insertion_sort_unguarded2_refine)
    apply auto done



  lemma final_insertion_sort2_refine: "\<lbrakk>(xsi,xs) \<in> slicep_rel l h\<rbrakk> 
    \<Longrightarrow> final_insertion_sort2 xsi l h \<le> \<Down>(slice_rel xsi l h) (timerefine (TR_fi2 is_threshold) (final_insertion_sort xs))"  
    unfolding final_insertion_sort2_def final_insertion_sort_def
    unfolding SPECc2_alt consume_RETURNT[symmetric] 
    apply normalize_blocks

    supply [refine] = insertion_sort_guarded2_refine_prepared
                        insertion_sort_unguarded2_refine_prepared

    apply (refine_rcg bindT_refine_conc_time_my_inres MIf_refine consumea_refine) 
    apply refine_dref_type
   apply clarsimp_all


      apply(all \<open>(simp add: timerefineA_propagate timerefineA_update_cost timerefineA_update_apply_same_cost;fail)?\<close>)


             apply (auto simp: slicep_rel_def idx_shift_rel_def ) [10] 
    subgoal
      apply(simp add: norm_cost norm_pp TR_is_insert3_def)
      apply(subst timerefineA_propagate)
      by(auto simp: norm_cost  intro!: wfR''_upd)
    subgoal
      by (simp add: norm_cost norm_pp TR_is_insert3_def) 
    subgoal
      apply(simp add: norm_cost norm_pp TR_is_insert3_def)
      apply sc_solve by simp
    subgoal 
        apply (subst slice_rel_rebase, assumption)
      apply(refine_rcg insertion_sort_unguarded2_refine_prepared)
      by (auto simp: slice_rel_alt idx_shift_rel_def slicep_rel_def) 
    done

  
  abbreviation "fi2_cost s \<equiv> enat 17 *m TR_is_insert3 is_threshold ''icmp_slt''
         + enat 17 *m TR_is_insert3 is_threshold ''add''
           + enat 17 *m TR_is_insert3 is_threshold ''is_insert_g''
           + enat 17 *m TR_is_insert3 is_threshold ''call'' +
          enat 17 *m TR_is_insert3 is_threshold ''if'' +
          TR_is_insert3 is_threshold ''add'' +
          TR_is_insert3 is_threshold ''add'' +
          TR_is_insert3 is_threshold ''if'' +
          TR_is_insert3 is_threshold ''sub'' +
          TR_is_insert3 is_threshold ''icmp_sle'' +
          (enat (Suc (s)) *m TR_is_insert3 is_threshold ''icmp_slt''
             + enat (Suc (s)) *m TR_is_insert3 is_threshold ''add''
           + enat (Suc (s)) *m TR_is_insert3 is_threshold ''is_insert'' +
           enat (Suc (s)) *m TR_is_insert3 is_threshold ''call'' +
           enat (Suc (s)) *m TR_is_insert3 is_threshold ''if'')"

subsubsection \<open>Correctness Theorem\<close>

  lemma final_insertion_sort2_correct: 
    assumes [simplified, simp]: "(xs',xs)\<in>Id" "(l',l)\<in>Id" "(h',h)\<in>Id"   
      and "T ''slice_sort'' = fi2_cost (h-l)"
    shows "final_insertion_sort2 xs' l' h' \<le> \<Down>Id (timerefine T (final_sort_spec xs l h))"
    unfolding final_sort_spec_def slice_sort_spec_def
    apply(intro refine0)
    apply(rule order_trans)
    apply(rule final_insertion_sort2_refine[where xs="slice l h xs"])
    subgoal by(auto simp: slicep_rel_def)
    apply(rule order_trans[OF nrest_Rel_mono])
    apply(rule timerefine_mono2)
    subgoal  by simp
    apply(rule final_insertion_sort_correct)
       apply simp
      apply simp
     apply simp
    apply(simp add: SPEC_timerefine_conv)
    unfolding slice_rel_def
    apply(simp add: build_rel_SPEC_conv)
    apply(rule SPEC_leq_SPEC_I_strong)
    subgoal by auto
    subgoal apply (auto simp: timerefineA_cost_apply_costmult   norm_cost)
      apply(subst assms(4)) apply simp
      done
    done
  
end


subsection \<open>final_insertion_sort3\<close>

context sort_impl_context begin


  definition "final_insertion_sort3 xs l h \<equiv> doN {
    ASSERT (l<h);
    lxs \<leftarrow> SPECc2 ''sub'' (-) h l;
    if\<^sub>N SPECc2 ''icmp_sle'' (\<le>) lxs is_threshold then do {
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      insertion_sort_guarded3 l l' h xs
    }
    else doN {
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      l'' \<leftarrow> SPECc2 ''add'' (+) l is_threshold;
      xs \<leftarrow> insertion_sort_guarded3 l l' l'' xs;
      insertion_sort_unguarded3 is_threshold l'' h xs
    }
  }"  


subsubsection \<open>Refinement Lemma\<close>

  lemma final_insertion_sort3_refines:
    "(xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id 
      \<Longrightarrow> final_insertion_sort3 xs l h \<le> \<Down>Id (timerefine TR_cmp_swap (final_insertion_sort2 xs' l' h'))"
    supply conc_Id[simp del]
    unfolding final_insertion_sort3_def final_insertion_sort2_def
    supply [refine] = insertion_sort_unguarded3_refines insertion_sort_guarded3_refines
    apply(refine_rcg MIf_refine SPECc2_refine' bindT_refine_conc_time_my_inres monadic_WHILEIT_refine' )
    apply refine_dref_type
    apply(all \<open>(intro  preserves_curr_other_updI wfR''_upd wfR''_TId preserves_curr_TId)?\<close>)
    apply (simp_all (no_asm))
    by auto 

subsubsection \<open>Synthesize final_insertion_sort_impl\<close>
 
  sepref_register final_insertion_sort3  
  sepref_def final_insertion_sort_impl is "uncurry2 (PR_CONST final_insertion_sort3)" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding final_insertion_sort3_def PR_CONST_def
    apply (annot_snat_const "TYPE('size_t)")
    by sepref
 

end 

end
