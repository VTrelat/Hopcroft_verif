(* Obsolete version without unguarded-option! *)
theory Sorting_Insertion_Sort
  imports Sorting_Setup 
   "../../lib/Asymptotics_1D"
  "../../nrest/NREST_Automation"
begin


section \<open>Insertion Sort\<close>  
          
lemma mop_eo_extract_slice_refine:
  assumes *: "\<And>x y. T x = T y"
  shows
   "\<lbrakk> (i, i') \<in> idx_shift_rel l; (xs, xs') \<in> slice_rel xs\<^sub>0 l h\<rbrakk>
       \<Longrightarrow> mop_eo_extract T xs i \<le> \<Down> (Id \<times>\<^sub>r slice_rel xs\<^sub>0 l h) (timerefine TId (mop_eo_extract T xs' i'))"  
  by (auto intro!:  refine0   simp: *[THEN eq_refl] idx_shift_rel_def slice_rel_def in_br_conv take_map drop_map slice_nth slice_upd_sym algebra_simps)
  
  
lemma mop_eo_set_slice_refine:
  assumes *: "\<And>x y. T x = T y"
  shows "\<lbrakk>(i, i') \<in> idx_shift_rel l; (xs, xs') \<in> slice_rel xs\<^sub>0 l h; (v,v')\<in>Id\<rbrakk> 
      \<Longrightarrow> mop_eo_set T xs i v \<le> \<Down> (slice_rel xs\<^sub>0 l h) (timerefine TId (mop_eo_set T xs' i' v'))"  
  by (auto intro!: refine0 simp: *[THEN eq_refl] idx_shift_rel_def slice_rel_def in_br_conv take_map drop_map slice_nth slice_upd_sym algebra_simps)
  
lemma mop_to_eo_conv_slice_refine:
  shows "\<lbrakk>(xs, xs') \<in> slice_rel xs\<^sub>0 l h; (i, i') \<in> idx_shift_rel l\<rbrakk>
    \<Longrightarrow> mop_to_eo_conv xs \<le> \<Down> (slice_rel (map Some xs\<^sub>0) l h) (timerefine TId (mop_to_eo_conv xs'))"  
  unfolding mop_to_eo_conv_def 
  by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv slice_map take_map drop_map)  
  
lemma mop_to_wo_conv_slice_refine:
  "\<lbrakk>(xs, xs') \<in> slice_rel (map Some xs\<^sub>0) l h\<rbrakk> \<Longrightarrow> mop_to_wo_conv xs \<le> \<Down> (slice_rel xs\<^sub>0 l h) (timerefine TId (mop_to_wo_conv xs'))"
  unfolding mop_to_wo_conv_def
  apply (intro refine0)
  subgoal
    apply (simp add: slice_rel_def in_br_conv)
    apply (auto simp: in_set_conv_nth slice_nth list_eq_iff_nth_eq algebra_simps)
    by (metis Groups.add_ac(2) add_diff_inverse_nat less_diff_conv)
  subgoal 
    by simp
  subgoal 
    by simp
  subgoal  
    by (auto simp: slice_rel_def in_br_conv drop_map take_map slice_map)
  done

context weak_ordering begin
  lemma mop_cmp_v_idx_slice_refine: "\<lbrakk> (xs, xs') \<in> slice_rel xs\<^sub>0 l h; (i, i') \<in> idx_shift_rel l; (v,v')\<in>Id \<rbrakk>
    \<Longrightarrow> mop_cmpo_v_idx T xs v i \<le> \<Down> bool_rel (timerefine TId (mop_cmpo_v_idx T xs' v' i'))"
    supply [simp del] = conc_Id
    by (auto intro!: refine0 simp: idx_shift_rel_def slice_rel_def in_br_conv slice_nth algebra_simps)
end  

context weak_ordering begin


(* TODO: Move *)
abbreviation "mop_cmpo_v_idxN \<equiv> mop_cmpo_v_idx (cost ''list_cmpo_v'' 1)"
abbreviation "mop_eo_extractN \<equiv> mop_eo_extract (\<lambda>_. cost ''olist_extract'' 1)"
abbreviation "mop_eo_setN \<equiv> mop_eo_set (\<lambda>_. cost ''olist_set'' 1)"

definition "is_insert_spec xs i xs' \<equiv> 
  \<exists>i'\<le>i.
    i<length xs
  \<and> (length xs' = length xs) 
  \<and> (\<forall>j\<in>{0..<i'}. xs'!j=xs!j)
  \<and> (xs'!i' = xs!i)
  \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> xs!i\<^bold><xs'!j)
  \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j = xs!j)
  \<and> (i'>0 \<longrightarrow> \<not>(xs!i \<^bold>< xs'!(i'-1)) )
  "

  (*
lemma intv_split_auxE:  
  fixes k N :: nat
  assumes "k<N" "i'\<le>i" "i<N"
  obtains "k\<in>{0..<i'}" | "k=i'" | "k\<in>{i'<..i}" | "k\<in>{i<..<N}"  
  using assms
  by fastforce
*)  
  
  
lemma is_insert_spec_imp_sorted:
  "\<lbrakk>is_insert_spec xs i xs'; sorted_wrt_lt (\<^bold><) (take i xs)\<rbrakk> 
    \<Longrightarrow> sorted_wrt_lt (\<^bold><) (take (i+1) xs')"  
  (* TODO: Clean up this mess! *)
  apply (subgoal_tac "i<length xs")
  unfolding sorted_wrt_iff_nth_less le_by_lt_def
  subgoal
    apply clarsimp
    unfolding is_insert_spec_def
    apply (clarsimp;safe)
    apply (smt greaterThanAtMost_iff less_trans linorder_neqE_nat nat_Suc_less_le_imp nat_le_Suc_less_imp nz_le_conv_less unfold_lt_to_le zero_order(3))
    by (smt One_nat_def add_diff_cancel_left' atLeast0LessThan greaterThanAtMost_iff itrans le_less lessThan_iff less_Suc_eq_0_disj less_trans linorder_neqE_nat not_less_eq plus_1_eq_Suc unfold_lt_to_le wo_leI)
  subgoal
    using is_insert_spec_def by blast
  done    
  



abbreviation "mop_cmp_v_idxN \<equiv> mop_cmp_v_idx (cost ''list_cmp_v'' 1)"
abbreviation "mop_i_gtN \<equiv> SPECc2 ''i_gt'' (<)"
abbreviation "mop_i_subN \<equiv> SPECc2 ''i_sub'' (-)"

definition "E_u i == cost ''list_cmp_v'' ( ( i))
                     + cost ''list_get'' (1 +  (i))
                     + cost ''list_set'' (2 * ( i))
                     + cost ''i_sub'' (2 *  i)
                     + cost ''if'' (3 *  ( i))
                     + cost ''call'' ( ( i))
                     + cost ''i_gt'' (1 +  ( i))"
abbreviation "EEE \<equiv> (\<lambda>(xs::'a list,i::nat). E_u i)"
lemma EEE_def: "EEE =(\<lambda>(xs::'a list,i::nat). cost ''list_cmp_v'' ( ( i))
                     + cost ''list_get'' (1 +  (i))
                     + cost ''list_set'' (2 * ( i))
                     + cost ''i_sub'' (2 *  i)
                     + cost ''if'' (3 *  ( i))
                     + cost ''call'' ( ( i))
                     + cost ''i_gt'' (1 +  ( i)))" unfolding E_u_def by simp

definition "EE \<equiv> (\<lambda>(xs::'a list,i). cost ''list_cmp_v'' (enat ( i))
                     + cost ''list_get'' (1 + enat (i))
                     + cost ''list_set'' (2 * enat ( i))
                     + cost ''i_sub'' (2 * enat ( i))
                     + cost ''if'' (2 * enat ( i))
                     + cost ''i_gt'' (1 + enat ( i)))"
definition is_insert :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list,(_,enat) acost) nrest" where "is_insert xs i \<equiv> doN {
  ASSERT (i<length xs);
  x \<leftarrow> mop_list_getN xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). 
    i'\<ge>0 \<and> i'\<le>i \<and> length xs'=length xs
  \<and> (\<forall>j\<in>{0..i'}. xs'!j = xs!j)  
  \<and> (\<forall>j\<in>{i'<..i}. xs'!j = xs!(j-1) \<and> x\<^bold><xs'!j)  
  \<and> (\<forall>j\<in>{i<..<length xs}. xs'!j=xs!j)
  ) 
    (\<lambda>(xs,i). doN { a \<leftarrow> mop_i_gtN 0 i;
                    MIf a (doN { i' \<leftarrow> mop_i_subN i 1;
                                 mop_cmp_v_idxN xs x i' }) (RETURN False) })
     (\<lambda>(xs,i). doN {
      ASSERT (i>0 \<and> i<length xs);
      i' \<leftarrow> mop_i_subN i 1;
      t \<leftarrow> mop_list_getN xs i';
      xs \<leftarrow> mop_list_setN xs i t;
      RETURN (xs,i')
    }) (xs,i);

  xs \<leftarrow> mop_list_setN xs i x;  
  
  RETURN xs
}"

definition "is_insert_cost i = lift_acost (E_u i) + cost ''list_get'' 1"


lemma is_insert_correct: "i<length xs \<Longrightarrow> is_insert xs i \<le> SPEC (is_insert_spec xs i) (\<lambda>_. is_insert_cost (length xs))"
  unfolding is_insert_cost_def
  unfolding is_insert_def
  unfolding monadic_WHILEIET_def[symmetric, where E=EEE]
  unfolding SPEC_def SPECc2_def mop_cmp_v_idx_def
  apply(rule gwp_specifies_I)
  unfolding mop_list_get_def
  apply (refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET) 
  subgoal unfolding wfR2_def EEE_def zero_acost_def cost_def by auto
  subgoal for s a i'
    apply simp_all apply safe
    subgoal apply (refine_vcg \<open>-\<close>) (* loop body *)
      subgoal apply(rule loop_body_conditionI)
        subgoal (* A *)
          unfolding E_u_def
          apply sc_solve by simp
        subgoal (* B *)
          unfolding E_u_def
          apply sc_solve by (auto simp add: numeral_eq_enat one_enat_def)
        apply auto 
        subgoal by (smt Suc_lessI Suc_pred greaterThanAtMost_iff le_less_trans nth_list_update_eq nth_list_update_neq)
        subgoal by (smt Suc_lessI Suc_pred greaterThanAtMost_iff le_less_trans nth_list_update_eq nth_list_update_neq)
        done
      subgoal
        by blast
      done
    subgoal (* exiting loop because of wrong first part of guard (i=0 i.e.) *)
      apply(rule loop_exit_conditionI)
      apply (refine_vcg \<open>-\<close>)
      unfolding is_insert_spec_def apply auto (* why two times the same goal? *)
      subgoal
        apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        unfolding E_u_def apply(sc_solve) by (auto simp: one_enat_def)
      subgoal
        apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
        unfolding E_u_def apply(sc_solve) by (auto simp: one_enat_def)
      subgoal apply (rule exI[where x=i']) 
        by auto
      done
    done
  subgoal apply simp  
    by linarith
  subgoal for s a b(* wrong second part of guard (right position found) *) 
    apply simp
    apply(rule loop_exit_conditionI)
    apply (refine_vcg \<open>-\<close>)
    unfolding is_insert_spec_def apply auto (* why two times the same goal? *)
    subgoal
      apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
      unfolding E_u_def apply(sc_solve) by (auto simp: one_enat_def)
    subgoal
      apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
      unfolding E_u_def apply(sc_solve) by (auto simp: one_enat_def)
    subgoal apply(rule exI[where x=0]) by auto
    done 
      (*  subgoal (* progress *) by( progress \<open>simp add: pfa\<close>) *)
  subgoal apply simp done
  apply simp_all done
 


definition is_insert2 :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list,_) nrest" where "is_insert2 xs i \<equiv> doN {
  ASSERT (i<length xs);
  
  xs \<leftarrow> mop_to_eo_conv xs;
  
  (x,xs) \<leftarrow> mop_eo_extractN xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). doN { a \<leftarrow> mop_i_gtN 0 i;
                    MIf a (doN { i' \<leftarrow> mop_i_subN i 1;
                                 mop_cmpo_v_idxN xs x i' }) (RETURN False) })
   (\<lambda>(xs,i). doN {
      ASSERT (i>0);
      i' \<leftarrow> mop_i_subN i 1;
      (t,xs) \<leftarrow> mop_eo_extractN xs i';
      xs \<leftarrow> mop_eo_setN xs i t;
      RETURN (xs,i')
    }) (xs,i);

  xs \<leftarrow> mop_eo_setN xs i x;  
  
  xs \<leftarrow> mop_to_wo_conv xs;
  
  RETURN xs
}"


definition "ii2_loop_rel \<equiv> {((xs',i'), (xs,i)). i'=i \<and> length xs' = length xs \<and> i<length xs \<and> (\<forall>j\<in>{0..<length xs}-{i}. xs'!j = Some (xs!j)) \<and> xs'!i=None}"

lemma 
    mop_to_eo_conv_refine:
    "M (map Some xs) \<le> \<Down>R M' \<Longrightarrow> do { xs' \<leftarrow> mop_to_eo_conv xs; M xs' } \<le> \<Down>R M'"
  unfolding mop_to_eo_conv_def 
  unfolding lift_acost_def apply(subst consume_zero) by(auto simp: zero_acost_def zero_enat_def)

thm refine0




definition "E2 = TId(''list_get'':=cost ''olist_extract'' (1::enat),
                    ''list_cmp_v'':=cost ''list_cmpo_v'' (1::enat),
                    ''list_set'':=cost ''olist_set'' (1::enat)) "


find_theorems SPECc2 timerefine


lemma wfR_E2[simp]: "wfR'' E2"
  unfolding E2_def by (auto intro!: wfR''_upd)

lemma sp_E2: "struct_preserving E2"
  apply(rule struct_preservingI)
  subgoal by(auto simp: E2_def timerefineA_upd timerefineA_TId)
  subgoal by(auto simp: E2_def timerefineA_upd timerefineA_TId)
  done

lemma is_insert2_refine: "is_insert2 xs i \<le>\<Down>(\<langle>Id\<rangle>list_rel) (timerefine E2 (is_insert xs i))"
  unfolding is_insert2_def is_insert_def
  supply [simp del] = conc_Id
  unfolding mop_list_get_def mop_to_eo_conv_def mop_eo_extract_def
  apply(simp only: consume_alt nres_acost_bind_assoc)

  apply (intro refine0; simp )
  apply(simp only: consumea_shrink)
  apply(rule bindT_refine_conc_time2) 
  subgoal apply(rule wfR_E2) done
  apply(auto intro!: consumea_refine) [1] 
  subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
  apply simp 
  apply(rule bindT_refine_conc_time2)
  subgoal apply(rule wfR_E2) done
  unfolding monadic_WHILEIET_def
   apply (rule monadic_WHILEIT_refine_t[where R=ii2_loop_rel])
  subgoal apply(rule wfR_E2) done
  subgoal apply(rule sp_E2) done
  subgoal by (auto simp: ii2_loop_rel_def)
  subgoal by simp
  subgoal
    unfolding mop_cmpo_v_idx_def mop_cmp_v_idx_def consume_alt nres_acost_bind_assoc SPECc2_alt
    apply (clarsimp split: prod.splits simp: ii2_loop_rel_def)
    apply(rule bindT_refine_conc_time2)
    subgoal apply(rule sp_E2 wfR_E2) done
     apply (refine_rcg consumea_refine)
     apply refine_dref_type
    apply simp
    subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
    apply(rule MIf_refine)
    subgoal  apply(rule sp_E2 wfR_E2) done
    subgoal by simp
      apply simp
    apply(rule bindT_refine_conc_time2) 
    subgoal  apply(rule sp_E2 wfR_E2) done
      apply(rule consumea_refine)
       apply refine_dref_type
    apply simp
      subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
       apply simp
     apply (refine_rcg; simp)
    apply(rule bindT_refine_conc_time2) 
    subgoal apply(rule sp_E2 wfR_E2) done
      apply(rule consumea_refine) 
       apply refine_dref_type
       apply simp
      subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
     apply (refine_rcg; simp)
      apply (refine_rcg; simp)
    done
  subgoal  
    unfolding SPECc2_alt consume_alt nres_acost_bind_assoc mop_cmp_v_idx_def mop_cmpo_v_idx_def
    unfolding ii2_loop_rel_def
    apply clarsimp
    apply refine_rcg 
    apply simp
    apply(rule bindT_refine_conc_time2) 
    subgoal apply(rule sp_E2 wfR_E2) done
      apply(rule consumea_refine) 
       apply refine_dref_type
       apply simp
      subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
      apply refine_rcg 
      apply simp
    apply(rule bindT_refine_conc_time2) 
    subgoal apply(rule sp_E2 wfR_E2) done
      apply(rule consumea_refine) 
       apply refine_dref_type
       apply simp
      subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
    apply(rule bindT_refine_conc_time2) 
    subgoal apply(rule sp_E2 wfR_E2) done
      apply(rule consumea_refine) 
       apply refine_dref_type
       apply simp
      subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
    apply refine_rcg 
    apply (auto simp: nth_list_update split: if_splits)
    done
  subgoal
    unfolding consume_alt mop_to_wo_conv_def
    apply refine_rcg
    apply (auto simp: ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])
    apply(simp add: consumea_shrink)  
    apply(rule bindT_refine_conc_time2) 
    subgoal apply(rule sp_E2 wfR_E2) done
      apply(rule consumea_refine) 
       apply refine_dref_type
       apply simp
      subgoal unfolding E2_def by(simp add: lift_acost_zero timerefineA_upd  timerefineA_TId)
      apply refine_rcg
    apply (auto simp: ii2_loop_rel_def nth_list_update in_set_conv_nth intro: list_eq_iff_nth_eq[THEN iffD2])
    done
  done
  
  
definition "is_insert3 xs l i \<equiv> doN {

  ASSERT (i<length xs);
  
  xs \<leftarrow> mop_to_eo_conv xs;
  
  (x,xs) \<leftarrow> mop_eo_extractN xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). do {  a \<leftarrow> mop_i_gtN l i;
                    MIf a ((doN { i' \<leftarrow> mop_i_subN i 1; mop_cmpo_v_idxN xs x i'}))
                          (RETURNT False)}) (\<lambda>(xs,i). doN {
      ASSERT (i>0);
      i' \<leftarrow> mop_i_subN i 1;
      (t,xs) \<leftarrow> mop_eo_extractN xs i';
      xs \<leftarrow> mop_eo_setN xs i t;
      RETURN (xs,i')
    }) (xs,i);

  xs \<leftarrow> mop_eo_setN xs i x;  
  
  xs \<leftarrow> mop_to_wo_conv xs;
  
  RETURN xs
}"
  

\<^cancel>\<open>
definition "is_unguarded_insert3 xs l i \<equiv> doN {

  ASSERT (i<length xs);
  
  xs \<leftarrow> mop_to_eo_conv xs;
  
  (x,xs) \<leftarrow> mop_eo_extract xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). doN { ASSERT (i>l); mop_cmpo_v_idx xs x (i-1)}) (\<lambda>(xs,i). doN {
      ASSERT (i>0);
      (t,xs) \<leftarrow> mop_eo_extract xs (i-1);
      xs \<leftarrow> mop_eo_set xs i t;
      let i = i-1;
      RETURN (xs,i)
    }) (xs,i);

  xs \<leftarrow> mop_eo_set xs i x;  
  
  xs \<leftarrow> mop_to_wo_conv xs;
  
  RETURN xs
}"
\<close>



lemma gt_refine: 
  "(x2c,x2b)\<in>idx_shift_rel l \<Longrightarrow> (SPECc2 ''i_gt'' (<) l x2c :: (_,(_,enat)acost) nrest)\<le> \<Down> bool_rel (timerefine TId (SPECc2 ''i_gt'' (<) 0 x2b))"
  unfolding SPECc2_def
  by (simp add: timerefine_id idx_shift_rel_def)

lemma sub_refine:
  "x2b>0 \<Longrightarrow> (x2c,x2b)\<in>idx_shift_rel l \<Longrightarrow> (SPECc2 ''i_sub'' (-) x2c 1 :: (_,(_,enat)acost) nrest) \<le> \<Down> (idx_shift_rel l) (timerefine TId (SPECc2 ''i_sub'' (-) x2b 1))"
  apply(rule SPECc2_refine) using SPECc2_refine
  by(auto simp:   cost_n_leq_TId_n idx_shift_rel_def) 

lemma is_insert3_refine: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h; (i,i')\<in>idx_shift_rel l; i<h \<rbrakk> \<Longrightarrow> is_insert3 xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (timerefine TId (is_insert2 xs' i'))"
  unfolding is_insert2_def is_insert3_def
  supply [simp del] = conc_Id
  (*apply (simp cong: if_cong)*)
  supply [refine_dref_RELATES] = 
    RELATESI[of "slice_rel xs\<^sub>0 l h"] 
    RELATESI[of "slice_rel (map Some xs\<^sub>0) l h"] 
    RELATESI[of "slice_rel (map Some xs\<^sub>0) l h \<times>\<^sub>r idx_shift_rel l"] 
  apply (refine_rcg slice_nth_refine' slice_upd_refine' 
    mop_eo_extract_slice_refine mop_eo_set_slice_refine mop_to_eo_conv_slice_refine
    mop_cmp_v_idx_slice_refine mop_to_wo_conv_slice_refine bindT_refine_conc_time_my_inres

    gt_refine MIf_refine sub_refine
  )
  apply refine_dref_type
  apply (simp_all only: inres_SPECc2 sp_TId wfR''_TId)
  apply (all \<open>(assumption|simp add: idx_shift_rel_def;simp add: slice_rel_def in_br_conv)?\<close>)
  done

lemma is_insert3_refine1: 
  assumes "(xs,xs')\<in>slice_rel xs\<^sub>0 l h" "(i,i')\<in>idx_shift_rel l" "i<h"
  shows "is_insert3 xs l i \<le>\<Down>(slice_rel xs\<^sub>0 l h) (timerefine E2 (is_insert xs' i'))"
proof -
  have "is_insert3 xs l i  \<le>\<Down>(slice_rel xs\<^sub>0 l h) (timerefine TId (is_insert2 xs' i'))"
    by(rule is_insert3_refine[OF assms]) 
  also have "\<dots> \<le> \<Down>(slice_rel xs\<^sub>0 l h) (\<Down>(\<langle>Id\<rangle>list_rel) (timerefine E2 (is_insert xs' i')))"
    apply(rule nrest_Rel_mono)
    apply(simp only: timerefine_id)
    apply(rule is_insert2_refine)
    done
  also have "\<dots> \<le> \<Down>(slice_rel xs\<^sub>0 l h) (timerefine E2 (is_insert xs' i'))"
    by(simp add: conc_fun_complete_lattice_chain)
  finally show ?thesis .
qed







end
  
context sort_impl_context begin

thm sepref_fr_rules

abbreviation "mop_nat_gtN \<equiv> SPECc2 ''icmp_slt'' (<)"
abbreviation "mop_nat_subN \<equiv> SPECc2 ''sub'' (-)"

definition "is_insert4 xs l i \<equiv> doN {

  ASSERT (i<length xs);
  
  xs \<leftarrow> mop_to_eo_conv xs;
  
  (x,xs) \<leftarrow> mop_oarray_extract xs i;

  (xs,i)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i'). True) 
    (\<lambda>(xs,i). do {  a \<leftarrow> mop_nat_gtN l i;
                    MIf a ((doN { i' \<leftarrow> mop_nat_subN i 1; cmpo_v_idx2' xs x i'}))
                          (RETURNT False)}) (\<lambda>(xs,i). doN {
      ASSERT (i>0); 
      i' \<leftarrow> mop_nat_subN i 1;
      (t,xs) \<leftarrow> mop_oarray_extract xs i';
      xs \<leftarrow> mop_oarray_upd xs i t;
      RETURN (xs,i')
    }) (xs,i);

  xs \<leftarrow> mop_oarray_upd xs i x;  
  
  xs \<leftarrow> mop_to_wo_conv xs;
  
  RETURN xs
}"
  

definition "E_insert4 == TId(''list_cmpo_v'':=(lift_acost mop_array_upd_cost + lift_acost mop_array_nth_cost + cost lt_curr_name 1),
                            ''olist_extract'':=lift_acost mop_array_nth_cost,
                            ''olist_set'':=lift_acost mop_array_upd_cost,
                            ''i_gt'':=cost ''icmp_slt'' 1,
                            ''i_sub'':=cost ''sub'' 1,
                            ''i_add'':= cost ''add'' 1)   "

lemma wfR''E4[simp]: "wfR'' E_insert4"
  unfolding E_insert4_def
  by(intro wfR''_upd wfR''_TId)

lemma sp_E4[simp]: "struct_preserving E_insert4"
  by (auto intro!: struct_preservingI simp: E_insert4_def timerefineA_upd timerefineA_TId)


thm cmpo_v_idx2'_refine cmpo_v_idx2_refine
lemma cmpo_v_idx2'_refine4_elegant:
  "(cmpo_v_idx2', mop_cmpo_v_idxN) \<in> Id \<rightarrow> Id \<rightarrow> nat_rel \<rightarrow> nrest_trel bool_rel E_insert4"
  oops

lemma cmpo_v_idx2'_refine4:
  "(cmpo_v_idx2', mop_cmpo_v_idxN) \<in> Id \<rightarrow> Id \<rightarrow> nat_rel \<rightarrow> nrest_trel bool_rel E_insert4"
  supply conc_Id[simp del]
  apply(intro fun_relI nrest_trelI)
  apply(auto simp add: cmpo_v_idx2'_def mop_oarray_extract_def SPECc2_alt unborrow_def mop_oarray_upd_def)
  apply normalize_blocks 
  apply(split prod.splits)
  apply normalize_blocks
  apply simp
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  apply refine_dref_type 
   apply(auto simp add: E_insert4_def timerefineA_update_apply_same_cost intro!: wfR''_upd)
   apply sc_solve apply simp 
  done

lemma cmpo_v_idx2'_refine4': "\<lbrakk>(x, x') \<in> Id; (xa, x'a) \<in> Id; (xb, x'b) \<in> nat_rel\<rbrakk> \<Longrightarrow> cmpo_v_idx2' x xa xb \<le> \<Down> bool_rel (timerefine E_insert4 (mop_cmpo_v_idxN x' x'a x'b))"
  using  cmpo_v_idx2'_refine4[unfolded nrest_trel_def_internal, THEN fun_relD, THEN fun_relD, THEN fun_relD]
  by simp

lemma mop_oarray_extract_refine4: 
  "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> 
    mop_oarray_extract a b \<le> \<Down> Id (timerefine E_insert4 (mop_eo_extract (\<lambda>_. cost ''olist_extract'' 1) a' b'))"
  unfolding mop_oarray_extract_def E_insert4_def
  supply conc_Id[simp del]
  apply (simp)
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  by(auto simp: timerefineA_update_apply_same_cost intro!: wfR''_upd) 


lemma mop_oarray_set_refine4: 
  "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> 
    mop_oarray_upd xs a b \<le> \<Down> Id (timerefine E_insert4 (mop_eo_set (\<lambda>_. cost ''olist_set'' 1) xs' a' b'))"
  unfolding mop_oarray_extract_def E_insert4_def mop_oarray_upd_def
  supply conc_Id[simp del]
  apply (simp)
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  by(auto simp: timerefineA_update_apply_same_cost intro!: wfR''_upd)

lemma mop_gt_refine4:                                                               
   "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> SPECc2 ''icmp_slt'' (<) a b \<le> \<Down> Id ( timerefine E_insert4 (SPECc2 ''i_gt'' (<) a' b'))"
  apply(rule SPECc2_refine)
  by(simp_all add: E_insert4_def)

lemma mop_sub_refine4: 
  "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> SPECc2 ''sub'' (-) a b \<le> \<Down> Id ( timerefine E_insert4 (SPECc2 ''i_sub'' (-) a' b'))"
  apply(rule SPECc2_refine)
  by(simp_all add: E_insert4_def)


lemma mop_to_wo_conv_refine4:
  "(xs,xs')\<in>Id \<Longrightarrow> mop_to_wo_conv xs \<le> \<Down> Id (timerefine E_insert4 (mop_to_wo_conv xs'))"
  supply conc_Id[simp del]
  apply (simp add: mop_to_wo_conv_def)
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  by(auto simp: lift_acost_zero E_insert4_def timerefineA_update_apply_same_cost intro!: wfR''_upd)
  

lemma mop_to_eo_conv_refine4:
  "(xs,xs')\<in>Id \<Longrightarrow> mop_to_eo_conv xs \<le> \<Down> Id (timerefine E_insert4 (mop_to_eo_conv xs'))"
  supply conc_Id[simp del]
  apply (simp add: mop_to_eo_conv_def)
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  by(auto simp: lift_acost_zero E_insert4_def timerefineA_update_apply_same_cost intro!: wfR''_upd)

lemma is_insert4_refine: "(is_insert4,is_insert3) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> nrest_trel Id E_insert4"
  unfolding is_insert4_def is_insert3_def
  unfolding nrest_trel_def_internal
  apply (intro frefI nrest_relI fun_relI) 
  apply safe
  supply bindT_refine_conc_time2[refine] 
  supply mop_oarray_extract_refine4[refine]
  supply mop_oarray_set_refine4[refine]
  supply mop_gt_refine4[refine]
  supply MIf_refine[refine]
  supply cmpo_v_idx2'_refine4'[refine]
  supply mop_sub_refine4[refine]
  supply mop_to_wo_conv_refine4[refine]
  supply mop_to_eo_conv_refine4[refine]
  apply (refine_rcg) 
  apply refine_dref_type
  apply simp_all
  done

 (* TODO: compare this rule set with the original framework *)
thm sepref_frame_merge_rules
  sepref_register is_insert4

  find_in_thms mop_oarray_extract in sepref_fr_rules

  sepref_def is_insert_impl is "uncurry2 (PR_CONST is_insert4)" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding is_insert4_def PR_CONST_def 
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
  apply sepref(*_dbg_preproc
     apply sepref_dbg_cons_init
    apply sepref_dbg_id  
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
        apply sepref_dbg_trans 
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints *)
    done
  print_theorems

  thm is_insert_impl.refine is_insert4_refine is_insert3_refine1 is_insert_correct

text \<open>how to use FCOMP\<close>
\<^cancel>\<open>context
begin
  
  lemma nrest_trel_comp: "nrest_trel A EA O nrest_trel B EB = nrest_trel (A O B) (pp EA EB)"
    sorry
  (*
  thm fref_compI_PRE
  thm is_insert3_refine1
  lemma is_insert3_refine1: 
    assumes "(xs,xs')\<in>slice_rel xs\<^sub>0 l h" "(i,i')\<in>idx_shift_rel l" "i<h"
    shows "(is_insert3,is_insert) \<in> (slice_rel xs\<^sub>0 l h) \<rightarrow> nat_rel \<rightarrow> (idx_shift_rel l)
     \<rightarrow>\<^sub>f (\<lambda>(xs,l). nrest_trel (slice_rel xs\<^sub>0 l h) (timerefine E ( xs' i')))"
  thm is_insert4_refine[FCOMP is_insert3_refine1]
  *)
  lemma pp3: "(is_insert4, (timerefine E_insert4) ooo is_insert3) \<in> Id \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    sorry
  lemma pp: "(is_insert4, (timerefine E_insert4) ooo is_insert3) \<in> Id \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    sorry
  
    thm is_insert4_refine[unfolded nrest_trel_def_internal, folded nrest_rel_def_internal]
  
    thm hfref_compI_PRE[OF  is_insert_impl.refine]
    thm hfref_compI_PRE[OF  is_insert_impl.refine, unfolded PR_CONST_def
            , of "uncurry2 ((timerefine E_insert4 \<circ>\<circ>\<circ> weak_ordering.is_insert3) (\<^bold><))"
            , of "\<lambda>(a, b). (case a of (a, b) \<Rightarrow> True \<and> True) \<and> True"
            , of "(Id \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel"
            , of "\<lambda>_. Id"]  pp[to_fref]
  
    thm is_insert_impl.refine[unfolded PR_CONST_def, FCOMP pp]
  
  term is_insert_impl

end
\<close>

\<^cancel>\<open>    
  sepref_register is_unguarded_insert3
  
  sepref_def is_unguarded_insert_impl is "uncurry2 (PR_CONST is_unguarded_insert3)" 
    :: "(woarray_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn elem_assn"
    unfolding is_unguarded_insert3_def PR_CONST_def
    supply [[goals_limit = 1]]
    apply (annot_snat_const "TYPE(size_t)")
    by sepref
  \<close>  
    
end    


(*
  thm unat_sort_impl_context
  global_interpretation unat_sort: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult "''icmp_ult''" unat_assn
  defines
       unat_sort_is_insert_impl = unat_sort.is_insert_impl
    by (rule unat_sort_impl_context)

lemmas [llvm_inline] = eoarray_nth_impl_def

export_llvm "unat_sort_is_insert_impl::32 word ptr \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 32 word ptr llM"
*)



(*
lemma id_mop_call[id_rules]: 
  "mop_call ::\<^sub>i TYPE(('a, (char list, 'b) acost) nrest \<Rightarrow> ('a, (char list, 'b) acost) nrest)"
  by simp

lemma monadic_WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (monadic_WHILEIT I)$b$f$s \<equiv> 
    NREST.bindT$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$b$f$s
    )"
  by (simp)
find_in_thms  in sepref_monadify_comb

sepref_register mop_call *)



context weak_ordering begin

lemma is_insert_spec_split: "is_insert_spec xs i xs' \<Longrightarrow> (\<exists>i'\<le>i. 
  xs' = take i' xs @ xs!i # drop i' (take i xs) @ drop (i+1) xs)"
  unfolding is_insert_spec_def
  apply clarify
  subgoal for i'
    apply (rule exI[where x=i'])
    apply (simp add: list_eq_iff_nth_eq)
    apply (clarsimp simp: nth_append nth_Cons split: nat.splits)
    apply (safe; clarsimp?)
    subgoal for j k
      by (metis One_nat_def Suc_le_eq add.commute add_Suc_right add_diff_cancel_left' add_diff_inverse_nat greaterThanAtMost_iff less_diff_conv plus_1_eq_Suc zero_less_Suc)
    subgoal by (metis add_Suc leI le_add_diff_inverse2)
    done
  done
  
  
lemma is_insert_spec_imp_mset_eq:
  assumes A: "is_insert_spec xs i xs'"  
  shows "mset xs' = mset xs"
proof -
  from A have L: "i<length xs"
    unfolding is_insert_spec_def by blast

  from is_insert_spec_split[OF A] obtain i' where
    I': "i'\<le>i" 
    and XS'_EQ: "xs' = take i' xs @ xs ! i # drop i' (take i xs) @ drop (i + 1) xs"
    by blast  
  
  have XS_EQ: "xs = take i' xs @ drop i' (take i xs) @ xs!i # drop (i + 1) xs"  
    using L I'
    apply auto 
    by (metis atd_lem drop_Suc_nth drop_take_drop_unsplit)  
  
  show ?thesis
    apply (rewrite in "\<hole> = _" XS'_EQ)
    apply (rewrite in "_ = \<hole>" XS_EQ)
    by (auto)  
    
qed    


definition "sort_one_more_spec xs i \<equiv> doN {
    ASSERT (i<length xs \<and> sorted_wrt_lt (\<^bold><) (take i xs)); 
    SPEC (\<lambda>xs'. mset xs' = mset xs \<and> sorted_wrt_lt (\<^bold><) (take (i+1) xs')) (\<lambda>_. cost ''sort_one_more'' 1)
  }"  

definition "E_sort_one_more lxs = TId(''sort_one_more'':= lift_acost (E_u lxs+ cost ''list_get'' 1))"

lemma is_insert_sorts_one_more[param_fo, THEN nrest_trelD,refine]: 
  "(uncurry is_insert, uncurry sort_one_more_spec) 
      \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>(ys,_). nrest_trel (\<langle>Id\<rangle>list_rel) (E_sort_one_more (length ys)))"
  unfolding nrest_trel_def_internal
  apply (intro frefI fun_relI nrest_relI)   (* nice *) 
  using is_insert_correct 
        is_insert_spec_imp_sorted is_insert_spec_imp_mset_eq
  unfolding sort_one_more_spec_def (*
  by ( si mp add: pw_acost_le_iff refine_pw_simps; blast)
  *) oops




lemma is_insert_sorts_one_more_refine_param:
  assumes "(xs, xs') \<in> \<langle>Id\<rangle>list_rel" "(i, i') \<in> nat_rel" " (length xs) = lxs"
  shows " is_insert xs i \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine (E_sort_one_more lxs) (sort_one_more_spec xs' i'))"
  unfolding sort_one_more_spec_def
  apply(rule refine0)
  using assms[symmetric] apply simp
  apply(rule order.trans[OF is_insert_correct]) apply simp
  unfolding SPEC_REST_emb'_conv
  apply(rule SPECT_emb'_timerefine)
  subgoal using 
        is_insert_spec_imp_sorted is_insert_spec_imp_mset_eq by simp
  subgoal unfolding  E_sort_one_more_def is_insert_cost_def
    apply (auto simp: E_u_def timerefineA_upd)
    apply sc_solve by (auto simp: one_enat_def) 
  done

    
definition "insertion_sort_whole xs \<equiv> doN {
  (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i). 
    i\<le>length xs' \<and> length xs'=length xs \<and> mset xs' = mset xs \<and> sorted_wrt_lt (\<^bold><) (take i xs')) 
    (\<lambda>(xs,i). SPECc2 ''i_gt'' (<) i (length xs)) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> mop_call (sort_one_more_spec xs i);
      ASSERT (i<length xs);
      i' \<leftarrow> SPECc2 ''i_add'' (+) i 1;
      RETURN (xs,i')
    }) (xs,0);
  RETURN xs
}"  

definition "E_is_whole \<equiv> (\<lambda>(xs,i). cost ''sort_one_more'' (length xs - i)
                                     +  cost ''i_gt'' (1+length xs - i) 
                                     +  cost ''i_add'' (length xs - i) 
                                     +  cost ''if'' (1+length xs - i) 
                                     +  cost ''call'' (2*(1+length xs - i)) )"


definition "insort_time lxs =   lift_acost (cost ''sort_one_more'' (lxs) 
                                        + cost ''i_gt'' (Suc (lxs))
                                        + cost ''i_add'' (lxs)
                                        + cost ''if'' (Suc (lxs))
                                        + cost ''call'' (2*(Suc (lxs))))"


definition "E_final lxs = TId(''slice_sort'':=insort_time lxs)"
 
  lemma "insort_time (length xs) = lift_acost (E_is_whole (xs,0))"
  unfolding E_is_whole_def insort_time_def by simp

lemma wfR2_E_is_whole: "wfR2 (E_is_whole s)"
  unfolding E_is_whole_def wfR2_def
  apply(cases s)
  by (auto simp only: the_acost_propagate  split: prod.splits
          intro!: finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero)


lemma insertion_sort_whole_correct: 
  "insertion_sort_whole xs \<le> SPEC (sort_spec (\<^bold><) xs) (\<lambda>_. insort_time (length xs))"
  unfolding insertion_sort_whole_def sort_one_more_spec_def sort_spec_def sorted_sorted_wrt SPECc2_def
  unfolding mop_call_def
  apply(subst monadic_WHILEIET_def[symmetric, where E=E_is_whole])
  apply(subst (2) SPEC_def)
  apply(rule gwp_specifies_I)
  apply (refine_vcg \<open>-\<close>)
  apply(rule gwp_monadic_WHILEIET)
  subgoal apply(rule wfR2_If_if_wfR2) by(rule wfR2_E_is_whole)
    apply (refine_vcg \<open>-\<close>)
    apply safe
    apply simp
    apply safe
  subgoal (* loop body *)
    unfolding SPEC_REST_emb'_conv
    apply (refine_vcg \<open>-\<close>)
    subgoal
      apply(rule loop_body_conditionI)
      subgoal 
        unfolding E_is_whole_def  
        apply sc_solve by (auto dest: mset_eq_length)
      subgoal
        unfolding E_is_whole_def
        apply sc_solve  by (auto dest: mset_eq_length  simp: numeral_eq_enat one_enat_def)
      subgoal apply (auto dest: mset_eq_length) done
      done
    subgoal apply auto
      using mset_eq_length by force  
    done
  subgoal (* exit the loop *)
    apply(rule loop_exit_conditionI)
    apply (refine_vcg \<open>-\<close>)
    apply auto
    subgoal
      apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right lift_acost_diff_to_the_right_Some)
      unfolding insort_time_def E_is_whole_def apply(sc_solve) by (auto simp: one_enat_def)
    done
  apply simp
  done


lemma insertion_sort_whole_refine: 
  "(insertion_sort_whole, \<lambda>xs. (SPEC (sort_spec (\<^bold><) xs)) (\<lambda>_. insort_time (length xs))) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel\<rangle>nrest_rel"
  using insertion_sort_whole_correct
  apply (intro fun_relI nrest_relI)
  by auto  
  
definition "insertion_sort_whole2 xs \<equiv> doN {
  (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>(xs',i). i\<le>length xs' \<and> mset xs' = mset xs \<and> sorted_wrt_lt (\<^bold><) (take i xs')) 
    (\<lambda>(xs,i). SPECc2 ''i_gt'' (<) i (length xs)) 
    (\<lambda>(xs,i). doN {
      xs \<leftarrow> mop_call (is_insert xs i);
      ASSERT (i<length xs);
      i' \<leftarrow> SPECc2 ''i_add'' (+) i 1;
      RETURN (xs,i')
    }) (xs,0);
  RETURN xs
}"  


lemma gt_Id_refine: 
  "(a,a')\<in>nat_rel \<Longrightarrow>(x2c,x2b)\<in>nat_rel \<Longrightarrow> (SPECc2 ''i_gt'' (<) a x2c :: (_,(_,enat)acost) nrest)\<le> \<Down> bool_rel (timerefine (E_sort_one_more xs) (SPECc2 ''i_gt'' (<) a' x2b))"
  apply(rule SPECc2_refine)
  by (auto simp add: timerefine_id E_sort_one_more_def cost_n_leq_TId_n) 


lemma plus_Id_refine: 
  "(a,a')\<in>nat_rel \<Longrightarrow>(x2c,x2b)\<in>nat_rel \<Longrightarrow> (SPECc2 ''i_add'' (+) a x2c :: (_,(_,enat)acost) nrest)\<le> \<Down> nat_rel (timerefine (E_sort_one_more xs) (SPECc2 ''i_add'' (+) a' x2b))"
  apply(rule SPECc2_refine)
  by (auto simp add: timerefine_id E_sort_one_more_def cost_n_leq_TId_n) 


lemma wfR''_E_sort_one_more[simp]: "wfR'' (E_sort_one_more a')" 
  unfolding E_sort_one_more_def
  by(intro wfR''_upd wfR''_TId)

lemma sp_E_sort_one_more[simp]: "struct_preserving (E_sort_one_more a')"
  by (auto intro!: struct_preservingI simp: timerefineA_upd timerefineA_TId E_sort_one_more_def)

lemma insertion_sort_whole2_refines: 
 (* "(insertion_sort_whole2, insertion_sort_whole) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> nrest_trel (\<langle>Id\<rangle>list_rel) (E_sort_one_more ys)" (* PROBLEM *)
  apply(intro nrest_trelI fun_relI)  *)
"(a, a') \<in> \<langle>Id\<rangle>list_rel \<Longrightarrow> insertion_sort_whole2 a \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine (E_sort_one_more (length a')) (insertion_sort_whole a'))"
  unfolding insertion_sort_whole2_def insertion_sort_whole_def   
  unfolding mop_call_def
  supply consume_refine[refine]
  supply bindT_refine_conc_time2[refine] 
  supply monadic_WHILEIT_refine_t[refine]
  supply gt_Id_refine[refine] 
  supply plus_Id_refine[refine]
  supply is_insert_sorts_one_more_refine_param[refine]
  apply (refine_rcg )
  apply refine_dref_type
  apply auto
  by (auto simp: E_sort_one_more_def)

definition "insertion_sort xs l h \<equiv> doN {
  (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)  
    (\<lambda>(xs,i). SPECc2 ''i_gt'' (<) i h) 
    (\<lambda>(xs,i). doN {                                            
      xs \<leftarrow> mop_call (is_insert3 xs l i);
      ASSERT (i<h);
      i' \<leftarrow> SPECc2 ''i_add'' (+) i 1;
      RETURN (xs,i')
    }) (xs,l);
  RETURN xs
}"  


lemma i_gt_if_idx_shift_rel: "(aa,x1) \<in> slice_rel xs\<^sub>0 l h \<Longrightarrow> (x2a, x2) \<in> idx_shift_rel l \<Longrightarrow> SPECc2 ''i_gt'' (<) x2a h \<le> \<Down> bool_rel (timerefine E2 (SPECc2 ''i_gt'' (<) x2 (length x1)))"
  unfolding slice_rel_def in_br_conv idx_shift_rel_def
  unfolding SPECc2_def     apply(subst SPECT_refine_t) by (auto simp: E2_def timerefineA_upd timerefineA_TId)

lemma plus_Id_refine2:
  "(a,a')\<in>idx_shift_rel l \<Longrightarrow>(x2c,x2b)\<in>nat_rel \<Longrightarrow> (SPECc2 ''i_add'' (+) a x2c :: (_,(_,enat)acost) nrest)\<le> \<Down> (idx_shift_rel l) (timerefine E2 (SPECc2 ''i_add'' (+) a' x2b))"
  unfolding SPECc2_def 
  apply(subst SPECT_refine_t)
  by (simp_all add: idx_shift_rel_def E2_def timerefineA_upd timerefineA_TId)

lemma extract_knowledge_from_inresT_SPECc2[simp]:
  "inresT (project_acost e (SPECc2 n op a b)) v t \<longleftrightarrow> op a b = v \<and> (if n=e then t\<le>1 else t=0)"
  unfolding SPECc2_def project_acost_SPECT' inresT_def by (auto simp add: cost_def le_fun_def one_enat_def zero_enat_def zero_acost_def split: if_splits)

lemma insertion_sort_refines: "\<lbrakk> (xs,xs')\<in>slice_rel xs\<^sub>0 l h \<rbrakk> \<Longrightarrow> insertion_sort xs l h \<le>\<Down>(slice_rel xs\<^sub>0 l h) (timerefine E2 (insertion_sort_whole2 xs'))"  
  unfolding insertion_sort_def insertion_sort_whole2_def 
  unfolding mop_call_def
  supply consume_refine[refine]
  supply bindT_refine_conc_time2[refine] 
  supply monadic_WHILEIT_refine_t[refine]
  supply plus_Id_refine2[refine] 
  supply i_gt_if_idx_shift_rel[refine]
  apply (refine_rcg is_insert3_refine1)
  supply [refine_dref_RELATES] = 
    RELATESI[of "slice_rel xs\<^sub>0 l h"] 
    RELATESI[of "slice_rel xs\<^sub>0 l h \<times>\<^sub>r idx_shift_rel l"] 
  apply refine_dref_type        (* TODO: investigate ?aa16 *)
  apply (simp_all only: wfR_E2 sp_E2)
             apply (auto simp: idx_shift_rel_def slice_rel_def in_br_conv)
  apply(auto simp: E2_def)
  done


lemma extract_knowlesdge_from_inresT_SPECc2[simp]:
  "inresT (project_acost e (SPECT Q)) v t \<longleftrightarrow> (\<exists>tt. Q v = Some tt \<and> the_acost tt e \<ge> enat t)"
  apply(simp only: project_acost_SPECT' inresT_def)
  by (auto simp: le_fun_def split: option.splits)

lemma extract_knowlesdge_from_inresT_SPEC__1[simp]:
  "inresT (project_acost e (timerefine E (SPECT Q))) v t \<longleftrightarrow> (\<exists>tt. Q v = Some tt \<and> the_acost (timerefineA E tt) e \<ge> enat t)"
  apply(simp only: project_acost_SPECT' inresT_def)
  by (auto simp: le_fun_def timerefine_def project_acost_def timerefineA_def split: option.splits )

lemma insertion_sort_correct: "(uncurry2 insertion_sort, uncurry2 (slice_sort_spec (\<^bold><)))
  \<in> (\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>((xs,l),h). nrest_trel Id ((pp (pp E2 (E_sort_one_more (h - l))) (E_final (h - l)))))"
  unfolding slice_sort_spec_def unfolding uncurry_def                                                                
  apply (intro frefI fun_relI nrest_trelI)   apply safe
  apply (intro frefI fun_relI nrest_trelI) 
  apply(rule  ASSERT_D3_leI)
  (* TODO: Can we do this reasoning chain more beautiful? *)
  apply (rule order_trans) apply (rule insertion_sort_refines[OF slice_in_slice_rel]; simp)
  apply (rule order_trans) apply (rule nrest_Rel_mono)
   apply(rule timerefine_mono2) apply(rule wfR_E2)
   apply (rule insertion_sort_whole2_refines[simplified, OF refl])
  apply (rule order_trans) apply (rule nrest_Rel_mono)
   apply(rule timerefine_mono2) apply(rule wfR_E2)
   apply(rule timerefine_mono2) apply(rule wfR''_E_sort_one_more)  apply (rule insertion_sort_whole_correct)
  apply (subst timerefine_iter2) apply(rule wfR_E2) apply(rule wfR''_E_sort_one_more)
  apply (auto simp: pw_acost_le_iff refine_pw_simps slice_rel_def in_br_conv SPEC_def )
  unfolding E_final_def apply(subst timerefineA_iter2[symmetric]) 
  subgoal apply(rule wfR''_ppI) by auto
  subgoal by auto
  by(simp add: timerefineA_upd)
  
  
end  


context sort_impl_context begin

 
abbreviation "mop_nat_addN \<equiv> SPECc2 ''add'' (+)"

  definition "insertion_sort' xs l h \<equiv> doN {
    (xs,_)\<leftarrow>monadic_WHILEIT (\<lambda>_. True)  
      (\<lambda>(xs,i). mop_nat_gtN i h) 
      (\<lambda>(xs,i). doN {                                            
        xs \<leftarrow> mop_call (is_insert4 xs l i);
        ASSERT (i<h);
        i' \<leftarrow> mop_nat_addN i 1;
        RETURN (xs,i')
      }) (xs,l);
    RETURN xs
  }"  

lemma mop_add_refine4: 
  "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> SPECc2 ''add'' (+) a b \<le> \<Down> Id ( timerefine E_insert4 (SPECc2 ''i_add'' (+) a' b'))"
  apply(rule SPECc2_refine)
  by (auto simp add: timerefine_id E_insert4_def cost_n_leq_TId_n) 

lemmas is_insert4_refine' = is_insert4_refine[to_foparam, THEN nrest_trelD ]

lemma insertion_sort'_refines: "(  insertion_sort',   insertion_sort) \<in> Id \<rightarrow> Id \<rightarrow>  Id \<rightarrow>  nrest_trel Id E_insert4"
  unfolding insertion_sort'_def insertion_sort_def
  unfolding nrest_trel_def_internal mop_call_def
  apply (intro frefI nrest_relI fun_relI) 
  apply safe
  supply consume_refine[refine]
  supply bindT_refine_conc_time2[refine] 
  supply mop_gt_refine4[refine]
  supply mop_add_refine4[refine]
  supply is_insert4_refine'[refine]
  apply (refine_rcg) 
  apply refine_dref_type  
  apply (simp_all add: wfR''E4 sp_E4)
  apply (simp_all add: E_insert4_def)
  done

  sepref_register insertion_sort'

  thm sepref_fr_rules

  sepref_def insertion_sort_impl is "uncurry2 (PR_CONST insertion_sort')" 
    :: "(array_assn elem_assn)\<^sup>d *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a array_assn elem_assn"
    unfolding insertion_sort'_def PR_CONST_def
    apply (annot_snat_const "TYPE(size_t)")
    by sepref



definition "slice_insertion_sort_cost lxs =
       timerefineA (E_sort_one_more lxs) ( lift_acost (cost ''sort_one_more'' (lxs) 
                                        + cost ''i_gt'' (Suc (lxs))
                                        + cost ''i_add'' (lxs)
                                        + cost ''if'' (Suc (lxs))
                                        + cost ''call'' (Suc (lxs))))" 

definition "slice_insertion_sort_spec lt xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0);
    SPEC (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec lt (Misc.slice l h xs\<^sub>0) (Misc.slice l h xs))
         (\<lambda>_. slice_insertion_sort_cost (l-h))
  }"

(* This pattern should be the interface of an algorithm
  first a refinement in NREST which may be dependent of some inputs
lemma slice_insertion_sort_refines:
  "slice_insertion_sort_spec lt xs\<^sub>0 l h \<le> timerefine (E_insertion_sort (h-l)) (slice_sort_spec lt xs\<^sub>0 l h)"
  sorry

  then a final hn-refinement that only has constant exchange rates.
lemma hnr_insertion_sort_impl:
  "(insertion_sort_impl, (timerefine E) oooo slice_insertion_sort_spec) \<in> (\<langle>Id\<rangle>arr_assn \<times>\<^sub>a snat_assn) \<times>\<^sub>a snat_assn \<rightarrow>\<^sub>a \<langle>Id\<rangle>arr_assn "  
  sorry
*)

  
lemma wfE_final[simp]: "wfR'' (E_final x)"
  unfolding   E_final_def 
  apply(rule wfR''_upd)
  apply(rule wfR''_TId)
  done

lemma insertion_sort'_correct: "(uncurry2 insertion_sort', uncurry2 (slice_sort_spec (\<^bold><)))
  \<in> (\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow>\<^sub>f\<^sub>d (\<lambda>((xs,l),h). nrest_trel Id ((pp (pp (pp E_insert4 E2) (E_sort_one_more (h - l))) (E_final (h - l)))))"
  unfolding slice_sort_spec_def unfolding uncurry_def                                                                
  apply (intro frefI fun_relI nrest_trelI)   apply safe
  apply (intro frefI fun_relI nrest_trelI) 
  apply(rule  ASSERT_D3_leI)
  (* TODO: Can we do this reasoning chain more beautiful? *)
  apply (rule order_trans) apply(rule insertion_sort'_refines[to_foparam, THEN nrest_trelD, simplified, OF refl refl refl ])
  apply (rule order_trans)
   apply(rule timerefine_mono2) apply(rule wfR''E4)
    apply (rule insertion_sort_refines[OF slice_in_slice_rel]; simp)
  apply (rule order_trans)
   apply(rule timerefine_mono2) apply(rule wfR''E4)
   apply (rule nrest_Rel_mono) apply(rule timerefine_mono2) apply(rule wfR_E2)
   apply (rule insertion_sort_whole2_refines[simplified, OF refl])
  apply (rule order_trans)
   apply(rule timerefine_mono2) apply(rule wfR''E4)
   apply (rule nrest_Rel_mono)
   apply(rule timerefine_mono2) apply(rule wfR_E2)
   apply(rule timerefine_mono2) apply(rule wfR''_E_sort_one_more)  apply (rule insertion_sort_whole_correct)


  apply (subst timerefine_iter2) apply(rule wfR_E2) apply(rule wfR''_E_sort_one_more)
  apply(rule order.trans)
   apply(rule timerefine_mono2) apply(rule wfR''E4)
   apply(rule timerefine_conc_fun_ge2) apply(rule wfR''_ppI) apply(rule wfR_E2) apply(rule wfR''_E_sort_one_more)
  apply (subst timerefine_iter2) apply(rule wfR''E4) apply(rule wfR''_ppI) apply(rule wfR_E2) apply(rule wfR''_E_sort_one_more)
  apply simp
  apply (subst (2) timerefine_iter2[symmetric]) apply(intro wfR''_ppI wfR_E2 wfR''E4 wfR''_E_sort_one_more) apply(rule wfE_final)
  apply(subst pp_assoc)
  subgoal by (intro wfR''E4)  
  subgoal by (intro wfR_E2)
  apply(rule timerefine_mono2) apply(intro wfR''_ppI wfR_E2 wfR''E4 wfR''_E_sort_one_more)
  apply (auto simp: pw_acost_le_iff refine_pw_simps slice_rel_def in_br_conv SPEC_def )
  unfolding E_final_def by (simp add: timerefineA_upd)
  
  thm insertion_sort_impl.refine insertion_sort'_correct

lemma nrest_trel_to_nrest_rel: "(a,b) \<in> nrest_trel R E \<Longrightarrow> (a,timerefine E b) \<in> nrest_rel R"
  unfolding nrest_trel_def_internal nrest_rel_def_internal by simp

thm insertion_sort'_correct[to_foparam, THEN nrest_trelD, no_vars, unfolded nrest_rel_def_internal]
lemmas hea = insertion_sort'_correct[to_foparam, THEN nrest_trelD, unfolded nrest_rel_def_internal]
thm insertion_sort_impl.refine[to_hnr]


lemma aaah: "hn_refine (hn_ctxt arr_assn a ai \<and>* hn_val snat_rel bb bia \<and>* hn_val snat_rel bc bi) (insertion_sort_impl ai bia bi)
     (hn_invalid arr_assn a ai \<and>* hn_val snat_rel bb bia \<and>* hn_val snat_rel bc bi) arr_assn
     (timerefine (pp (pp (pp E_insert4 E2) (E_sort_one_more (bc - bb))) (E_final (bc - bb))) (slice_sort_spec (\<^bold><) a bb bc))"
  apply(rule hn_refine_result[OF insertion_sort_impl.refine[to_hnr], unfolded PR_CONST_def APP_def,
        OF hea, simplified]) apply simp_all
  apply(rule attains_sup_sv) by simp

term hn_refine
thm  hn_refineI''

lemma skalar_acost_propagate:
  "acostC (\<lambda>x. (a::enat) * the_acost (cost n t + z) x) = cost n (a * t) + (acostC (\<lambda>x. a * the_acost z x))"
  "acostC (\<lambda>x. (a::enat) * the_acost (cost n t) x) = cost n (a * t)"
  apply(cases z)
  by(auto simp: cost_def zero_acost_def plus_acost_alt ring_distribs intro!: ext) 

definition in_sort_time :: "nat \<Rightarrow> (char list, nat) acost" where "in_sort_time h = cost lt_curr_name (  (h * h)) +
    (cost ''if'' (  (1+ (h + h * (3 * h)))) +
     (cost ''call'' (  (h * h)) +
      (cost ''icmp_slt'' (  (1+ (h + (h + h * h)))) +
       (cost ''load'' (  (h + (h + h * h + h * h))) +
        (cost ''add'' (  h) +
         (cost ''store'' (  (h * h)) +
          (cost ''sub'' (  (h * (2 * h))) +
           (cost ''store'' (  (h * (2 * h))) +
            (cost ''ofs_ptr'' (  (5 * (h * h) + 2 * h)) + cost ''call'' ( 2* (1+ h)))))))))))"

lemma iii_le: "timerefineA (pp (pp (pp E_insert4 E2) (E_sort_one_more h)) (E_final h)) (cost ''slice_sort'' 1)
    \<le> lift_acost (in_sort_time h)"
  supply [simp] = timerefineA_TId_eq timerefineA_upd lift_acost_cost add.assoc
                  skalar_acost_propagate lift_acost_propagate timerefineA_propagate
  apply(subst timerefineA_iter2[symmetric]) 
  subgoal apply(intro wfR''_ppI) by auto
  subgoal by auto
  apply(subst timerefineA_iter2[symmetric]) 
  subgoal apply(intro wfR''_ppI) by auto
  subgoal by auto
  apply(subst timerefineA_iter2[symmetric]) 
  subgoal by auto
  subgoal by auto
  apply(simp add: E_final_def)
  apply(simp add: insort_time_def)
  apply(simp add: E_sort_one_more_def E_u_def)
  apply(simp add: E2_def)
  apply(simp add: E_insert4_def)
  apply(simp add: add.left_commute cost_same_curr_add cost_same_curr_left_add)
  unfolding in_sort_time_def
  apply sc_solve_debug apply safe apply(all \<open>(auto simp: sc_solve_debug_def zero_enat_def; fail)?\<close>)
  done
 

term "(insertion_sort_impl ai bia bi)"

text \<open>the final Hoare Triple:\<close>
 


lemmas pff = aaah[unfolded slice_sort_spec_def SPEC_REST_emb'_conv, THEN ht_from_hnr]

thm llvm_htriple_more_time[OF iii_le pff, simplified, no_vars]

lemma HT': "l \<le> h \<and> h \<le> length a \<Longrightarrow>
llvm_htriple ($lift_acost (in_sort_time (h - l)) \<and>* hn_ctxt arr_assn a ai \<and>* hn_val snat_rel l bia \<and>* hn_val snat_rel h bi)
             (insertion_sort_impl ai bia bi)
 (\<lambda>r. (\<lambda>s. \<exists>x. (\<up>(length x = length a \<and> take l x = take l a \<and> drop h x = drop h a \<and> sort_spec (\<^bold><) (slice l h a) (slice l h x)) \<and>* arr_assn x r) s) \<and>*
      hn_invalid arr_assn a ai \<and>* hn_val snat_rel l bia \<and>* hn_val snat_rel h bi)"
  apply(rule llvm_htriple_more_time)
   apply(rule iii_le)
  apply(rule pff) apply simp 
  done


definition "slice_sorted xs xs' l h \<equiv> length xs' = length xs \<and> take l xs' = take l xs \<and> drop h xs' = drop h xs \<and> sort_spec (\<^bold><) (slice l h xs) (slice l h xs')"

lemma slice_sorted_complete: "slice_sorted xs xs' 0 (length xs) = (mset xs'=mset xs \<and> sorted_wrt_lt (\<^bold><) xs' )"
  apply(simp add: slice_sorted_def sort_spec_def ) 
  apply(rule)
  subgoal using slice_complete by metis 
  subgoal using slice_complete by (metis mset_eq_length order_eq_iff)
  done

lemma HT: "l \<le> h \<and> h \<le> length xs \<Longrightarrow>
llvm_htriple ($lift_acost (in_sort_time (h - l)) \<and>* hn_ctxt arr_assn xs xsi \<and>* hn_val snat_rel l li \<and>* hn_val snat_rel h hi)
             (insertion_sort_impl xsi li hi)
 (\<lambda>r. (EXS xs'. (\<up>(slice_sorted xs xs' l h ) \<and>* arr_assn xs' r)) )"
  unfolding slice_sorted_def
  apply(rule cons_post_rule) 
   apply(rule HT')
   apply simp
  apply (auto simp add: invalid_assn_def hn_ctxt_def pure_part_def pure_def pred_lift_def)
  by (simp add: pred_lift_extract_simps(2) sep.mult.left_commute)  




lemma Sum_any_cost: "Sum_any (the_acost (cost n x)) = x"
  unfolding cost_def by (simp add: zero_acost_def)



lemma Sum_any_calc: "Sum_any (the_acost (in_sort_time x)) = 4 + (18 * (x * x) + 10 * x)"
  unfolding in_sort_time_def 
  apply(simp add: the_acost_propagate add.assoc)
  apply(subst Sum_any.distrib; auto simp only: Sum_any_cost 
          intro!: finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero)+ 
  done

(*
lemma "finite {y. the_acost (in_sort_time x) y \<noteq> 0}"
  sorry

lemma "(\<lambda>x. real (Sum_any (the_acost (in_sort_time x))) ) \<in> \<Theta>(\<lambda>n. (real n)*(real n))"
  unfolding Sum_any_calc
  by auto2

lemma "\<And>x. x\<ge>c1 \<Longrightarrow> Sum_any (the_acost (in_sort_time x)) \<le> c2 * (x*Discrete.log x + LENGTH('v::len))
      \<and> c1 \<le> 2^30 \<and> c2 \<le> 2^30"
  oops



*  define theta'' mit constanten c1 und c2
* sanity check , thetha'' \<Longrightarrow> theta

\<rightarrow> damit ist die spezifikation von unten passend
\<rightarrow> 

zusätzlich, c1 und c2 abschätzen \<rightarrow> gibt un

- literatur recherche für O Landau Symbolen für finite machines

*)

lemma HT'': "llvm_htriple ($lift_acost (in_sort_time (length xs)) \<and>* hn_ctxt arr_assn xs xsi
                             \<and>* hn_val snat_rel 0 li \<and>* hn_val snat_rel (length xs) hi)
           (insertion_sort_impl xsi li hi) 
            (\<lambda>r s. \<exists>x. (\<up>(mset x = mset xs \<and> sorted_wrt_lt (\<^bold><) x) \<and>* arr_assn x r) s)"
  using HT[where l=0 and h="length xs" and xs=xs, unfolded slice_sorted_complete, simplified] 
  by blast


(* TODO: tidy up 
abbreviation "in_sort_cost lxs \<equiv> lift_acost (in_sort_time lxs)"

lemma "finite {y. the_acost (in_sort_cost x) y \<noteq> 0}"
      "\<And>y. the_acost (in_sort_cost x) y < \<infinity>"
    "(\<lambda>x. real (the_enat (Sum_any (the_acost (in_sort_cost x)))) ) \<in> \<Theta>(\<lambda>n. (real n)*(real n))"
  sorry         

term "\<Theta>\<^sub>2(\<lambda>(n,w). w*(real n)*(real n))"

lemma HT''': 
  "llvm_htriple
    ($in_sort_cost (length xs) \<and>* arr_assn xs xsi \<and>* snat_assn 0 li \<and>* snat_assn (length xs) hi)
      (insertion_sort_impl xsi li hi) 
    (\<lambda>r s. \<exists>x. (\<up>(mset x = mset xs \<and> sorted_wrt_lt (\<^bold><) x) \<and>* arr_assn x r) s)"
  using HT'' unfolding hn_ctxt_def 
  by blast


definition theta' where "theta' f = {g. (\<lambda>x. real (the_enat (Sum_any (the_acost (g x)))) )\<in>\<Theta>(f)
             \<and> (\<forall>x. finite {y. the_acost (g x) y \<noteq> 0})
             \<and> (\<forall>x y. the_acost (in_sort_cost x) y < \<infinity>)}"

definition "O'' c1 c2 g =  {f. \<forall>n\<ge>c1. f n \<le> c2 * g n}"

lemma "O'' c1 c2 g \<subseteq> O(g)"
  sorry

lemma "\<exists>g\<in>theta'' (c1 LENGTH('b::len2)) (c2 LENGTH('b::len2))
                       (\<lambda>n. (real n)*(real n) + real LENGTH('b::len2)). 
    \<forall>xs li hi. 
    llvm_htriple
    ($g (length xs) \<and>* arr_assn xs xsi \<and>* snat_assn 0 li \<and>* snat_assn (length xs) (hi::'b::len2 word))
      (insertion_sort_impl_a xsi li hi) 
    (\<lambda>r s. \<exists>x. (\<up>(mset x = mset xs \<and> sorted_wrt_lt (\<^bold><) x) \<and>* arr_assn x r) s)"
  oops
*)


  thm hn_refine_result


(*  lemmas insertion_sort_impl_hnr[sepref_fr_rules] = insertion_sort_impl.refine[FCOMP ah]
  *)


end


global_interpretation insort_interp: pure_sort_impl_context "(\<le>)" "(<)" ll_icmp_ult  "''icmp_ult''" unat_assn
  defines 
      insort_interp_is_insert_impl = insort_interp.is_insert_impl
      and insort_interp_insertion_sort_impl = insort_interp.insertion_sort_impl
  by (rule unat_sort_impl_context)

(* declare insort_interp.is_insert_impl_def[llvm_inline] *)
export_llvm "insort_interp_insertion_sort_impl :: 64 word ptr \<Rightarrow> _" file "../code/insort.ll"



end
