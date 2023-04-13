section "Implementing Labelled Transition Systems by Maps"
theory LTSByTripleSetAQQ
imports TripleSetSpec LTSSpec LTSGA
begin


locale ltsbm_AQQ_defs = 
  ts: triple_set ts_\<alpha> ts_invar
  for ts_\<alpha>::"'ts \<Rightarrow> ('A \<times> 'Q \<times> 'Q) set"
  and ts_invar
begin

  definition ltsbm_\<alpha> :: "('Q,'A,'ts) lts_\<alpha>" where
    "ltsbm_\<alpha> ts \<equiv> (\<lambda>(a, q, q'). (q, a, q')) ` (ts_\<alpha> ts)"

  lemma ltsbm_\<alpha>_alt_def :
    "ltsbm_\<alpha> ts = {(q, a, q') . (a, q, q') \<in> ts_\<alpha> ts}"
  unfolding ltsbm_\<alpha>_def
  by (auto simp add: image_iff set_eq_iff Bex_def)

  definition "ltsbm_invar \<equiv> ts_invar"

  lemma ltsbm_empty_correct: 
    "triple_set_empty ts_\<alpha> ts_invar emp \<Longrightarrow>
     lts_empty ltsbm_\<alpha> ltsbm_invar emp"    
    unfolding lts_empty_def triple_set_empty_def ltsbm_\<alpha>_def ltsbm_invar_def
    by simp

  definition ltsbm_memb :: "_ \<Rightarrow> ('Q,'A,'ts) lts_memb" where 
    "ltsbm_memb memb ts q a q' \<equiv> memb ts a q q'"

  lemma ltsbm_memb_correct:
    "triple_set_memb ts_\<alpha> ts_invar memb \<Longrightarrow>
     lts_memb ltsbm_\<alpha> ltsbm_invar (ltsbm_memb memb)"
  unfolding lts_memb_def ltsbm_memb_def ltsbm_invar_def ltsbm_\<alpha>_def triple_set_memb_def
  by (simp add: image_iff Bex_def)

  definition ltsbm_add :: "_ \<Rightarrow> ('Q,'A,'ts) lts_add" where 
    "ltsbm_add add q a q' ts \<equiv> add a q q' ts"

  lemma ltsbm_add_correct:
    "triple_set_add ts_\<alpha> ts_invar add \<Longrightarrow>
     lts_add ltsbm_\<alpha> ltsbm_invar (ltsbm_add add)"
  unfolding lts_add_def ltsbm_add_def ltsbm_invar_def ltsbm_\<alpha>_def triple_set_add_def
  by simp

  definition ltsbm_add_succs :: "_ \<Rightarrow> ('Q,'A,'ts) lts_add_succs" where 
    "ltsbm_add_succs add_Cl q a qs ts \<equiv> add_Cl a q qs ts" 

  lemma ltsbm_add_succs_correct:
    "triple_set_add_Cl ts_\<alpha> ts_invar add_Cl \<Longrightarrow>
     lts_add_succs ltsbm_\<alpha> ltsbm_invar (ltsbm_add_succs add_Cl)"
    unfolding lts_add_succs_def ltsbm_\<alpha>_alt_def ltsbm_invar_def ltsbm_add_succs_def
              triple_set_add_Cl_def
    by auto

  definition ltsbm_delete :: "_ \<Rightarrow> ('Q,'A,'ts) lts_delete" where 
    "ltsbm_delete ts_del q a q' ts \<equiv> ts_del a q q' ts"

  lemma ltsbm_delete_correct:
    "triple_set_delete ts_\<alpha> ts_invar ts_del \<Longrightarrow>
     lts_delete ltsbm_\<alpha> ltsbm_invar (ltsbm_delete ts_del)"
    unfolding lts_delete_def ltsbm_delete_def ltsbm_\<alpha>_alt_def ltsbm_invar_def 
              triple_set_delete_def
    by auto

  definition ltsbm_succ_it where
   "ltsbm_succ_it it (ts::'ts) (q::'Q) (a::'A) = it ts a q"

  lemma ltsbm_succ_it_correct :
    assumes "triple_set_C_it ts_\<alpha> ts_invar it"
    shows "lts_succ_it ltsbm_\<alpha> ltsbm_invar (ltsbm_succ_it it)"
  using assms
  unfolding lts_succ_it_def triple_set_C_it_def ltsbm_succ_it_def ltsbm_invar_def ltsbm_\<alpha>_alt_def
  by simp

  lemma ltsbm_succ_label_it_correct :
    assumes "triple_set_AC_it ts_\<alpha> ts_invar it"
    shows "lts_succ_label_it ltsbm_\<alpha> ltsbm_invar it"
  using assms
  unfolding lts_succ_label_it_def triple_set_AC_it_def ltsbm_invar_def ltsbm_\<alpha>_alt_def
  by simp

  definition ltsbm_filter_it where
   "ltsbm_filter_it it P_q P_a P_q' (P::('Q \<times> 'A \<times> 'Q) \<Rightarrow> bool) ts = 
    set_iterator_image (\<lambda>(a, q, q'). (q, a, q')) 
       (it P_a P_q P_q' (\<lambda>(a, q, q'). P (q, a, q')) ts)"

  lemma ltsbm_filter_it_correct :
    assumes filter_it: "triple_set_filter_it ts_\<alpha> ts_invar it"
    shows "lts_filter_it ltsbm_\<alpha> ltsbm_invar (ltsbm_filter_it it)"
  unfolding lts_filter_it_def
  proof (intro allI impI)
    fix ts P_q1 P_a P_q2 P
    assume invar_ts: "ltsbm_invar ts"
   
    let ?P' = "\<lambda>(a::'A, q::'Q, q'::'Q). (P (q, a, q'))::bool"
    let ?S1 = "{(q1, a, q2). (q1, a, q2) \<in> ltsbm_\<alpha> ts \<and>
                     P_q1 q1 \<and> P_a a \<and> P_q2 q2 \<and> P (q1, a, q2)} "
    let ?S2 = "{(a, q1, q2). (q1, a, q2) \<in> ltsbm_\<alpha> ts \<and>
                     P_a a \<and> P_q1 q1 \<and> P_q2 q2 \<and> P (q1, a, q2)} "

    from triple_set_filter_it.triple_set_filter_it_correct [OF filter_it, 
         of ts P_a P_q1 P_q2 ?P'] invar_ts 
    have step: "set_iterator (it P_a P_q1 P_q2 ?P' ts) ?S2"
      unfolding triple_set_BC_it_def ltsbm_\<alpha>_alt_def ltsbm_invar_def 
      by simp
    
    show "set_iterator (ltsbm_filter_it it P_q1 P_a P_q2 P ts) ?S1" 
    unfolding ltsbm_filter_it_def
      apply (rule set_iterator_image_correct[OF step])
      apply (auto simp add: inj_on_def image_iff) 
    done
  qed

  definition ltsbm_it where
   "ltsbm_it it ts = 
    set_iterator_image (\<lambda>(a::'A, q::'Q, q'::'Q). (q, a, q')) (it ts)"

  lemma ltsbm_it_correct :
    assumes it: "triple_set_iterator ts_\<alpha> ts_invar it"
    shows "lts_iterator ltsbm_\<alpha> ltsbm_invar (ltsbm_it it)"
  unfolding lts_iterator_def
  proof (intro allI impI)
    fix ts 
    assume invar_ts: "ltsbm_invar ts"
   
    from triple_set_iterator.triple_set_it_correct [OF it, of ts] invar_ts 
    have step: "set_iterator (it ts) {(a, q1, q2). (q1, a, q2) \<in> ltsbm_\<alpha> ts}"
      unfolding triple_set_BC_it_def ltsbm_\<alpha>_alt_def ltsbm_invar_def 
      by simp
    
    show "set_iterator (ltsbm_it it ts) (ltsbm_\<alpha> ts)" 
    unfolding ltsbm_it_def
      apply (rule set_iterator_image_correct[OF step])
      apply (auto simp add: inj_on_def image_iff) 
    done
  qed

  definition ltsbm_pre_it where
   "ltsbm_pre_it it (ts::'ts) (q'::'Q) (a::'A) = it ts a q'"

  lemma ltsbm_pre_it_correct :
    assumes "triple_set_B_it ts_\<alpha> ts_invar it"
    shows "lts_pre_it ltsbm_\<alpha> ltsbm_invar (ltsbm_pre_it it)"
  using assms
  unfolding lts_pre_it_def triple_set_B_it_def ltsbm_pre_it_def ltsbm_invar_def ltsbm_\<alpha>_alt_def
  by simp

  definition ltsbm_pre_label_it where
   "ltsbm_pre_label_it it (ts::'ts) (q::'Q) = 
    set_iterator_image (\<lambda>(a, q'). (q', a)) (it ts q)"

  lemma ltsbm_pre_label_it_correct :
    assumes AB_it: "triple_set_AB_it ts_\<alpha> ts_invar it"
    shows "lts_pre_label_it ltsbm_\<alpha> ltsbm_invar (ltsbm_pre_label_it it)"
  unfolding lts_pre_label_it_def
  proof (intro allI impI)
    fix ts q'
    assume invar_ts: "ltsbm_invar ts"
   
    let ?S1 = "{(a, q) . (q, a, q') \<in> ltsbm_\<alpha> ts}"
    let ?S2 = "{(q, a) . (q, a, q') \<in> ltsbm_\<alpha> ts}"

    from triple_set_AB_it.triple_set_AB_it_correct [OF AB_it, of ts] invar_ts 
    have step: "set_iterator (it ts q') ?S1"
      unfolding triple_set_BC_it_def ltsbm_\<alpha>_alt_def ltsbm_invar_def by simp
    
    show "set_iterator (ltsbm_pre_label_it it ts q') ?S2" 
    unfolding ltsbm_pre_label_it_def
      apply (rule set_iterator_image_correct[OF step])
      apply (auto simp add: inj_on_def)
    done
  qed
end

end
