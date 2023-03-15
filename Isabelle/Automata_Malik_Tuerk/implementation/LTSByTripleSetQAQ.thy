header "Implementing Labelled Transition Systems by a TripleSet"
theory LTSByTripleSetQAQ
imports TripleSetSpec LTSSpec LTSGA
begin


locale ltsbm_QAQ_defs = 
  ts: triple_set ts_\<alpha> ts_invar
  for ts_\<alpha>::"'ts \<Rightarrow> ('Q \<times> 'A \<times> 'Q) set"
  and ts_invar
begin

  abbreviation ltsbm_\<alpha> :: "('Q,'A,'ts) lts_\<alpha>" where "ltsbm_\<alpha> \<equiv> ts_\<alpha>"
  abbreviation "ltsbm_invar \<equiv> ts_invar"

  lemma ltsbm_empty_correct: 
    "triple_set_empty ts_\<alpha> ts_invar emp \<Longrightarrow>
     lts_empty ltsbm_\<alpha> ltsbm_invar emp"    
    unfolding lts_empty_def triple_set_empty_def
    by simp

  lemma ltsbm_memb_correct: 
    "triple_set_memb ts_\<alpha> ts_invar memb \<Longrightarrow>
     lts_memb ltsbm_\<alpha> ltsbm_invar memb"    
    unfolding lts_memb_def triple_set_memb_def
    by simp

  lemma ltsbm_add_correct:
    "triple_set_add ts_\<alpha> ts_invar add \<Longrightarrow>
     lts_add ltsbm_\<alpha> ltsbm_invar add"
  unfolding lts_add_def triple_set_add_def by simp

  lemma ltsbm_add_succs_correct:
    "triple_set_add_Cl ts_\<alpha> ts_invar add_Cl \<Longrightarrow>
     lts_add_succs ltsbm_\<alpha> ltsbm_invar add_Cl"
    unfolding lts_add_succs_def triple_set_add_Cl_def by auto

  lemma ltsbm_delete_correct:
    "triple_set_delete ts_\<alpha> ts_invar ts_del \<Longrightarrow>
     lts_delete ltsbm_\<alpha> ltsbm_invar ts_del"
    unfolding lts_delete_def triple_set_delete_def by simp

  lemma ltsbm_succ_it_correct :
    assumes "triple_set_C_it ts_\<alpha> ts_invar it"
    shows "lts_succ_it ltsbm_\<alpha> ltsbm_invar it"
  using assms unfolding lts_succ_it_def triple_set_C_it_def by simp

  lemma ltsbm_succ_label_it_correct :
    assumes "triple_set_BC_it ts_\<alpha> ts_invar it"
    shows "lts_succ_label_it ltsbm_\<alpha> ltsbm_invar it"
  using assms 
  unfolding lts_succ_label_it_def triple_set_BC_it_def 
  by simp

  lemma ltsbm_filter_it_correct :
    assumes "triple_set_filter_it ts_\<alpha> ts_invar it"
    shows "lts_filter_it ltsbm_\<alpha> ltsbm_invar it"
  using assms
  unfolding lts_filter_it_def triple_set_filter_it_def 
  by simp

  lemma ltsbm_it_correct :
    assumes "triple_set_iterator ts_\<alpha> ts_invar it"
    shows "lts_iterator ltsbm_\<alpha> ltsbm_invar it"
  using assms
  unfolding lts_iterator_def triple_set_iterator_def 
  by simp


  definition ltsbm_pre_it where
   "ltsbm_pre_it it (ts::'ts) (q'::'Q) (a::'A) = it ts a q'"

  lemma ltsbm_pre_it_correct :
    assumes "triple_set_A_it ts_\<alpha> ts_invar it"
    shows "lts_pre_it ltsbm_\<alpha> ltsbm_invar (ltsbm_pre_it it)"
  using assms
  unfolding lts_pre_it_def triple_set_A_it_def ltsbm_pre_it_def 
  by simp

  lemma ltsbm_pre_label_it_correct :
    assumes "triple_set_AB_it ts_\<alpha> ts_invar it"
    shows "lts_pre_label_it ltsbm_\<alpha> ltsbm_invar it"
  using assms
  unfolding lts_pre_label_it_def triple_set_AB_it_def 
  by simp
end

end
