theory IICF_Array_List
imports "../Intf/IICF_List" "../../../ds/LLVM_DS_Array_List"
begin
  
abbreviation (input) "raw_al_assn \<equiv> \<upharpoonleft>arl_assn"

definition "al_assn R \<equiv> hr_comp raw_al_assn (\<langle>the_pure R\<rangle>list_rel)"

abbreviation "al_assn' TYPE('l::len2) R \<equiv> al_assn R :: (_ \<Rightarrow> (_,'l)array_list \<Rightarrow> _)"

lemma arl_assn_free[sepref_frame_free_rules]: "MK_FREE (\<upharpoonleft>arl_assn) arl_free"
  apply rule by vcg

lemma al_assn_free[sepref_frame_free_rules]: "MK_FREE (al_assn R) arl_free"
  unfolding al_assn_def by (rule sepref_frame_free_rules)+

lemma al_assn_boundD[sepref_bounds_dest]: 
  "rdomp (al_assn' TYPE('l::len2) A) xs \<Longrightarrow> length xs < max_snat LENGTH('l)"
  unfolding al_assn_def arl_assn_def arl_assn'_def
  apply (simp add: rdomp_hrcomp_conv sep_algebra_simps split: prod.splits)
  by (auto 
    simp: rdomp_def snat.assn_def sep_algebra_simps pred_lift_extract_simps
    list_rel_imp_same_length[symmetric]
    )
  
lemma rdomp_al_dest': 
  "rdomp (al_assn' TYPE('l::len2) A) xs \<Longrightarrow> is_pure A \<Longrightarrow> length xs < max_snat LENGTH('l) \<and> (\<forall>i<length xs. rdomp A (xs!i))"
  unfolding al_assn_def arl_assn_def arl_assn'_def
  apply (simp add: rdomp_hrcomp_conv sep_algebra_simps split: prod.splits)
  apply (auto 
    simp: rdomp_def snat.assn_def sep_algebra_simps pred_lift_extract_simps
    list_rel_imp_same_length[symmetric]
    )
  by (auto 0 3 simp: list_rel_def list_all2_conv_all_nth is_pure_conv pure_app_eq pred_lift_extract_simps)
    
      
text \<open>This functions deletes all elements of a resizable array, without resizing it.\<close>
sepref_decl_op emptied_list: "\<lambda>_::'a list. []::'a list" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .

sepref_decl_op al_custom_replicate: op_list_replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .

lemma al_fold_custom_replicate:
  "replicate = op_al_custom_replicate"
  "op_list_replicate = op_al_custom_replicate"
  "mop_list_replicate = mop_al_custom_replicate"
  by (auto simp: fun_eq_iff)


context
  fixes l_dummy :: "'l::len2 itself" 
    and L AA
  defines [simp]: "L \<equiv> (LENGTH ('l))"
  defines [simp]: "AA \<equiv> raw_al_assn :: _ \<Rightarrow> (_,'l) array_list \<Rightarrow> _" 
begin

private lemma n_unf: "hr_comp AA (\<langle>the_pure A\<rangle>list_rel) = al_assn A" unfolding al_assn_def AA_def ..

private lemma params: 
  "(max_snat, max_snat) \<in> Id \<rightarrow> Id"
  "(L,L)\<in>nat_rel"
  by auto

  
context 
  notes [fcomp_norm_unfold] = n_unf
  notes [param] = params
  notes [simp] = refine_pw_simps
begin  

  thm bool1_rel_def bool.assn_is_rel[symmetric]

  private method m_ref =     
      ((unfold snat_rel_def snat.assn_is_rel[symmetric] bool1_rel_def bool.assn_is_rel[symmetric])?,
       sepref_to_hoare, vcg_monadify,
       vcg')

       
  lemma al_empty_hnr_aux: 
    "(uncurry0 (arl_new_raw::(_,'l::len2)array_list llM), uncurry0 (RETURN op_list_empty)) 
      \<in> [\<lambda>_. 4 < L]\<^sub>a unit_assn\<^sup>k \<rightarrow> AA"
    by m_ref  
  sepref_decl_impl (no_register) al_empty: al_empty_hnr_aux .
       
  lemma al_replicate_hnr_aux:
    "(uncurry arl_new_repl, uncurry (RETURN oo op_al_custom_replicate)) 
    \<in> [\<lambda>_. 4 < L]\<^sub>a (snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
    by m_ref
  sepref_decl_impl al_replicate: al_replicate_hnr_aux .
  

  lemma al_nth_hnr_aux: "(uncurry arl_nth, uncurry mop_list_get) 
    \<in> AA\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    by m_ref  
    
  sepref_decl_impl (ismop) al_nth: al_nth_hnr_aux .
      
  lemma al_upd_hnr_aux: "(uncurry2 arl_upd, uncurry2 mop_list_set) 
    \<in> AA\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a AA"
    by m_ref  
  sepref_decl_impl (ismop) al_upd: al_upd_hnr_aux .
  
  lemma al_append_hnr_aux: "(uncurry arl_push_back, uncurry mop_list_append)
    \<in> [\<lambda>(xs,_). length xs + 1 < max_snat L]\<^sub>a AA\<^sup>d *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
    by m_ref  
  sepref_decl_impl (ismop) al_append: al_append_hnr_aux .

  lemma al_take_hnr_aux: "(uncurry arl_take, uncurry mop_list_take)
    \<in> snat_assn\<^sup>k *\<^sub>a AA\<^sup>d \<rightarrow>\<^sub>a AA"
    by m_ref  
  sepref_decl_impl (ismop) al_take: al_take_hnr_aux .
  
  lemma al_pop_last_hnr_aux: "(arl_pop_back, mop_list_pop_last)
    \<in> AA\<^sup>d \<rightarrow>\<^sub>a id_assn \<times>\<^sub>a AA"
    by m_ref  
  sepref_decl_impl (ismop) al_pop_last: al_pop_last_hnr_aux .
  
  lemma al_butlast_hnr_aux: "(arl_butlast, mop_list_butlast) \<in> AA\<^sup>d \<rightarrow>\<^sub>a AA"
    by m_ref
  sepref_decl_impl (ismop) al_butlast: al_butlast_hnr_aux .

  lemma al_last_hnr_aux: "(arl_last, mop_list_last) \<in> AA\<^sup>k \<rightarrow>\<^sub>a id_assn"
    by m_ref
  sepref_decl_impl (ismop) al_last: al_last_hnr_aux .
    
  lemma al_len_hnr_aux: "(arl_len, mop_list_length) \<in> AA\<^sup>k \<rightarrow>\<^sub>a snat_assn"
    by m_ref  
  sepref_decl_impl (ismop) al_len: al_len_hnr_aux .

  lemma al_is_empty_hnr_aux: 
    "(\<lambda>al. doM { l\<leftarrow>arl_len al; ll_icmp_eq l (signed_nat 0) }, mop_list_is_empty) \<in> AA\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    by m_ref
  sepref_decl_impl (ismop) al_is_empty: al_is_empty_hnr_aux .

  lemma al_emptied_hnr_aux: "(arl_clear,mop_emptied_list)\<in>AA\<^sup>d\<rightarrow>\<^sub>aAA"
    by m_ref
  sepref_decl_impl (ismop) al_emptied_hnr_aux .
    
    
end

end

  definition [simp]: "op_al_empty TYPE('l::len2) \<equiv> op_list_empty"     
  sepref_register "op_al_empty TYPE('l::len2)"
  lemma al_custom_empty_hnr[sepref_fr_rules]: 
    "(uncurry0 arl_new_raw, uncurry0 (RETURN (PR_CONST (op_al_empty TYPE('l::len2))))) 
      \<in> [\<lambda>_. 4<LENGTH('l)]\<^sub>a unit_assn\<^sup>k \<rightarrow> al_assn' TYPE('l) A"
    apply simp
    apply (rule al_empty_hnr[simplified])
    done
  
  lemma al_fold_custom_empty:
    "[] = op_al_empty TYPE('l::len2)"
    "op_list_empty = op_al_empty TYPE('l::len2)"
    "mop_list_empty = RETURN (op_al_empty TYPE('l::len2))"
    by auto
  



subsection \<open>Ad-Hoc Regression Tests\<close>

experiment
begin

  sepref_definition example [llvm_code] is "\<lambda>n. do {
    let l = op_list_empty; 
    l \<leftarrow> mop_list_append l 42;
    l \<leftarrow> mop_emptied_list l;
    l \<leftarrow> mop_list_append l 43;
    l \<leftarrow> mop_list_append l 44;
    l \<leftarrow> mop_list_append l 45;
    l \<leftarrow> mop_list_append l 46;
    let x = l!2;
    let l = l[2:=l!3];
    l \<leftarrow> mop_list_set l 3 x;
    let (_,l) = op_list_pop_last l;
    
    l2 \<leftarrow> mop_list_replicate 100 False;
    l2 \<leftarrow> mop_list_append l2 True;
    l2 \<leftarrow> mop_list_append l2 True;
    l2 \<leftarrow> mop_list_append l2 False;
    l2 \<leftarrow> mop_list_set l2 3 True;
    
    RETURN l
  }" :: "(snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a al_assn' TYPE(32) (snat_assn' TYPE(32))"
    apply (annot_snat_const "TYPE(32)")
    apply (rewrite al_fold_custom_empty[where 'l=32])
    apply (rewrite al_fold_custom_replicate)
    by sepref
    
  export_llvm example


end




            
        
end
