\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Arrays and Option Arrays\<close>
theory Hnr_Primitives_Experiment
imports Sepref "../ds/LLVM_DS_Dflt"
begin
  hide_const (open) LLVM_DS_Array.array_assn


paragraph \<open>Summary\<close>
text \<open>This theory introduces monadic operations on lists and lists with explicit ownership.
    Then it defines data strucutres for arrays and arrays with explicit ownership.\<close>


  abbreviation "raw_array_assn \<equiv> \<upharpoonleft>LLVM_DS_NArray.narray_assn"

lemma satminus_lift_acost: "satminus ta (the_acost (lift_acost t) b) = 0 \<longleftrightarrow> ta \<le> the_acost t b"
  unfolding satminus_def lift_acost_def by auto

term lift_acost
lemma hnr_SPECT_D:
  fixes \<Phi> :: "_ \<Rightarrow> ((_,enat) acost) option"
  shows
      "do { ASSERT P; consume (RETURNT x) (lift_acost t) } = SPECT \<Phi>
      \<Longrightarrow> P \<and> Some (lift_acost t) \<le> \<Phi> x"
  apply(simp add: pw_acost_eq_iff)
  apply(simp add: refine_pw_simps)
  apply(auto simp: satminus_lift_acost)
  apply(cases "\<Phi> x")
  subgoal    
    by force  
  subgoal  premises prems for e
    apply(rule acost_componentwise_leI[where e=e] )
    subgoal using prems by simp  
    subgoal for b
      using prems(2)[rule_format, where x=x and t="the_acost t b" and b=b]
      using prems(3)      
      by (auto simp: lift_acost_def)
    done
  done

lemma lift_acost_plus_distrib[named_ss fri_prepare_simps]:
  "$lift_acost (a + b) = ($lift_acost a ** $lift_acost b)"
  unfolding time_credits_assn_def lift_acost_def SND_def EXACT_def
  apply (cases a; cases b)
  apply (auto simp add: sep_algebra_simps fun_eq_iff sep_conj_def sep_disj_acost_def sep_disj_enat_def)
  done

(* BEWARE, conflicting abbreviation snat_assn *)
lemma snat_assn_to_basic_layer: "snat_assn = \<upharpoonleft>snat.assn" 
  by (simp add: snat.assn_is_rel snat_rel_def)   
                                     
lemma DECOMP_HNR[vcg_decomp_rules]: "DECOMP_HTRIPLE (hn_refine \<Gamma> c \<Gamma>' R a) \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a" by (simp add: vcg_tag_defs)

lemma hn_refine_pre_pureI:
  assumes "pure_part \<Gamma> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  using assms unfolding hn_refine_def
  apply auto
  using prep_ext_state pure_part_split_conj by blast


lemma hnr_mop_vcgI[htriple_vcg_intros]: 
  assumes "\<And>F s cr. \<lbrakk>\<Phi>; pure_part \<Gamma>; llSTATE (\<Gamma>**F**$(lift_acost t)) (s,cr+(lift_acost t))\<rbrakk> \<Longrightarrow> 
                     EXTRACT (wp c (\<lambda>ri. POSTCOND ll_\<alpha> (\<Gamma>' ** R r ri ** F ** GC)) (s,cr+lift_acost t))"
  shows "hn_refine \<Gamma> c \<Gamma>' R (do {ASSERT \<Phi>; consume (RETURNT r) (lift_acost t)})"  
  apply (rule hn_refine_pre_pureI)
  apply (rule hnr_vcgI)
  apply(drule hnr_SPECT_D, clarify)
  apply (rule exI[where x="r"])
  apply (rule exI[where x="t"])
  using assms by blast

lemmas hnr_mop_vcgI_nopre[htriple_vcg_intros] = hnr_mop_vcgI[where \<Phi>=True, simplified]  


subsection \<open>List Operations\<close>

subsubsection \<open>Monadic List Operations\<close>

context
  fixes  T :: "(nat \<times> nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_list_get  :: "'a list \<Rightarrow> nat \<Rightarrow> ('a, _) nrest"
    where [simp]: "mop_list_get xs i \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs!i)) (T (length xs,i)) }"
  sepref_register "mop_list_get"
end

lemma param_mop_list_get:
  "(mop_list_get T, mop_list_get T) \<in> \<langle>the_pure A\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>the_pure A\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_list_get_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 


context
  fixes  T :: "(nat \<times> unit \<times> unit) \<Rightarrow> (char list, enat) acost"
begin
  definition [simp]: "mop_list_set xs i x \<equiv> do { ASSERT (i<length xs); consume (RETURNT (xs[i:=x])) (T (length xs,(),())) }"
  sepref_register "mop_list_set"
  print_theorems
end

lemma param_mop_list_set:
  "(mop_list_set T, mop_list_set T) \<in> \<langle>the_pure A\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> (the_pure A) \<rightarrow> \<langle>\<langle>the_pure A\<rangle> list_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_list_set_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 

context
  fixes  T :: "(nat \<times> unit) \<Rightarrow> (char list, enat) acost"
begin
  definition [simp]: "mop_list_replicate n x \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n x)) (T (n,())) }"
  sepref_register "mop_list_replicate"
end

lemma param_mop_list_replicate:
  "(mop_list_replicate T, mop_list_replicate T) \<in> nat_rel \<rightarrow> (A) \<rightarrow> \<langle>\<langle>A\<rangle> list_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_list_replicate_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 


context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition [simp]: "mop_list_init x n \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n x)) (T n) }"
  definition [simp]: "mop_list_init_raw n \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n init)) (T n) }"
  context fixes x begin sepref_register "mop_list_init x" end
  sepref_register "mop_list_init_raw"
end

find_theorems is_init
(* TODO: is it parametric ? It is with a precondition! *)
lemma refine_mop_list_init_raw:
  assumes "GEN_ALGO x (is_init A)"
  shows "(mop_list_init_raw T, PR_CONST (mop_list_init T x)) \<in> nat_rel \<rightarrow> \<langle>\<langle>the_pure A\<rangle> list_rel\<rangle> nrest_rel"
  using assms
  apply(intro nrest_relI fun_relI)
  unfolding mop_list_init_def mop_list_init_raw_def
  unfolding GEN_ALGO_def is_init_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 



subsubsection \<open>Monadic Option List Operations\<close>

context
  fixes  T :: "(nat \<times> unit) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_eo_extract  :: "'a option list \<Rightarrow> nat \<Rightarrow> (_, _) nrest"
    where [simp]: "mop_eo_extract xs i \<equiv> do { ASSERT (i<length xs \<and> xs!i\<noteq>None); consume (RETURNT (the (xs!i), xs[i:=None])) (T (length xs,())) }"
  sepref_register "mop_eo_extract"
end

(* TODO:  is it not parametric?
lemma param_mop_olist_get:
  "(mop_olist_get T, mop_olist_get T) \<in> \<langle>\<langle>the_pure A\<rangle> option_rel\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>the_pure A\<times>\<^sub>r\<langle>\<langle>the_pure A\<rangle> option_rel\<rangle> list_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_olist_get_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 
*)

context
  fixes  T :: "(nat \<times> unit \<times> unit) \<Rightarrow> (char list, enat) acost"
begin
  definition [simp]: "mop_eo_set xs i x \<equiv> do { ASSERT (i<length xs \<and> xs!i=None); consume (RETURNT (xs[i:=Some x])) (T (length xs,(),())) }"
  sepref_register "mop_eo_set"
  print_theorems
end

context
  fixes  T :: "(nat) \<Rightarrow> (char list, enat) acost"
begin
  definition [simp]: "mop_olist_new n \<equiv> do { ASSERT (PROTECT True); consume (RETURNT (replicate n None)) (T n) }"
  sepref_register "mop_olist_new"
end

lemma param_mop_olist_new:
  "(mop_olist_new T, mop_olist_new T) \<in> nat_rel \<rightarrow> \<langle>\<langle>\<langle>the_pure A\<rangle> option_rel\<rangle> list_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_olist_new_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 


subsubsection \<open>Array Operation costs\<close>

abbreviation "mop_array_nth_cost \<equiv> (cost ''load'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))"
abbreviation "mop_array_upd_cost \<equiv> (cost ''store'' (Suc 0)+cost ''ofs_ptr'' (Suc 0))"
abbreviation "cost'_narray_new n \<equiv> cost ''malloc'' n + cost ''free'' 1 + cost ''if'' 1 + cost ''if'' 1 + cost ''icmp_eq'' 1 + cost ''ptrcmp_eq'' 1"

  
subsection \<open>Option Array\<close>
    
  
text \<open>Assertion that adds constraint on concrete value. Used to carry through concrete equalities.\<close>
definition "cnc_assn \<phi> A a c \<equiv> \<up>(\<phi> c) ** A a c"


lemma cnc_assn_prod_conv[named_ss sepref_frame_normrel]:
  shows "\<And>A B \<phi>. A \<times>\<^sub>a cnc_assn \<phi> B = cnc_assn (\<phi> o snd) (A\<times>\<^sub>aB)"
    and "\<And>A B \<phi>. cnc_assn \<phi> A \<times>\<^sub>a B = cnc_assn (\<phi> o fst) (A\<times>\<^sub>aB)"
  unfolding cnc_assn_def
  by (auto simp: sep_algebra_simps fun_eq_iff)


lemma norm_ceq_assn[named_ss sepref_frame_normrel]: "hn_ctxt (cnc_assn \<phi> A) a c = (\<up>(\<phi> c) ** hn_ctxt A a c)"
  unfolding hn_ctxt_def cnc_assn_def by simp
  

definition "mop_oarray_extract \<equiv> mop_eo_extract (\<lambda>_. lift_acost mop_array_nth_cost)"
lemma "mop_oarray_extract xs i = doN { ASSERT (i<length xs \<and> xs!i\<noteq>None); consume (RETURNT (the (xs!i), xs[i:=None])) (lift_acost mop_array_nth_cost) }"
  by(auto simp: mop_oarray_extract_def)
definition "mop_oarray_upd \<equiv> mop_eo_set (\<lambda>_. lift_acost mop_array_upd_cost)"
lemma "mop_oarray_upd xs i x = do { ASSERT (i<length xs \<and> xs!i=None); consume (RETURNT (xs[i:=Some x])) (lift_acost mop_array_upd_cost) }"
  by(auto simp: mop_oarray_upd_def)
definition "mop_oarray_new \<equiv> mop_olist_new (\<lambda>n. lift_acost (cost'_narray_new n))"
lemma "mop_oarray_new n = consume (RETURNT (replicate n None)) (lift_acost (cost'_narray_new n))"
  by(auto simp: mop_oarray_new_def)

      
sepref_register mop_oarray_extract
  
definition "eoarray_assn A \<equiv> \<upharpoonleft>(nao_assn (mk_assn A))"

definition [llvm_inline]: "eoarray_nth_impl xsi ii \<equiv> doM {
  r \<leftarrow> array_nth xsi ii;
  return (r,xsi)
}"  
  
lemma hnr_eoarray_nth: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii)
  (eoarray_nth_impl xsi ii)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii)
  (cnc_assn (\<lambda>(_,xsi'). xsi'=xsi) (A \<times>\<^sub>a eoarray_assn A))
  (mop_oarray_extract $ xs $ i)"  
  unfolding snat_assn_to_basic_layer
  unfolding  hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_extract_def eoarray_nth_impl_def
  by vcg 
\<comment> \<open>thm hnr_eoarray_nth[sepref_fr_rules] (* BEWARE: needs $ for APP *) \<close>


lemma hnr_eoarray_nth'[sepref_fr_rules]: "(uncurry eoarray_nth_impl, uncurry mop_oarray_extract)
       \<in> (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>x (ai, _). A \<times>\<^sub>a cnc_assn (\<lambda>x. x = ai) (eoarray_assn A))"
  unfolding snat_assn_to_basic_layer
  apply(rule hfrefI)
  unfolding to_hnr_prod_fst_snd keep_drop_sels hf_pres_fst mop_oarray_extract_def hn_ctxt_def
            pure_def invalid_assn_def cnc_assn_def eoarray_assn_def eoarray_nth_impl_def
  by vcg

lemma hnr_eoarray_upd: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt A x xi)
  (array_upd xsi ii xi)
  (hn_invalid (eoarray_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_invalid A x xi)
  (cnc_assn (\<lambda>ri. ri=xsi) (eoarray_assn A))
  (mop_oarray_upd $ xs $ i $ x)"  
  unfolding snat_assn_to_basic_layer
  unfolding hn_ctxt_def pure_def invalid_assn_def cnc_assn_def eoarray_assn_def mop_oarray_upd_def
  by vcg

(* write in higher order form *)
lemma hnr_eoarray_upd'[sepref_fr_rules]: "(uncurry2 array_upd, uncurry2 mop_oarray_upd)
       \<in> (eoarray_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>x ((ai, _), _). cnc_assn (\<lambda>x. x = ai) (eoarray_assn A))"
  unfolding snat_assn_to_basic_layer
  apply(rule hfrefI)
  unfolding to_hnr_prod_fst_snd keep_drop_sels hf_pres_fst mop_oarray_upd_def hn_ctxt_def pure_def
            invalid_assn_def cnc_assn_def eoarray_assn_def eoarray_nth_impl_def
  by vcg

(* thm hnr_eoarray_upd[sepref_fr_rules] *)
(* thm hnr_eoarray_upd[to_hfref] TODO: BUG, to_hfref loops here*)
   
lemma hnr_eoarray_new: "hn_refine 
  (hn_ctxt snat_assn i ii)
  (narrayo_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn i ii)
  (eoarray_assn A)
  (mop_oarray_new i)" 
  unfolding snat_assn_to_basic_layer
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_oarray_new_def
  by vcg

lemma hnr_eoarray_new'[sepref_fr_rules]: "( (narrayo_new TYPE('a::llvm_rep)), mop_oarray_new )
       \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a (eoarray_assn A)"
  unfolding snat_assn_to_basic_layer
  apply(rule hfrefI)
  unfolding to_hnr_prod_fst_snd keep_drop_sels hf_pres_fst hn_ctxt_def pure_def invalid_assn_def mop_oarray_new_def cnc_assn_def eoarray_assn_def eoarray_nth_impl_def
  by vcg

    
definition "mop_oarray_free xs \<equiv> do { ASSERT (set xs \<subseteq> {None}); consume (RETURNT ()) (lift_acost 0) }"
  
lemma hnr_eoarray_free[sepref_fr_rules]: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi)
  (narray_free xsi)
  (hn_invalid (eoarray_assn A) xs xsi)
  (id_assn)
  (mop_oarray_free $ xs)"
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_oarray_free_def
  apply vcg_step
  apply vcg_step
  by vcg
  
(* This rule does not hold! The elements must be de-allocated first!  
  for explicit ownership management, free the array manually using mop_oarray_free!   
lemma FREE_eoarray_assn[sepref_frame_free_rules]:
  shows "MK_FREE (eoarray_assn A) narray_free"  
  apply (rule MK_FREEI)
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_oarray_free_def
  apply vcg_step
  apply vcg_step
  apply vcg_step
  sorry  
*)  
  
  
(* Conversions between plain array and explicit ownership array*)  
definition "mop_to_eo_conv xs \<equiv> do { consume (RETURNT (map Some xs)) (lift_acost 0) }"  
definition "mop_to_wo_conv xs \<equiv> do { ASSERT (None\<notin>set xs); consume (RETURNT (map the xs)) (lift_acost 0) }"  


sepref_register mop_to_eo_conv

  lemma mop_to_eo_conv_alt: "mop_to_eo_conv xs \<equiv> (RETURNT (map Some xs)) "
    unfolding mop_to_eo_conv_def lift_acost_zero  consume_0 .


lemma mop_to_eo_conv_refine: "wfR'' R \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> mop_to_eo_conv xs \<le> \<Down> Id (timerefine R (mop_to_eo_conv xs'))"
  unfolding mop_to_eo_conv_def
  apply(intro refine0)
  by (auto simp: lift_acost_zero  simp del: conc_Id )
  
lemma mop_to_wo_conv_refines: "wfR'' R \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> mop_to_wo_conv a \<le> \<Down> Id (timerefine R (mop_to_wo_conv a'))"
  unfolding mop_to_wo_conv_def 
  apply(intro refine0 bindT_refine_easy SPECc2_refine')
  by (auto simp: lift_acost_zero) 


(* XXX: Need "array_assn A" first for this to be meaningful! ra-comp! *)  
  
definition "some_rel \<equiv> br the (Not o is_None)"
definition "array_assn A \<equiv> hr_comp (eoarray_assn A) (\<langle>some_rel\<rangle>list_rel)"

lemma map_the_some_rel_list_rel_iff: "(xs, map the xs) \<in> \<langle>some_rel\<rangle>list_rel \<longleftrightarrow> None \<notin> set xs"
  unfolding some_rel_def
  apply (auto simp: map_in_list_rel_conv split: option.splits)
  by (metis option.exhaust)

  
lemma map_in_list_rel_br_iff: "(map f xs, xs) \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> (\<forall>x\<in>set xs. I (f x) \<and> \<alpha> (f x) = x)"  
  apply (induction xs)
  apply (auto simp: in_br_conv)
  done
  
lemma in_br_list_rel_conv: "(xs,ys) \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> (\<forall>x\<in>set xs. I x) \<and> ys = map \<alpha> xs"  
  apply (rule)
  subgoal premises prems
    using prems
    apply (induction rule: list_rel_induct)
    by (auto simp: in_br_conv)
  subgoal by (auto simp: map_in_list_rel_conv)
  done
  
lemma in_some_rel_list_rel_conv: "(x,xi) \<in>\<langle>some_rel\<rangle>list_rel \<longleftrightarrow> x = map Some xi"
  unfolding some_rel_def
  by (auto simp: in_br_list_rel_conv map_idI split: option.splits)
  
  
(* Conversion between implicit and explicit ownership array *)
  
lemma hnr_to_wo_conv[sepref_fr_rules]: "hn_refine 
  (hn_ctxt (eoarray_assn A) xs xsi)
  (return xsi)
  (hn_invalid (eoarray_assn A) xs xsi)
  (array_assn A)
  (mop_to_wo_conv $ xs)"
  unfolding mop_to_wo_conv_def
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def 
    array_assn_def hr_comp_def
  apply Basic_VCG.vcg'
  apply (simp add: map_the_some_rel_list_rel_iff)
  done

lemma mop_to_wo_conv_hnr_dep: "(return,mop_to_wo_conv)\<in>(eoarray_assn A)\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ xi. cnc_assn (\<lambda>x. x=xi) (array_assn A))"
  unfolding mop_to_wo_conv_def cnc_assn_def
  apply(rule hfrefI) apply simp
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def 
    array_assn_def hr_comp_def
  apply Basic_VCG.vcg'
  apply (simp add: map_the_some_rel_list_rel_iff)
  done
  

lemma hnr_to_eo_conv[sepref_fr_rules]: "hn_refine 
  (hn_ctxt (array_assn A) xs xsi)
  (return xsi)
  (hn_invalid (array_assn A) xs xsi)
  (eoarray_assn A)
  (mop_to_eo_conv $ xs)"
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def mop_to_eo_conv_def
    array_assn_def hr_comp_def
  supply [simp] = in_some_rel_list_rel_conv
  by vcg


lemma mop_to_eo_conv_hnr_dep: "(return,mop_to_eo_conv)\<in>(array_assn A)\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ xi. cnc_assn (\<lambda>x. x=xi) (eoarray_assn A))"
  unfolding mop_to_eo_conv_def cnc_assn_def
  apply(rule hfrefI) apply simp
  unfolding mop_to_eo_conv_def cnc_assn_def
  unfolding hn_ctxt_def pure_def invalid_assn_def eoarray_assn_def 
    array_assn_def hr_comp_def
  supply [simp] = in_some_rel_list_rel_conv
  by vcg

(* Array operations for pure content, backed by eoarray *)  

lemma the_pure_pure_part_conv: "is_pure A \<Longrightarrow> the_pure A = {(c,a). pure_part (A a c)}"
  apply safe
  subgoal by (metis Sepref_Basic.pure_part_pure pure_the_pure)
  subgoal by (metis Sepref_Basic.pure_part_pure pure_the_pure)
  done

lemma is_pure_assn_pred_lift: "is_pure A \<Longrightarrow> A a c = \<up>((c,a)\<in>the_pure A)"
  by (metis Sepref_Basic.pure_def pure_the_pure)

lemma pure_list_assn_list_rel_conv: "is_pure A \<Longrightarrow> \<upharpoonleft>(list_assn (mk_assn A)) xs xsi = \<up>((xsi,xs)\<in>\<langle>the_pure A\<rangle>list_rel)"
proof (induction xs arbitrary: xsi)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    apply (cases xsi; simp)
    by (auto simp add: sep_algebra_simps pred_lift_extract_simps fun_eq_iff is_pure_assn_pred_lift)
  
qed

definition [to_relAPP]: "oelem_rel A \<equiv> {(c,a) . case a of None \<Rightarrow> True | Some b \<Rightarrow> (c,b)\<in>A}"

lemma oelem_pure_assn_conv: "oelem_assn (mk_assn (pure A)) = mk_assn (pure (\<langle>A\<rangle>oelem_rel))"
  unfolding oelem_assn_def sel_mk_assn oelem_rel_def
  apply (rule arg_cong[where f=mk_assn])
  by (auto simp: fun_eq_iff pure_def sep_algebra_simps split: option.split )

  
lemma map_some_oelem_list_rel_conv: "(xs, map Some ys) \<in> \<langle>\<langle>R\<rangle>oelem_rel\<rangle>list_rel \<longleftrightarrow> (xs,ys) \<in> \<langle>R\<rangle>list_rel"  
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    apply (cases ys)
    by (auto simp: oelem_rel_def)
    
qed


  definition "unborrow src dst \<equiv> doN {ASSERT (src=dst); RETURN ()}"
  sepref_register unborrow

  lemma unborrow_rule[sepref_comb_rules]:
    assumes FRAME: "\<Gamma> \<turnstile> hn_ctxt R src srci ** hn_invalid R dst dsti ** F"
    assumes [simp]: "vassn_tag \<Gamma> \<Longrightarrow> srci = dsti"
    shows "hn_refine \<Gamma> (return ():: _ llM) (hn_invalid R src srci ** hn_ctxt R dst dsti ** F) unit_assn (unborrow$src$dst)"
    apply (rule hn_refine_vassn_tagI)
    apply (rule hn_refine_cons_pre[rotated,OF FRAME])
    unfolding unborrow_def APP_def
    apply (rule hn_refineI'')
    apply (simp add: refine_pw_simps)
    unfolding hn_ctxt_def invalid_assn_def pure_def
    by vcg'



subsection \<open>Array\<close>

definition "mop_array_nth \<equiv> mop_list_get (\<lambda>_. lift_acost mop_array_nth_cost) "
definition "mop_array_upd \<equiv> mop_list_set (\<lambda>_. lift_acost mop_array_upd_cost)"
definition mop_array_new :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest"
  where "mop_array_new A \<equiv> mop_list_init (\<lambda>n. lift_acost (cost'_narray_new n))"

context fixes A :: "'a \<Rightarrow> 'c \<Rightarrow> assn" and x :: 'a begin
  sepref_register "mop_array_new A x"
end


subsubsection \<open>Raw hnr rules\<close>

thm vcg_rules
lemma hnr_raw_array_nth: "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  id_assn
  (mop_array_nth xs i)" 
  unfolding snat_assn_to_basic_layer
  unfolding hn_ctxt_def pure_def mop_array_nth_def
  apply vcg_step
  apply vcg_step
  by vcg

(*lemma hnr_raw_array_upd: "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt id_assn x xi)
  (array_upd xsi ii xi)
  (hn_invalid raw_array_assn xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt id_assn x xi)
  raw_array_assn
  (mop_array_upd $ xs $ i $ x)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_upd_def
  by vcg
*)  

lemma hnr_raw_array_upd: "((uncurry2 array_upd, uncurry2 mop_array_upd)
       \<in> [\<lambda>((a, b), x). True]\<^sub>a raw_array_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> raw_array_assn)"
  unfolding snat_assn_to_basic_layer
  apply(intro hfrefI)
  unfolding to_hnr_prod_fst_snd keep_drop_sels hf_pres_fst hn_ctxt_def pure_def invalid_assn_def mop_array_upd_def
  by vcg


lemma hnr_raw_array_new: 
  "(narray_new TYPE('a::llvm_rep), mop_list_init_raw (\<lambda>n. lift_acost (cost'_narray_new n))) : snat_assn\<^sup>k \<rightarrow>\<^sub>a raw_array_assn"
  unfolding snat_assn_to_basic_layer
  apply (rule hfrefI)
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_new_def mop_list_init_raw_def
  by vcg
  
(*
lemma hnr_raw_array_new: "hn_refine 
  (hn_ctxt snat_assn i ii)
  (narray_new TYPE('a::llvm_rep) ii)
  (hn_ctxt snat_assn i ii)
  raw_array_assn
  (mop_li $ i)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_new_def
  by vcg
*)  
  
lemma FREE_raw_array_assn: "MK_FREE raw_array_assn narray_free"  
  apply rule
  by vcg



subsubsection \<open>hnr rules\<close>
  
lemma pure_array_assn_alt:
  assumes "is_pure A"  
  shows "array_assn A = hr_comp raw_array_assn (\<langle>the_pure A\<rangle>list_rel)"  
  apply (rewrite pure_the_pure[of A, symmetric, OF assms])
  unfolding array_assn_def eoarray_assn_def nao_assn_def hr_comp_def
  apply (auto 
    simp: fun_eq_iff sep_algebra_simps pred_lift_extract_simps oelem_pure_assn_conv 
    simp: pure_list_assn_list_rel_conv in_some_rel_list_rel_conv map_some_oelem_list_rel_conv
  )
  done

lemma norm_array_assn[fcomp_norm_simps]:
  assumes "CONSTRAINT is_pure A"  
  shows "hr_comp raw_array_assn (\<langle>the_pure A\<rangle>list_rel) = array_assn A"
  using pure_array_assn_alt[OF assms[THEN CONSTRAINT_D]] by simp
    

lemma one_time_bind_ASSERT: "(\<Phi> \<Longrightarrow> one_time m) \<Longrightarrow> one_time (do {_ \<leftarrow> ASSERT \<Phi>; m })"
  apply(cases \<Phi>) by (auto simp: OT_fail)

context
  fixes A :: "'a  \<Rightarrow> 'b:: llvm_rep \<Rightarrow> assn"
  assumes [fcomp_norm_simps]: "CONSTRAINT is_pure A"
begin
  (* lemmas hnr_array_upd[sepref_fr_rules] = hnr_raw_array_upd[unfolded mop_array_upd_def, FCOMP param_mop_list_set[of _ A], folded mop_array_upd_def] *)
  lemma hnr_array_upd[sepref_fr_rules]: "(uncurry2 array_upd, uncurry2 mop_array_upd) \<in> (array_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a array_assn A"
    apply(rule hnr_raw_array_upd[unfolded mop_array_upd_def, FCOMP param_mop_list_set[of _ A], folded mop_array_upd_def]) 
    unfolding SC_attains_sup_def mop_array_upd_def
    apply safe
    apply(rule one_time_attains_sup)
    apply simp
    by(intro OT_consume OT_return one_time_bind_ASSERT) 

  (* TODO: solve side condition in FCOMP automatically
  lemmas hnr_array_nth[sepref_fr_rules] = hnr_raw_array_nth[unfolded mop_array_nth_def, FCOMP param_mop_list_get[of _ A], folded mop_array_nth_def] *)
  lemma hnr_array_nth[sepref_fr_rules]: "(uncurry array_nth, uncurry mop_array_nth) \<in> (array_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"
    apply(rule hnr_raw_array_nth[unfolded mop_array_nth_def, FCOMP param_mop_list_get[of _ A], folded mop_array_nth_def])
    unfolding SC_attains_sup_def mop_array_nth_def
    apply safe
    apply(rule one_time_attains_sup)
    apply simp
    by(intro OT_consume OT_return one_time_bind_ASSERT) 
  
end  

thm OT_intros

context 
  fixes A :: "'a  \<Rightarrow> 'c:: llvm_rep \<Rightarrow> assn"
    and x :: 'a
  assumes INIT: "GEN_ALGO x (is_init A)"
begin  
  private lemma PURE: "CONSTRAINT is_pure A"
    using INIT unfolding GEN_ALGO_def CONSTRAINT_def is_init_def by simp
  
  context
    notes PURE[fcomp_norm_simps]
begin

lemma cheat[OT_intros]: "SC_attains_sup (\<forall>a1 b1.  attains_sup (mop_list_init_raw (\<lambda>n. lift_acost (cost'_narray_new n)) b1) (PR_CONST (mop_array_new A x) a1) (\<langle>the_pure A\<rangle>list_rel))"
  apply(intro allI SC_attains_supI)
  apply (rule one_time_attains_sup)
  unfolding PR_CONST_def mop_array_new_def mop_list_init_def apply simp
  apply(intro OT_intros) done

    lemmas hnr_array_new[sepref_fr_rules] 
      = hnr_raw_array_new[FCOMP refine_mop_list_init_raw[OF INIT], folded mop_array_new_def[of A], OF cheat]
   end  
  
end  
  

(* TODO: Move *)
lemma FREE_hrcompI:
  assumes "MK_FREE (A) f"  
  shows "MK_FREE (hr_comp A R) f"  
  supply [vcg_rules] = MK_FREED[OF assms]
  apply (rule)
  unfolding hr_comp_def
  by vcg


lemma FREE_array_assn[sepref_frame_free_rules]:
  assumes PURE: "is_pure A"
  shows "MK_FREE (array_assn A) narray_free"  
  apply (rewrite pure_array_assn_alt[OF PURE])
  apply (rule FREE_hrcompI)
  apply (rule FREE_raw_array_assn)
  done



  
  
(* ************************************************************
  Deprecated from here !?

*)  
  
(*  
  
    
  
(* TODO: Move *)  
lemma hn_ctxt_hr_comp_extract: "hn_ctxt (hr_comp A R) a c = (EXS b. \<up>((b,a)\<in>R) ** hn_ctxt A b c)"  
  unfolding hn_ctxt_def hr_comp_def
  by (simp add: sep_algebra_simps)

(* TODO: Move *)  
lemma invalid_hr_comp_ctxt: "hn_invalid (hr_comp A R) a c = hn_ctxt (hr_comp (invalid_assn A) R) a c"  
  unfolding invalid_assn_def hr_comp_def hn_ctxt_def
  by (auto simp: sep_algebra_simps fun_eq_iff pred_lift_extract_simps pure_part_def)
    
lemma hn_refine_extract_pre_ex: "hn_refine (EXS x. \<Gamma> x) c \<Gamma>' R a = (\<forall>x. hn_refine (\<Gamma> x) c \<Gamma>' R a)"  
  unfolding hn_refine_def
  by (auto simp: sep_algebra_simps STATE_extract; blast)
  
lemma hn_refine_extract_pre_pure: "hn_refine (\<up>\<phi> ** \<Gamma>) c \<Gamma>' R a = (\<phi> \<longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a)"
  unfolding hn_refine_def
  by (auto simp: sep_algebra_simps STATE_extract)
  
(* TODO: Use FCOMP and parametricity lemma for this! Currently, it's FCOMP done manually! *)  
lemma deprecated_hnr_array_nth: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    A
    (mop_array_nth xs i)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> AR)
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (clarsimp simp only: hn_refine_extract_pre_ex hn_refine_extract_pre_pure sep_algebra_simps sep_conj_assoc)
    apply (rule hn_refine_cons_res_complete)
    apply (rule hnr_raw_array_nth)
    apply (rule)
    apply (rewrite pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (auto simp add: sep_algebra_simps pred_lift_extract_simps entails_def) []
    apply (rule)
    subgoal
      unfolding mop_array_nth_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    apply (rule SV)
    done
qed



              
thm hnr_raw_array_upd
lemma hnr_raw_array_upd': "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt id_assn x xi)
  (array_upd xsi ii xi)
  (hn_invalid raw_array_assn xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt id_assn x xi)
  raw_array_assn
  (mop_array_upd $ xs $  i $  x)" 
  unfolding hn_ctxt_def pure_def invalid_assn_def mop_array_upd_def
  by vcg


context
  fixes A :: "'a  \<Rightarrow> 'b:: llvm_rep \<Rightarrow> assn"
  assumes [fcomp_norm_simps]: "CONSTRAINT is_pure A"
begin


(*lemmas hm = hnr_raw_array_upd'_h[unfolded mop_array_upd_def, FCOMP param_mop_list_set[of _ A], simplified pure_array_assn_alt[symmetric] fcomp_norm_simps,
      folded mop_array_upd_def]
thm hm[no_vars]
lemmas hm[sepref_fr_rules]
*)

end





lemma hnr_raw_array_nth': "hn_refine 
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  (array_nth xsi ii)
  (hn_ctxt raw_array_assn xs xsi ** hn_ctxt snat_assn i ii)
  id_assn
  (mop_array_nth xs i)" 
  unfolding hn_ctxt_def pure_def mop_array_nth_def
  by vcg

thm mop_list_get.mcomb
thm mop_list_get_def

lemma param_mop_array_nth:
  "(mop_array_nth, mop_array_nth) \<in> \<langle>the_pure A\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>the_pure A\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_array_nth_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by simp 

context
  fixes A :: "'a  \<Rightarrow> 'b:: llvm_rep \<Rightarrow> assn"
  assumes [fcomp_norm_simps]: "CONSTRAINT is_pure A"
begin

lemmas hnr_array_nth[sepref_fr_rules] = hnr_raw_array_nth'[unfolded mop_array_nth_def, FCOMP param_mop_list_get[of _ A], folded mop_array_nth_def]

end



(*
  With loose rule, and syntactic check that time does not depend on result
*)
thm hnr_array_nth
lemma hnr_array_nth': 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    A
    (mop_array_nth $ xs $ i)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> AR)
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (clarsimp simp only: hn_refine_extract_pre_ex hn_refine_extract_pre_pure sep_algebra_simps sep_conj_assoc)
    apply (rule hn_refine_cons_res_complete_loose)
    apply (rule hnr_raw_array_nth)
    apply (rule)
    apply (rewrite pure_array_assn_alt[OF PURE])
    apply (rewrite hn_ctxt_hr_comp_extract)
    apply (auto simp add: sep_algebra_simps pred_lift_extract_simps entails_def) []
    apply (rule)
    subgoal
      unfolding mop_array_nth_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    subgoal  
      unfolding mop_array_nth_def
      apply simp
      apply (rule attains_sup_mop_return)
      done
    done
qed




(* Without single-valued! Re-doing the proof on the low-level. *)  
lemma deprecated_hnr_array_nth': 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    (array_nth xsi ii)
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii)
    A
    (mop_array_nth xs i)" 
proof -
  have AR: "A = pure (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

  note [is_pure_rule] = PURE  
    
  show ?thesis  
    unfolding pure_array_assn_alt[OF PURE]
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> AR)
    unfolding hn_ctxt_def pure_def mop_array_nth_def hr_comp_def
    supply [simp] = list_rel_imp_same_length
    apply vcg'
    apply parametricity
    by simp

qed


(* TODO: Use FCOMP and parametricity lemma for mop_list_get! *)  
lemma deprecated_hnr_array_upd_SV: 
  assumes PURE: "is_pure A"
  assumes SV: "single_valued (the_pure A)"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt A x xi)
    (array_upd xsi ii xi)
    (hn_invalid (array_assn A) xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt A x xi)
    (array_assn A)
    (mop_array_upd xs i x)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_refine _ _ \<hole> _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_ctxt A\<close> in \<open>hn_refine \<hole> _ _ _ _\<close> AR)
    apply (rewrite in \<open>hn_ctxt A\<close> in \<open>hn_refine _ _ \<hole> _ _\<close> AR)
    
    apply (simp only: hn_ctxt_hr_comp_extract invalid_hr_comp_ctxt)
    apply (clarsimp simp: hn_refine_extract_pre_ex hn_refine_extract_pre_pure hn_ctxt_def pure_def sep_algebra_simps)
    apply (rule hn_refine_cons_res_complete)
    applyS (rule hnr_raw_array_upd[where x=xi and xi=xi])
    
    apply1 (clarsimp simp: hn_ctxt_def pure_def sep_algebra_simps entails_lift_extract_simps)
    applyS rule
    
    apply1 (clarsimp simp: hn_ctxt_def pure_def sep_algebra_simps entails_lift_extract_simps)
    apply1 (rule ENTAILSD) 
    applyS fri
    
    applyS rule
    
    subgoal
      unfolding mop_array_upd_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    
    applyS (simp add: list_rel_sv_iff SV)
    done
qed    


lemma deprecated_hnr_array_upd: 
  assumes PURE: "is_pure A"
  shows "hn_refine 
    (hn_ctxt (array_assn A) xs xsi ** hn_ctxt snat_assn i ii ** hn_ctxt A x xi)
    (array_upd xsi ii xi)
    (hn_invalid (array_assn A) xs xsi ** hn_ctxt snat_assn i ii  ** hn_ctxt A x xi)
    (array_assn A)
    (mop_array_upd xs i x)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

    
  show ?thesis  
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_refine \<hole> _ _ _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_refine _ _ \<hole> _ _\<close> pure_array_assn_alt[OF PURE])
    apply (rewrite in \<open>hn_ctxt A\<close> in \<open>hn_refine \<hole> _ _ _ _\<close> AR)
    apply (rewrite in \<open>hn_ctxt A\<close> in \<open>hn_refine _ _ \<hole> _ _\<close> AR)
    
    apply (simp only: hn_ctxt_hr_comp_extract invalid_hr_comp_ctxt)
    apply (clarsimp simp: hn_refine_extract_pre_ex hn_refine_extract_pre_pure hn_ctxt_def pure_def sep_algebra_simps)
    apply (rule hn_refine_cons_res_complete_loose)
    applyS (rule hnr_raw_array_upd[where x=xi and xi=xi])
    
    apply1 (clarsimp simp: hn_ctxt_def pure_def sep_algebra_simps entails_lift_extract_simps)
    applyS rule
    
    apply1 (clarsimp simp: hn_ctxt_def pure_def sep_algebra_simps entails_lift_extract_simps)
    apply1 (rule ENTAILSD) 
    applyS fri
    
    applyS rule
    
    subgoal
      unfolding mop_array_upd_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply parametricity
      by simp
    
    subgoal
      unfolding mop_array_upd_def 
      apply simp
      by (rule attains_sup_mop_return)
      
    done
qed    

text \<open>Array new\<close>

thm hnr_raw_array_new

context  
  
thm hnr_raw_array_new[FCOMP (no_check) refine_mop_list_init_raw]
  

find_theorems mop_list_init

lemma hnr_array_new: 
  assumes PURE: "is_pure A"
  assumes INIT: "(init,init) \<in> the_pure A"
  shows "hn_refine 
    (hn_ctxt snat_assn i ii)
    (narray_new TYPE('a::llvm_rep) ii)
    (hn_ctxt snat_assn i ii)
    (array_assn A)
    (mop_array_new $ i)" 
proof -
  have AR: "A = hr_comp id_assn (the_pure A)"
    by (simp add: \<open>is_pure A\<close>)

  show ?thesis  
    unfolding APP_def
    apply (rewrite in \<open>hn_refine _ _ _ \<hole> _\<close> pure_array_assn_alt[OF PURE])
    apply (rule hn_refine_cons_res_complete_loose)
    applyS (rule hnr_raw_array_new)
    applyS rule
    applyS rule
    applyS rule
    subgoal     
      unfolding mop_array_new_def
      apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
      apply (parametricity add: INIT)
      by simp
    subgoal
      unfolding mop_array_new_def mop_list_init_def
      by (rule attains_sup_mop_return)
    done
qed

  
  
lemma "(xs,xsi)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> i<length xs \<Longrightarrow> mop_array_nth xs i \<le>\<Down>A (mop_array_nth xsi i)"  
  apply (auto simp: mop_array_nth_def pw_acost_le_iff refine_pw_simps)
  apply parametricity by simp


  
thm sepref_fr_rules
*)

end
