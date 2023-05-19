\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Sorting Setup\<close>
theory Sorting_Setup
  imports "../../sepref/Hnr_Primitives_Experiment" Sorting_Misc "../../nrest/Refine_Heuristics"
  "../../nrest/NREST_Automation"
begin
  hide_const (open) Word.slice


paragraph \<open>Summary\<close>
text \<open>This theory sets up reasoning infrastructur and basic operations used in the verification of
  sorting algorithms.\<close>

paragraph \<open>Main Theorems/Definitions\<close>
text \<open>
\<^item> mop_cmpo_idxs, mop_cmp_idxs, mop_cmpo_idx_v, mop_cmp_v_idx, mop_cmpo_v_idx:
    specifications for compare operations on arrays and option arrays
\<^item> myswap: algorithm for swapping elements on array using option arrays internatlly.
\<^item> TR_cmp_swap: exchange rate that exchanges from using the mops above and myswap 
    to using implementations that only use LLVM instructions. 
\<close>


subsection \<open>Weakordering Locales\<close>

definition "le_by_lt lt a b \<equiv> \<not>lt b a"  
definition "lt_by_le le a b \<equiv> le a b \<and> \<not>le b a"

locale weak_ordering_le =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes trans: "a \<^bold>\<le> b \<Longrightarrow> b \<^bold>\<le> c \<Longrightarrow> a \<^bold>\<le> c"
  assumes connex: "a\<^bold>\<le>b \<or> b\<^bold>\<le>a"

locale weak_ordering_lt =
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 50)
  assumes asym: "a\<^bold><b \<Longrightarrow> \<not>b\<^bold><a"
  assumes itrans: "a\<^bold><c \<Longrightarrow> a\<^bold><b \<or> b\<^bold><c"
      
locale weak_ordering = 
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 50)
  assumes trans[trans]: "a \<^bold>\<le> b \<Longrightarrow> b \<^bold>\<le> c \<Longrightarrow> a \<^bold>\<le> c"
  assumes connex: "a\<^bold>\<le>b \<or> b\<^bold>\<le>a"
  assumes asym: "a\<^bold><b \<Longrightarrow> \<not>b\<^bold><a"
  assumes itrans: "a\<^bold><c \<Longrightarrow> a\<^bold><b \<or> b\<^bold><c"
  assumes lt_by_le: "lt_by_le (\<^bold>\<le>) = (\<^bold><)"
  assumes le_by_lt: "le_by_lt (\<^bold><) = (\<^bold>\<le>)"
begin


  lemma unfold_lt_to_le: "a \<^bold>< b \<longleftrightarrow> a\<^bold>\<le>b \<and> \<not>b\<^bold>\<le>a" unfolding lt_by_le[symmetric] lt_by_le_def by simp
  lemma unfold_le_to_lt: "a \<^bold>\<le> b \<longleftrightarrow> \<not>b\<^bold><a" unfolding le_by_lt[symmetric] le_by_lt_def by simp

  abbreviation (input) greater_eq (infix "\<^bold>\<ge>" 50) where "b\<^bold>\<ge>a \<equiv> a\<^bold>\<le>b"
  abbreviation (input) greater (infix "\<^bold>>" 50) where "b\<^bold>>a \<equiv> a\<^bold><b"

  lemma wo_refl[iff]: "a \<^bold>\<le> a" using connex by auto
  lemma wo_irrefl[iff]: "\<not>a\<^bold><a" using asym by blast
  lemma wo_less_trans[trans]: "a\<^bold><b \<Longrightarrow> b\<^bold><c \<Longrightarrow> a\<^bold><c" using asym itrans by blast

  lemma [iff]:
    shows transp_le: "transp (\<^bold>\<le>)"
      and reflp_le: "reflp (\<^bold>\<le>)"
      and transp_lt: "transp (\<^bold><)"
      and irreflp_lt: "irreflp (\<^bold><)"
    unfolding transp_def reflp_def irreflp_def
    using trans wo_less_trans   
    by blast+
    
  
  
  definition eq (infix "\<^bold>=" 50) where "a \<^bold>= b \<equiv> \<not>a\<^bold><b \<and> \<not>b\<^bold><a"
    
  lemma eq_refl[iff]: "a \<^bold>= a"
    unfolding eq_def by blast
        
  lemma eq_sym: "a \<^bold>= b \<longleftrightarrow> b \<^bold>= a"  
    unfolding eq_def by blast
    
  lemma eq_trans: "a \<^bold>= b \<Longrightarrow> b \<^bold>= c \<Longrightarrow> a \<^bold>= c"
    unfolding eq_def using itrans by blast
  
  lemma eq_equiv: "equivp (\<^bold>=)"
    apply (intro equivpI reflpI sympI transpI)
    using eq_sym eq_trans by blast+

  text \<open>Compatibility lemmas, similar names as for order\<close>  
    
  lemma wo_leI: "\<not> x \<^bold>< y \<Longrightarrow> y \<^bold>\<le> x" by (simp add: unfold_le_to_lt)
  
  lemma wo_leD: "y \<^bold>\<le> x \<Longrightarrow> \<not> x \<^bold>< y" by (simp add: unfold_le_to_lt)
  
  lemma wo_not_le_imp_less: "\<not> y \<^bold>\<le> x \<Longrightarrow> x \<^bold>< y" by (simp add: unfold_le_to_lt)
    
  lemma wo_le_less_trans[trans]: "x \<^bold>\<le> y \<Longrightarrow> y \<^bold>< z \<Longrightarrow> x \<^bold>< z"
    using itrans wo_leD by blast
  
  lemma wo_less_le_trans[trans]: "x \<^bold>< y \<Longrightarrow> y \<^bold>\<le> z \<Longrightarrow> x \<^bold>< z"
    using itrans wo_leD by blast
    
  lemma wo_less_not_sym: "x \<^bold>< y \<Longrightarrow> \<not> (y \<^bold>< x)"
    using asym by blast
  
  lemma wo_less_asym: "x \<^bold>< y \<Longrightarrow> (\<not> P \<Longrightarrow> y \<^bold>< x) \<Longrightarrow> P"
    using asym by blast
    
    
    

end  

sublocale weak_ordering_lt < weak_ordering "le_by_lt (\<^bold><)"
  apply (unfold_locales)
  unfolding le_by_lt_def lt_by_le_def using asym itrans by blast+

sublocale weak_ordering_le < weak_ordering "(\<^bold>\<le>)" "lt_by_le (\<^bold>\<le>)"
  apply (unfold_locales)
  unfolding le_by_lt_def lt_by_le_def using trans connex by blast+

  
  
lemma linwo: "weak_ordering (\<le>) ((<)::_::linorder \<Rightarrow> _)"
  apply unfold_locales
  unfolding le_by_lt_def lt_by_le_def
  by (auto simp: fun_eq_iff)

lemma funwo: "weak_ordering (\<lambda>a b. f a \<le> f b) (\<lambda>a b. f a < f b)" for f :: "'a \<Rightarrow> 'b::linorder"
  apply unfold_locales
  unfolding le_by_lt_def lt_by_le_def
  by (auto simp: fun_eq_iff)
  
lemma le_by_linorder[simp]: "le_by_lt ((<)::_::linorder \<Rightarrow> _) = (\<le>)"  
  unfolding le_by_lt_def less_le_not_le by (intro ext) auto
  
lemma lt_by_linorder[simp]: "lt_by_le ((\<le>)::_::linorder \<Rightarrow> _) = (<)"  
  unfolding lt_by_le_def less_le_not_le by (intro ext) auto
    
  
lemma bex_intv_shift_aux: "(\<forall>x\<in>{0..<Suc n}. P x) \<longleftrightarrow> (P 0 \<and> (\<forall>x\<in>{0..<n}. P (Suc x)))"
  apply auto
  using less_Suc_eq_0_disj by auto

lemma sorted_wrt_adjacent: "\<lbrakk>transp R\<rbrakk> \<Longrightarrow> sorted_wrt R xs \<longleftrightarrow> (\<forall>i\<in>{0..<length xs-1}. R (xs!i) (xs!Suc i))"
  supply [simp del] = sorted_wrt.simps(2) and [simp] = sorted_wrt2_simps
  apply (induction xs rule: induct_list012)
  apply (auto simp: bex_intv_shift_aux)
  done

abbreviation "sorted_wrt_lt lt \<equiv> sorted_wrt (le_by_lt lt)"

lemma sorted_wrt_lt_adjacent: 
  assumes "weak_ordering_lt lt" 
  shows "sorted_wrt_lt lt xs \<longleftrightarrow> (\<forall>i\<in>{0..<length xs-1}. \<not>lt (xs!Suc i) (xs!i))"
proof -
  interpret weak_ordering_lt lt by fact
  
  show ?thesis
    apply (subst sorted_wrt_adjacent)
    apply (simp_all add: le_by_lt_def)
    done
    
qed

subsection \<open>Specification of Sorting Algorithms\<close>


lemma sorted_sorted_wrt_lt: "sorted = sorted_wrt_lt ((<)::_::linorder \<Rightarrow>_)"
  apply (intro ext) by simp

definition "sort_spec lt xs xs' \<equiv> mset xs'=mset xs \<and> sorted_wrt_lt lt xs'" 
  
definition "slice_sort_spec lt xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0);
    SPEC (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec lt (Misc.slice l h xs\<^sub>0) (Misc.slice l h xs))
         (\<lambda>_. cost ''slice_sort'' 1)
  }"


definition "slice_sort_specT T lt xs\<^sub>0 l h \<equiv> doN {
    ASSERT (l\<le>h \<and> h\<le>length xs\<^sub>0);
    SPEC (\<lambda>xs. length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0 \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec lt (Misc.slice l h xs\<^sub>0) (Misc.slice l h xs))
         (\<lambda>_. T)
  }"
      


lemma slice_sort_spec_refine_sort: "\<lbrakk>(xsi,xs) \<in> slice_rel xs\<^sub>0 l h; l'=l; h'=h\<rbrakk> \<Longrightarrow> slice_sort_spec lt xsi l h \<le>\<Down>(slice_rel xs\<^sub>0 l' h') (SPEC (sort_spec lt xs)  (\<lambda>_. cost ''slice_sort'' (1::enat)))"
  unfolding slice_sort_spec_def sort_spec_def
  apply (refine_rcg)
  by (auto simp: slice_rel_def in_br_conv)

lemma slice_sort_spec_eq_sort': "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h\<rbrakk> \<Longrightarrow> \<Down>(slice_rel xsi' l' h') (SPEC (sort_spec lt xs) (\<lambda>_. cost ''slice_sort'' (1::enat))) = slice_sort_spec lt xsi l h"
  unfolding slice_sort_spec_def sort_spec_def
  apply (auto simp: slice_rel_def slicep_rel_def in_br_conv build_rel_SPEC_conv intro!: SPEC_cong)
  done
  
corollary slice_sort_spec_refine_sort': "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h\<rbrakk> \<Longrightarrow> slice_sort_spec lt xsi l h \<le>\<Down>(slice_rel xsi' l' h') (SPEC (sort_spec lt xs) (\<lambda>_. cost ''slice_sort'' (1::enat)))"
  by (simp add: slice_sort_spec_eq_sort')
  
corollary slice_sort_spec_refine_sort'_sym: "\<lbrakk>(xsi,xs) \<in> slicep_rel l h; xsi'=xsi; l'=l; h'=h\<rbrakk> \<Longrightarrow> \<Down>(slice_rel xsi' l' h') (SPEC (sort_spec lt xs) (\<lambda>_. cost ''slice_sort'' (1::enat))) \<le> slice_sort_spec lt xsi l h"
  by (simp add: slice_sort_spec_eq_sort')
  
lemma slice_sort_spec_alt: "slice_sort_spec lt xs l h = doN {
    ASSERT (l\<le>h \<and> h\<le>length xs);
    SPEC (\<lambda>xs'. eq_outside_range xs' xs l h
      \<and> mset (slice l h xs') = mset (slice l h xs)
      \<and> sorted_wrt_lt lt (slice l h xs')
    ) (\<lambda>_. cost ''slice_sort'' (1::enat))
  }"
  unfolding slice_sort_spec_def sort_spec_def eq_outside_range_def
  by (auto simp: pw_acost_eq_iff refine_pw_simps)
      
  
  lemma slice_sort_spec_sem_alt: "slice_sort_spec lt xs l h = doN {
      ASSERT (l \<le> h \<and> h \<le> length xs);
      SPEC (\<lambda>xs'. slice_eq_mset l h xs xs' \<and> sorted_wrt_lt lt (slice l h xs')) (\<lambda>_. cost ''slice_sort'' (1::enat))
    }"
    unfolding slice_sort_spec_alt
    by (auto simp: pw_acost_eq_iff SPEC_def refine_pw_simps slice_eq_mset_alt slice_eq_mset_eq_length eq_outside_rane_lenD dest: eq_outside_range_sym)
  
  
  
text \<open> Sorting a permutation of a list amounts to sorting the list! \<close>
lemma sort_spec_permute: "\<lbrakk>mset xs' = mset xs; sort_spec lt xs' ys\<rbrakk> \<Longrightarrow> sort_spec lt xs ys"
  unfolding sort_spec_def by auto

subsection \<open>Specification of Compare Operations on Arrays\<close>

context weak_ordering begin  

context
  fixes T :: "(string, enat) acost"
begin
  
  definition "mop_cmpo_idxs xs i j = doN {
      ASSERT (i<length xs \<and> j<length xs \<and> xs!i\<noteq>None \<and> xs!j\<noteq>None);
      consume (RETURNT (the (xs!i) \<^bold>< the (xs!j))) T
    }"
  
  sepref_register mop_cmpo_idxs
  
  lemma mop_cmpo_idxs_param: "(mop_cmpo_idxs,mop_cmpo_idxs) \<in> \<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
    unfolding mop_cmpo_idxs_def
    apply(intro fun_relI)
    apply (parametricity)
    unfolding  list_rel_id_simp option_rel_id_simp apply (simp add: Id_def)
    apply (simp add: Id_def)
    apply(rule nrest_relI)
    by simp
  
end

context
  fixes T :: "(string, enat) acost"
begin  
  definition "mop_cmp_idxs xs i j = doN {
      ASSERT (i<length xs \<and> j<length xs);
      consume (RETURNT ( (xs!i) \<^bold><  (xs!j))) T
    }"
  
  sepref_register mop_cmp_idxs
  
  lemma mop_cmp_idxs_param: "(mop_cmp_idxs,mop_cmp_idxs) \<in> \<langle>Id::'a rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
    unfolding mop_cmp_idxs_def
    apply(intro fun_relI)
    apply (parametricity)
    unfolding  list_rel_id_simp option_rel_id_simp 
    apply(rule nrest_relI)
    by simp
end


context
  fixes T :: "(string, enat) acost"
begin  
  definition [simp]: "mop_cmp_v_idx xs v j = doN {
      ASSERT (j<length xs);
      consume (RETURNT ( v \<^bold><  (xs!j))) T
    }"
  
  sepref_register mop_cmp_v_idx
  
  lemma mop_cmp_v_idx_param: "(mop_cmp_v_idx,mop_cmp_v_idx) \<in> \<langle>Id::'a rel\<rangle>list_rel \<rightarrow> (Id::'a rel) \<rightarrow> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
    unfolding mop_cmp_v_idx_def
    apply(intro fun_relI)
    apply (parametricity)
    unfolding  list_rel_id_simp
    apply(rule nrest_relI)
    by simp
end

context
  fixes T :: "(string, enat) acost"
begin  
  definition [simp]: "mop_cmpo_v_idx xs v j = doN {
      ASSERT (j<length xs \<and> xs!j \<noteq> None);
      consume (RETURNT ( v \<^bold><  the (xs!j))) T
    }"
  
  sepref_register mop_cmpo_v_idx
  
  lemma mop_cmpo_v_idx_param: "(mop_cmpo_v_idx,mop_cmpo_v_idx) \<in> \<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel \<rightarrow> (Id::'a rel) \<rightarrow> nat_rel \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
    unfolding mop_cmpo_v_idx_def
    apply(intro fun_relI)
    apply (parametricity)
    unfolding  list_rel_id_simp option_rel_id_simp
    apply(simp add: Id_def)
    apply(rule nrest_relI)
    by simp
end


context
  fixes T :: "(string, enat) acost"
begin  
  definition "mop_cmpo_idx_v xs i v = doN {
      ASSERT (i<length xs \<and> xs!i \<noteq> None);
      consume (RETURNT ( the (xs!i) \<^bold>< v)) T
    }"
  
  sepref_register mop_cmpo_idx_v
  
  lemma mop_cmpo_idx_v_param: "(mop_cmpo_idx_v,mop_cmpo_idx_v) \<in> \<langle>\<langle>Id::'a rel\<rangle>option_rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> (Id::'a rel) \<rightarrow> \<langle>bool_rel\<rangle> nrest_rel"
    unfolding mop_cmpo_idx_v_def
    apply(intro fun_relI)
    apply (parametricity)
    unfolding  list_rel_id_simp option_rel_id_simp
    apply(simp add: Id_def)
    apply(rule nrest_relI)
    by simp
end
        
(*
  definition refines_cmp_idxs :: "('a list \<Rightarrow> _ \<Rightarrow> assn) \<Rightarrow> (_ \<Rightarrow> 'l::len2 word \<Rightarrow> 'l word \<Rightarrow> 1 word llM) \<Rightarrow> bool" 
    where "refines_cmp_idxs A ci_impl \<equiv> (uncurry2 ci_impl, uncurry2 (PR_CONST mop_cmp_idxs)) \<in> A\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
                                
  lemma gen_refines_cmp_idxsD: 
      "GEN_ALGO ci_impl (refines_cmp_idxs A) 
        \<Longrightarrow> (uncurry2 ci_impl, uncurry2 (PR_CONST mop_cmp_idxs)) \<in> A\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"        
    and gen_refines_cmp_idxsI[intro?]: 
      "(uncurry2 ci_impl, uncurry2 (PR_CONST mop_cmp_idxs)) \<in> A\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn
        \<Longrightarrow> GEN_ALGO ci_impl (refines_cmp_idxs A)"
    unfolding refines_cmp_idxs_def GEN_ALGO_def by auto    
*)    
    
end  



  definition "SPECc3 c aop == ( (\<lambda>a b. SPECT ( [(aop a b)\<mapsto> c])))"



(* TODO: move *)
lemma gwp_SPECc3[vcg_rules']:
  fixes t :: ecost
  assumes "Some (t + c) \<le> Q (op a b)"
  shows "Some t \<le> gwp (SPECc3 c op a b) Q"
  unfolding SPECc3_def 
  apply(refine_vcg \<open>-\<close>)
  using assms by auto


lemma SPECc3_alt: "SPECc3 c aop = ( (\<lambda>a b. consume (RETURNT (aop a b)) c))"
  unfolding SPECc3_def consume_def by(auto simp: RETURNT_def intro!: ext)

(*
lemma SPECc3_refine':
  fixes TR :: "'h \<Rightarrow> ('h, enat) acost"
  shows "(op x y, op' x' y')\<in>R \<Longrightarrow> preserves_curr TR n  \<Longrightarrow> SPECc3 c op x y \<le> \<Down> R (\<Down>\<^sub>C TR (SPECc3 c op' x' y'))"
  unfolding SPECc3_def    
  apply(subst SPECT_refine_t) by (auto simp: preserves_curr_def timerefineA_cost_apply) 
  *)

lemma SPECc3_refine:
  fixes c :: ecost
  shows "(op x y, op' x' y')\<in>R \<Longrightarrow> c \<le> timerefineA TR c'  \<Longrightarrow> SPECc3 c op x y \<le> \<Down> R (\<Down>\<^sub>C TR (SPECc3 c' op' x' y'))"
  unfolding SPECc3_def    
  apply(subst SPECT_refine_t) by auto


context 
  fixes c :: ecost and f:: "('a \<Rightarrow> 'b \<Rightarrow> 'c)"
begin
  sepref_register timed_binop': "SPECc3 c f"
end

definition "refines_relp A c op Rimpl \<equiv> (uncurry Rimpl,uncurry (PR_CONST (SPECc3 c op))) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn"

lemma gen_refines_relpD: "GEN_ALGO Rimpl (refines_relp A c op)
   \<Longrightarrow> (uncurry Rimpl,uncurry (PR_CONST (SPECc3 c op))) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn"
  by (simp add: GEN_ALGO_def refines_relp_def)

lemma gen_refines_relpI[intro?]: "(uncurry Rimpl,uncurry (SPECc3 c op)) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn \<Longrightarrow> GEN_ALGO Rimpl (refines_relp A c op)"
  by (simp add: GEN_ALGO_def refines_relp_def)
  
(*  
locale sort_impl_context = weak_ordering +
  fixes cmp_idxs_impl :: "'ai::llvm_rep \<Rightarrow> 'l::len2 word \<Rightarrow> 'l word \<Rightarrow> 1 word llM"
    and arr_assn :: "'a list \<Rightarrow> 'ai \<Rightarrow> assn"
  assumes cmp_idxs_impl: "GEN_ALGO cmp_idxs_impl (refines_cmp_idxs arr_assn)"
  
begin

  lemmas lt_hnr[sepref_fr_rules] = gen_refines_cmp_idxsD[OF cmp_idxs_impl]
  
  declare [[sepref_register_adhoc "(\<^bold><)"]]
  

end  
*)  


subsection \<open>Locale for Specifying the Word Length\<close>

locale size_t_context = 
  fixes size_t :: "'size_t::len2 itself" 
  assumes SIZE_T: "8\<le>LENGTH('size_t)"
begin
  lemma size_t_le_maxI[simp]:
    assumes "n<128"  
    shows "n<max_snat LENGTH('size_t)"
  proof -
    from SIZE_T have "7 \<le> LENGTH('size_t)-1"
      using SIZE_T
      by simp
    hence "2^7 \<le> max_snat LENGTH('size_t)"  
      unfolding max_snat_def
      by (simp add: numeral_2_eq_2)
    with assms show ?thesis by simp       
  qed  

  lemma size_t_le_maxI'[simp]:
    fixes n :: nat
    assumes "n<128"  
    shows "n<2^(LENGTH('size_t)-Suc 0)"
    using size_t_le_maxI assms
    unfolding max_snat_def by simp
    
  
  abbreviation "size_assn \<equiv> snat_assn' TYPE('size_t)"
  
end


subsection \<open>Locale for assuming an implementation of the compare operation\<close>

(* TODO: Move *)
term array_assn
locale sort_impl_context = size_t_context size_t + weak_ordering
  for size_t :: "'size_t::len2 itself" +
  fixes
        lt_impl :: "'ai::llvm_rep \<Rightarrow> 'ai \<Rightarrow> 1 word llM"
    and lt_acost :: "(_,nat) acost"
    and elem_assn :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
  assumes lt_impl: "GEN_ALGO lt_impl (refines_relp elem_assn (lift_acost lt_acost) (\<^bold><))"
  assumes no_clash:
    "the_acost (lift_acost lt_acost) ''eo_extract'' = 0"
    "the_acost (lift_acost lt_acost) ''eo_set'' = 0" (* both are no llvm currencies, thus it does not
                                                clash!  *)
  assumes lt_acost_finite: "finite {a. the_acost lt_acost a \<noteq> 0}"                                                
  notes lt_hnr[sepref_fr_rules] = gen_refines_relpD[OF lt_impl]
  
  notes [[sepref_register_adhoc "(\<^bold><)"]]
  notes [[sepref_register_adhoc "lt_acost"]]
begin

lemmas size_t_min = SIZE_T (* TODO propagate *)

  abbreviation "arr_assn \<equiv> array_assn elem_assn"

  abbreviation "lt_cost == (lift_acost lt_acost)"

  thm lt_hnr

subsubsection \<open>Implementing the Array-Compare Operations\<close>

  
  definition "cmpo_idxs2 xs\<^sub>0 i j \<equiv> doN {
    ASSERT (i \<noteq> j);
    (vi,xs) \<leftarrow> mop_eo_extract (\<lambda>_. cost ''eo_extract'' 1) xs\<^sub>0 i;
    (vj,xs) \<leftarrow> mop_eo_extract (\<lambda>_. cost ''eo_extract'' 1) xs j;
    r \<leftarrow> SPECc3 lt_cost (\<^bold><) vi vj;
    xs \<leftarrow> mop_eo_set (\<lambda>_. cost ''eo_set'' 1) xs i vi; \<comment> \<open>TODO: Let's hope the optimizer eliminates these assignments. In mid-term, eliminate them during sepref phase!\<close>
    xs \<leftarrow> mop_eo_set (\<lambda>_. cost ''eo_set'' 1) xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"
  
  definition "cmpo_v_idx2 xs\<^sub>0 v j \<equiv> doN {
    (vj,xs) \<leftarrow> mop_eo_extract (\<lambda>_. cost ''eo_extract'' 1) xs\<^sub>0 j;
    r \<leftarrow> SPECc3 lt_cost (\<^bold><) v vj;
    xs \<leftarrow> mop_eo_set (\<lambda>_. cost ''eo_set'' 1) xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"
  
  definition "cmpo_idx_v2 xs\<^sub>0 i v \<equiv> doN {
    (vi,xs) \<leftarrow> mop_eo_extract (\<lambda>_. cost ''eo_extract'' 1) xs\<^sub>0 i;
    r \<leftarrow> SPECc3 lt_cost (\<^bold><) vi v;
    xs \<leftarrow> mop_eo_set (\<lambda>_. cost ''eo_set'' 1) xs i vi;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"

  definition "cmp_idxs2 xs\<^sub>0 i j \<equiv> doN {
    xs \<leftarrow> mop_to_eo_conv xs\<^sub>0;
    b \<leftarrow> cmpo_idxs2 xs i j;
    xs \<leftarrow> mop_to_wo_conv xs;
    unborrow xs xs\<^sub>0;
    RETURN b
  }"  
 


  lemma cmpo_idxs2_refine: "(uncurry2 cmpo_idxs2, uncurry2 (PR_CONST (mop_cmpo_idxs (cost ''eo_set'' 1 + cost ''eo_set'' 1 + cost ''eo_extract'' 1 + cost ''eo_extract'' 1 + lt_cost)))) \<in> [\<lambda>((xs,i),j). i\<noteq>j]\<^sub>f (Id\<times>\<^sub>rId)\<times>\<^sub>rId \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    unfolding cmpo_idxs2_def  mop_cmpo_idxs_def unborrow_def SPECc2_def
    apply (intro frefI nrest_relI)
    apply clarsimp
    subgoal for xs i j
      apply(rule gwp_specifies_acr_I)
      apply (refine_vcg \<open>-\<close>)
           apply (simp_all add: list_update_swap[of i j] map_update[symmetric])
      subgoal apply(simp add: add.assoc) done 
      subgoal by (metis list_update_id list_update_overwrite option.sel)
      done
    done


  definition "E_cmpo_idxs \<equiv> TId(''cmpo_idxs'':=(cost ''eo_extract'' 2) + lt_cost)"



  lemma cmpo_v_idx2_refine: "(cmpo_v_idx2, PR_CONST (mop_cmpo_v_idx (cost ''eo_set'' 1 + (cost ''eo_extract'' 1 + lt_cost)))) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
     unfolding cmpo_v_idx2_def  mop_cmpo_v_idx_def unborrow_def SPECc2_def
    apply (intro frefI nrest_relI fun_relI)
    apply clarsimp
    subgoal for xs i j
      apply(rule gwp_specifies_acr_I)
      apply (refine_vcg \<open>-\<close>)
      subgoal by force
      subgoal by (metis Pair_inject list_update_id list_update_overwrite option.sel)
      subgoal by auto
      subgoal by auto
      done
    done


  lemma cmpo_idx_v2_refine: "(cmpo_idx_v2, PR_CONST (mop_cmpo_idx_v (cost ''eo_set'' 1 + (cost ''eo_extract'' 1 + lt_cost)))) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nrest_rel"
    unfolding cmpo_idx_v2_def mop_cmpo_idx_v_def unborrow_def SPECc2_def
    apply (intro frefI nrest_relI fun_relI)
    apply clarsimp
    subgoal for xs i j
      apply(rule gwp_specifies_acr_I)
      apply (refine_vcg \<open>-\<close>)
      subgoal by force
      subgoal by (metis Pair_inject list_update_id list_update_overwrite option.sel)
      subgoal by auto
      subgoal by auto
      done
    done

  definition "cmpo_idxs2' xs\<^sub>0 i j \<equiv> doN {
    ASSERT (i \<noteq> j);
    (vi,xs) \<leftarrow> mop_oarray_extract xs\<^sub>0 i;
    (vj,xs) \<leftarrow> mop_oarray_extract xs j;
    r \<leftarrow> SPECc3 lt_cost (\<^bold><) vi vj;
    xs \<leftarrow> mop_oarray_upd xs i vi; \<comment> \<open>TODO: Let's hope the optimizer eliminates these assignments. In mid-term, eliminate them during sepref phase!\<close>
    xs \<leftarrow> mop_oarray_upd xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"
  
  definition "cmpo_v_idx2' xs\<^sub>0 v i \<equiv> doN {
    (vi,xs) \<leftarrow> mop_oarray_extract xs\<^sub>0 i;
    r \<leftarrow> SPECc3 lt_cost (\<^bold><) v vi;
    xs \<leftarrow> mop_oarray_upd xs i vi;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"
  
  definition "cmpo_idx_v2' xs\<^sub>0 i v \<equiv> doN {
    (vi,xs) \<leftarrow> mop_oarray_extract xs\<^sub>0 i;
    r \<leftarrow> SPECc3 lt_cost (\<^bold><) vi v;
    xs \<leftarrow> mop_oarray_upd xs i vi;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"

  definition "cmp_idxs2' xs\<^sub>0 i j \<equiv> doN {
    xs \<leftarrow> mop_to_eo_conv xs\<^sub>0;
    b \<leftarrow> cmpo_idxs2' xs i j;
    xs \<leftarrow> mop_to_wo_conv xs;
    unborrow xs xs\<^sub>0;
    RETURN b
  }"  
  sepref_register cmpo_idx_v2' cmpo_v_idx2' cmpo_idxs2' cmp_idxs2'

  definition "E_mop_oarray_extract \<equiv> TId(''eo_extract'':=lift_acost mop_array_nth_cost, ''eo_set'':=lift_acost mop_array_upd_cost)"
 
  lemma mop_oarray_extract_refine: 
    "mop_oarray_extract a b \<le> \<Down> Id (timerefine E_mop_oarray_extract (mop_eo_extract (\<lambda>_. cost ''eo_extract'' 1) a b))"
    unfolding mop_oarray_extract_def E_mop_oarray_extract_def mop_eo_extract_def       
    apply(intro refine0)
    by(auto simp: timerefineA_update_apply_same_cost intro!: wfR''_upd) 
  
  lemma mop_eo_set_ghost[refine]:
    "(x,x') \<in> A \<Longrightarrow> (xs,xs') \<in> \<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel \<Longrightarrow> (i,i')\<in>nat_rel \<Longrightarrow> wfR'' R \<Longrightarrow>
      lift_acost mop_array_upd_cost \<le> R ''eo_set'' \<Longrightarrow>  mop_oarray_upd xs i x \<le> \<Down> (\<langle>\<langle>A\<rangle>option_rel\<rangle>list_rel) (timerefine R (mop_eo_set (\<lambda>_. cost ''eo_set'' 1) xs' i' x'))"
    unfolding mop_oarray_upd_def     mop_eo_set_def
    apply(intro refine0)
       apply safe
    subgoal  
      by (simp add: list_rel_imp_same_length)  
    subgoal  
      using param_nth by fastforce   
    subgoal by(simp add: timerefineA_cost)
    subgoal  
      by (smt length_list_update list_rel_eq_listrel listrel_iff_nth nth_list_update option_relI(2) relAPP_def)  
    done 

lemma unborrow_refine[refine]: 
  fixes E :: "'e \<Rightarrow> ('c, enat) acost"
  shows "((), ()) \<in> R \<Longrightarrow> (a, a') \<in> Id \<Longrightarrow> (b, b') \<in> Id \<Longrightarrow> unborrow a b \<le> \<Down>R (timerefine E (unborrow a' b'))"
    unfolding unborrow_def
    apply(intro refine0) 
   apply simp_all
    done

lemma the_acost_timerefineA_upd_if_neq: "the_acost T y = 0 \<Longrightarrow> timerefineA (F(y := t)) T = timerefineA F T"
  unfolding timerefineA_def
  unfolding fun_upd_def 
  apply simp apply(rule ext)
  apply(rule Sum_any.cong) by auto

  lemma SPECc2_lt_refine[refine]:
    "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> SPECc3 lt_cost (\<^bold><) a b \<le> \<Down> bool_rel (timerefine E_mop_oarray_extract (SPECc3 lt_cost (\<^bold><) a' b'))"
    apply(rule SPECc3_refine) 
     apply (auto simp: cost_n_leq_TId_n E_mop_oarray_extract_def)
    using no_clash
    unfolding less_eq_acost_def
    apply(auto)
    subgoal for x
      apply(cases "x=''eo_extract''") apply simp
      apply(cases "x=''eo_set''") apply simp
      apply(subst the_acost_timerefineA_upd_if_neq) apply simp
      apply(subst the_acost_timerefineA_upd_if_neq) apply simp 
      by simp
    done

lemma wfR_E: "wfR'' E_mop_oarray_extract"
  by(auto simp: E_mop_oarray_extract_def intro!: wfR''_upd) 
  
  
  lemma cmpo_v_idx2'_refine: "(cmpo_v_idx2', cmpo_v_idx2) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> nrest_trel Id E_mop_oarray_extract"
    unfolding cmpo_v_idx2'_def cmpo_v_idx2_def
    unfolding nrest_trel_def_internal
    apply (intro frefI nrest_relI fun_relI) 
    apply safe
    supply bindT_refine_conc_time2[refine] 
    supply mop_oarray_extract_refine[refine]
    apply (refine_rcg) 
    apply refine_dref_type
    apply (simp_all add: wfR_E)
    apply (simp add: E_mop_oarray_extract_def )
    done 

  lemma cmpo_idx_v2'_refine: "(cmpo_idx_v2', cmpo_idx_v2) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> nrest_trel Id E_mop_oarray_extract"
    unfolding cmpo_idx_v2'_def cmpo_idx_v2_def
    unfolding nrest_trel_def_internal
    apply (intro frefI nrest_relI fun_relI) 
    apply safe
    supply bindT_refine_conc_time2[refine] 
    supply mop_oarray_extract_refine[refine]
    apply (refine_rcg) 
    apply refine_dref_type
    apply (simp_all add: wfR_E)
    apply (simp add: E_mop_oarray_extract_def )
    done
  
  
  lemma cmp_idxs2_refine: "(uncurry2 cmp_idxs2,uncurry2 (PR_CONST (mop_cmp_idxs (cost ''eo_set'' 1 + cost ''eo_set'' 1 + cost ''eo_extract'' 1 + cost ''eo_extract'' 1 + lt_cost))))\<in>[\<lambda>((xs,i),j). i\<noteq>j]\<^sub>f (Id\<times>\<^sub>rId)\<times>\<^sub>rId \<rightarrow> \<langle>Id\<rangle>nrest_rel"
      unfolding cmp_idxs2_def mop_cmp_idxs_def PR_CONST_def cmpo_idxs2_def unborrow_def SPECc2_def
      unfolding mop_to_eo_conv_def mop_to_wo_conv_def 
      apply (intro frefI nrest_relI)
      apply clarsimp
      subgoal for xs i j
        apply(rule gwp_specifies_acr_I)
        apply (refine_vcg \<open>-\<close>)
        subgoal apply (simp add: lift_acost_zero add.assoc) by force
        subgoal by auto 
        subgoal by auto
        subgoal by (metis Pair_inject list_update_id list_update_overwrite list_update_swap option.sel)
        subgoal by auto
        subgoal by auto 
        subgoal by auto 
        subgoal by auto 
        done
      done


definition "cmpo_v_idx2'_cost = lift_acost mop_array_nth_cost + (lt_cost + lift_acost mop_array_upd_cost)"


lemma  cmpo_v_idx2'_refines_mop_cmpo_v_idx_with_E:
  assumes "wfR'' EE"
    and "cmpo_v_idx2'_cost \<le> timerefineA EE (cost ''cmpo_v_idx'' 1)"
  shows "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> cmpo_v_idx2' a b c \<le> \<Down> bool_rel (timerefine EE (mop_cmpo_v_idx (cost ''cmpo_v_idx'' 1) a' b' c'))"
  supply conc_Id[simp del]
    unfolding cmpo_v_idx2'_def mop_cmpo_v_idx_def
    unfolding mop_oarray_extract_def mop_eo_extract_def unborrow_def SPECc3_alt
          mop_oarray_upd_def mop_eo_set_def consume_alt
    apply normalize_blocks apply(split prod.splits)+
    apply normalize_blocks
    apply simp
    apply(intro refine0 consumea_refine bindT_refine_easy)
            apply refine_dref_type
    subgoal by auto  
    subgoal by auto  
    subgoal using assms(1) by auto  
    subgoal by auto   
    subgoal
      apply(rule order.trans[OF _ assms(2)])
      by(simp add: cmpo_v_idx2'_cost_def)
    subgoal by simp
    done

definition "cmpo_idxs2'_cost = lift_acost mop_array_nth_cost + (lift_acost mop_array_nth_cost 
        + (lt_cost + (lift_acost mop_array_upd_cost + lift_acost mop_array_upd_cost)))"
    
    
lemma cmpo_idxs2'_refines_mop_cmpo_idxs_with_E:
  assumes "wfR'' E"
    "cmpo_idxs2'_cost \<le> timerefineA E (cost ''cmpo_idxs'' 1)"
  shows 
  "b'\<noteq>c' \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
    cmpo_idxs2' a b c \<le> \<Down> bool_rel (timerefine E (mop_cmpo_idxs (cost ''cmpo_idxs'' 1) a' b' c'))"
  supply conc_Id[simp del]
    unfolding cmpo_idxs2'_def mop_cmpo_idxs_def
    unfolding mop_oarray_extract_def mop_eo_extract_def unborrow_def SPECc3_alt
          mop_oarray_upd_def mop_eo_set_def consume_alt
    apply normalize_blocks apply(split prod.splits)+
    apply normalize_blocks
    apply simp
    apply(intro refine0 consumea_refine bindT_refine_easy)
            apply refine_dref_type
    subgoal by auto  
    subgoal by auto  
    subgoal by auto  
    subgoal by auto   
    subgoal by (metis list_update_id list_update_overwrite list_update_swap option.sel)
    subgoal using assms(1) by simp
    subgoal by simp
    subgoal
      apply(rule order.trans[OF _ assms(2)])
      by(simp add: cmpo_idxs2'_cost_def)
    subgoal by simp
    done


definition "cmp_idxs2'_cost = lift_acost mop_array_nth_cost + (lift_acost mop_array_nth_cost
                 + (lt_cost + (lift_acost mop_array_upd_cost
                 + lift_acost mop_array_upd_cost)))"

lemma cmp_idxs2'_refines_mop_cmp_idxs_with_E:
  assumes "wfR'' E"
    "cmp_idxs2'_cost \<le> timerefineA E (cost ''cmp_idxs'' 1)"
  shows 
  "b'\<noteq>c' \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
    cmp_idxs2' a b c \<le> \<Down> bool_rel (timerefine E (mop_cmp_idxs (cost ''cmp_idxs'' 1) a' b' c'))"
  supply conc_Id[simp del]
    unfolding cmp_idxs2'_def cmpo_idxs2'_def  mop_cmp_idxs_def
    unfolding  mop_oarray_extract_def mop_eo_extract_def unborrow_def SPECc3_alt
          mop_oarray_upd_def mop_eo_set_def consume_alt
    unfolding mop_to_eo_conv_def mop_to_wo_conv_def
    apply normalize_blocks apply(split prod.splits)+
    apply normalize_blocks
    apply simp
    apply(intro refine0 consumea_refine bindT_refine_easy)
            apply refine_dref_type
    subgoal by auto  
    subgoal by auto  
    subgoal by auto  
    subgoal by auto   
    subgoal by (metis list_update_id list_update_overwrite list_update_swap option.sel)
    subgoal using assms(1) by simp
    subgoal by simp
    subgoal
      apply(rule order.trans[OF _ assms(2)]) 
      by (simp add: lift_acost_zero cmp_idxs2'_cost_def) 
    subgoal by simp
    done


subsubsection \<open>Synthesizing LLVM Code for the Array-Compare Operations\<close>

  sepref_def cmpo_idxs_impl [llvm_inline] is "uncurry2 (PR_CONST cmpo_idxs2')" :: "(eoarray_assn elem_assn)\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cmpo_idxs2'_def PR_CONST_def
    by sepref

  sepref_def cmpo_v_idx_impl [llvm_inline] is "uncurry2 (PR_CONST cmpo_v_idx2')" :: "(eoarray_assn elem_assn)\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cmpo_v_idx2'_def PR_CONST_def
   (* supply [sepref_fr_rules] = eo_hnr_dep *)
    by sepref

  thm cmp_idxs2_def cmp_idxs2'_def
  term cmp_idxs2'

  sepref_def cmp_idxs_impl [llvm_inline] is "uncurry2 (PR_CONST cmp_idxs2')" :: "(array_assn elem_assn)\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cmp_idxs2'_def cmpo_idxs2'_def PR_CONST_def
    supply [sepref_fr_rules] = mop_to_wo_conv_hnr_dep mop_to_eo_conv_hnr_dep
    by sepref
  
  sepref_definition cmpo_idx_v_impl [llvm_inline] is "uncurry2 cmpo_idx_v2'" :: "(eoarray_assn elem_assn)\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cmpo_idx_v2'_def PR_CONST_def
    by sepref

      \<^cancel>\<open>
  context notes [fcomp_norm_unfold] = list_rel_id_simp option_rel_id_simp begin
    sepref_decl_impl (ismop) cmp_idxs_impl.refine[FCOMP cmp_idxs2_refine] .
    sepref_decl_impl (ismop) cmpo_idxs_impl.refine[FCOMP cmpo_idxs2_refine] .
    sepref_decl_impl (ismop) cmpo_v_idx_impl.refine[FCOMP cmpo_v_idx2_refine] .
    sepref_decl_impl (ismop) cmpo_idx_v_impl.refine[FCOMP cmpo_idx_v2_refine] .
  end  
     \<close>
end

locale pure_sort_impl_context = sort_impl_context +
  constrains size_t :: "'size_t::len2 itself" 
  assumes pureA[safe_constraint_rules]: "CONSTRAINT is_pure elem_assn"
  notes [sepref_frame_free_rules] = mk_free_is_pure[OF CONSTRAINT_D[OF pureA]]
begin
\<^cancel>\<open>

  definition "cmp_idxs2' xs i j \<equiv> doN {
    ASSERT (i<length xs \<and> j<length xs);
    RETURN (xs!i \<^bold>< xs!j)
  }"  
  
  lemma cmp_idxs2'_refine: "(cmp_idxs2',PR_CONST mop_cmp_idxs)\<in>Id\<rightarrow>Id\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>nres_rel"  
    unfolding cmp_idxs2'_def mop_cmp_idxs_def
    apply clarsimp
    apply refine_vcg
    by auto
        
  sepref_definition cmp_idxs'_impl [llvm_inline] is "uncurry2 cmp_idxs2'" :: "(woarray_assn elem_assn)\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding cmp_idxs2'_def PR_CONST_def
    by sepref
    
    
    
  context notes [fcomp_norm_unfold] = list_rel_id_simp option_rel_id_simp begin
    sepref_decl_impl (ismop) cmp_idxs'_impl.refine[FCOMP cmp_idxs2'_refine] .
  end  
    
  
  
  
  
  (*  
  xxx, ctd here: Adapt sorting algorithms to use cmp_idxs! 
    then refine to delayed swap and eo-optimizations!
  *)  
    
  
  (*
  lemma mop_cmp_idxs_alt: "mop_cmp_idxs xs i j = doN { x \<leftarrow> mop_list_get xs i; y \<leftarrow> mop_list_get xs j; RETURN (x \<^bold>< y) }"
    by (auto simp: pw_eq_iff refine_pw_simps)

  sepref_def cmp_idxs_impl [llvm_inline] is "uncurry2 (PR_CONST mop_cmp_idxs)" :: "(array_assn elem_assn)\<^sup>k *\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding mop_cmp_idxs_alt PR_CONST_def
    apply sepref_dbg_keep
    done
  *)
  (*    
  sublocale sort_impl_context "(\<^bold>\<le>)" "(\<^bold><)" cmp_idxs_impl "array_assn elem_assn"
    apply unfold_locales
    apply rule
    by (rule cmp_idxs_impl.refine)  
  *)  
    \<close>
end  

(*
  TODO: Explicit ownership collection data structures!
  
    Idea: Make ownership abstractly visible by sum type as abstract element type
      Inl x - element x, but no ownership (free to overwrite or return)
      Inr x - element x with ownership
  
    operation get: transfers ownership, leaves Inl
    operation set: overwrites Inl, Inr must be freed (by user!?)
    operation ret: returns ownership, also concrete value must not have changed. 
      *** Hard to implement, as abstractly not visible! BUT not needed for sorting, 
          and optimizer may eliminate redundant writes in many cases!
      



*)

(*  
locale sort_impl_context = weak_ordering +
  fixes lt_impl :: "'ai::llvm_rep \<Rightarrow> 'ai \<Rightarrow> 1 word llM"
    and elem_assn :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
  assumes lt_impl: "GEN_ALGO lt_impl (refines_relp elem_assn (\<^bold><))"
  assumes pureA[safe_constraint_rules]: "CONSTRAINT is_pure elem_assn"
  notes [sepref_frame_free_rules] = mk_free_is_pure[OF CONSTRAINT_D[OF pureA]]
  
  notes lt_hnr[sepref_fr_rules] = gen_refines_relpD[OF lt_impl]
  
  notes [[sepref_register_adhoc "(\<^bold><)"]]
  
begin
  abbreviation "arr_assn \<equiv> array_assn elem_assn"
end  
*)
(* TODO: Refine lemmas to support more general size datatypes! *)
  
   
lemma SPECc3_to_SPECc2: "SPECc3 (cost n 1) aop = SPECc2 n aop"
  unfolding SPECc3_def SPECc2_def by auto
thm hn_unat_ops(13)                                                  
lemma unat_sort_impl_context: "8 \<le> LENGTH('size_t) \<Longrightarrow> pure_sort_impl_context TYPE('size_t::len2) (\<le>) (<) ll_icmp_ult (cost ''icmp_ult'' 1) unat_assn"
  apply intro_locales
  subgoal apply unfold_locales .
  apply (rule linwo)
  apply unfold_locales
      apply rule 
      apply(simp_all  only: lift_acost_cost )
    unfolding Extended_Nat.enat_1 SPECc3_to_SPECc2
    apply (rule hn_unat_ops[unfolded PR_CONST_def]) 
  apply (simp add: zero_acost_def cost_def)
  apply (simp add: zero_acost_def cost_def)
  apply (metis finite_sum_nonzero_cost) 
  apply (solve_constraint)
  done
  
  \<^cancel>\<open>
subsection \<open>Parameterized Sorting\<close>  

text \<open>Extension of a weak ordering with explicit carrier set is always possible, 
  e.g., by putting all elements not in the carrier set into one equivalence class,
  which is smaller than any other class.\<close>  
locale weak_ordering_on_lt =
  fixes C :: "'a set"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 50)
  assumes asym: "\<lbrakk> a\<in>C; b\<in>C \<rbrakk> \<Longrightarrow> a\<^bold><b \<Longrightarrow> \<not>b\<^bold><a"
  assumes itrans: "\<lbrakk> a\<in>C; b\<in>C; c\<in>C \<rbrakk> \<Longrightarrow> a\<^bold><c \<Longrightarrow> a\<^bold><b \<or> b\<^bold><c"

definition "ext_lt C lt a b \<equiv> lt a b \<and> a\<in>C \<and> b\<in>C \<or> a\<in>C \<and> b\<notin>C"  
  
lemma weak_ordering_on_lt_extend: "weak_ordering_lt (ext_lt C lt) \<longleftrightarrow> weak_ordering_on_lt C lt"
  unfolding weak_ordering_on_lt_def weak_ordering_lt_def ext_lt_def
  by blast
  
  
(* TODO: Restrict cdom constraint to slice! *)
definition "pslice_sort_spec cdom pless cparam xs l h \<equiv> doN {
  \<^cancel>\<open>ASSERT (set (slice l h xs) \<subseteq> cdom cparam);\<close>
  ASSERT (set xs \<subseteq> cdom cparam);
  slice_sort_spec (pless cparam) xs l h
}"  
  

locale parameterized_weak_ordering =
  fixes cdom :: "'cparam \<Rightarrow> 'a set"
    and pless :: "'cparam \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and pcmp :: "'cparam \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (bool,_) nrest"
    and pcmp_time :: "ecost"
  assumes weak_ordering_on_lt: "weak_ordering_on_lt (cdom cparam) (pless cparam)"
  assumes pcmp_correct[refine_vcg]: "\<lbrakk> a\<in>cdom cparam; b\<in>cdom cparam\<rbrakk> 
    \<Longrightarrow> pcmp cparam a b \<le> SPEC (\<lambda>r. r \<longleftrightarrow> pless cparam a b) (\<lambda>_. pcmp_time)"
begin    

  definition "cdom_rel cparam \<equiv> br id (\<lambda>x. x\<in>cdom cparam)"
  definition "cdom_list_rel cparam \<equiv> \<langle>cdom_rel cparam\<rangle>list_rel"
  definition "cdom_olist_rel cparam \<equiv> \<langle>\<langle>cdom_rel cparam\<rangle>option_rel\<rangle>list_rel"
  
  lemma br_id_list_rel_conv: "(xs,xs')\<in>\<langle>br id I\<rangle>list_rel \<longleftrightarrow> xs=xs' \<and> set xs' \<subseteq> Collect I"
    apply (induction xs arbitrary: xs')
    subgoal for xs' by (auto)
    subgoal for x xs xs' by (cases xs') (auto simp: in_br_conv)
    done  
  
  lemma br_id_olist_rel_conv: "(xs,xs')\<in>\<langle>\<langle>br id I\<rangle>option_rel\<rangle>list_rel \<longleftrightarrow> xs=xs' \<and> (\<forall>x. Some x\<in>set xs' \<longrightarrow> I x)"
    apply (induction xs arbitrary: xs')
    subgoal for xs' by (auto)
    subgoal for x xs xs' by (cases xs') (auto simp: in_br_conv option_rel_def)
    done  
  
  lemma cdom_list_rel_alt: "cdom_list_rel cparam = br id (\<lambda>xs. set xs \<subseteq> cdom cparam)"
    unfolding cdom_list_rel_def cdom_rel_def
    by (auto simp: in_br_conv br_id_list_rel_conv)
  
  lemma cdom_olist_rel_alt: "cdom_olist_rel cparam = br id (\<lambda>xs. \<forall>x. Some x \<in> set xs \<longrightarrow> x\<in>cdom cparam)"
    unfolding cdom_olist_rel_def cdom_rel_def
    by (auto simp: in_br_conv br_id_olist_rel_conv)

  definition "less' cparam \<equiv> (ext_lt (cdom cparam) (pless cparam))"

  lemma weak_ordering_lt: "weak_ordering_lt (less' cparam)" 
    using weak_ordering_on_lt less'_def by (simp add: weak_ordering_on_lt_extend) 

  lemma weak_ordering: "weak_ordering (le_by_lt (less' cparam)) (less' cparam)"
  proof -
    interpret weak_ordering_lt "less' cparam" by (rule weak_ordering_lt)
    show ?thesis by unfold_locales
  qed      

  sublocale WO: weak_ordering "le_by_lt (less' cparam)" "less' cparam"
    by (rule weak_ordering)
  
  
  lemma sorted_wrt_ext: "set xs \<subseteq> cdom cparam \<Longrightarrow> sorted_wrt (less' cparam) xs = sorted_wrt (pless cparam) xs"
    apply (intro iffI; erule sorted_wrt_mono_rel[rotated])
    apply (auto simp: less'_def ext_lt_def)
    done
  
  (* TODO: Move *)  
  lemma set_slice_ss: "set (slice l h xs) \<subseteq> set xs"  
    by (metis Misc.slice_def dual_order.trans set_drop_subset set_take_subset)
    
  lemma slice_sort_spec_xfer: "\<Down> (cdom_list_rel cparam) (slice_sort_spec (less' cparam) xs l h) \<le> pslice_sort_spec cdom pless cparam xs l h"
    unfolding pslice_sort_spec_def cdom_list_rel_alt 
    apply (auto simp: pw_le_iff refine_pw_simps in_br_conv)
    unfolding slice_sort_spec_alt
    apply (auto simp: refine_pw_simps)
    using sorted_wrt_ext
    by (smt ext_lt_def le_by_lt_def less'_def set_slice_ss sorted_wrt_mono_rel subsetD)
    
(*
  lemma pslice_sort_spec_xfer:
    assumes "m \<le> slice_sort_spec (less' cparam) xs l h"
    assumes "mm \<le> \<Down>(cdom_list_rel cparam) m"
    assumes "(xs',xs)\<in>cdom_list_rel cparam"
    shows "mm \<le> pslice_sort_spec cdom pless cparam xs l h"
    using assms unfolding pslice_sort_spec_def cdom_list_rel_alt 
    apply (auto simp: pw_le_iff refine_pw_simps in_br_conv)
    unfolding slice_sort_spec_alt
    apply (auto simp: refine_pw_simps)
    using sorted_wrt_ext
    by (smt ext_lt_def le_by_lt_def less'_def set_slice_ss sorted_wrt_mono_rel subset_code(1))
*)  

    
    
    
  lemma olist_to_eo_conv_refine[refine]: 
    "(xs',xs)\<in>cdom_list_rel cparam \<Longrightarrow> mop_to_eo_conv xs' \<le> \<Down>(cdom_olist_rel cparam) (mop_to_eo_conv xs)"
    apply (rule nres_relD)
    unfolding mop_to_eo_conv_def cdom_olist_rel_def cdom_list_rel_def
    by (parametricity)
    
  lemma olist_to_wo_conv_refine[refine]: 
    "\<lbrakk>(xs',xs)\<in>cdom_olist_rel cparam\<rbrakk> \<Longrightarrow> mop_to_wo_conv xs' \<le> \<Down>(cdom_list_rel cparam) (mop_to_wo_conv xs)"
    apply simp
    apply refine_rcg
    apply (auto simp: cdom_olist_rel_alt cdom_list_rel_alt in_br_conv)
    by (metis option.collapse)

    
  lemma olist_extract_refine[refine]: "\<lbrakk> (xs',xs)\<in>cdom_olist_rel cparam; (i',i)\<in>Id \<rbrakk> 
    \<Longrightarrow> mop_eo_extract xs' i' \<le> \<Down> ((br id (\<lambda>x. x\<in>cdom cparam)) \<times>\<^sub>r cdom_olist_rel cparam) (mop_eo_extract xs i)"
    unfolding mop_eo_extract_alt
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_alt in_br_conv)
    by (metis in_set_upd_cases option.distinct(1))
    
  lemma listo_eo_set_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_olist_rel cparam;
    (i',i)\<in>Id;
    (v',v)\<in>Id; v\<in>cdom cparam
  \<rbrakk> \<Longrightarrow> mop_eo_set xs' i' v' \<le> \<Down> (cdom_olist_rel cparam) (mop_eo_set xs i v)"  
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_alt in_br_conv)
    by (metis in_set_upd_cases option.sel)

    
  definition "pcmpo_idxs2 cparam xs\<^sub>0 i j \<equiv> doN {
    ASSERT (i \<noteq> j);
    (vi,xs) \<leftarrow> mop_eo_extract xs\<^sub>0 i;
    (vj,xs) \<leftarrow> mop_eo_extract xs j;
    r \<leftarrow> pcmp cparam vi vj;
    xs \<leftarrow> mop_eo_set xs i vi; \<comment> \<open>TODO: Let's hope the optimizer eliminates these assignments. In mid-term, eliminate them during sepref phase!\<close>
    xs \<leftarrow> mop_eo_set xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"
    
  definition "pcmpo_v_idx2 cparam xs\<^sub>0 v j \<equiv> doN {
    (vj,xs) \<leftarrow> mop_eo_extract xs\<^sub>0 j;
    r \<leftarrow> pcmp cparam v vj;
    xs \<leftarrow> mop_eo_set xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"

  definition "pcmpo_idx_v2 cparam xs\<^sub>0 i v \<equiv> doN {
    (vi,xs) \<leftarrow> mop_eo_extract xs\<^sub>0 i;
    r \<leftarrow> pcmp cparam vi v;
    xs \<leftarrow> mop_eo_set xs i vi;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"

  definition "pcmp_idxs2 cparam xs\<^sub>0 i j \<equiv> doN {
    xs \<leftarrow> mop_to_eo_conv xs\<^sub>0;
    b \<leftarrow> pcmpo_idxs2 cparam xs i j;
    xs \<leftarrow> mop_to_wo_conv xs;
    unborrow xs xs\<^sub>0;
    RETURN b
  }"  
  
  lemma pcmpo_idxs_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_olist_rel cparam;
    i\<noteq>j;
    (i',i)\<in>Id;
    (j',j)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmpo_idxs2 cparam xs' i' j' \<le> \<Down> bool_rel (WO.mop_cmpo_idxs cparam xs i j)"  
    unfolding pcmpo_idxs2_def
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_alt in_br_conv less'_def ext_lt_def
           list_update_swap[of i j] map_update[symmetric])
    done
  
  
  lemma pcmpo_v_idx_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_olist_rel cparam;
    (v',v)\<in>Id; v\<in>cdom cparam;
    (i',i)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmpo_v_idx2 cparam xs' v' i' \<le> \<Down> bool_rel (WO.mop_cmpo_v_idx cparam xs v i)"  
    unfolding pcmpo_v_idx2_def
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_alt in_br_conv less'_def ext_lt_def)
    done
    
  lemma pcmpo_idx_v_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_olist_rel cparam;
    (v',v)\<in>Id; v\<in>cdom cparam;
    (i',i)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmpo_idx_v2 cparam xs' i' v' \<le> \<Down> bool_rel (WO.mop_cmpo_idx_v cparam xs i v)"  
    unfolding pcmpo_idx_v2_def
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_alt in_br_conv less'_def ext_lt_def)
    done
  
  lemma pcmp_idxs_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_list_rel cparam;
    i\<noteq>j;
    (i',i)\<in>Id;
    (j',j)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmp_idxs2 cparam xs' i' j' \<le> \<Down> bool_rel (WO.mop_cmp_idxs cparam xs i j)"  
    unfolding pcmp_idxs2_def pcmpo_idxs2_def
    apply simp
    apply refine_vcg
    apply (auto 0 3 simp: cdom_list_rel_alt in_br_conv less'_def ext_lt_def 
           list_update_swap[of i j] map_update[symmetric])
    using nth_mem by blast
    
    
    
end
\<close>

\<^cancel>\<open>
locale parameterized_weak_ordering = weak_ordering +
  fixes (*cparam :: 'cparam*)
        cdom :: "'cparam \<Rightarrow> 'a set"
    and pcmp :: "'cparam \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool nres"
  assumes pcmp_correct[refine_vcg]: "\<lbrakk> a\<in>cdom cparam; b\<in>cdom cparam\<rbrakk> 
    \<Longrightarrow> pcmp cparam a b \<le> SPEC (\<lambda>r. r \<longleftrightarrow> a\<^bold><b)"
    
    
    
begin
  (* TODO: The refinements established here are just a special case of list-element refinement.
    We should use list-rel here! And generic parametricity lemmas from the operations!
  *)
  definition "cdom_list_rel cparam \<equiv> br id (\<lambda>xs. set xs \<subseteq> cdom cparam)"
  definition "cdom_olist_rel cparam \<equiv> br id (\<lambda>xs. \<forall>x. Some x \<in> set xs \<longrightarrow> x\<in>cdom cparam)"

  lemma olist_to_eo_conv_refine[refine]: 
    "(xs',xs)\<in>cdom_list_rel cparam \<Longrightarrow> mop_to_eo_conv xs' \<le> \<Down>(cdom_olist_rel cparam) (mop_to_eo_conv xs)"
    unfolding mop_to_eo_conv_def cdom_list_rel_def cdom_olist_rel_def
    by (auto simp: in_br_conv)
    
  lemma olist_to_wo_conv_refine[refine]: 
    "\<lbrakk>(xs',xs)\<in>cdom_olist_rel cparam\<rbrakk> \<Longrightarrow> mop_to_wo_conv xs' \<le> \<Down>(cdom_list_rel cparam) (mop_to_wo_conv xs)"
    apply simp
    apply refine_rcg
    apply (auto simp: cdom_olist_rel_def cdom_list_rel_def in_br_conv)
    by (metis option.collapse)

    
  lemma olist_extract_refine[refine]: "\<lbrakk> (xs',xs)\<in>cdom_olist_rel cparam; (i',i)\<in>Id \<rbrakk> 
    \<Longrightarrow> mop_eo_extract xs' i' \<le> \<Down> ((br id (\<lambda>x. x\<in>cdom cparam)) \<times>\<^sub>r cdom_olist_rel cparam) (mop_eo_extract xs i)"
    unfolding mop_eo_extract_alt
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_def in_br_conv)
    by (metis in_set_upd_cases option.distinct(1))
    
  lemma listo_eo_set_refine[refine]: "\<lbrakk>
    (xs',xs)\<in>cdom_olist_rel cparam;
    (i',i)\<in>Id;
    (v',v)\<in>Id; v\<in>cdom cparam
  \<rbrakk> \<Longrightarrow> mop_eo_set xs' i' v' \<le> \<Down> (cdom_olist_rel cparam) (mop_eo_set xs i v)"  
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_def in_br_conv)
    by (metis in_set_upd_cases option.sel)

    
  definition "pcmpo_idxs2 cparam xs\<^sub>0 i j \<equiv> doN {
    ASSERT (i \<noteq> j);
    (vi,xs) \<leftarrow> mop_eo_extract xs\<^sub>0 i;
    (vj,xs) \<leftarrow> mop_eo_extract xs j;
    r \<leftarrow> pcmp cparam vi vj;
    xs \<leftarrow> mop_eo_set xs i vi; \<comment> \<open>TODO: Let's hope the optimizer eliminates these assignments. In mid-term, eliminate them during sepref phase!\<close>
    xs \<leftarrow> mop_eo_set xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"
    
  definition "pcmpo_v_idx2 cparam xs\<^sub>0 v j \<equiv> doN {
    (vj,xs) \<leftarrow> mop_eo_extract xs\<^sub>0 j;
    r \<leftarrow> pcmp cparam v vj;
    xs \<leftarrow> mop_eo_set xs j vj;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"

  definition "pcmpo_idx_v2 cparam xs\<^sub>0 i v \<equiv> doN {
    (vi,xs) \<leftarrow> mop_eo_extract xs\<^sub>0 i;
    r \<leftarrow> pcmp cparam vi v;
    xs \<leftarrow> mop_eo_set xs i vi;
    unborrow xs xs\<^sub>0;
    RETURN r
  }"

  definition "pcmp_idxs2 cparam xs\<^sub>0 i j \<equiv> doN {
    xs \<leftarrow> mop_to_eo_conv xs\<^sub>0;
    b \<leftarrow> pcmpo_idxs2 cparam xs i j;
    xs \<leftarrow> mop_to_wo_conv xs;
    unborrow xs xs\<^sub>0;
    RETURN b
  }"  
  
  lemma pcmpo_idxs_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_olist_rel cparam;
    i\<noteq>j;
    (i',i)\<in>Id;
    (j',j)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmpo_idxs2 cparam xs' i' j' \<le> \<Down> bool_rel (mop_cmpo_idxs xs i j)"  
    unfolding pcmpo_idxs2_def
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_def in_br_conv 
           list_update_swap[of i j] map_update[symmetric])
    done
  
  
  lemma pcmpo_v_idx_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_olist_rel cparam;
    (v',v)\<in>Id; v\<in>cdom cparam;
    (i',i)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmpo_v_idx2 cparam xs' v' i' \<le> \<Down> bool_rel (mop_cmpo_v_idx xs v i)"  
    unfolding pcmpo_v_idx2_def
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_def in_br_conv)
    done
    
  lemma pcmpo_idx_v_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_olist_rel cparam;
    (v',v)\<in>Id; v\<in>cdom cparam;
    (i',i)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmpo_idx_v2 cparam xs' i' v' \<le> \<Down> bool_rel (mop_cmpo_idx_v xs i v)"  
    unfolding pcmpo_idx_v2_def
    apply simp
    apply refine_vcg
    apply (auto simp: cdom_olist_rel_def in_br_conv)
    done
  
  lemma pcmp_idxs_refine[refine]: "\<lbrakk>
    (xs',xs)\<in> cdom_list_rel cparam;
    i\<noteq>j;
    (i',i)\<in>Id;
    (j',j)\<in>Id
  \<rbrakk> \<Longrightarrow> pcmp_idxs2 cparam xs' i' j' \<le> \<Down> bool_rel (mop_cmp_idxs xs i j)"  
    unfolding pcmp_idxs2_def pcmpo_idxs2_def
    apply simp
    apply refine_vcg
    apply (auto 0 3 simp: cdom_list_rel_def in_br_conv
           list_update_swap[of i j] map_update[symmetric])
    done
    
    
end
\<close>

subsection \<open>Random Access Iterator\<close>
text \<open>The compare function takes an external parameter.\<close>  

term mop_eo_set

locale random_access_iterator =
  fixes wo_assn :: "'a list \<Rightarrow> 'oi::llvm_rep \<Rightarrow> assn"
    and eo_assn :: "'a option list \<Rightarrow> 'oi \<Rightarrow> assn"
    and elem_assn :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
    and to_eo_impl :: "'oi \<Rightarrow> 'oi llM"
    and to_wo_impl :: "'oi \<Rightarrow> 'oi llM"
    and extract_impl :: "'oi \<Rightarrow> 'size::len2 word \<Rightarrow> ('ai \<times> 'oi) llM"
    and extract_impl_cost :: "ecost" 
    and set_impl :: "'oi \<Rightarrow> 'size word \<Rightarrow> 'ai \<Rightarrow> 'oi llM"
    and set_impl_cost :: "ecost" 
  assumes
          to_eo_hnr: "(to_eo_impl, mop_to_eo_conv) \<in> wo_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ai. cnc_assn (\<lambda>x. x=ai) eo_assn)" 
      and to_wo_hnr: "(to_wo_impl, mop_to_wo_conv) \<in> eo_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ai. cnc_assn (\<lambda>x. x=ai) wo_assn)"
      and eo_extract_hnr_aux: "(uncurry extract_impl, uncurry (mop_eo_extract (\<lambda>_. extract_impl_cost))) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ (ai,_). elem_assn \<times>\<^sub>a cnc_assn (\<lambda>x. x = ai) eo_assn)"
      and eo_set_hnr_aux: "(uncurry2 set_impl, uncurry2 (mop_eo_set (\<lambda>_. set_impl_cost))) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ((ai,_),_). cnc_assn (\<lambda>x. x=ai) eo_assn)"
      
  notes [[sepref_register_adhoc to_eo_impl to_wo_impl extract_impl set_impl]]
begin

context
  notes [fcomp_norm_simps] = option_rel_id_simp list_rel_id prod_rel_id_simp hrr_comp_id_conv
begin  

  private method rl_mono = 
    (rule hfref_cons; 
      clarsimp_all; 
      clarsimp_all simp: cnc_assn_def sep_algebra_simps entails_lift_extract_simps)

  lemma eo_extract_nodep_hnr_aux: 
    "(uncurry extract_impl, uncurry (mop_eo_extract (\<lambda>_. extract_impl_cost))) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a eo_assn"
    using eo_extract_hnr_aux 
    by rl_mono

  lemma eo_set_nodep_hnr_aux: 
    "(uncurry2 set_impl, uncurry2 (mop_eo_set (\<lambda>_. set_impl_cost))) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a eo_assn"
    using eo_set_hnr_aux
    by rl_mono
    
  lemma to_eo_nodep_hnr[sepref_fr_rules]: "(to_eo_impl, mop_to_eo_conv) \<in> wo_assn\<^sup>d \<rightarrow>\<^sub>a eo_assn"
    using to_eo_hnr
    by rl_mono

  lemma to_wo_nodep_hnr[sepref_fr_rules]: "(to_wo_impl, mop_to_wo_conv) \<in> eo_assn\<^sup>d \<rightarrow>\<^sub>a wo_assn"
    using to_wo_hnr
    by rl_mono
  
        \<^cancel>\<open>
    
  sepref_decl_impl (ismop,no_register) eo_extract: eo_extract_hnr_aux .
  sepref_decl_impl (ismop) eo_extract_nodep: eo_extract_nodep_hnr_aux .
  
  sepref_decl_impl (ismop,no_register) eo_set: eo_set_hnr_aux .
  sepref_decl_impl (ismop) eo_set_nodep: eo_set_nodep_hnr_aux .
        
    
  lemmas eo_hnr_dep = eo_extract_dep_hnr eo_extract_hnr_mop eo_set_hnr eo_set_hnr_mop 
    to_eo_hnr to_wo_hnr
  lemmas eo_hnr_nodep = eo_extract_nodep_hnr eo_extract_nodep_hnr_mop eo_set_nodep_hnr eo_set_nodep_hnr_mop
    to_eo_nodep_hnr to_wo_nodep_hnr
    
    
  sepref_definition swap_eo_impl_aux is "uncurry2 swap_eo" :: "wo_assn\<^sup>d *\<^sub>a (snat_assn' TYPE('size))\<^sup>k *\<^sub>a (snat_assn' TYPE('size))\<^sup>k \<rightarrow>\<^sub>a wo_assn"
    unfolding swap_eo_def
    by sepref
    \<close>
end    

\<^cancel>\<open>
concrete_definition (in -) swap_eo_impl[llvm_inline] is random_access_iterator.swap_eo_impl_aux_def
  
context
  notes [fcomp_norm_simps] = option_rel_id_simp list_rel_id prod_rel_id_simp hrr_comp_id_conv
begin  
  sepref_decl_impl (ismop) swap_eo_impl_aux.refine[FCOMP swap_eo_refine, unfolded swap_eo_impl.refine[OF random_access_iterator_axioms]]
     uses mop_list_swap.fref[where A=Id] .

end     
       
(*  sepref_decl_impl (ismop) swap_eo_impl.refine[FCOMP swap_eo_refine] uses mop_list_swap.fref[where A=Id] .*)
  \<close>  
    
end


definition "refines_param_relp P A R Rimpl \<equiv> (uncurry2 Rimpl,uncurry2 R) \<in> P\<^sup>k*\<^sub>aA\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn"

lemma gen_refines_param_relpD: "GEN_ALGO Rimpl (refines_param_relp P A R) 
  \<Longrightarrow> (uncurry2 Rimpl,uncurry2 R) \<in> P\<^sup>k*\<^sub>aA\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool1_assn"
  by (simp add: GEN_ALGO_def refines_param_relp_def)

\<^cancel>\<open>
locale parameterized_sort_impl_context = random_access_iterator + parameterized_weak_ordering + 
  constrains "cdom" :: "'cparam \<Rightarrow> _" and pless :: _ and pcmp :: "'cparam \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool nres"
    and elem_assn :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
    and wo_assn :: "'a list \<Rightarrow> 'oi::llvm_rep \<Rightarrow> assn"
    and eo_assn :: "'a option list \<Rightarrow> 'oi \<Rightarrow> assn"
    and elem_assn :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
    and to_eo_impl :: "'oi \<Rightarrow> 'oi llM"
    and to_wo_impl :: "'oi \<Rightarrow> 'oi llM"
    and extract_impl :: "'oi \<Rightarrow> size_t word \<Rightarrow> ('ai \<times> 'oi) llM"
    and set_impl :: "'oi \<Rightarrow> size_t word \<Rightarrow> 'ai \<Rightarrow> 'oi llM"
    
  fixes pcmp_impl :: "'cparami \<Rightarrow> 'ai \<Rightarrow> 'ai \<Rightarrow> 1 word llM"
    and cparam_assn :: "'cparam \<Rightarrow> 'cparami \<Rightarrow> assn"
    
  assumes lt_impl: "GEN_ALGO pcmp_impl (refines_param_relp cparam_assn elem_assn pcmp)"
  notes pcmp_aux_hnr[sepref_fr_rules] = gen_refines_param_relpD[OF lt_impl]
  
  notes [[sepref_register_adhoc "pcmp"]]
  
begin

  thm pcmp_aux_hnr
  
  term pcmpo_v_idx2
  
  sepref_register pcmpo_idxs2 pcmpo_v_idx2 pcmpo_idx_v2 pcmp_idxs2

  sepref_def pcmpo_idxs_impl [llvm_inline] is "uncurry3 (PR_CONST pcmpo_idxs2)" :: 
    "cparam_assn\<^sup>k *\<^sub>a eo_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding pcmpo_idxs2_def PR_CONST_def
    supply [sepref_fr_rules] = eo_hnr_dep
    by sepref
    
    
  sepref_def pcmpo_v_idx_impl [llvm_inline] is "uncurry3 (PR_CONST pcmpo_v_idx2)" :: 
    "cparam_assn\<^sup>k *\<^sub>a eo_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding pcmpo_v_idx2_def PR_CONST_def
    supply [sepref_fr_rules] = eo_hnr_dep
    by sepref

  sepref_def pcmpo_idx_v_impl [llvm_inline] is "uncurry3 (PR_CONST pcmpo_idx_v2)" :: 
    "cparam_assn\<^sup>k *\<^sub>a eo_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding pcmpo_idx_v2_def PR_CONST_def
    supply [sepref_fr_rules] = eo_hnr_dep
    by sepref

  sepref_def pcmp_idxs_impl [llvm_inline] is "uncurry3 (PR_CONST pcmp_idxs2)" :: 
    "cparam_assn\<^sup>k *\<^sub>a wo_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding pcmp_idxs2_def PR_CONST_def
    supply [sepref_fr_rules] = eo_hnr_dep
    by sepref


end  

\<close>



subsection "Some more commands"
(* TODO: Move *)               
context
  fixes  T :: "(nat \<times> nat \<times> nat) \<Rightarrow> (char list, enat) acost"
begin
  definition mop_list_swap  :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list, _) nrest"
    where [simp]: "mop_list_swap xs i j \<equiv> do { ASSERT (i<length xs \<and> j<length xs); consume (RETURNT (swap xs i j)) (T (length xs,i,j)) }"
  sepref_register "mop_list_swap"
end

lemma param_mop_list_get:
  "(mop_list_swap T, mop_list_swap T) \<in> \<langle>the_pure A\<rangle> list_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>\<langle>the_pure A\<rangle> list_rel\<rangle> nrest_rel"
  apply(intro nrest_relI fun_relI)
  unfolding mop_list_swap_def swap_def
  apply (auto simp: pw_acost_le_iff refine_pw_simps list_rel_imp_same_length)
  apply parametricity
  by auto              

abbreviation "mop_list_swapN \<equiv> mop_list_swap (\<lambda>_. cost ''list_swap'' 1)"
abbreviation "mop_list_getN \<equiv> mop_list_get (\<lambda>_. cost ''list_get'' 1)"
abbreviation "mop_list_setN \<equiv> mop_list_set (\<lambda>_. cost ''list_set'' 1)"

abbreviation "SPECc2F aop \<equiv> ( (\<lambda>a b. consume (RETURNT (aop a b)) top))"
abbreviation "mop_list_getF \<equiv> mop_list_get (\<lambda>_. top)"
abbreviation "mop_list_setF \<equiv> mop_list_set (\<lambda>_. top)"
abbreviation "mop_list_swapF \<equiv> mop_list_swap (\<lambda>_. top)"        
abbreviation (in weak_ordering) "mop_cmp_idxsF \<equiv> mop_cmp_idxs top"



subsubsection \<open>Implementing Swap\<close>


definition myswap where "myswap xs l h =
  doN { 
      xs \<leftarrow> mop_to_eo_conv xs;
      (x,xs) \<leftarrow> mop_oarray_extract xs l;
      (y,xs) \<leftarrow> mop_oarray_extract xs h;
      xs \<leftarrow> mop_oarray_upd xs l y;
      xs \<leftarrow> mop_oarray_upd xs h x;
      xs \<leftarrow> mop_to_wo_conv xs;
      RETURN xs
  }"

definition myswap_cost :: ecost where 
  "myswap_cost = lift_acost mop_array_nth_cost + lift_acost mop_array_nth_cost + lift_acost mop_array_upd_cost + lift_acost mop_array_upd_cost "

lemma myswap_refine:
  assumes "wfR'' E"
    "myswap_cost \<le> timerefineA E (cost ''list_swap'' 1)"
  shows 
   "l\<noteq>h \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id
       \<Longrightarrow> myswap xs l h \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine E (mop_list_swapN xs' l' h'))"
  unfolding myswap_def mop_list_swap_def 
  unfolding mop_to_eo_conv_def mop_to_wo_conv_def
  unfolding mop_oarray_extract_def mop_oarray_upd_def
  unfolding mop_eo_extract_def mop_eo_set_def
  apply normalize_blocks
  apply(split prod.splits)+
  apply normalize_blocks
  apply safe
  apply(intro refine0 bindT_refine_conc_time_my_inres consumea_refine)
  apply refine_dref_type 
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto
    by (metis None_notin_image_Some list.set_map list_update_overwrite list_update_swap map_update)  
  subgoal using assms by auto
  subgoal by auto
  subgoal
    apply(rule order.trans[OF _ assms(2)])
    unfolding myswap_cost_def
    by (auto simp: add.assoc timerefineA_update_apply_same_cost   lift_acost_zero)
  subgoal by (auto simp add: More_List.swap_def list_update_swap map_update option.exhaust_sel)  
  done


subsection \<open>An Exchange Rate that refines compare and swap operations to executable ones\<close>

context sort_impl_context
begin

abbreviation "TR_cmp_swap \<equiv> TId(''cmp_idxs'':=cmp_idxs2'_cost, ''cmpo_idxs'':=cmpo_idxs2'_cost,''cmpo_v_idx'':=cmpo_v_idx2'_cost, ''list_swap'':= myswap_cost)"

lemma wfR''E[simp]: " wfR'' TR_cmp_swap" by (auto intro!: wfR''_upd)

lemma sp_E45[simp]: "struct_preserving TR_cmp_swap"
  by (auto intro!: struct_preserving_upd_I)



lemma myswap_TR_cmp_swap_refine:
   "l\<noteq>h \<Longrightarrow> (xs,xs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (h,h')\<in>Id
       \<Longrightarrow> myswap xs l h \<le> \<Down> (\<langle>Id\<rangle>list_rel) (timerefine TR_cmp_swap (mop_list_swapN xs' l' h'))"
  apply(rule myswap_refine)
  by (auto simp: timerefineA_update_apply_same_cost   lift_acost_zero) 
 

lemma mop_oarray_upd_refines:
  assumes "wfR'' TR"
    and "preserves_curr TR ''store''"
    and "preserves_curr TR ''ofs_ptr''"
  shows "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow>
      mop_oarray_upd a b c \<le> \<Down> Id (timerefine TR (mop_oarray_upd a' b' c'))"
  unfolding mop_oarray_upd_def mop_eo_set_def   
  using assms
    apply(intro refine0)
    apply (auto simp: timerefineA_cost_apply_costmult timerefineA_propagate
          lift_acost_propagate lift_acost_cost timerefineA_update_apply_same_cost intro!: wfR''_upd) 
  apply(simp add: assms(2,3)[THEN preserves_curr_D] costmult_cost)
  done

lemma mop_oarray_extract_refines:
  assumes "wfR'' TR"
    and "preserves_curr TR ''load''"
    and "preserves_curr TR ''ofs_ptr''"
  shows "(x,x')\<in>Id \<Longrightarrow> (i,i')\<in>Id \<Longrightarrow> 
      mop_oarray_extract x i \<le> \<Down> Id (timerefine TR (mop_oarray_extract x' i'))"
  unfolding mop_oarray_extract_def mop_eo_extract_def   
  using assms
    apply(intro refine0)
    apply (auto simp: timerefineA_cost_apply_costmult timerefineA_propagate
          lift_acost_propagate lift_acost_cost timerefineA_update_apply_same_cost intro!: wfR''_upd) 
  apply(simp add: assms(2,3)[THEN preserves_curr_D] costmult_cost)
  done 




end



end
