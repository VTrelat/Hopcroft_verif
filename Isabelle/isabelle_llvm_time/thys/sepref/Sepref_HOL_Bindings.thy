section \<open>HOL Setup\<close>
theory Sepref_HOL_Bindings
imports Sepref_Tool
begin

subsection \<open>Assertion Annotation\<close>
text \<open>Annotate an assertion to a term. The term must then be refined with this assertion.\<close>
(* TODO: Version for monadic expressions.*)
definition ASSN_ANNOT :: "('a \<Rightarrow> 'ai \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> 'a" where [simp]: "ASSN_ANNOT A x \<equiv> x"
context fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn" begin
  sepref_register "PR_CONST (ASSN_ANNOT A)"
  lemma [def_pat_rules]: "ASSN_ANNOT$A \<equiv> UNPROTECT (ASSN_ANNOT A)" by simp
  lemma [sepref_fr_rules]: "(return o (\<lambda>x. x), RETURN o PR_CONST (ASSN_ANNOT A)) \<in> A\<^sup>d\<rightarrow>\<^sub>aA"
    apply sepref_to_hoare
    by vcg

end  

lemma annotate_assn: "x \<equiv> ASSN_ANNOT A x" by simp


subsection \<open>Identity Relations\<close>
definition "IS_ID R \<equiv> R=Id"
definition "IS_BELOW_ID R \<equiv> R\<subseteq>Id"

lemma [safe_constraint_rules]: 
  "IS_ID Id"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (R1 \<rightarrow> R2)"
  "IS_ID R \<Longrightarrow> IS_ID (\<langle>R\<rangle>option_rel)"
  "IS_ID R \<Longrightarrow> IS_ID (\<langle>R\<rangle>list_rel)"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (R1 \<times>\<^sub>r R2)"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (\<langle>R1,R2\<rangle>sum_rel)"
  by (auto simp: IS_ID_def)

lemma [safe_constraint_rules]: 
  "IS_BELOW_ID Id"
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>option_rel)"
  "IS_BELOW_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<times>\<^sub>r R2)"
  "IS_BELOW_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (\<langle>R1,R2\<rangle>sum_rel)"
  by (auto simp: IS_ID_def IS_BELOW_ID_def option_rel_def sum_rel_def list_rel_def)

lemma IS_BELOW_ID_fun_rel_aux: "R1\<supseteq>Id \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<rightarrow> R2)"
  by (auto simp: IS_BELOW_ID_def dest: fun_relD)

corollary IS_BELOW_ID_fun_rel[safe_constraint_rules]: 
  "IS_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<rightarrow> R2)"
  using IS_BELOW_ID_fun_rel_aux[of Id R2]
  by (auto simp: IS_ID_def)


lemma IS_BELOW_ID_list_rel[safe_constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>list_rel)"
  unfolding IS_BELOW_ID_def
proof safe
  fix l l'
  assume A: "R\<subseteq>Id" 
  assume "(l,l')\<in>\<langle>R\<rangle>list_rel"
  thus "l=l'"
    apply induction
    using A by auto
qed

lemma IS_ID_imp_BELOW_ID[constraint_rules]: 
  "IS_ID R \<Longrightarrow> IS_BELOW_ID R"
  by (auto simp: IS_ID_def IS_BELOW_ID_def )



subsection \<open>Inverse Relation\<close>

lemma inv_fun_rel_eq[simp]: "(A\<rightarrow>B)\<inverse> = A\<inverse>\<rightarrow>B\<inverse>"
  by (auto dest: fun_relD)

lemma inv_option_rel_eq[simp]: "(\<langle>K\<rangle>option_rel)\<inverse> = \<langle>K\<inverse>\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma inv_prod_rel_eq[simp]: "(P \<times>\<^sub>r Q)\<inverse> = P\<inverse> \<times>\<^sub>r Q\<inverse>"
  by (auto)

lemma inv_sum_rel_eq[simp]: "(\<langle>P,Q\<rangle>sum_rel)\<inverse> = \<langle>P\<inverse>,Q\<inverse>\<rangle>sum_rel"
  by (auto simp: sum_rel_def)

lemma inv_list_rel_eq[simp]: "(\<langle>R\<rangle>list_rel)\<inverse> = \<langle>R\<inverse>\<rangle>list_rel"
  unfolding list_rel_def
  apply safe
  apply (subst list.rel_flip[symmetric])
  apply (simp add: conversep_iff[abs_def])
  apply (subst list.rel_flip[symmetric])
  apply (simp add: conversep_iff[abs_def])
  done

lemmas [constraint_simps] =
  Relation.converse_Id
  inv_fun_rel_eq
  inv_option_rel_eq
  inv_prod_rel_eq
  inv_sum_rel_eq
  inv_list_rel_eq


subsection \<open>Single Valued and Total Relations\<close>

(* TODO: Link to other such theories: Transfer, Autoref *)
definition "IS_LEFT_UNIQUE R \<equiv> single_valued (R\<inverse>)"
definition "IS_LEFT_TOTAL R \<equiv> Domain R = UNIV"
definition "IS_RIGHT_TOTAL R \<equiv> Range R = UNIV"
abbreviation (input) "IS_RIGHT_UNIQUE \<equiv> single_valued"

lemmas IS_RIGHT_UNIQUED = single_valuedD
lemma IS_LEFT_UNIQUED: "\<lbrakk>IS_LEFT_UNIQUE r; (y, x) \<in> r; (z, x) \<in> r\<rbrakk> \<Longrightarrow> y = z"
  by (auto simp: IS_LEFT_UNIQUE_def dest: single_valuedD)

lemma prop2p:
  "IS_LEFT_UNIQUE R = left_unique (rel2p R)"
  "IS_RIGHT_UNIQUE R = right_unique (rel2p R)"
  "right_unique (rel2p (R\<inverse>)) = left_unique (rel2p R)"
  "IS_LEFT_TOTAL R = left_total (rel2p R)"
  "IS_RIGHT_TOTAL R = right_total (rel2p R)"
  by (auto 
    simp: IS_LEFT_UNIQUE_def left_unique_def single_valued_def
    simp: right_unique_def
    simp: IS_LEFT_TOTAL_def left_total_def
    simp: IS_RIGHT_TOTAL_def right_total_def
    simp: rel2p_def
    )

lemma p2prop:
  "left_unique P = IS_LEFT_UNIQUE (p2rel P)"
  "right_unique P = IS_RIGHT_UNIQUE (p2rel P)"
  "left_total P = IS_LEFT_TOTAL (p2rel P)"
  "right_total P = IS_RIGHT_TOTAL (p2rel P)"
  "bi_unique P \<longleftrightarrow> left_unique P \<and> right_unique P"
  by (auto 
    simp: IS_LEFT_UNIQUE_def left_unique_def single_valued_def
    simp: right_unique_def bi_unique_alt_def
    simp: IS_LEFT_TOTAL_def left_total_def
    simp: IS_RIGHT_TOTAL_def right_total_def
    simp: p2rel_def
    )

lemmas [safe_constraint_rules] = 
  single_valued_Id  
  prod_rel_sv 
  list_rel_sv 
  option_rel_sv 
  sum_rel_sv

lemma [safe_constraint_rules]:
  "IS_LEFT_UNIQUE Id"
  "IS_LEFT_UNIQUE R1 \<Longrightarrow> IS_LEFT_UNIQUE R2 \<Longrightarrow> IS_LEFT_UNIQUE (R1\<times>\<^sub>rR2)"
  "IS_LEFT_UNIQUE R1 \<Longrightarrow> IS_LEFT_UNIQUE R2 \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R\<rangle>option_rel)"
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R\<rangle>list_rel)"
  by (auto simp: IS_LEFT_UNIQUE_def prod_rel_sv sum_rel_sv option_rel_sv list_rel_sv)

lemma IS_LEFT_TOTAL_alt: "IS_LEFT_TOTAL R \<longleftrightarrow> (\<forall>x. \<exists>y. (x,y)\<in>R)"
  by (auto simp: IS_LEFT_TOTAL_def)

lemma IS_RIGHT_TOTAL_alt: "IS_RIGHT_TOTAL R \<longleftrightarrow> (\<forall>x. \<exists>y. (y,x)\<in>R)"
  by (auto simp: IS_RIGHT_TOTAL_def)

lemma [safe_constraint_rules]:
  "IS_LEFT_TOTAL Id"
  "IS_LEFT_TOTAL R1 \<Longrightarrow> IS_LEFT_TOTAL R2 \<Longrightarrow> IS_LEFT_TOTAL (R1\<times>\<^sub>rR2)"
  "IS_LEFT_TOTAL R1 \<Longrightarrow> IS_LEFT_TOTAL R2 \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_LEFT_TOTAL R \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R\<rangle>option_rel)"
  apply (auto simp: IS_LEFT_TOTAL_alt sum_rel_def option_rel_def list_rel_def)
  apply (rename_tac x; case_tac x; auto)
  apply (rename_tac x; case_tac x; auto)
  done

lemma [safe_constraint_rules]: "IS_LEFT_TOTAL R \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R\<rangle>list_rel)"
  unfolding IS_LEFT_TOTAL_alt
proof safe
  assume A: "\<forall>x.\<exists>y. (x,y)\<in>R"
  fix l
  show "\<exists>l'. (l,l')\<in>\<langle>R\<rangle>list_rel"
    apply (induction l)
    using A
    by (auto simp: list_rel_split_right_iff)
qed

lemma [safe_constraint_rules]:
  "IS_RIGHT_TOTAL Id"
  "IS_RIGHT_TOTAL R1 \<Longrightarrow> IS_RIGHT_TOTAL R2 \<Longrightarrow> IS_RIGHT_TOTAL (R1\<times>\<^sub>rR2)"
  "IS_RIGHT_TOTAL R1 \<Longrightarrow> IS_RIGHT_TOTAL R2 \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_RIGHT_TOTAL R \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R\<rangle>option_rel)"
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (rename_tac x; case_tac x; auto)
  apply (clarsimp simp: IS_RIGHT_TOTAL_alt option_rel_def)
  apply (rename_tac x; case_tac x; auto)
  done

lemma [safe_constraint_rules]: "IS_RIGHT_TOTAL R \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R\<rangle>list_rel)"
  unfolding IS_RIGHT_TOTAL_alt
proof safe
  assume A: "\<forall>x.\<exists>y. (y,x)\<in>R"
  fix l
  show "\<exists>l'. (l',l)\<in>\<langle>R\<rangle>list_rel"
    apply (induction l)
    using A
    by (auto simp: list_rel_split_left_iff)
qed
  
lemma [constraint_simps]:
  "IS_LEFT_TOTAL (R\<inverse>) \<longleftrightarrow> IS_RIGHT_TOTAL R "
  "IS_RIGHT_TOTAL (R\<inverse>) \<longleftrightarrow> IS_LEFT_TOTAL R  "
  "IS_LEFT_UNIQUE (R\<inverse>) \<longleftrightarrow> IS_RIGHT_UNIQUE R"
  "IS_RIGHT_UNIQUE (R\<inverse>) \<longleftrightarrow> IS_LEFT_UNIQUE R "
  by (auto simp: IS_RIGHT_TOTAL_alt IS_LEFT_TOTAL_alt IS_LEFT_UNIQUE_def)

lemma [safe_constraint_rules]:
  "IS_RIGHT_UNIQUE A \<Longrightarrow> IS_RIGHT_TOTAL B \<Longrightarrow> IS_RIGHT_TOTAL (A\<rightarrow>B)"
  "IS_RIGHT_TOTAL A \<Longrightarrow> IS_RIGHT_UNIQUE B \<Longrightarrow> IS_RIGHT_UNIQUE (A\<rightarrow>B)"
  "IS_LEFT_UNIQUE A \<Longrightarrow> IS_LEFT_TOTAL B \<Longrightarrow> IS_LEFT_TOTAL (A\<rightarrow>B)"
  "IS_LEFT_TOTAL A \<Longrightarrow> IS_LEFT_UNIQUE B \<Longrightarrow> IS_LEFT_UNIQUE (A\<rightarrow>B)"
  apply (simp_all add: prop2p rel2p)
  (*apply transfer_step TODO: Isabelle 2016 *)
  apply (blast intro!: transfer_raw)+
  done

lemma [constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_RIGHT_UNIQUE R"
  "IS_BELOW_ID R \<Longrightarrow> IS_LEFT_UNIQUE R"
  "IS_ID R \<Longrightarrow> IS_RIGHT_TOTAL R"
  "IS_ID R \<Longrightarrow> IS_LEFT_TOTAL R"
  by (auto simp: IS_BELOW_ID_def IS_ID_def IS_LEFT_UNIQUE_def IS_RIGHT_TOTAL_def IS_LEFT_TOTAL_def
    intro: single_valuedI)

thm constraint_rules

subsubsection \<open>Additional Parametricity Lemmas\<close>
(* TODO: Move. Problem: Depend on IS_LEFT_UNIQUE, which has to be moved to!*)

lemma param_distinct[param]: "\<lbrakk>IS_LEFT_UNIQUE A; IS_RIGHT_UNIQUE A\<rbrakk> \<Longrightarrow> (distinct, distinct) \<in> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"  
  apply (fold rel2p_def)
  apply (simp add: rel2p)
  apply (rule distinct_transfer)
  apply (simp add: p2prop)
  done

lemma param_Image[param]: 
  assumes "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A"
  shows "((``), (``)) \<in> \<langle>A\<times>\<^sub>rB\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>B\<rangle>set_rel"
  apply (clarsimp simp: set_rel_def; intro conjI)  
  apply (fastforce dest: IS_RIGHT_UNIQUED[OF assms(2)])
  apply (fastforce dest: IS_LEFT_UNIQUED[OF assms(1)])
  done

lemma pres_eq_iff_svb: "((=),(=))\<in>K\<rightarrow>K\<rightarrow>bool_rel \<longleftrightarrow> (single_valued K \<and> single_valued (K\<inverse>))"
  apply (safe intro!: single_valuedI)
  apply (metis (full_types) IdD fun_relD1)
  apply (metis (full_types) IdD fun_relD1)
  by (auto dest: single_valuedD)

definition "IS_PRES_EQ R \<equiv> ((=), (=))\<in>R\<rightarrow>R\<rightarrow>bool_rel"
lemma [constraint_rules]: "\<lbrakk>single_valued R; single_valued (R\<inverse>)\<rbrakk> \<Longrightarrow> IS_PRES_EQ R"
  by (simp add: pres_eq_iff_svb IS_PRES_EQ_def)


subsection \<open>Bounded Assertions\<close>
definition "b_rel R P \<equiv> R \<inter> UNIV\<times>Collect P"
definition "b_assn A P \<equiv> \<lambda>x y. \<up>(P x) ** A x y"

lemma b_assn_pure_conv[constraint_simps]: "b_assn (pure R) P = pure (b_rel R P)"
  by (auto del: ext intro!: ext simp: b_rel_def b_assn_def pure_def pred_lift_extract_simps)
lemmas [sepref_import_rewrite, named_ss sepref_frame_normrel, fcomp_norm_unfold] 
  = b_assn_pure_conv[symmetric]

lemma b_rel_nesting[simp]: 
  "b_rel (b_rel R P1) P2 = b_rel R (\<lambda>x. P1 x \<and> P2 x)"
  by (auto simp: b_rel_def)
lemma b_rel_triv[simp]: 
  "b_rel R (\<lambda>_. True) = R"
  by (auto simp: b_rel_def)
lemma b_assn_nesting[simp]: 
  "b_assn (b_assn A P1) P2 = b_assn A (\<lambda>x. P1 x \<and> P2 x)"
  by (auto simp: b_assn_def pure_def pred_lift_extract_simps del: ext intro!: ext)
lemma b_assn_triv[simp]: 
  "b_assn A (\<lambda>_. True) = A"
  by (auto simp: b_assn_def pure_def pred_lift_extract_simps del: ext intro!: ext)

lemmas [constraint_simps,sepref_import_rewrite, named_ss sepref_frame_normrel, fcomp_norm_unfold]
  = b_rel_nesting b_assn_nesting

lemma b_rel_simp[simp]: "(x,y)\<in>b_rel R P \<longleftrightarrow> (x,y)\<in>R \<and> P y"
  by (auto simp: b_rel_def)

lemma b_assn_simp[simp]: "b_assn A P x y = (\<up>(P x) ** A x y)"
  by (auto simp: b_assn_def)

lemma b_rel_Range[simp]: "Range (b_rel R P) = Range R \<inter> Collect P" by auto
lemma b_assn_rdom[simp]: "rdomp (b_assn R P) x \<longleftrightarrow> rdomp R x \<and> P x"
  by (auto simp: rdomp_def pred_lift_extract_simps)


lemma b_rel_below_id[constraint_rules,relator_props]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (b_rel R P)"
  by (auto simp: IS_BELOW_ID_def)

lemma b_rel_left_unique[constraint_rules,relator_props]: 
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (b_rel R P)"
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def)
  
lemma b_rel_right_unique[constraint_rules,relator_props]: 
  "IS_RIGHT_UNIQUE R \<Longrightarrow> IS_RIGHT_UNIQUE (b_rel R P)"
  by (auto simp: single_valued_def)

\<comment> \<open>Registered as safe rule, although may loose information in the 
    odd case that purity depends condition.\<close>
lemma b_assn_is_pure[safe_constraint_rules, simp]:
  "is_pure A \<Longrightarrow> is_pure (b_assn A P)"
  by (auto simp: is_pure_conv b_assn_pure_conv)

lemma R_comp_brel_id_conv[fcomp_norm_simps]: "R O b_rel Id P = b_rel R P" by auto
  
  
\<comment> \<open>Most general form\<close>
lemma b_assn_subtyping_match[sepref_frame_match_rules]:
  assumes "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt A' x y"
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y); vassn_tag (hn_ctxt A' x y); P x\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt (b_assn A' P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
  by (auto simp: pred_lift_extract_simps)
  
\<comment> \<open>Simplified forms:\<close>
lemma b_assn_subtyping_match_eqA[sepref_frame_match_rules]:
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y); P x\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt (b_assn A P') x y"
  apply (rule b_assn_subtyping_match)
  subgoal 
    unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
    by (auto simp: pred_lift_extract_simps)
  subgoal
    using assms .
  done  

lemma b_assn_subtyping_match_tR[sepref_frame_match_rules]:
  assumes "\<lbrakk>P x\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<turnstile> hn_ctxt A' x y"
  shows "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt A' x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def
  by (auto simp: pred_lift_extract_simps)

lemma b_assn_subtyping_match_tL[sepref_frame_match_rules]:
  assumes "hn_ctxt A x y \<turnstile> hn_ctxt A' x y"
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y)\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt A x y \<turnstile> hn_ctxt (b_assn A' P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
  by (auto simp: pred_lift_extract_simps)


lemma b_assn_subtyping_match_eqA_tR[sepref_frame_match_rules]: 
  "hn_ctxt (b_assn A P) x y \<turnstile> hn_ctxt A x y"
  unfolding hn_ctxt_def b_assn_def entails_def
  by (auto simp: pred_lift_extract_simps)

lemma b_assn_subtyping_match_eqA_tL[sepref_frame_match_rules]:
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y)\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt A x y \<turnstile> hn_ctxt (b_assn A P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entails_def vassn_tag_def
  by (auto simp: pred_lift_extract_simps)

  
lemma b_rel_gen_merge:
  assumes A: "MERGE1 A f B g C"  
  shows "MERGE1 (b_assn A P) f (b_assn B Q) g (b_assn C (\<lambda>x. P x \<or> Q x))"  
  supply [vcg_rules] = MERGE1D[OF A]
  apply rule
  by vcg
  
lemmas b_rel_merge_eq[sepref_frame_merge_rules] = b_rel_gen_merge[where P=P and Q=P for P, simplified]
lemmas [sepref_frame_merge_rules] = b_rel_gen_merge
lemmas b_rel_merge_left[sepref_frame_merge_rules] = b_rel_gen_merge[where Q="\<lambda>_. True", simplified]
lemmas b_rel_merge_right[sepref_frame_merge_rules] = b_rel_gen_merge[where P="\<lambda>_. True", simplified]
  
(*  
\<comment> \<open>General form\<close>
lemma b_rel_subtyping_merge[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A' P') x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn Am (\<lambda>x. P x \<or> P' x)) x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def)
  
\<comment> \<open>Simplified forms\<close>
lemma b_rel_subtyping_merge_eqA[sepref_frame_merge_rules]:
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  apply (rule b_rel_subtyping_merge)
  by simp

lemma b_rel_subtyping_merge_tL[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt A x y \<or>\<^sub>A hn_ctxt (b_assn A' P') x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  using b_rel_subtyping_merge[of A x y A' Am "\<lambda>_. True" P', simplified] assms .

lemma b_rel_subtyping_merge_tR[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  using b_rel_subtyping_merge[of A x y A' Am P "\<lambda>_. True", simplified] assms .

lemma b_rel_subtyping_merge_eqA_tL[sepref_frame_merge_rules]:
  shows "hn_ctxt A x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  using b_rel_subtyping_merge_eqA[of A "\<lambda>_. True" x y P', simplified] .

lemma b_rel_subtyping_merge_eqA_tR[sepref_frame_merge_rules]:
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  using b_rel_subtyping_merge_eqA[of A P x y "\<lambda>_. True", simplified] .

(* TODO: Combinatorial explosion :( *)
lemma b_assn_invalid_merge1: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_invalid (b_assn A P') x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge2: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_invalid A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge3: "hn_invalid A x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge4: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge5: "hn_ctxt (b_assn A P') x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge6: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_ctxt A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge7: "hn_ctxt A x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge8: "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_invalid A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge9: "hn_invalid A x y \<or>\<^sub>A hn_ctxt (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemmas b_assn_invalid_merge[sepref_frame_merge_rules] = 
  b_assn_invalid_merge1
  b_assn_invalid_merge2
  b_assn_invalid_merge3
  b_assn_invalid_merge4
  b_assn_invalid_merge5
  b_assn_invalid_merge6
  b_assn_invalid_merge7
  b_assn_invalid_merge8
  b_assn_invalid_merge9

*)



abbreviation nbn_rel :: "nat \<Rightarrow> (nat \<times> nat) set" 
  \<comment> \<open>Natural numbers with upper bound.\<close>
  where "nbn_rel n \<equiv> b_rel nat_rel (\<lambda>x::nat. x<n)"  


lemma in_R_comp_nbn_conv: "(a,b)\<in>(R O nbn_rel N) \<longleftrightarrow> (a,b)\<in>R \<and> b<N" by auto
lemma range_comp_nbn_conv: "Range (R O nbn_rel N) = Range R \<inter> {0..<N}"
  by (auto 0 3 simp: b_rel_def)

lemma mk_free_b_assn[sepref_frame_free_rules]:
  assumes "MK_FREE A f"  
  shows "MK_FREE (b_assn A P) f"  
proof -
  note [vcg_rules] = assms[THEN MK_FREED]
  show ?thesis by rule vcg
qed

lemma intf_of_b_rel[synth_rules]: "INTF_OF_REL R I \<Longrightarrow> INTF_OF_REL (b_rel R P) I" by simp

lemma b_assn_intf[intf_of_assn]: "intf_of_assn V I \<Longrightarrow> intf_of_assn (b_assn V P) I"
  by simp


text \<open>Introduce extra goal for bounded result\<close>
lemma hfref_bassn_resI:
  assumes "\<And>xs. \<lbrakk>rdomp (fst As) xs; C xs\<rbrakk> \<Longrightarrow> a xs \<le>\<^sub>n SPEC P t"
  assumes "(c,a)\<in>[C]\<^sub>a As \<rightarrow> R"
  shows "(c,a)\<in>[C]\<^sub>a As \<rightarrow> b_assn R P"
  apply rule
  apply (rule hn_refine_preI)
  apply (rule hn_refine_cons)
  apply (rule hn_refine_augment_res)
  apply (rule assms(2)[to_hnr, unfolded hn_ctxt_def autoref_tag_defs])
  apply simp
  apply (rule assms(1))
  apply (auto simp: rdomp_def sep_algebra_simps)
  done

  
  
subsection \<open>Tool Setup\<close>
lemmas [sepref_relprops] = 
  sepref_relpropI[of IS_LEFT_UNIQUE]
  sepref_relpropI[of IS_RIGHT_UNIQUE]
  sepref_relpropI[of IS_LEFT_TOTAL]
  sepref_relpropI[of IS_RIGHT_TOTAL]
  sepref_relpropI[of is_pure]
  sepref_relpropI[of "IS_PURE \<Phi>" for \<Phi>]
  sepref_relpropI[of IS_ID]
  sepref_relpropI[of IS_BELOW_ID]
 


lemma [sepref_relprops_simps]:
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_BELOW_ID) A"
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_LEFT_TOTAL) A"
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_RIGHT_TOTAL) A"
  "CONSTRAINT (IS_PURE IS_BELOW_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A"
  "CONSTRAINT (IS_PURE IS_BELOW_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A"
  by (auto 
    simp: IS_ID_def IS_BELOW_ID_def IS_PURE_def IS_LEFT_UNIQUE_def
    simp: IS_LEFT_TOTAL_def IS_RIGHT_TOTAL_def
    simp: single_valued_below_Id)

declare True_implies_equals[sepref_relprops_simps]

lemma [sepref_relprops_transform]: "single_valued (R\<inverse>) = IS_LEFT_UNIQUE R"
  by (auto simp: IS_LEFT_UNIQUE_def)

  
subsection \<open>Default Initializers\<close>  
text \<open>We define a generic algorithm scheme to determine the abstract counterpart of
  the \<^term>\<open>init::'a::llvm_rep\<close> value wrt. an assertion. This is important for 
  initializing container data structures directly from zero-initializing \<open>calloc\<close>, 
  rather than having to \<open>memset\<close> each array.\<close>

definition is_init :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" 
  where "is_init A i \<equiv> is_pure A \<and> (init,i) \<in> the_pure A"
  
lemma is_init_id_assn[sepref_gen_algo_rules]: "GEN_ALGO init (is_init id_assn)"
  by (auto simp: GEN_ALGO_def is_init_def)
  
  
subsection \<open>Arithmetics\<close>





context 
  fixes name :: ecost and g:: "('a \<Rightarrow> 'c)"
begin
  sepref_register timed_unop': "SPECc1' name g"
end

context 
  fixes name :: string and g:: "('a \<Rightarrow> 'c)"
begin
  sepref_register timed_unop: "SPECc1 name g"
end

context 
  fixes name :: string and f:: "('a \<Rightarrow> 'b \<Rightarrow> 'c)"
begin
  sepref_register timed_binop: "SPECc2 name f"
end


subsubsection \<open>Connecting to Standard Operation Abstraction from LLVM-RS\<close>

text \<open>We will hide the connection behind an additional abstraction layer, 
  introduced by definitions. So, the definitions from this locale should not 
  be used by the end-user.
\<close>
context standard_opr_abstraction begin
  definition "rel \<equiv> br \<alpha> I"

  lemma assn_is_rel: "\<upharpoonleft>assn = pure rel"
    unfolding pure_def rel_def in_br_conv assn_def
    apply (intro ext)
    apply (auto simp: pred_lift_extract_simps)
    done
    
  abbreviation (input) sepref_assn where "sepref_assn \<equiv> pure rel"  

 
  lemma hn_un_op:
    assumes "is_un_op name PRE cop xmop aop"  
    shows "(cop,SPECc1 name aop) \<in> [\<lambda>a. PRE TYPE('c) a]\<^sub>a sepref_assn\<^sup>k \<rightarrow> sepref_assn"
    unfolding assn_is_rel[symmetric] SPECc1_def
    apply sepref_to_hoare
    supply [vcg_rules] = un_op_tmpl[OF assms, unfolded one_enat_def lift_acost_cost, folded one_enat_def] 
    by vcg

  lemma hn_bin_op:
    assumes "is_bin_op name PRE cop xmop aop"  
    shows "(uncurry cop,uncurry (SPECc2 name aop)) \<in> [\<lambda>(a,b). PRE TYPE('c) a b]\<^sub>a sepref_assn\<^sup>k *\<^sub>a sepref_assn\<^sup>k \<rightarrow> sepref_assn"
    unfolding assn_is_rel[symmetric] SPECc2_def
    apply sepref_to_hoare
    supply [vcg_rules] = bin_op_tmpl[OF assms, unfolded one_enat_def lift_acost_cost, folded one_enat_def]
    by vcg
    
  lemma hn_cmp_op:  
    assumes "is_cmp_op name cop xmop aop"
    shows "(uncurry cop,uncurry (SPECc2 name aop)) \<in> sepref_assn\<^sup>k *\<^sub>a sepref_assn\<^sup>k \<rightarrow>\<^sub>a bool.sepref_assn"
    unfolding assn_is_rel[symmetric] bool.assn_is_rel[symmetric] SPECc2_def
    apply sepref_to_hoare
    supply [vcg_rules] = cmp_op_tmpl[OF assms, unfolded one_enat_def lift_acost_cost, folded one_enat_def]
    by vcg
    

end
subsubsection \<open>Operator Setup\<close>

text \<open>Not-Equals is an operator in LLVM, but not in HOL\<close>
definition [simp]: "op_neq a b \<equiv> a\<noteq>b"  
(* TODO: Maybe have this pattern rule only for certain types.
  Otherwise, op_neq has to be implemented by every type that has custom eq-operator!

  The best solution would, or course, be to have a generic algorithm!
*)
lemma op_neq_pat[def_pat_rules]: "Not$((=)$a$b) \<equiv> op_neq$a$b" by simp
sepref_register op_neq_word: "op_neq :: _ word \<Rightarrow> _"


text \<open>For technical reasons, we need the operands as parameters to the operators 
  on the concrete side of refinement theorems. Thus, we define the following shortcut
  for comparison operators. \<close>    
(* TODO/FIXME: This, in turn, relies on LLVM-inlining of from_bool (comparison)! 
  Perhaps we should directly generate the ll_icmp instructions
*)  
definition [llvm_inline]: "lift_cmp_op c a b \<equiv> from_bool (c a b)"  
  


   
subsubsection \<open>Boolean\<close>

definition "bool1_rel \<equiv> bool.rel"
abbreviation "bool1_assn \<equiv> (pure bool1_rel)"

lemma bool_const_refine[sepref_import_param]:
  "(0,False)\<in>bool1_rel"  
  "(1,True)\<in>bool1_rel"  
  by (auto simp: bool1_rel_def bool.rel_def in_br_conv)
  


lemma hn_bool_ops:
  "(uncurry ll_and, uncurry (PR_CONST (SPECc2 ''and'' (\<and>)))) \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
   "(uncurry ll_or, uncurry (PR_CONST (SPECc2 ''or'' (\<or>)))) \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_xor, uncurry (PR_CONST (SPECc2 ''xor'' (op_neq)))) \<in> bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  "(ll_not1, PR_CONST (SPECc1 ''add'' Not)) \<in> bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn" (* TODO: this is strange, but LLVM seems to implement Not, with an add opration *)
  using bool_bin_ops[THEN bool.hn_bin_op, folded bool1_rel_def, unfolded to_hfref_post]
    and bool_un_ops[THEN bool.hn_un_op, folded bool1_rel_def]
  unfolding op_neq_def
  by simp_all

lemmas f = hn_bool_ops[to_hnr]
lemmas hn_bool_ops[sepref_fr_rules] (* TODO: strange error *)
thm f[to_hfref]
thm sepref_fr_rules

thm hnr_bind
thm app_rule app'_rule
thm id_rules pat_rules
definition "mop_impl x y = do { nx \<leftarrow> SPECc1 ''add'' Not x; SPECc2 ''and'' (\<and>) nx y }"

text \<open>We define an implies connective, using sepref\<close>
sepref_definition ll_implies is "uncurry mop_impl" :: "bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding imp_conv_disj mop_impl_def
  by sepref  


declare ll_implies_def[llvm_inline]
declare ll_implies.refine[sepref_fr_rules]

lemma is_init_bool[sepref_gen_algo_rules]:
  "GEN_ALGO False (is_init bool1_assn)"
  unfolding GEN_ALGO_def is_init_def
  unfolding bool1_rel_def bool.rel_def
  by (simp add: in_br_conv)

subsubsection \<open>Direct Word Arithmetic\<close>

abbreviation "word_rel \<equiv> (Id::(_::len word \<times> _) set)"
abbreviation "word_assn \<equiv> (id_assn::_::len word \<Rightarrow> _)"
abbreviation word_assn' :: "'a::len itself \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> (llvm_amemory*_) \<Rightarrow> bool" 
  where "word_assn' _ \<equiv> word_assn"

(* TODO: Move *)  
definition ll_not :: "'a::len word \<Rightarrow> 'a word llM" where 
  [llvm_inline]: "ll_not a \<equiv> doM { a \<leftarrow> ll_sub 0 a; ll_sub a 1 }"
  
(* plain wrong with time
context llvm_prim_arith_setup begin
  
  lemma ll_not_normalize[vcg_normalize_simps]: "ll_not a = return (~~a)"
    unfolding ll_not_def
    supply [simp] = NOT_eq
    by vcg_normalize
  
end *)


context begin  
  interpretation llvm_prim_arith_setup .  

context fixes a::num begin  
  sepref_register 
    "numeral a :: _ word"  
    "0 :: _ word"
    "1 :: _ word"

  lemma word_numeral_param[sepref_import_param]:
    "(numeral a,PR_CONST (numeral a)) \<in> word_rel"  
    "(0,0)\<in>word_rel"
    "(1,1)\<in>word_rel"
    by auto
        
end
  
   
sepref_register 
  plus_word: "(+):: _ word \<Rightarrow> _"  
  minus_word: "(-):: _ word \<Rightarrow> _"  
  times_word: "(*):: _ word \<Rightarrow> _"  
  and_word: "(AND):: _ word \<Rightarrow> _"  
  or_word: "(OR):: _ word \<Rightarrow> _"  
  xor_word: "(XOR):: _ word \<Rightarrow> _"  
  
lemma word_param_imports[sepref_import_param]:
  "((+),(+)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((-),(-)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((*),(*)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((AND),(AND)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((OR),(OR)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  "((XOR),(XOR)) \<in> word_rel \<rightarrow> word_rel \<rightarrow> word_rel"
  by simp_all

sepref_register 
  not_word: "NOT:: _ word \<Rightarrow> _"  

lemma hn_word_NOT_aux: "cost ''sub'' 2 = cost ''sub'' 1 + cost ''sub'' 1"
  by (auto simp add: cost_same_curr_add) 

lemma lift_acost_add: "lift_acost t + lift_acost t' = lift_acost (t+t')"
  unfolding lift_acost_def by (cases t; cases t'; auto)

lemma hn_word_NOT_aux2: "$(lift_acost (t + t')) = ($(lift_acost t) ** $(lift_acost t'))"
  by (simp add: time_credits_add lift_acost_add)

lemma hn_word_NOT[sepref_fr_rules]: "(ll_not,PR_CONST (SPECc1' (cost ''sub'' (enat 2)) (NOT))) \<in> word_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
  unfolding SPECc1'_def ll_not_def hn_word_NOT_aux PR_CONST_def
  unfolding hn_word_NOT_aux one_enat_def lift_acost_cost[symmetric]
  apply sepref_to_hoare
  apply(simp only: hn_word_NOT_aux2)
  supply [simp] = NOT_eq
  by vcg



sepref_register 
  div_word: "(div):: _ word \<Rightarrow> _"  
  mod_word: "(mod):: _ word \<Rightarrow> _"  
  sdiv_word: "(sdiv):: _ word \<Rightarrow> _"  
  smod_word: "(smod):: _ word \<Rightarrow> _"  
thm vcg_rules
lemma hn_word_div_op[sepref_fr_rules]:
  "(uncurry (ll_udiv),uncurry (PR_CONST (SPECc2 ''udiv'' (div)))) \<in> [\<lambda>(_,d). d\<noteq>0]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  "(uncurry (ll_urem),uncurry (PR_CONST (SPECc2 ''urem'' (mod)))) \<in> [\<lambda>(_,d). d\<noteq>0]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  "(uncurry (ll_sdiv),uncurry (PR_CONST (SPECc2 ''sdiv'' (sdiv)))) \<in> [\<lambda>(c,d). d\<noteq>0 \<and> in_srange (sdiv) c d]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  "(uncurry (ll_srem),uncurry (PR_CONST (SPECc2 ''srem'' (smod)))) \<in> [\<lambda>(c,d). d\<noteq>0 \<and> in_srange (sdiv) c d]\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow> word_assn"  
  unfolding SPECc2_def PR_CONST_def
      unfolding one_enat_def lift_acost_cost[symmetric]
      by (sepref_to_hoare, vcg')+

sepref_register 
  eq_word: "(=):: _ word \<Rightarrow> _"  
  neq_word: "op_neq:: _ word \<Rightarrow> _"  
  ult_word: "(<):: _ word \<Rightarrow> _"  
  ule_word: "(\<le>):: _ word \<Rightarrow> _"  
  slt_word: "(<s):: _ word \<Rightarrow> _"  
  sle_word: "(\<le>s):: _ word \<Rightarrow> _"  
    
lemma hn_word_icmp_op[sepref_fr_rules]:
  "(uncurry (ll_icmp_eq), uncurry (PR_CONST (SPECc2 ''icmp_eq'' (=)))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_ne), uncurry (PR_CONST (SPECc2 ''icmp_ne'' (op_neq)))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_ult), uncurry (PR_CONST (SPECc2 ''icmp_ult'' (<)))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_ule), uncurry (PR_CONST (SPECc2 ''icmp_ule'' (\<le>)))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_slt), uncurry (PR_CONST (SPECc2 ''icmp_slt'' (\<lambda>a b. a <s b)))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry (ll_icmp_sle), uncurry (PR_CONST (SPECc2 ''icmp_sle'' (\<lambda>a b. a <=s b)))) \<in> word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding bool1_rel_def bool.rel_def PR_CONST_def SPECc2_def
  unfolding one_enat_def lift_acost_cost[symmetric]
       supply [simp] = in_br_conv
  by (sepref_to_hoare, vcg)+
  
  
lemma is_init_word[sepref_gen_algo_rules]:
  "GEN_ALGO 0 (is_init word_assn)"
  unfolding GEN_ALGO_def is_init_def
  by (simp)
  
end  
      

subsubsection \<open>Integer by Word\<close>
  
definition "sint_rel \<equiv> sint.rel"
abbreviation "sint_assn \<equiv> pure sint_rel"  

abbreviation (input) "sint_rel' TYPE('a::len) \<equiv> sint_rel :: ('a word \<times> _) set"
abbreviation (input) "sint_assn' TYPE('a::len) \<equiv> sint_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"


definition [simp]: "sint_const TYPE('a::len) c \<equiv> (c::int)"
context fixes c::int begin
  sepref_register "sint_const TYPE('a::len) c" :: "int"
end


lemma fold_sint:
  "0 = sint_const TYPE('a::len) 0"  
  "1 = sint_const TYPE('a::len) 1"  
  "-1 \<equiv> (sint_const TYPE('a::len) (-1))"  
  "numeral n \<equiv> (sint_const TYPE('a::len) (numeral n))"
  "-(numeral n) \<equiv> (sint_const TYPE('a::len) (-numeral n))"
  by simp_all


lemma hn_sint_0[sepref_import_param]:
  "(0,sint_const TYPE('a) 0) \<in> sint_rel' TYPE('a::len)"
  by (auto simp: sint_rel_def sint.rel_def in_br_conv)

lemma hn_sint_1[sepref_fr_rules]:
  "LENGTH('a)\<noteq>1 \<Longrightarrow> hn_refine \<box> (return 1::_ llM) \<box> (sint_assn' TYPE('a::len)) (RETURNTecost$PR_CONST (sint_const TYPE('a) 1))"
  unfolding APP_def
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv by vcg

lemma hn_sint_minus_1[sepref_fr_rules]:
  "hn_refine \<box> (return (-1)::_ llM) \<box> (sint_assn' TYPE('a::len)) (RETURN$PR_CONST (sint_const TYPE('a) (-1)))"
  unfolding APP_def
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv by vcg
  
lemma hn_sint_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> sints LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)::_ llM) \<box> (sint_assn' TYPE('a::len)) (RETURN$(PR_CONST (sint_const TYPE('a) (numeral n))))"
  unfolding APP_def
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv 
  apply vcg'
  by (auto simp: sbintrunc_mod2p min_sint_def max_sint_def ll_const_signed_aux)

lemma hn_sint_minus_numeral[sepref_fr_rules]:
  "\<lbrakk>-numeral n \<in> sints LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (-numeral n)::_ llM) \<box> (sint_assn' TYPE('a::len)) (RETURN$(PR_CONST (sint_const TYPE('a) (-numeral n))))"
  unfolding APP_def
  apply sepref_to_hoare unfolding sint_rel_def sint.rel_def in_br_conv 
  apply vcg'
  apply (auto simp: sbintrunc_mod2p min_sint_def max_sint_def ll_const_signed_aux)
  by (smt diff_Suc_less int_mod_eq' len_gt_0 neg_numeral_le_numeral power_strict_increasing_iff)

  
sepref_register 
  plus_int: "(+)::int\<Rightarrow>_"    :: "int \<Rightarrow> int \<Rightarrow> int"
  minus_int: "(-)::int\<Rightarrow>_"   :: "int \<Rightarrow> int \<Rightarrow> int"
  times_int: "(*)::int\<Rightarrow>_"  :: "int \<Rightarrow> int \<Rightarrow> int"
  sdiv_int: "(sdiv)::int\<Rightarrow>_" :: "int \<Rightarrow> int \<Rightarrow> int"
  smod_int: "(smod)::int\<Rightarrow>_" :: "int \<Rightarrow> int \<Rightarrow> int"
  
sepref_register 
  eq_int: "(=)::int\<Rightarrow>_"        :: "int \<Rightarrow> int \<Rightarrow> bool"
  op_neq_int: "op_neq::int\<Rightarrow>_" :: "int \<Rightarrow> int \<Rightarrow> bool"
  lt_int: "(<)::int\<Rightarrow>_"        :: "int \<Rightarrow> int \<Rightarrow> bool"
  le_int: "(\<le>)::int\<Rightarrow>_"        :: "int \<Rightarrow> int \<Rightarrow> bool"
  
sepref_register    
  and_int: "(AND):: int \<Rightarrow> _"  
  or_int: "(OR):: int \<Rightarrow> _"  
  xor_int: "(XOR):: int \<Rightarrow> _"
  shiftr_int: "(<<) :: int \<Rightarrow> nat \<Rightarrow> int"
  shiftl_int: "(>>) :: int \<Rightarrow> nat \<Rightarrow> int"


thm sint_cmp_ops[THEN sint.hn_cmp_op, folded sint_rel_def, unfolded to_hfref_post]  
thm sint_bin_ops[THEN sint.hn_bin_op, folded sint_rel_def, unfolded to_hfref_post]  
  
lemma hn_sint_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (PR_CONST (SPECc2 ''add'' (+))))
    \<in> [\<lambda>(a, b). a + b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_sub, uncurry (PR_CONST (SPECc2 ''sub'' (-))))
    \<in> [\<lambda>(a, b). a - b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_mul, uncurry (PR_CONST (SPECc2 ''mul'' (*))))
    \<in> [\<lambda>(a, b). a * b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_sdiv, uncurry (PR_CONST (SPECc2 ''sdiv'' (sdiv))))
    \<in> [\<lambda>(a, b). b \<noteq> 0 \<and> a sdiv b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
  "(uncurry ll_srem, uncurry (PR_CONST (SPECc2 ''srem'' (smod))))
    \<in> [\<lambda>(a, b). b \<noteq> 0 \<and> a sdiv b \<in> sints LENGTH('a)]\<^sub>a sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow> sint_assn' TYPE('a::len)"
    
  "(uncurry ll_icmp_eq, uncurry (PR_CONST (SPECc2 ''icmp_eq''  (=)))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (PR_CONST (SPECc2 ''icmp_ne''  (op_neq)))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_sle, uncurry (PR_CONST (SPECc2 ''icmp_sle'' (\<le>)))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_slt, uncurry (PR_CONST (SPECc2 ''icmp_slt'' (<)))) \<in> sint_assn\<^sup>k *\<^sub>a sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding op_neq_def PR_CONST_def
  using sint_bin_ops[THEN sint.hn_bin_op, folded sint_rel_def, unfolded to_hfref_post]
    and sint_cmp_ops[THEN sint.hn_cmp_op, folded sint_rel_def bool1_rel_def, unfolded to_hfref_post]
  apply simp_all
  done


      
definition [simp]: "sint_init TYPE('a::len) \<equiv> 0::int"

(* TODO: Add rule for 0 *)
lemma is_init_sint[sepref_gen_algo_rules]:
  "GEN_ALGO (sint_init TYPE('a::len)) (is_init (sint_assn' TYPE('a)))"
  unfolding GEN_ALGO_def sint_init_def is_init_def
  unfolding sint_rel_def sint.rel_def
  by (simp add: in_br_conv)
  
lemma is_init_sint0[sepref_gen_algo_rules]: 
  "GEN_ALGO (sint_const TYPE('a::len) 0) (is_init (sint_assn' TYPE('a)))"
  using is_init_sint[where 'a='a]
  by simp
  

subsubsection \<open>Natural Numbers by Unsigned Word\<close>

sepref_register 
  plus_nat: "(+)::nat\<Rightarrow>_"    :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_nat: "(-)::nat\<Rightarrow>_"   :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_nat: "(*)::nat\<Rightarrow>_"  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  div_nat: "(div)::nat\<Rightarrow>_"   :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  mod_nat: "(mod)::nat\<Rightarrow>_"   :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  
sepref_register 
  eq_nat: "(=)::nat\<Rightarrow>_"        :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  op_neq_nat: "op_neq::nat\<Rightarrow>_" :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  lt_nat: "(<)::nat\<Rightarrow>_"        :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  le_nat: "(\<le>)::nat\<Rightarrow>_"        :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  
sepref_register    
  and_nat: "(AND):: nat \<Rightarrow> _"  
  or_nat: "(OR):: nat \<Rightarrow> _"  
  xor_nat: "(XOR):: nat \<Rightarrow> _"  
  shiftr_nat: "(<<) :: nat \<Rightarrow> _ \<Rightarrow> _"
  shiftl_nat: "(>>) :: nat \<Rightarrow> _ \<Rightarrow> _"


definition unat_rel :: "('a::len word \<times> nat) set" where "unat_rel \<equiv> unat.rel"
abbreviation "unat_assn \<equiv> pure unat_rel"  

abbreviation (input) "unat_rel' TYPE('a::len) \<equiv> unat_rel :: ('a word \<times> _) set"
abbreviation (input) "unat_assn' TYPE('a::len) \<equiv> unat_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"


definition [simp]: "unat_const TYPE('a::len) c \<equiv> (c::nat)"
context fixes c::nat begin
  sepref_register "unat_const TYPE('a::len) c" :: "nat"
end

lemma fold_unat:
  "0 = unat_const TYPE('a::len) 0"  
  "1 = unat_const TYPE('a::len) 1"  
  "numeral n \<equiv> (unat_const TYPE('a::len) (numeral n))"
  by simp_all

  
lemma hn_unat_0[sepref_fr_rules]:
  "hn_refine \<box> (return 0::_ llM) \<box> (unat_assn' TYPE('a::len)) (RETURN$PR_CONST (unat_const TYPE('a) 0))"
  unfolding APP_def
  apply sepref_to_hoare
  unfolding unat_rel_def unat.rel_def in_br_conv
  apply vcg
  done
  
lemma hn_unat_1[sepref_fr_rules]:
  "hn_refine \<box> (return 1::_ llM) \<box> (unat_assn' TYPE('a::len)) (RETURN$PR_CONST (unat_const TYPE('a) 1))"
  unfolding APP_def
  apply sepref_to_hoare
  unfolding unat_rel_def unat.rel_def in_br_conv
  apply vcg
  done
  
  
lemma hn_unat_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> unats LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)::_ llM) \<box> (unat_assn' TYPE('a::len)) (RETURN$(PR_CONST (unat_const TYPE('a) (numeral n))))"
  unfolding APP_def
  apply sepref_to_hoare unfolding unat_rel_def unat.rel_def in_br_conv 
  apply vcg'
  by (simp add: max_unat_def take_bit_eq_mod)

  
lemma hn_unat_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (PR_CONST (SPECc2 ''add'' (+)))) \<in> [\<lambda>(a, b). a + b < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a::len)"
  "(\<lambda>x. ll_add x 1, (PR_CONST (SPECc1 ''add'' Suc))) \<in> [\<lambda>a. Suc a < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a)"
  "(uncurry ll_sub, uncurry (PR_CONST (SPECc2 ''sub'' (-)))) \<in> [\<lambda>(a, b). b \<le> a]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  "(uncurry ll_mul, uncurry (PR_CONST (SPECc2 ''mul'' (*)))) \<in> [\<lambda>(a, b). a * b < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a::len)"
  "(uncurry ll_udiv, uncurry (PR_CONST (SPECc2 ''udiv'' (div)))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  "(uncurry ll_urem, uncurry (PR_CONST (SPECc2 ''urem'' (mod)))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  
  "(uncurry ll_and, uncurry (PR_CONST (SPECc2 ''and'' (AND)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  "(uncurry ll_or, uncurry (PR_CONST (SPECc2 ''or'' (OR)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  "(uncurry ll_xor, uncurry (PR_CONST (SPECc2 ''xor'' (XOR)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  
  "(uncurry ll_icmp_eq, uncurry (PR_CONST (SPECc2 ''icmp_eq'' (=)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (PR_CONST (SPECc2 ''icmp_ne'' (op_neq)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ule, uncurry (PR_CONST (SPECc2 ''icmp_ule'' (\<le>)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ult, uncurry (PR_CONST (SPECc2 ''icmp_ult'' (<)))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding op_neq_def PR_CONST_def
  
  using unat_bin_ops[THEN unat.hn_bin_op, folded unat_rel_def]
    and unat_un_ops[THEN unat.hn_un_op, folded unat_rel_def]
    and unat_bin_ops_bitwise[THEN unat.hn_bin_op, folded unat_rel_def]
    and unat_cmp_ops[THEN unat.hn_cmp_op, folded unat_rel_def bool1_rel_def]
  by (simp_all add: prod_casesK)
  
definition [simp]: "unat_init TYPE('a::len) \<equiv> 0::nat"

lemma is_init_unat[sepref_gen_algo_rules]:
  "GEN_ALGO (unat_init TYPE('a::len)) (is_init (unat_assn' TYPE('a)))"
  unfolding GEN_ALGO_def unat_init_def is_init_def
  unfolding unat_rel_def unat.rel_def
  by (simp add: in_br_conv)
  
lemma is_init_unat0[sepref_gen_algo_rules]: 
  "GEN_ALGO (unat_const TYPE('a::len2) 0) (is_init (unat_assn' TYPE('a)))"
  using is_init_unat[where 'a='a]
  by simp

lemma exists_pure_conv:
  \<open>(\<exists>x. (\<up>(x = a)) s) = \<box>s\<close>
  by (auto intro!: exI[of _ a] simp: pure_true_conv pred_lift_def)

lemma unat_distr_shr: "unat (ai >> k) = (unat ai >> k)"
  by (metis shiftr_div_2n' shiftr_eq_div)

lemma bit_lshift_unat_assn[sepref_fr_rules]:
  \<open>(uncurry ll_lshr, uncurry (PR_CONST (SPECc2 ''lshr'' (>>)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a
    (unat_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (unat_assn)\<^sup>k \<rightarrow> (unat_assn)\<close>
  unfolding PR_CONST_def SPECc2_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  apply sepref_to_hoare
  unfolding ll_lshr_def op_lift_arith2_def Let_def
  apply (vcg)
  subgoal by (auto simp: shift_ovf_def unat_rel_def unat.rel_def word_to_lint_to_uint_conv in_br_conv)
  subgoal by (simp add: sep_algebra_simps bitLSHR'_def word_to_lint_to_uint_conv
        unat_rel_def unat.rel_def in_br_conv POSTCOND_def unat_distr_shr exists_pure_conv
        flip: word_to_lint_lshr)

  done
  
lemma unat_distr_shl:
  "unat a << k < max_unat LENGTH('l) \<Longrightarrow> k < LENGTH('l)  \<Longrightarrow> unat (a << k) = unat (a::'l::len word) << k"
  apply (auto simp: shiftl_def push_bit_eq_mult)
  by (metis max_unat_def unat_mult_lem unat_power_lower)

lemma bit_shiftl_unat_assn[sepref_fr_rules]:
  \<open>(uncurry ll_shl, uncurry (PR_CONST (SPECc2 ''shl'' (<<)))) \<in> [\<lambda>(a,b). b < LENGTH('a) \<and> (a << b) < max_unat LENGTH('a)]\<^sub>a
    (unat_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (unat_assn)\<^sup>k \<rightarrow> (unat_assn)\<close>
proof -
  have [simp]: \<open>nat (bi) < LENGTH('a :: len2) \<Longrightarrow>
       nat (uint (ai :: 'a word) * 2 ^ nat (bi)) < max_unat LENGTH('a) \<Longrightarrow>
       nat (bintrunc (size ai) (uint ai << nat (bi))) = nat (uint ai * 2 ^ nat (bi))\<close> for bi ai
    by (metis (full_types) max_unat_def nat_less_numeral_power_cancel_iff shiftl_int_def uint_mult_lem
        uint_power_lower uint_word_arith_bintrs(3) word_size)
  show ?thesis
    unfolding PR_CONST_def SPECc2_def
    unfolding one_enat_def lift_acost_cost[symmetric]
    apply sepref_to_hoare
    unfolding ll_shl_def op_lift_arith2_def Let_def
    apply (vcg)
    subgoal by (auto simp: shift_ovf_def unat_rel_def unat.rel_def word_to_lint_to_uint_conv in_br_conv)
    subgoal apply (simp add: sep_algebra_simps bitSHL'_def word_to_lint_to_uint_conv
          unat_rel_def unat.rel_def in_br_conv POSTCOND_def unat_distr_shr exists_pure_conv unat_distr_shl
          flip: word_to_lint_shl)
      done
    done
qed

subsubsection \<open>Natural Numbers by Signed Word\<close>

definition snat_rel :: "('a::len2 word \<times> nat) set" where "snat_rel \<equiv> snat.rel"
abbreviation "snat_assn \<equiv> pure snat_rel"  

abbreviation (input) "snat_rel' TYPE('a::len2) \<equiv> snat_rel :: ('a word \<times> _) set"
abbreviation (input) "snat_assn' TYPE('a::len2) \<equiv> snat_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"

(* TODO: Too many snat_rel_ < max_snat lemma variants! *)
lemma snat_rel_range: "Range (snat_rel' TYPE('l)) = {0..<max_snat LENGTH('l::len2)}"
  (* TODO: Clean up proof! *)
  apply (auto simp: Range_iff snat_rel_def snat.rel_def in_br_conv)
  subgoal for x
    apply (rule exI[where x="word_of_int (int x)"])
    apply (auto simp: max_snat_def snat_invar_def)
    subgoal
      by (metis One_nat_def snat_eq_unat_aux1 snat_in_bounds_aux unat_of_nat_len)
    subgoal
      by (simp add: More_Word.of_nat_power not_msb_from_less)
    done
  done


definition [simp]: "snat_const TYPE('a::len2) c \<equiv> (c::nat)"
context fixes c::nat begin
  sepref_register "snat_const TYPE('a::len2) c" :: "nat"
end


lemma fold_snat:
  "0 = snat_const TYPE('a::len2) 0"  
  "1 = snat_const TYPE('a::len2) 1"  
  "numeral n \<equiv> (snat_const TYPE('a::len2) (numeral n))"
  by simp_all

(* TODO: Move, and use for proofs about snat in LLVM_Shallow_RS *)  
lemma snat_invar_0: "snat_invar (0)"  
  by (simp add: snat_invar_def)

lemma snat_invar_1: "snat_invar (1)"  
  by (simp add: snat_invar_def)
  
lemma snat_invar_numeral: "\<lbrakk> numeral a < max_snat LENGTH('a::len2) \<rbrakk> \<Longrightarrow>
  snat_invar (numeral a::'a word)"
  by (metis (full_types) One_nat_def ll_const_signed_nat_aux2 max_snat_def snat_invar_def)
  
  
lemma hn_snat_0[sepref_fr_rules]:
  "hn_refine \<box> (return 0::_ llM) \<box> (snat_assn' TYPE('a::len2)) (RETURN$PR_CONST (snat_const TYPE('a) 0))"
  unfolding APP_def
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def in_br_conv
  supply [simp] = snat_invar_0
  apply vcg
  done
  
lemma hn_snat_1[sepref_fr_rules]:
  "hn_refine \<box> (return 1::_ llM) \<box> (snat_assn' TYPE('a::len2)) (RETURN$PR_CONST (snat_const TYPE('a) 1))"
  unfolding APP_def
  apply sepref_to_hoare
  unfolding snat_rel_def snat.rel_def in_br_conv
  supply [simp] = snat_invar_1
  apply vcg
  done
  
  
lemma hn_snat_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> snats LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)::_ llM) \<box> (snat_assn' TYPE('a::len2)) (RETURN$(PR_CONST (snat_const TYPE('a) (numeral n))))"
  unfolding APP_def
  apply sepref_to_hoare unfolding snat_rel_def snat.rel_def in_br_conv 
  supply [simp] = snat_invar_numeral
  apply vcg'
  done
  
lemma hn_snat_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (PR_CONST (SPECc2 ''add'' (+)))) \<in> [\<lambda>(a, b). a + b < max_snat LENGTH('a)]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn' TYPE('a::len2)"
  "(\<lambda>x. ll_add x 1, (PR_CONST (SPECc1 ''add'' Suc))) \<in> [\<lambda>a. Suc a < max_snat LENGTH('a)]\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn' TYPE('a::len2)"
  "(uncurry ll_sub, uncurry (PR_CONST (SPECc2 ''sub'' (-)))) \<in> [\<lambda>(a, b). b \<le> a]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
  "(uncurry ll_mul, uncurry (PR_CONST (SPECc2 ''mul'' (*)))) \<in> [\<lambda>(a, b). a * b < max_snat LENGTH('a)]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn' TYPE('a::len2)"
  "(uncurry ll_udiv, uncurry (PR_CONST (SPECc2 ''udiv'' (div)))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
  "(uncurry ll_urem, uncurry (PR_CONST (SPECc2  ''urem'' (mod)))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> snat_assn"
  
  "(uncurry ll_icmp_eq, uncurry (PR_CONST (SPECc2 ''icmp_eq'' (=)))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (PR_CONST (SPECc2 ''icmp_ne'' (op_neq)))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_sle, uncurry (PR_CONST (SPECc2 ''icmp_sle'' (\<le>)))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_slt, uncurry (PR_CONST (SPECc2 ''icmp_slt'' (<)))) \<in> snat_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding op_neq_def
  using snat_bin_ops[THEN snat.hn_bin_op, folded snat_rel_def]
    and snat_un_ops[THEN snat.hn_un_op, folded snat_rel_def]
    and snat_cmp_ops[THEN snat.hn_cmp_op, folded snat_rel_def bool1_rel_def]
  by simp_all
  
lemma exists_eq_star_conv: "(\<lambda>s. (\<exists>x. (\<up>(x = k) \<and>* F) s)) = F"
  by (auto simp: sep_algebra_simps sep_conj_def pred_lift_extract_simps)
  

lemma bit_lshift_snat_assn[sepref_fr_rules]:
  \<open>(uncurry ll_lshr, uncurry (PR_CONST (SPECc2 ''lshr'' (>>)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a
    (snat_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow> (snat_assn)\<close>
  unfolding PR_CONST_def SPECc2_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  apply sepref_to_hoare
  unfolding ll_lshr_def op_lift_arith2_def Let_def
  apply (vcg)
  subgoal by (auto simp: shift_ovf_def snat_rel_def snat.rel_def word_to_lint_to_uint_conv in_br_conv snat_invar_alt snat_eq_unat_aux1)
  subgoal for b bi a ai F sa sb
    apply (simp add: sep_algebra_simps bitLSHR'_def word_to_lint_to_uint_conv
        snat_rel_def unat.rel_def in_br_conv POSTCOND_def unat_distr_shr exists_pure_conv
        cnv_snat_to_uint(1)
        flip: word_to_lint_lshr snat_eq_unat_aux2)    

    apply (simp add: snat.rel_def in_br_conv)
    apply (auto simp add: snat_def snat_invar_alt)
    apply (subgoal_tac "nat (sint (ai >> unat bi)) = nat (sint ai) >> nat (sint bi) \<and> unat (ai >> unat bi) < 2 ^ n")
    apply (auto simp: exists_eq_star_conv sep_algebra_simps)
    subgoal
      by (metis add_diff_cancel_left' nat_power_minus_less nat_uint_eq sint_eq_uint snat_invar_alt snat_invar_def unat_distr_shr unat_shiftr_less_t2n)
    subgoal 
      by (metis add_diff_cancel_left' nat_power_minus_less unat_shiftr_less_t2n)
    done
  done

lemma bit_shiftl_snat_assn[sepref_fr_rules]:
  \<open>(uncurry ll_shl, uncurry (PR_CONST (SPECc2 ''shl'' (<<)))) \<in> [\<lambda>(a,b). b < LENGTH('a) \<and> (a << b) < max_snat LENGTH('a)]\<^sub>a
    (snat_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow> (snat_assn)\<close>
proof -
  have H: \<open>nat (bi) < LENGTH('a :: len2) \<Longrightarrow>
       nat (uint (ai :: 'a word) * 2 ^ nat (bi)) < max_unat LENGTH('a) \<Longrightarrow>
       nat (bintrunc (size ai) (uint ai << nat (bi))) = nat (uint ai * 2 ^ nat (bi))\<close> for bi ai
    by (metis max_unat_def nat_less_numeral_power_cancel_iff shiftl_int_def uint_mult_lem
      uint_power_lower uint_word_arith_bintrs(3) word_size)
  have H': \<open>nat (bi) < LENGTH('a :: len2) \<Longrightarrow>
       nat (uint (ai :: 'a word) * 2 ^ nat (bi)) < max_snat LENGTH('a) \<Longrightarrow>
       nat (bintrunc (size ai) (uint ai << nat (bi))) = nat (uint ai * 2 ^ nat (bi))\<close> for bi ai
    using H[of bi ai] apply (auto simp: max_snat_def max_unat_def)
    using nat_less_numeral_power_cancel_iff snat_in_bounds_aux by blast

  show ?thesis
  unfolding PR_CONST_def SPECc2_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  proof (sepref_to_hoare, vcg)
    fix bi ai :: \<open>'a word\<close> and  a b F and sa :: llvm_memory and sb :: "(char list, enat) acost"
    assume
       le: \<open>b < LENGTH('a)\<close>  \<open>a << b < max_snat LENGTH('a)\<close> and
       a: \<open>(ai, a) \<in> snat_rel\<close> and
       b: \<open>(bi, b) \<in> snat_rel\<close> and
       state: \<open>llSTATE ($lift_acost (cost ''shl'' (Suc 0)) \<and>* F) (sa, sb)\<close>
    have \<open>nat (uint ai) << nat (uint bi) < 2 ^ (LENGTH('a) - Suc 0)\<close>
      using le a b
      apply (auto simp: snat_rel_def snat.rel_def in_br_conv) 
      apply (auto simp: max_snat_def snat_def snat_invar_alt)
      by (simp add: msb_unat_big sint_eq_uint)
    then have le': \<open>ai << nat (uint bi) < 2 ^ (LENGTH('a) - Suc 0)\<close>
      using le 
      by (metis (mono_tags, lifting) Suc_0_lt_2p_len_of Suc_lessD 
        diff_Suc_less len_gt_0 
        len_not_eq_0 mult_0_right nat_uint_eq nat_zero_less_power_iff push_bit_eq_mult shiftl_def 
        snat_in_bounds_aux unat_2tp_if unat_mult_lem word_less_nat_alt)

    have [simp]: \<open>nat (bintrunc (size ai) (uint ai << nat (uint bi))) = nat (uint ai * 2 ^ nat (uint bi))\<close>
      using le a b 
      apply (auto simp: snat_rel_def snat.rel_def in_br_conv) 
      apply (auto simp: max_snat_def snat_def snat_invar_alt)
      by (smt (z3) H' One_nat_def diff_Suc_Suc diff_zero max_snat_def nat_mult_distrib nat_uint_eq 
          push_bit_eq_mult shiftl_def sint_eq_uint snat_invar_alt snat_invar_def uint_lt_0 
          uint_power_lower unat_2tp_if)
    
   have \<open>- (3 * 2 ^ (LENGTH('a) - Suc 0)) \<le> uint ai * 2 ^ nat (uint bi)\<close>
     by (smt int_nat_eq nat_mult_distrib of_nat_mult uint_add_ge0 zero_le_power)
   moreover have \<open>uint ai * 2 ^ nat (uint bi) < 3 * 2 ^ (LENGTH('a) - Suc 0)\<close>
     apply (subst nat_less_eq_zless[symmetric], simp, subst nat_mult_distrib)
     using le a b
     apply (auto simp: snat_rel_def snat.rel_def in_br_conv) 
     apply (auto simp: max_snat_def snat_def snat_invar_alt)
     by (smt (z3) shiftl_def Groups.mult_ac(2) One_nat_def Word.of_nat_unat \<open>nat (take_bit (size ai) (uint ai << nat (uint bi))) = nat (uint ai * 2 ^ nat (uint bi))\<close> diff_Suc_1 le' le_less_trans lessI nat_less_numeral_power_cancel_iff nat_mult_distrib nat_power_eq nat_uint_eq nat_zero_less_power_iff not_le of_nat_numeral semiring_1_class.of_nat_power uint_power_lower uint_shiftl unat_arith_simps(2) unat_power_lower zero_less_nat_eq)
   moreover have \<open>\<not>2 ^ (LENGTH('a) - Suc 0) \<le> uint ai * 2 ^ nat (uint bi)\<close>
     using le
     apply (subst nat_le_eq_zle[symmetric], simp, subst nat_mult_distrib)
     using H'[of \<open>uint bi\<close> ai]  le a b
     by (auto simp del: H' simp: sint_uint word_size uint_shiftl sbintrunc_If
      shiftl_int_def max_snat_def max_unat_def snat_rel_def snat.rel_def br_def
      cnv_snat_to_uint(1) nat_power_eq nat_shiftr_div)
   moreover have \<open>\<not>uint ai * 2 ^ nat (uint bi) < - (2 ^ (LENGTH('a) - Suc 0))\<close>
     apply (subst nat_less_eq_zless[symmetric], simp, subst nat_mult_distrib)
     using le a b
     by (auto simp: snat_rel_def snat.rel_def in_br_conv) 
   ultimately have \<open>nat (sint (ai << nat (uint bi))) = nat (uint ai * 2 ^ nat (uint bi))\<close>
     using H'[of \<open>uint bi\<close> ai]  le a b
     apply (auto simp: sint_uint word_size uint_shiftl sbintrunc_If shiftl_def
      shiftl_int_def max_snat_def max_unat_def snat_rel_def snat.rel_def)
     by (simp add: push_bit_eq_mult signed_take_bit_int_eq_self)
   have [simp]: \<open>\<not> msb (ai << nat (uint bi))\<close>
     apply (subst msb_shiftl_word[OF _])
     using le le' a b state
     unfolding snat_rel_def snat.rel_def br_def
     by (auto simp: br_def snat_def ll_shl_def wp_return
        op_lift_arith2_def Let_def fcheck_def shift_ovf_def word_to_lint_to_uint_conv bitSHL'_def
        nat_div_distrib nat_power_eq pred_lift_merge_simps sint_eq_uint max_snat_def
          cnv_snat_to_uint(1) in_br_conv snat.rel_def snat_invar_def
          POSTCOND_def STATE_extract(2) shiftr_div_2n 
       uint_shiftl exists_pure_conv)
       
   show 
     "wp (ll_shl ai bi) (\<lambda>r. llPOST ((
      \<up>((ai, a) \<in> snat_rel) \<and>* \<up>((bi, b) \<in> snat_rel) 
      \<and>* \<up>((r, a << b) \<in> snat_rel) \<and>* GC) \<and>* F)) 
      (sa, sb)"
     using le a b state
     unfolding snat_rel_def snat.rel_def br_def
     apply (auto simp: br_def snat_def ll_shl_def wp_return
         op_lift_arith2_def Let_def fcheck_def shift_ovf_def word_to_lint_to_uint_conv bitSHL'_def
         nat_div_distrib nat_power_eq pred_lift_merge_simps sint_eq_uint max_snat_def
         cnv_snat_to_uint(1) in_br_conv snat.rel_def snat_invar_def
         simp flip: word_to_lint_shl nat_uint_eq)
     apply vcg'  
     using \<open>\<not> msb (ai << nat (uint bi))\<close> \<open>nat (sint (ai << nat (uint bi))) = nat (uint ai * 2 ^ nat (uint bi))\<close> nat_mult_distrib nat_power_eq nat_shiftr_div by auto
 qed
qed

definition [simp]: "snat_init TYPE('a::len) \<equiv> 0::nat"

lemma is_init_snat[sepref_gen_algo_rules]:
  "GEN_ALGO (snat_init TYPE('a::len2)) (is_init (snat_assn' TYPE('a)))"
  unfolding GEN_ALGO_def snat_init_def is_init_def
  unfolding snat_rel_def snat.rel_def
  by (simp add: snat_invar_0 in_br_conv)
  
lemma is_init_snat0[sepref_gen_algo_rules]: 
  "GEN_ALGO (snat_const TYPE('a::len2) 0) (is_init (snat_assn' TYPE('a)))"
  using is_init_snat[where 'a='a]
  by simp

subsubsection \<open>Ad-Hoc Method to Annotate Number Constructors\<close>  
lemma annot_num_const_cong: 
  "\<And>a b. snat_const a b = snat_const a b" 
  "\<And>a b. sint_const a b = sint_const a b" 
  "\<And>a b. unat_const a b = unat_const a b" 
  "ASSERT \<Phi> = ASSERT \<Phi>"
 (* "WHILEIT I = WHILEIT I"  TODO *)
  by simp_all
  
lemma unat_const_fold: 
  "0 = unat_const TYPE('a::len) 0"
  "1 = unat_const TYPE('a::len) 1"
  "numeral n = unat_const TYPE('a::len) (numeral n)"
  by simp_all
  
lemma snat_const_fold: 
  "0 = snat_const TYPE('a::len2) 0"
  "1 = snat_const TYPE('a::len2) 1"
  "numeral n = snat_const TYPE('a::len2) (numeral n)"
  by simp_all

lemma sint_const_fold: 
  "0 = sint_const TYPE('a::len) 0"
  "1 = sint_const TYPE('a::len) 1"
  "numeral n = sint_const TYPE('a::len) (numeral n)"
  "-sint_const TYPE('a::len) c = sint_const TYPE('a::len) (-c)"
  by simp_all
  
    
lemma hfref_absfun_convI: "CNV g g' \<Longrightarrow> (f,g') \<in> hfref P A R \<Longrightarrow> (f,g) \<in> hfref P A R" by simp

method annot_sint_const for T::"'a::len itself" = 
  (rule hfref_absfun_convI),
  (simp only: sint_const_fold[where 'a='a] cong: annot_num_const_cong),
  (rule CNV_I)
  
method annot_snat_const for T::"'a::len2 itself" = 
  (rule hfref_absfun_convI),
  (simp only: snat_const_fold[where 'a='a] cong: annot_num_const_cong),
  (rule CNV_I)
  
method annot_unat_const for T::"'a::len itself" = 
  (rule hfref_absfun_convI),
  (simp only: unat_const_fold[where 'a='a] cong: annot_num_const_cong),
  (rule CNV_I)
  
\<^cancel>\<open>  
subsubsection \<open>Casting\<close>  
(* TODO: Add other casts *)
  
context fixes T :: "'a::len2 itself" begin
  definition [simp]: "unat_snat_upcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"

  sepref_decl_op unat_snat_upcast: "unat_snat_upcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
end  

context fixes T :: "'a::len itself" begin
  definition [simp]: "snat_unat_downcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"

  sepref_decl_op snat_unat_downcast: "snat_unat_downcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
end  

context fixes T :: "'a::len2 itself" begin
  definition [simp]: "snat_snat_upcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"

  sepref_decl_op snat_snat_upcast: "snat_snat_upcast_aux" :: "nat_rel \<rightarrow> nat_rel" .

  definition [simp]: "snat_snat_downcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"

  sepref_decl_op snat_snat_downcast: "snat_snat_downcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
  
end

context fixes T :: "'a::len itself" begin
  definition [simp]: "unat_unat_upcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"
  definition [simp]: "unat_unat_downcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"

  sepref_decl_op unat_unat_upcast: "unat_unat_upcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
  sepref_decl_op unat_unat_downcast: "unat_unat_downcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
end

sepref_decl_op unat_snat_conv: "id::nat\<Rightarrow>_" :: "nat_rel \<rightarrow> nat_rel" .
sepref_decl_op snat_unat_conv: "id::nat\<Rightarrow>_" :: "nat_rel \<rightarrow> nat_rel" .


lemma annot_unat_snat_upcast: "x = op_unat_snat_upcast TYPE('l::len2) x" by simp 
lemma annot_snat_unat_downcast: "x = op_snat_unat_downcast TYPE('l::len) x" by simp 
lemma annot_snat_snat_upcast: "x = op_snat_snat_upcast TYPE('l::len2) x" by simp 
lemma annot_snat_snat_downcast: "x = op_snat_snat_downcast TYPE('l::len2) x" by simp 
lemma annot_unat_snat_conv: "x = op_unat_snat_conv x" by simp 
lemma annot_unat_unat_upcast: "x = op_unat_unat_upcast TYPE('l::len) x" by simp 
lemma annot_unat_unat_downcast: "x = op_unat_unat_downcast TYPE('l::len) x" by simp 
lemma annot_snat_unat_conv: "x = op_snat_unat_conv x" by simp  

lemma in_unat_rel_conv_assn: "\<up>((xi, x) \<in> unat_rel) = \<upharpoonleft>unat.assn x xi"
  by (auto simp: unat_rel_def unat.assn_is_rel pure_app_eq)

lemma in_snat_rel_conv_assn: "\<up>((xi, x) \<in> snat_rel) = \<upharpoonleft>snat.assn x xi"
  by (auto simp: snat_rel_def snat.assn_is_rel pure_app_eq)

context fixes BIG :: "'big::len2" and SMALL :: "'small::len" begin  
  lemma unat_snat_upcast_refine: 
    "(unat_snat_upcast TYPE('big::len2), PR_CONST (mop_unat_snat_upcast TYPE('big::len2))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (unat_assn' TYPE('small::len))\<^sup>k \<rightarrow> snat_assn"
    supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) unat_snat_upcast_refine fixes 'big 'small by simp
  
  
  lemma snat_unat_downcast_refine: 
    "(snat_unat_downcast TYPE('small), PR_CONST (mop_snat_unat_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> x<max_unat LENGTH('small)]\<^sub>a (snat_assn' TYPE('big))\<^sup>k \<rightarrow> unat_assn"
    supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) snat_unat_downcast_refine fixes 'big 'small by simp
end

context fixes BIG :: "'big::len2" and SMALL :: "'small::len2" begin  
  lemma snat_snat_upcast_refine: 
    "(snat_snat_upcast TYPE('big::len2), PR_CONST (mop_snat_snat_upcast TYPE('big::len2))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (snat_assn' TYPE('small::len2))\<^sup>k \<rightarrow> snat_assn"
    supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) snat_snat_upcast_refine fixes 'big 'small by simp
  
  lemma snat_snat_downcast_refine: 
    "(snat_snat_downcast TYPE('small), PR_CONST (mop_snat_snat_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> x<max_snat LENGTH('small)]\<^sub>a (snat_assn' TYPE('big))\<^sup>k \<rightarrow> snat_assn"
    supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) snat_snat_downcast_refine fixes 'big 'small by simp
  
end

context fixes BIG :: "'big::len" and SMALL :: "'small::len" begin  
  lemma unat_unat_upcast_refine: 
    "(unat_unat_upcast TYPE('big), PR_CONST (mop_unat_unat_upcast TYPE('big))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (unat_assn' TYPE('small::len))\<^sup>k \<rightarrow> unat_assn"
    supply [simp] = in_unat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) unat_unat_upcast_refine fixes 'big 'small by simp
  
  lemma unat_unat_downcast_refine: 
    "(unat_unat_downcast TYPE('small), PR_CONST (mop_unat_unat_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> x<max_unat LENGTH('small)]\<^sub>a (unat_assn' TYPE('big::len))\<^sup>k \<rightarrow> unat_assn"
    supply [simp] = in_unat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) unat_unat_downcast_refine fixes 'big 'small by simp
end

  
context fixes T::"'l::len2" begin
  lemma unat_snat_conv_refine: "(\<lambda>x. x, op_unat_snat_conv) 
    \<in> [\<lambda>x. x<max_snat LENGTH('l::len2)]\<^sub>f unat_rel' TYPE('l) \<rightarrow> snat_rel' TYPE('l)"
    by (force 
      intro!: frefI 
      simp: snat_rel_def unat_rel_def snat.rel_def unat.rel_def
      simp: in_br_conv max_snat_def snat_invar_alt
      simp: snat_eq_unat(1)
      )
      
  sepref_decl_impl unat_snat_conv_refine[sepref_param] fixes 'l by auto
  
  lemma snat_unat_conv_refine: "(\<lambda>x. x, op_snat_unat_conv)
    \<in> snat_rel' TYPE('l) \<rightarrow> unat_rel' TYPE('l)"
    by (force
      intro!: frefI
      simp: snat_rel_def unat_rel_def snat.rel_def unat.rel_def
      simp: in_br_conv max_snat_def snat_invar_alt
      simp: snat_eq_unat(1)
      )

  sepref_decl_impl snat_unat_conv_refine[sepref_param] fixes 'l .
end


text \<open>Converting to Word\<close>
sepref_register "of_nat :: _ \<Rightarrow> _ word "
lemma of_nat_word_refine[sepref_import_param]: 
  "(id,of_nat) \<in> unat_rel' TYPE('a::len) \<rightarrow> word_rel"
  by (auto simp: unat_rel_def unat.rel_def in_br_conv)

\<close>


subsubsection \<open>Bit-Shifting\<close>

sepref_register 
  shl_word: "(<<):: _ word \<Rightarrow> _"  
  lshr_word: "(>>):: _ word \<Rightarrow> _"  
  ashr_word: "(>>>):: _ word \<Rightarrow> _"  

context begin

interpretation llvm_prim_arith_setup .
  

lemma shl_hnr_unat[sepref_fr_rules]: "(uncurry ll_shl,uncurry (PR_CONST (SPECc2 ''shl'' (<<)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a (word_assn :: 'a::len word \<Rightarrow> _)\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> word_assn"
  unfolding unat_rel_def unat.assn_is_rel[symmetric] unat.assn_def
  unfolding SPECc2_def PR_CONST_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  apply sepref_to_hoare
  by vcg'

lemma lshr_hnr_unat[sepref_fr_rules]: "(uncurry ll_lshr,uncurry (PR_CONST (SPECc2 ''lshr'' (>>)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a (word_assn :: 'a::len word \<Rightarrow> _)\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> word_assn"
  unfolding unat_rel_def unat.assn_is_rel[symmetric] unat.assn_def
  unfolding SPECc2_def PR_CONST_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  apply sepref_to_hoare
  by vcg'

lemma ashr_hnr_unat[sepref_fr_rules]: "(uncurry ll_ashr,uncurry (PR_CONST (SPECc2 ''ashr'' (>>>)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a (word_assn :: 'a::len word \<Rightarrow> _)\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> word_assn"
  unfolding unat_rel_def unat.assn_is_rel[symmetric] unat.assn_def
  unfolding SPECc2_def PR_CONST_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  apply sepref_to_hoare
  by vcg'

lemma shl_hnr_snat[sepref_fr_rules]: "(uncurry ll_shl,uncurry (PR_CONST (SPECc2 ''shl'' (<<)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a (word_assn :: 'a::len2 word \<Rightarrow> _)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> word_assn"
  unfolding snat_rel_def snat.assn_is_rel[symmetric] snat.assn_def
  unfolding SPECc2_def PR_CONST_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  supply [simp] = snat_eq_unat
  apply sepref_to_hoare
  by vcg'
  
lemma lshr_hnr_snat[sepref_fr_rules]: "(uncurry ll_lshr,uncurry (PR_CONST (SPECc2 ''lshr'' (>>)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a (word_assn :: 'a::len2 word \<Rightarrow> _)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> word_assn"
  unfolding snat_rel_def snat.assn_is_rel[symmetric] snat.assn_def
  unfolding SPECc2_def PR_CONST_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  supply [simp] = snat_eq_unat
  apply sepref_to_hoare
  by vcg'

lemma ashr_hnr_snat[sepref_fr_rules]: "(uncurry ll_ashr,uncurry (PR_CONST (SPECc2 ''ashr'' (>>>)))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a (word_assn :: 'a::len2 word \<Rightarrow> _)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> word_assn"
  unfolding snat_rel_def snat.assn_is_rel[symmetric] snat.assn_def
  unfolding SPECc2_def PR_CONST_def
  unfolding one_enat_def lift_acost_cost[symmetric]
  supply [simp] = snat_eq_unat
  apply sepref_to_hoare
  by vcg'
  
      
end

subsubsection \<open>Bounds Solver Setup\<close>


lemma in_unat_rel_boundsD[sepref_bounds_dest]: "(w, n) \<in> unat_rel' TYPE('l) \<Longrightarrow> n < max_unat LENGTH('l::len)"
  by (simp add: unat_rel_def unat.rel_def in_br_conv)

(*lemma snat_rel_imp_less_max_snat: 
  "\<lbrakk>(x,n)\<in>snat_rel' TYPE('l::len2); L = LENGTH('l)\<rbrakk> \<Longrightarrow> n<max_snat L"
  by (auto simp: snat_rel_def snat.rel_def in_br_conv)
*)
  
lemma in_snat_rel_boundsD[sepref_bounds_dest]: 
  "(w, n) \<in> snat_rel' TYPE('l) \<Longrightarrow> n < max_snat LENGTH('l::len2)"
  by (auto simp: snat_rel_def snat.rel_def in_br_conv)
  
lemma in_sint_rel_boundsD[sepref_bounds_dest]: 
  "(w,i)\<in>sint_rel' TYPE('l::len) \<Longrightarrow> min_sint LENGTH('l) \<le> i \<and> i < max_sint LENGTH('l)"
  by (auto simp: sint_rel_def sint.rel_def in_br_conv)
  
lemmas [sepref_bounds_simps] = max_snat_def max_unat_def max_sint_def min_sint_def
  
subsection \<open>Default Inlinings\<close>
lemmas [llvm_inline] = id_def

subsection \<open>HOL Combinators\<close>

subsubsection \<open>If\<close>

thm htripleD
  lemma htripleD2:  
    assumes q': "\<And>r. Q' r = (Q r ** F)"
    assumes "(P**F) (\<alpha> s)"
    assumes "htriple \<alpha> P c Q"
    shows "wp c (\<lambda>r s'. (Q' r) (\<alpha> s')) s"
    unfolding q' apply(rule htripleD) 
    using assms by auto

lemma consume_two_steps: "NREST.consume m t' = doN { SPECT [()\<mapsto>t']; m}"
  by (auto simp: bindT_def consume_def split: nrest.splits)

lemma hnr_consume_aux: "t' = lift_acost t \<Longrightarrow> hn_refine \<Gamma> (ll_consume t) \<Gamma> (unit_assn) (SPECT [() \<mapsto> t'])"
  apply(rule hn_refineI_SPECT) unfolding pure_def by vcg

lemma hnr_consume: "hn_refine \<Gamma> c \<Gamma>' R m \<Longrightarrow> t' = lift_acost t \<Longrightarrow> hn_refine \<Gamma> (doM { ll_consume t; c }) \<Gamma>' R (NREST.consume m t')"
  unfolding consume_two_steps
  apply(rule hnr_bind_manual_free)
   apply(rule hnr_consume_aux) apply simp
  by(simp add: hn_refine_extract_pre_val)  

lemma hn_refine_extract_pre_val': 
  "((xc,xa)\<in>S \<longrightarrow> hn_refine (hn_val S xa xc ** \<Gamma>) c \<Gamma>' R m) \<Longrightarrow> hn_refine (hn_val S xa xc ** \<Gamma>) c \<Gamma>' R m"
  unfolding hn_refine_def hn_ctxt_def pure_def
  by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps htriple_extract_pre_pure)

lemma hnr_postprocess:
  assumes hnr: "hn_refine \<Gamma>1 b' \<Gamma>2b R b"
  assumes ht: "llvm_htriple \<Gamma>2b fb (\<lambda>r. \<Gamma>')"
  shows "hn_refine \<Gamma>1 (doM { r \<leftarrow> b'; fb; return r }) \<Gamma>' R b"
proof (rule)
  fix F s cr M
  assume "b = SPECT M" "(\<Gamma>1 \<and>* F) (ll_\<alpha> (s, cr))"
  from hnr[THEN hn_refineD, OF this] obtain ra Ca
    where "Some Ca \<le> M ra" and wpb: "wp b' (\<lambda>r s. (\<Gamma>2b \<and>* R ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)" 
    by blast

  show "\<exists>ra Ca. Some Ca \<le> M ra \<and> wp (doM { r \<leftarrow> b'; fb; return r })
                                      (\<lambda>r s. (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)"
    apply(rule exI[where x=ra])
    apply(rule exI[where x=Ca])
    apply safe apply fact
    apply(simp add: wp_bind)
    apply(rule wp_monoI[OF wpb])
    apply(simp add: wp_bind)
    apply(rule wp_monoI[OF ht[THEN htripleD]])
     apply(simp)
    apply (simp add: wp_return) 
    by (simp add: GC_move_left(4) sep_conj_commute sep_conj_left_commute)  
qed

lemma hn_if_aux:
  assumes P: "\<Gamma> \<turnstile> hn_val bool1_rel a a' ** \<Gamma>1"
  assumes RT: "a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) c' \<Gamma>2c R c"
  assumes MERGE: "MERGE \<Gamma>2b fb \<Gamma>2c fc \<Gamma>'"
  shows "hn_refine \<Gamma> 
    (llc_if a' (doM {r\<leftarrow>b'; fb; return r}) (doM {r\<leftarrow>c'; fc; return r})) 
    \<Gamma>' R (consume (if a then b else c) (cost ''if'' 1))"
  apply (rule hn_refine_nofailI)  
  apply (rule hn_refine_cons_pre[OF _ P])
  apply(rule hn_refine_extract_pre_val') 
proof (rule, cases a, goal_cases)
  assume "nofailT (NREST.consume (if a then b else c) (cost ''if'' 1))"
  then have NF: "nofailT (if a then b else c)"
    by (simp add: refine_pw_simps)
  
  have [vcg_normalize_simps, named_ss fri_prepare_simps]: "hn_val bool1_rel = \<upharpoonleft>bool.assn"
    unfolding bool1_rel_def bool.assn_is_rel hn_ctxt_def ..
  
  note me[vcg_rules] = MERGED[OF MERGE]  

  {
    case 1
    from 1 NF have [simp]: "nofailT b" by simp
    then obtain Mb where Mb: "b = SPECT Mb" apply(cases b) by auto

    from 1(2,3) have a': "to_bool a'"  
      by (simp add: bool.rel_def bool1_rel_def in_br_conv)  

    show ?case
      unfolding llc_if_def
      apply(subst (2) 1(3)) apply(subst a')
      apply simp
      apply(rule hnr_consume)
      apply(rule hnr_postprocess)
      apply(rule RT[OF 1(3)])
       apply(rule me(1))
      apply(subst lift_acost_cost)
      by(simp add:  one_enat_def)  
  }
  {
    case 2
    from 2 NF have [simp]: "nofailT c" by simp
    then obtain Mc where Mc: "c = SPECT Mc" apply(cases c) by auto

    from 2(2,3) have a': "\<not> to_bool a'"  
      by (simp add: bool.rel_def bool1_rel_def in_br_conv)  

    show ?case
      unfolding llc_if_def
      apply(subst (2) 2(3)) apply(subst a')
      apply simp
      apply(rule hnr_consume)
      apply(rule hnr_postprocess)
      apply(rule RE[OF 2(3)])
       apply(rule me(2))
      apply(subst lift_acost_cost)
      by(simp add:  one_enat_def)  
  }
qed    



lemma hn_refine_call[sepref_comb_rules]:
  assumes "hn_refine \<Gamma> mi \<Gamma>' R m"
  shows  "hn_refine \<Gamma> (ll_call mi) \<Gamma>' R (mop_call $ m)"
  unfolding mop_call_def ll_call_def APP_def
  apply(rule hnr_consume) apply(fact assms)
  by (simp add: lift_acost_cost one_enat_def) 



lemma hn_if[sepref_comb_rules]:
  assumes P: "\<Gamma> \<turnstile> hn_val bool1_rel a a' ** \<Gamma>1"
  assumes RT: "a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (hn_val bool1_rel a a' ** \<Gamma>1) c' \<Gamma>2c R c"
  assumes MERGE: "TERM If \<Longrightarrow> MERGE \<Gamma>2b fb \<Gamma>2c fc \<Gamma>'"
  shows "hn_refine \<Gamma> 
    (llc_if a' (doM {r\<leftarrow>b'; fb; return r}) (doM {r\<leftarrow>c'; fc; return r})) 
    \<Gamma>' R (MIf$a$b$c)"
  using P RT RE MERGE[OF TERMI]
  unfolding APP_def PROTECT2_def MIf_def
  by (rule hn_if_aux)


term whileT
subsubsection \<open>While\<close>  
(* TODO: Move WHILE-stuff to HOL-Bindings Theory *)
lemma WHILEIT_pat[def_pat_rules]:
  "whileIET$I \<equiv> UNPROTECT (whileIET I)"
(*  "whileT \<equiv> PR_CONST (whileIET (\<lambda>_. True) undefined)" *)
  by (simp_all add: whileIET_def)
\<^cancel>\<open>
lemma id_WHILEIT[id_rules]: 
  "PR_CONST (WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp

lemma WHILE_arities[sepref_monadify_arity]:
  (*"WHILET \<equiv> WHILEIT$(\<lambda>\<^sub>2_. True)"*)
  "PR_CONST (WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp_all add: WHILET_def)

lemma WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (WHILEIT I)$(\<lambda>\<^sub>2x. b x)$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2x. (EVAL$(b x)))$f$s
    )"
  by (simp_all add: WHILEIT_to_monadic)
  \<close>


lemma monadic_WHILEIT_pat[def_pat_rules]:
  "monadic_WHILEIT$I \<equiv> UNPROTECT (monadic_WHILEIT I)"
  by auto  
    
lemma id_monadic_WHILEIT[id_rules]: 
  "PR_CONST (monadic_WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> (bool,_) nrest) \<Rightarrow> ('a \<Rightarrow> ('a,_) nrest) \<Rightarrow> 'a \<Rightarrow> ('a,_) nrest)"
  by simp
    
lemma monadic_WHILEIT_arities[sepref_monadify_arity]:
  "PR_CONST (monadic_WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp)

lemma monadic_WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (monadic_WHILEIT I)$b$f$s \<equiv> 
    NREST.bindT$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$b$f$s
    )"
  by (simp)


(* TODO: Move *)
lemma addcost_NTERM_iff: "addcost c m = NTERM \<longleftrightarrow> m = NTERM"
  apply(cases m) by auto


(* TODO: clean up this mess and MOVE! *)
lemma mono_body_consume:
  assumes "M.mono_body (\<lambda>f. cB f x)"
  shows "M.mono_body (\<lambda>f. cB (\<lambda>x. ll_call (f x)) x)"
  apply(rule)
  subgoal for a b
    using assms
    apply -
    apply(erule monotoneD[of _ _ _ "(\<lambda>x. ll_call (a x))" "(\<lambda>x. ll_call (b x))"])
    unfolding fun_ord_def
    unfolding img_ord_def  flat_ord_def
    unfolding ll_call_def
    apply (force simp: run_simps addcost_NTERM_iff) 
    done
  done

lemma hnr_RECT_aux:
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px ** F) (cf px) (F' ax px) Ry (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px ** F) (cB cf px) (F' ax px) Ry (aB af ax)"
  assumes M: "(\<And>x. M.mono_body (\<lambda>f. cB f x))"
  shows "hn_refine 
    (hn_ctxt Rx ax px ** F) (ll_call (REC' cB px)) (F' ax px) Ry (RECT' aB ax)"
  unfolding REC'_def RECT'_def
  apply(subst ll_call_def)
  apply(rule hnr_consume)
  apply(rule hnr_RECT)
   apply(rule S)
  apply(subst ll_call_def)
  apply(rule hnr_consume) 
   apply assumption
  subgoal unfolding one_enat_def lift_acost_cost by simp
  subgoal apply(rule mono_body_consume) by(fact M)
  subgoal unfolding one_enat_def lift_acost_cost by simp
  done

lemma hn_RECT_wiewirshabenwollen[sepref_comb_rules]:
  assumes "INDEP Ry" "INDEP Rx" "INDEP Rx'"
  assumes FR: "P \<turnstile> hn_ctxt Rx ax px ** F"
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px ** F) (cf px) (hn_ctxt Rx' ax px ** F) Ry 
      (RCALL$af$ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px ** F) (cB cf px) (F' ax px) Ry 
          (aB af ax)"
  assumes FR': "\<And>ax px. F' ax px \<turnstile> hn_ctxt Rx' ax px ** F"
  assumes M: "(\<And>x. M.mono_body (\<lambda>f. cB f x))"
  (*assumes PREC[unfolded CONSTRAINT_def]: "CONSTRAINT precise Ry"*)
  shows "hn_refine 
    (P) (ll_call (REC' cB px)) (hn_ctxt Rx' ax px ** F) Ry 
        (RECT'$(\<lambda>\<^sub>2D x. aB D x)$ax)"
  unfolding APP_def PROTECT2_def
  apply (rule hn_refine_cons_pre[OF _ FR])
  apply (rule hnr_RECT_aux)

  apply (rule hn_refine_cons_post[OF _ FR'])
  apply (rule S[unfolded RCALL_def APP_def])
  apply assumption
  apply fact+
  done


lemma hn_refine_add_invalid: (* Very customized rule for manual derivation of while *)
  "hn_refine (hn_ctxt Rs a b ** \<Gamma>) c \<Gamma>' R m \<Longrightarrow> hn_refine (hn_ctxt Rs a b ** \<Gamma>) c (hn_invalid Rs a b ** \<Gamma>') R m"
  by (smt hn_refine_frame' invalidate_clone' sep_conj_commute sep_conj_left_commute)

lemma hn_monadic_WHILE_aux:
  assumes FR: "P \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (hn_ctxt Rs s' s ** \<Gamma>)
    (b s)
    (\<Gamma>b s' s)
    (pure bool1_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. \<Gamma>b s' s \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"

  assumes f_ref: "\<And>s' s. \<lbrakk>I s'\<rbrakk> \<Longrightarrow> hn_refine
    (hn_ctxt Rs s' s ** \<Gamma>)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. \<Gamma>f s' s \<turnstile> hn_ctxt Rsf s' s ** \<Gamma>"
  assumes free: "MK_FREE Rsf fr"
  (*assumes PREC: "precise Rs"*)
  shows "hn_refine (P) (llc_while b (\<lambda>s. doM {r \<leftarrow> f s; fr s; return r}) s) (hn_invalid Rs s' s ** \<Gamma>) Rs (monadic_WHILEIT I b' f' s')"
  apply1 (rule hn_refine_cons_pre[rotated, OF FR])
  apply (rule hn_refine_add_invalid)
  
  apply (rule hn_refine_synthI)
  unfolding monadic_WHILEIT_RECT'_conv
  focus (rule hnr_RECT_aux[where F'="\<lambda>s' s. \<Gamma>" and Ry=Rs])
    apply1 (rule hnr_ASSERT)
    focus (rule hnr_bind_manual_free)
      applyS (rule b_ref; simp)
  apply1 (rule hn_refine_cons_pre[rotated], sep_drule b_fr, rule entails_refl)
  unfolding MIf_def
      focus (rule hn_if_aux[OF _ _ _ MERGE_triv])
        apply (fri_rotate entails_pre_cong :-1) apply (rule conj_entails_mono[OF entails_refl]) apply (rule entails_refl)
        focus (* Then-Part *)
          apply1 (rule hn_refine_cons_pre[rotated], sep_drule drop_hn_val, simp, rule entails_refl)
          apply (rule hnr_bind_manual_free)
          applyS (rule f_ref, simp)
          apply1 (rule hn_refine_cons_pre[rotated], sep_drule f_fr, simp, rule entails_refl)
          apply (rule hnr_freeI[OF free])
          apply (rule hn_refine_cons_pre, assumption)
          applyS (simp add: sep_conj_ac; rule entails_refl)
          solved
        focus (* Else-Part *)  
          apply (rule hn_refine_cons_post)
          apply (rule hn_refine_frame[OF hnr_RETURN_pass])
          apply (fri_rotate entails_pre_cong :1) apply (rule entails_refl)
          apply1 (sep_drule drop_hn_invalid)
          apply1 (sep_drule drop_hn_val)
          apply (simp)
          solved
        solved
      solved
    focus apply pf_mono_prover solved
    solved
  subgoal by (simp add: llc_while_def mwhile_def llc_if_def cong: if_cong)
  subgoal ..
  subgoal ..
  done

lemma hn_monadic_WHILE_lin[sepref_comb_rules]:
  assumes "INDEP Rs"
  assumes FR: "P \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"
  assumes b_ref: "\<And>s s'. I s' \<Longrightarrow> hn_refine 
    (hn_ctxt Rs s' s ** \<Gamma>)
    (b s)
    (\<Gamma>b s' s)
    (pure bool1_rel)
    (b' s')"
  assumes b_fr: "\<And>s' s. TERM (monadic_WHILEIT,''cond'')
       \<Longrightarrow> \<Gamma>b s' s \<turnstile> hn_ctxt Rs s' s ** \<Gamma>"

  assumes f_ref: "\<And>s' s. I s' \<Longrightarrow> hn_refine
    (hn_ctxt Rs s' s ** \<Gamma>)
    (f s)
    (\<Gamma>f s' s)
    Rs
    (f' s')"
  assumes f_fr: "\<And>s' s. TERM (monadic_WHILEIT,''body'')
                   \<Longrightarrow> \<Gamma>f s' s \<turnstile> hn_ctxt Rsf s' s ** \<Gamma>"
  assumes free: "TERM (monadic_WHILEIT,''free-old-state'')
                   \<Longrightarrow> MK_FREE Rsf fr"
  shows "hn_refine 
    P 
    (llc_while b (\<lambda>s. doM {r \<leftarrow> f s; fr s; return r}) s) 
    (hn_invalid Rs s' s ** \<Gamma>)
    Rs 
    (PR_CONST (monadic_WHILEIT I)$(\<lambda>\<^sub>2s'. b' s')$(\<lambda>\<^sub>2s'. f' s')$(s'))"
  using assms(2-)
  unfolding APP_def PROTECT2_def CONSTRAINT_def PR_CONST_def
  by (rule hn_monadic_WHILE_aux)


  
subsubsection \<open>Let\<close>
lemma hn_let[sepref_comb_rules]:
  "hn_refine \<Gamma> c \<Gamma>' R (NREST.bindT$(PASS$v)$(\<lambda>\<^sub>2x. f x)) \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R (Let$v$(\<lambda>\<^sub>2x. f x))" 
  by simp


subsection \<open>Unit\<close>

lemma unit_hnr[sepref_import_param]: "((),())\<in>unit_rel" by auto
  
  
subsection "Product"


lemmas [sepref_import_rewrite, named_ss sepref_frame_normrel, fcomp_norm_unfold] = prod_assn_pure_conv[symmetric]


(* TODO Add corresponding rules for other types and add to datatype snippet *)
lemma intf_of_prod_assn[intf_of_assn]:
  assumes "intf_of_assn A TYPE('a)" "intf_of_assn B TYPE('b)"
  shows "intf_of_assn (prod_assn A B) TYPE('a * 'b)"
  by simp

lemma pure_prod[constraint_rules]: 
  assumes P1: "is_pure P1" and P2: "is_pure P2"
  shows "is_pure (prod_assn P1 P2)"
proof -
  from P1 obtain P1' where P1': "\<And>x x'. P1 x x' = \<up>(P1' x x')"
    using is_pureE by blast
  from P2 obtain P2' where P2': "\<And>x x'. P2 x x' = \<up>(P2' x x')"
    using is_pureE by blast

  show ?thesis proof
    fix x x'
    show "prod_assn P1 P2 x x' =
         \<up> (case (x, x') of ((a1, a2), c1, c2) \<Rightarrow> P1' a1 c1 \<and> P2' a2 c2)"
      unfolding prod_assn_def
      apply (simp add: P1' P2' sep_algebra_simps split: prod.split)
      done
  qed
qed

lemma prod_frame_match[sepref_frame_match_rules]:
  assumes "hn_ctxt A (fst x) (fst y) \<turnstile> hn_ctxt A' (fst x) (fst y)"
  assumes "hn_ctxt B (snd x) (snd y) \<turnstile> hn_ctxt B' (snd x) (snd y)"
  shows "hn_ctxt (prod_assn A B) x y \<turnstile> hn_ctxt (prod_assn A' B') x y"
  apply (cases x; cases y; simp)
  apply (simp add: hn_ctxt_def)
  apply (rule conj_entails_mono)
  using assms apply (auto simp: hn_ctxt_def)
  done

lemma prod_frame_merge[sepref_frame_merge_rules]:
  assumes "MERGE1 A frl1 A' frr1 Am"  
  assumes "MERGE1 B frl2 B' frr2 Bm"  
  shows "MERGE1 
    (prod_assn A B) (\<lambda>(a,b). doM {frl1 a; frl2 b}) 
    (prod_assn A' B') (\<lambda>(a,b). doM {frr1 a; frr2 b}) 
    (prod_assn Am Bm)"
  supply [vcg_rules] = MERGE1D[OF assms(1)] MERGE1D[OF assms(2)]
  by rule vcg
    
  

lemma entt_invalid_prod: "hn_invalid (prod_assn A B) p p' \<turnstile> hn_ctxt (prod_assn (invalid_assn A) (invalid_assn B)) p p'"
  unfolding hn_ctxt_def invalid_assn_def prod_assn_def
  by (auto split: prod.splits simp: entails_def pred_lift_extract_simps dest: pure_part_split_conj)

lemma gen_merge_cons_left: "L\<turnstile>L' \<Longrightarrow> MERGE L' fl R fr M \<Longrightarrow> MERGE L fl R fr M"  
  unfolding MERGE_def
  by (metis (mono_tags, lifting) cons_rule[where Q=Q and Q'=Q for Q] entails_def)
  
lemma gen_merge_cons_right: "R\<turnstile>R' \<Longrightarrow> MERGE L fl R' fr M \<Longrightarrow> MERGE L fl R fr M"  
  unfolding MERGE_def
  by (metis (mono_tags, lifting) cons_rule[where Q=Q and Q'=Q for Q] entails_def)
  
lemmas gen_merge_cons = gen_merge_cons_left gen_merge_cons_right

lemmas invalid_prod_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_prod]

lemma prod_assn_ctxt: "prod_assn A1 A2 x y = z \<Longrightarrow> hn_ctxt (prod_assn A1 A2) x y = z"
  by (simp add: hn_ctxt_def)

(* TODO: Move *)  
lemma drop_pureD: "is_pure A \<Longrightarrow> hn_ctxt A a b \<turnstile> \<box>"
  by (auto simp: is_pure_def entails_def pred_lift_extract_simps hn_ctxt_def)
  
lemma hn_case_prod_aux:
  assumes FR: "\<Gamma> \<turnstile> hn_ctxt (prod_assn P1 P2) p' p ** \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2'); p=(a1,a2)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 ** hn_ctxt P2 a2' a2 ** \<Gamma>1 ** hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt XX1 p' p ** \<Gamma>1') (R a1' a2' a1 a2) (f' a1' a2')"
  assumes PURE: "Sepref_Basic.is_pure XX1"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p ** \<Gamma>1')
    (R (fst p') (snd p') (fst p) (snd p)) (case_prod f' p')" (is "?G \<Gamma>")
    apply1 (rule hn_refine_cons_pre[OF _ FR])
    apply1 extract_hnr_invalids
  apply1 (cases p; cases p'; simp add: prod_assn_pair_conv[THEN prod_assn_ctxt]) 
    apply (rule hn_refine_cons[OF Pair _ _ entails_refl])
    applyS simp
    applyS simp
    applyS (simp add: hn_ctxt_def)
    using PURE apply (sep_drule drop_pureD[OF PURE])
    by (simp add: hn_ctxt_def sep_conj_ac)
  
    
(* TODO: This has caused "ENTER MATCH" unifier problems with flex-flex pairs. So disabled by default,
  and hn_case_prod_simple' is enabled, where the result cannot depend on the elements of the pair. *)    
lemma hn_case_prod':
  assumes FR: "\<Gamma> \<turnstile> hn_ctxt (prod_assn P1 P2) p' p ** \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2'); p=(a1,a2)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 ** hn_ctxt P2 a2' a2 ** \<Gamma>1 ** hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (\<Gamma>2 a1 a2 a1' a2') (R a1' a2' a1 a2) (f' a1' a2')"
  assumes FR2: "\<And>a1 a2 a1' a2'. \<Gamma>2 a1 a2 a1' a2' \<turnstile> hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt XX1 p' p ** \<Gamma>1'"        
  assumes PURE: "CONSTRAINT Sepref_Basic.is_pure XX1"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p ** \<Gamma>1')
    (R (fst p') (snd p') (fst p) (snd p)) (case_prod$(\<lambda>\<^sub>2a b. f' a b)$p')" (is "?G \<Gamma>")
    unfolding autoref_tag_defs PROTECT2_def
    apply (rule hn_case_prod_aux[OF _ hn_refine_cons_post])
    apply fact
    apply fact
    using FR2 apply blast
    using PURE by simp

lemma hn_case_prod_simple'[sepref_comb_rules]:
  assumes FR: "\<Gamma> \<turnstile> hn_ctxt (prod_assn P1 P2) p' p ** \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2'); p=(a1,a2)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 ** hn_ctxt P2 a2' a2 ** \<Gamma>1 ** hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (\<Gamma>2 a1 a2 a1' a2') R (f' a1' a2')"
  assumes FR2: "\<And>a1 a2 a1' a2'. \<Gamma>2 a1 a2 a1' a2' \<turnstile> hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt XX1 p' p ** \<Gamma>1'"        
  assumes PURE: "CONSTRAINT Sepref_Basic.is_pure XX1"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p ** \<Gamma>1')
    R (case_prod$(\<lambda>\<^sub>2a b. f' a b)$p')" (is "?G \<Gamma>")
    unfolding autoref_tag_defs PROTECT2_def
    apply (rule hn_case_prod_aux[OF _ hn_refine_cons_post])
    apply fact
    apply fact
    using FR2 apply blast
    using PURE by simp
    
    
lemma hn_Pair[sepref_fr_rules]: "(uncurry (return oo Pair), uncurry (RETURN oo Pair)) \<in> A\<^sup>d *\<^sub>a B\<^sup>d \<rightarrow>\<^sub>a A\<times>\<^sub>aB"    
  by sepref_to_hoare vcg
    

lemma fst_hnr[sepref_fr_rules]: "(return o fst,RETURN o fst) \<in> (prod_assn A B)\<^sup>d \<rightarrow>\<^sub>a A"
  apply sepref_to_hoare
  apply vcg
  oops (* TODO *)
lemma snd_hnr[sepref_fr_rules]: "(return o snd,RETURN o snd) \<in> (prod_assn A B)\<^sup>d \<rightarrow>\<^sub>a B"
  apply sepref_to_hoare
  apply vcg
  oops (* TODO *)


lemmas [constraint_simps] = prod_assn_pure_conv
lemmas [sepref_import_param] = param_prod_swap

lemma rdomp_prodD[dest!]: "rdomp (prod_assn A B) (a,b) \<Longrightarrow> rdomp A a \<and> rdomp B b"
  unfolding rdomp_def prod_assn_def
  by (auto simp: sep_conj_def)

subsection \<open>Option\<close>  

   
lemma option_patterns[def_pat_rules]: 
  "(=)$x$None \<equiv> is_None$x"
  "(=)$None$x \<equiv> is_None$x"
  "op_neq$x$None \<equiv> Not$(is_None$x)"
  "op_neq$None$x \<equiv> Not$(is_None$x)"
  apply (all \<open>rule eq_reflection\<close>)
  by (auto split: option.splits)

  \<^cancel>\<open>
text \<open>Option type via unused implementation value\<close>  
locale dflt_option =   
  fixes dflt and A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and is_dflt
  assumes UU: "A a dflt = sep_false"
  assumes CMP: "llvm_htriple \<box> (is_dflt k) (\<lambda>r. \<upharpoonleft>bool.assn (k=dflt) r)"
begin
  
  definition "option_assn a c \<equiv> if c=dflt then \<up>(a=None) else EXS aa. \<up>(a=Some aa) ** A aa c"
  
  lemma hn_None[sepref_fr_rules]: "(uncurry0 (return dflt), uncurry0 (RETURN None)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn"  
    apply sepref_to_hoare unfolding option_assn_def 
    apply vcg'
    done
  
  lemma hn_Some[sepref_fr_rules]: "(return, RETURN o Some) \<in> A\<^sup>d \<rightarrow>\<^sub>a option_assn"  
    apply sepref_to_hoare
    subgoal for a c
      apply (cases "c=dflt")
      using UU apply simp
      unfolding option_assn_def
      apply vcg
      done
    done
  
  lemma hn_the[sepref_fr_rules]: "(return, RETURN o the) \<in> [\<lambda>x. x \<noteq> None]\<^sub>a option_assn\<^sup>d \<rightarrow> A"
    apply sepref_to_hoare
    unfolding option_assn_def 
    apply clarsimp
    apply vcg'
    done
    
  lemma hn_is_None[sepref_fr_rules]: "(is_dflt, RETURN o is_None) \<in> option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bool1_rel_def bool.assn_is_rel[symmetric]
    apply sepref_to_hoare
    unfolding option_assn_def 
    apply clarsimp
    supply CMP[vcg_rules]
    apply vcg'
    done
    
  definition [llvm_inline]: "free_option fr c \<equiv> doM { d\<leftarrow>is_dflt c; llc_if d (return ()) (fr c) }"
    
  lemma mk_free_option[sepref_frame_free_rules]:
    assumes [THEN MK_FREED, vcg_rules]: "MK_FREE A fr"  
    shows "MK_FREE option_assn (free_option fr)"
    apply rule
    unfolding free_option_def option_assn_def
    apply clarsimp
    supply CMP[vcg_rules]
    apply vcg
    done
    
  lemma option_assn_pure[safe_constraint_rules]:
    assumes "is_pure A" 
    shows "is_pure option_assn"  
  proof -
    from assms obtain P where [simp]: "A = (\<lambda>a c. \<up>(P a c))"
      unfolding is_pure_def by blast
  
    show ?thesis  
      apply (rule is_pureI[where P'="\<lambda>a c. if c=dflt then a=None else \<exists>aa. a=Some aa \<and> P aa c"])
      unfolding option_assn_def
      by (auto simp: sep_algebra_simps pred_lift_extract_simps)
      
  qed    
    
    
end    

lemmas [named_ss llvm_inline cong] = refl[of "dflt_option.free_option _"]


locale dflt_pure_option = dflt_option +
  assumes A_pure[safe_constraint_rules]: "is_pure A"
begin
  find_theorems MK_FREE is_pure

  lemma A_free[sepref_frame_free_rules]: "MK_FREE A (\<lambda>_. return ())"
    by (rule mk_free_is_pure[OF A_pure])

end  

(* TODO: Redundancies with dflt_option *)
(* TODO: Setup id-op phase to identify those operations *)
text \<open>Option type via unused implementation value, own set of operations.\<close>  
locale dflt_option_private =   
  fixes dflt and A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and is_dflt
  assumes UU: "A a dflt = sep_false"
  assumes CMP: "llvm_htriple \<box> (is_dflt k) (\<lambda>r. \<upharpoonleft>bool.assn (k=dflt) r)"
begin
  
  definition "option_assn a c \<equiv> if c=dflt then \<up>(a=None) else EXS aa. \<up>(a=Some aa) ** A aa c"

  definition None where [simp]: "None \<equiv> Option.None"
  definition Some where [simp]: "Some \<equiv> Option.Some"
  definition the where [simp]: "the \<equiv> Option.the"
  definition is_None where [simp]: "is_None \<equiv> Autoref_Bindings_HOL.is_None"
  
  lemmas fold_None = None_def[symmetric]
  lemmas fold_Some = Some_def[symmetric]
  lemmas fold_the = the_def[symmetric]
  lemmas fold_is_None = is_None_def[symmetric]
  
  lemma fold_is_None2: 
    "a = None \<longleftrightarrow> is_None a"
    "None = a \<longleftrightarrow> is_None a"
    by (auto simp: is_None_def None_def split: option.split)
  
  lemmas fold_option = fold_None fold_Some fold_the fold_is_None fold_is_None2
  
  sepref_register None Some the is_None
  
    
  lemma hn_None[sepref_fr_rules]: "(uncurry0 (return dflt), uncurry0 (RETURN None)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn"  
    apply sepref_to_hoare unfolding option_assn_def None_def
    apply vcg'
    done
  
  lemma hn_Some[sepref_fr_rules]: "(return, RETURN o Some) \<in> A\<^sup>d \<rightarrow>\<^sub>a option_assn"  
    apply sepref_to_hoare
    subgoal for a c
      apply (cases "c=dflt")
      using UU apply simp
      unfolding option_assn_def Some_def
      apply vcg
      done
    done
  
  lemma hn_the[sepref_fr_rules]: "(return, RETURN o the) \<in> [\<lambda>x. x \<noteq> Option.None]\<^sub>a option_assn\<^sup>d \<rightarrow> A"
    apply sepref_to_hoare
    unfolding option_assn_def the_def
    apply clarsimp
    apply vcg'
    done
    
  lemma hn_is_None[sepref_fr_rules]: "(is_dflt, RETURN o is_None) \<in> option_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    unfolding bool1_rel_def bool.assn_is_rel[symmetric]
    apply sepref_to_hoare
    unfolding option_assn_def is_None_def
    apply clarsimp
    supply CMP[vcg_rules]
    apply vcg'
    done
    
  definition [llvm_inline]: "free_option fr c \<equiv> doM { d\<leftarrow>is_dflt c; llc_if d (return ()) (fr c) }"
    
  lemma mk_free_option[sepref_frame_free_rules]:
    assumes [THEN MK_FREED, vcg_rules]: "MK_FREE A fr"  
    shows "MK_FREE option_assn (free_option fr)"
    apply rule
    unfolding free_option_def option_assn_def
    apply clarsimp
    supply CMP[vcg_rules]
    apply vcg
    done
    
  lemma option_assn_pure[safe_constraint_rules]:
    assumes "is_pure A" 
    shows "is_pure option_assn"  
  proof -
    from assms obtain P where [simp]: "A = (\<lambda>a c. \<up>(P a c))"
      unfolding is_pure_def by blast
  
    show ?thesis  
      apply (rule is_pureI[where P'="\<lambda>a c. if c=dflt then a=Option.None else \<exists>aa. a=Option.Some aa \<and> P aa c"])
      unfolding option_assn_def
      by (auto simp: sep_algebra_simps pred_lift_extract_simps)
      
  qed    
    
    
end    

lemmas [named_ss llvm_inline cong] = refl[of "dflt_option_private.free_option _"]


locale dflt_pure_option_private = dflt_option_private +
  assumes A_pure[safe_constraint_rules]: "is_pure A"
begin
  lemma A_free[sepref_frame_free_rules]: "MK_FREE A (\<lambda>_. return ())"
    by (rule mk_free_is_pure[OF A_pure])

end  



interpretation snat: dflt_pure_option "-1" snat_assn "ll_icmp_eq (-1)"
  apply unfold_locales
  subgoal
    apply (auto simp: snat_rel_def pure_def pred_lift_extract_simps del: ext intro!: ext)
    apply (auto simp: snat.rel_def in_br_conv snat_invar_def)
    done
  subgoal proof goal_cases
    case 1
    interpret llvm_prim_arith_setup .
    show ?case
      unfolding bool.assn_def
      apply vcg'
      done
    qed
  subgoal by simp  
  done

abbreviation snat_option_assn' :: "'a itself \<Rightarrow> nat option \<Rightarrow> 'a::len2 word \<Rightarrow> llvm_amemory \<Rightarrow> bool" where
  "snat_option_assn' _ \<equiv> snat.option_assn"
  \<close>
  
\<^cancel>\<open>
subsection \<open>Additional Operations\<close>  

text \<open>Additional operations, for which we need the basic framework already set up.\<close>
  
subsubsection \<open>Subtraction that Saturates at 0 on Underflow\<close>  
  
definition op_nat_sub_ovf :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "op_nat_sub_ovf a b \<equiv> if a\<le>b then 0 else a-b"
lemma op_nat_sub_ovf_is_sub[simp]: "op_nat_sub_ovf = (-)"
  unfolding op_nat_sub_ovf_def by (auto split: if_split del: ext intro!: ext)

lemma fold_nat_sub_ovf: "(-) = op_nat_sub_ovf" by simp
  
sepref_definition snat_sub_ovf_impl [llvm_inline] is "uncurry (RETURN oo op_nat_sub_ovf)" 
  :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l::len2)"
  unfolding op_nat_sub_ovf_def 
  apply (annot_snat_const "TYPE('l)")
  by sepref
  
declare snat_sub_ovf_impl.refine[sepref_fr_rules]
  
  \<close>
  
  
  
    
\<^cancel>\<open>

subsection \<open>Ad-Hoc Regression Tests\<close>  
  
sepref_definition example1 is "\<lambda>x. doN {ASSERT (x\<in>{-10..10});
    RETURN (x<5 \<and> x\<noteq>2 \<longrightarrow> x-2 \<noteq> 0)}" :: "(sint_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (bool1_assn)" 
  apply (annot_sint_const "TYPE(7)")
  apply sepref
  done

sepref_definition example2 is "\<lambda>x. doN {ASSERT (x\<in>{-10..10}); RETURN (x+(-1) * (7 smod 15) - 3 sdiv 2)}" :: "(sint_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (sint_assn' TYPE(7))" 
  apply (annot_sint_const "TYPE(7)")
  apply sepref
  done

sepref_definition example1n is "\<lambda>x. doN {ASSERT (x\<in>{2..10});
    RETURN (x<5 \<and> x\<noteq>2 \<longrightarrow> x-2 \<noteq> 0)}" :: "(snat_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (bool1_assn)" 
  apply (annot_snat_const "TYPE(7)")
  apply sepref
  done

sepref_definition example2n is "\<lambda>x. doN {ASSERT (x\<in>{5..10}); RETURN ((x-1) * (7 mod 15) - 3 div 2)}" 
  :: "(snat_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(7))" 
  apply (annot_snat_const "TYPE(7)")
  apply sepref
  done
  
      
lemmas [llvm_code] = example1_def example2_def example1n_def example2n_def  
  
llvm_deps example1 example2 example1n example2n

export_llvm example1 example2 example1n example2n
  

definition example3_abs :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word nres" where "example3_abs a b \<equiv> do {
    (a,b) \<leftarrow> WHILET (\<lambda>(a,b). a\<noteq>b) (\<lambda>(a,b). if a<b then RETURN (a,b-a) else RETURN (a-b,b)) (a,b);
    RETURN a
  }"

sepref_definition example3 is "uncurry example3_abs" :: "word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a word_assn"
  unfolding example3_abs_def
  apply sepref_dbg_keep
  done

definition example3n_abs :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where "example3n_abs a b \<equiv> do {
    (a,b) \<leftarrow> WHILET (\<lambda>(a,b). a\<noteq>b) (\<lambda>(a,b). if a<b then RETURN (a,b-a) else RETURN (a-b,b)) (a,b);
    RETURN a
  }"

sepref_definition example3n is "uncurry example3n_abs" :: "(snat_assn' TYPE(32))\<^sup>k *\<^sub>a (snat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a (snat_assn' TYPE(32))"
  unfolding example3n_abs_def
  apply sepref_dbg_keep
  done
  
  
    
lemmas [llvm_code] = example3_def example3n_def  
export_llvm
  "example3 :: 32 word \<Rightarrow> _"
  "example3 :: 64 word \<Rightarrow> _"
  "example3n"


sepref_definition example4n is "\<lambda>x. do {
       x \<leftarrow> RETURN (x >> 1);
       ASSERT ((x << 1) < max_snat 7);
       RETURN ((x << 1) > x)
   }" :: "(snat_assn' TYPE(7))\<^sup>k \<rightarrow>\<^sub>a (bool1_assn)" 
  apply (annot_snat_const "TYPE(7)")
  apply sepref
  done

lemmas [llvm_code] = example4n_def

llvm_deps example4n

export_llvm example4n
 
(* TODO: Characters as i8 *)  
  *)
\<close>

end
