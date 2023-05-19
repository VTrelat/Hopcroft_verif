\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
\<^marker>\<open>contributor "Peter Lammich"\<close>
section \<open>More theory on NREST\<close>
theory NREST_Main
  imports NREST NREST_Type_Classes  Time_Refinement Data_Refinement
     NREST_Backwards_Reasoning NREST_Automation
begin
        

paragraph \<open>Summary\<close>
text \<open>This theory introduces more convenience lemmas on NREST\<close>


subsection \<open>Convenience Lemmas\<close>


lemma If_le_rule: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> (~c \<Longrightarrow> x \<le> b) \<Longrightarrow> x \<le> (if c then a else b)"
  by auto

lemma If_le_Some_rule2: "(c \<Longrightarrow> x \<le> a) \<Longrightarrow> c \<Longrightarrow> Some x \<le> (if c then Some a else None)"
  by auto

term inres
subsection \<open>Interaction between Currency Refinement and Data Refinement\<close>
                   
lemma timerefine_R_cf_mono:
  fixes R :: "_ \<Rightarrow> (_, enat) acost"
  assumes "wfR'' R'"
  shows "R\<le>R' \<Longrightarrow> \<Down> S (\<Down>\<^sub>C R c) \<le> \<Down> S (\<Down>\<^sub>C R' c)"
  by (simp add: assms nrest_Rel_mono timerefine_R_mono_wfR'')


lemma inresT_project_acost_timerefine: "inresT (project_acost b (\<Down>\<^sub>C E m')) x' t 
       \<Longrightarrow> \<exists>t b. inresT (project_acost b m') x' t"
  unfolding inresT_def project_acost_def timerefine_def
  apply(cases m'; auto simp: le_fun_def split: if_splits option.splits)
  by (metis zero_enat_def zero_le)  


lemma bindT_refine_conc_time:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR E" " m \<le> \<Down>R' (\<Down>\<^sub>C E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R';  \<exists>t b. inresT (project_acost b m) x t;  \<exists>t b. inresT (project_acost b m') x' t;
    nofailT m; nofailT m'\<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (\<Down>\<^sub>C E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
  using assms
proof -
  term "(\<Down>\<^sub>C E m')"
  term timerefine
  have "bindT m (\<lambda>x.  (f x)) \<le>  \<Down> R (bindT (\<Down>\<^sub>C E m') (\<lambda>x. \<Down>\<^sub>C E (f' x)))"
    apply(rule bindT_conc_acost_refine') apply(rule assms(2)) 
    apply(rule assms(3))  
    by (auto simp: refine_pw_simps dest: inresT_project_acost_timerefine) 
  also have "\<dots> \<le> \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
    apply(rule nrest_Rel_mono)
    apply(rule timerefine_bindT_ge) by(fact assms(1))
  finally show ?thesis .
qed
lemma bindT_refine_conc_time2:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (\<Down>\<^sub>C E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R';  \<exists>t b. inresT (project_acost b m) x t;  \<exists>t b. inresT (project_acost b m') x' t;
    nofailT m; nofailT m'\<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (\<Down>\<^sub>C E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
  using assms
proof -
  term "(\<Down>\<^sub>C E m')"
  term timerefine
  have "bindT m (\<lambda>x.  (f x)) \<le>  \<Down> R (bindT (\<Down>\<^sub>C E m') (\<lambda>x. \<Down>\<^sub>C E (f' x)))"
    apply(rule bindT_conc_acost_refine') apply(rule assms(2)) 
    apply(rule assms(3))  
    by (auto simp: refine_pw_simps dest: inresT_project_acost_timerefine) 
  also have "\<dots> \<le> \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
    apply(rule nrest_Rel_mono)
    apply(rule timerefine_bindT_ge2) by(fact assms(1))
  finally show ?thesis .
qed



lemma bindT_refine_conc_time_my:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (\<Down>\<^sub>C E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'; \<exists>t b. inresT (project_acost b m') x' t\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (\<Down>\<^sub>C E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2) using assms by auto



lemma timerefine_conc_fun_ge:
  fixes C :: "('f, ('b, enat) acost) nrest"
  assumes "wfR E"
  shows "\<Down>\<^sub>C E (\<Down> R C) \<ge> \<Down>R (\<Down>\<^sub>C E C)"

  unfolding conc_fun_def timerefine_def
  apply(cases C) apply auto apply(rule le_funI)
  apply(rule Sup_least)
  apply (auto split: option.splits)
  subgoal 
    by (metis (mono_tags, lifting) Sup_upper less_eq_option_Some_None mem_Collect_eq)
  unfolding less_eq_acost_def apply auto
  apply(rule Sum_any_mono)
  apply(rule mult_right_mono)
  subgoal     
    by (metis (mono_tags, lifting) Sup_upper less_eq_option_Some mem_Collect_eq the_acost_mono)
    apply simp
  apply(rule wfR_finite_mult_left )
  using assms by simp


lemma timerefine_conc_fun_ge2:
  fixes C :: "('f, ('b, enat) acost) nrest"
  assumes "wfR'' E"
  shows "\<Down>\<^sub>C E (\<Down> R C) \<ge> \<Down>R (\<Down>\<^sub>C E C)"

  unfolding conc_fun_def timerefine_def
  apply(cases C) apply auto apply(rule le_funI)
  apply(rule Sup_least)
  apply (auto split: option.splits)
  subgoal 
    by (metis (mono_tags, lifting) Sup_upper less_eq_option_Some_None mem_Collect_eq)
  unfolding less_eq_acost_def apply auto
  apply(rule Sum_any_mono)
  apply(rule mult_right_mono)
  subgoal     
    by (metis (mono_tags, lifting) Sup_upper less_eq_option_Some mem_Collect_eq the_acost_mono)
    apply simp
  apply(rule wfR_finite_mult_left2 )
  using assms by simp


lemma timerefine_conc_fun_le2:
  assumes "continuous E"
  shows "timerefine' E (\<Down> R C) = \<Down>R (timerefine' E C)"
  unfolding timerefine'_def conc_fun_def 
  apply(auto split: nrest.splits option.splits simp: fun_eq_iff)
  subgoal 
    by (smt Sup_bot_conv(1) bot_option_def mem_Collect_eq) 
  subgoal premises p for x2 x2a x2b x x2c
  proof -
    have "Sup {x2b a |a. (x, a) \<in> R} = Sup {map_option E (x2 a) |a. (x, a) \<in> R}"
      apply(rule arg_cong[where f=Sup])
      using p(3)[rule_format] p(4)
      apply auto
      subgoal by (smt map_option_eq_Some option.exhaust) 
      subgoal by (metis not_None_eq option.simps(8) option.simps(9)) 
      done
    also have "\<dots> = map_option E (Sup {x2 a |a. (x, a) \<in> R})" 
      apply(subst continuous_map_option[OF assms, THEN continuousD] )
      apply(rule arg_cong[where f=Sup])
      by auto
    also have "\<dots> = map_option E (Some x2c)"
      using p(2)[rule_format, of x, unfolded p(4)] by simp
    also have "\<dots> = Some (E x2c)" by simp
    finally show "Some (E x2c) = Sup {x2b a |a. (x, a) \<in> R}"  by simp
  qed
  done 

(* TODO: move*)
lemma nrest_le_formatI:
  fixes a :: "(_,(_,enat)acost) nrest"
  shows  "a \<le> \<Down>Id (\<Down>\<^sub>C TId b) \<Longrightarrow> a \<le> b"
  by (auto simp add: timerefine_id)


subsection \<open>nrest_trel\<close>

definition nrest_trel where 
  nrest_trel_def_internal: "nrest_trel R E \<equiv> {(c,a).  c \<le> \<Down>R (\<Down>\<^sub>C E a)}"


lemma nrest_trelD: "(c,a)\<in>nrest_trel R E \<Longrightarrow> c \<le> \<Down>R (\<Down>\<^sub>C E a)" by (simp add: nrest_trel_def_internal)

  
lemma nrest_trelI: "c \<le> \<Down>R (\<Down>\<^sub>C E a) \<Longrightarrow> (c,a)\<in>nrest_trel R E" by (simp add: nrest_trel_def_internal)


subsection \<open>Type Class nrest_cost\<close>

class nrest_cost = complete_lattice + needname_zero + nonneg + ordered_semiring + semiring_no_zero_divisors


subsection \<open>Setup for refinement condition generator\<close>

lemma consume_refine:
  fixes M :: "('e, ('b, enat) acost) nrest"
  assumes "wfR'' E"
  shows "\<lbrakk>t \<le> timerefineA E t'; M \<le> \<Down> R (\<Down>\<^sub>C E M')\<rbrakk> \<Longrightarrow> NREST.consume M t \<le> \<Down>R (\<Down>\<^sub>C E (NREST.consume M' t'))"
  apply(subst timerefine_consume)
  subgoal using assms .
  apply(subst conc_fun_consume)
  apply(rule consume_mono) by auto

lemma MIf_refine:
  fixes f :: "(_,(string, enat) acost) nrest"
  shows "struct_preserving E \<Longrightarrow> wfR'' E \<Longrightarrow> (b,b')\<in>bool_rel \<Longrightarrow> (b \<Longrightarrow> f \<le> \<Down>R (\<Down>\<^sub>C E f'))
           \<Longrightarrow> (\<not>b \<Longrightarrow> g \<le> \<Down>R (\<Down>\<^sub>C E g')) \<Longrightarrow>  MIf b f g  \<le> \<Down>R (\<Down>\<^sub>C E (MIf b' f' g' ))"
  by(auto simp: MIf_def timerefineA_update_apply_same_cost dest: struct_preservingD intro!: consume_refine)


lemma ASSERT_D_leI[refine,refine0]: 
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> M \<le> \<Down>R M') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. M) \<le> \<Down>R M'"
  by (auto)

lemma ASSERT_D2_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> S \<le> \<Down> R S') \<Longrightarrow> S \<le> \<Down> R (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   })"
  by (auto simp: pw_acost_le_iff refine_pw_simps)


lemma ASSERT_D3_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> S \<le> \<Down> R (\<Down>\<^sub>C E S')) \<Longrightarrow> S \<le> \<Down> R (\<Down>\<^sub>C E (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   }))"
  by (auto simp: pw_acost_le_iff refine_pw_simps)


lemma ASSERT_D4_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> S \<le> \<Down> R (\<Down>\<^sub>C E S')) \<Longrightarrow> do { _ \<leftarrow> ASSERT \<Phi>; S } \<le> \<Down> R (\<Down>\<^sub>C E (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   }))"
  by (auto simp: pw_acost_le_iff refine_pw_simps)


lemma refine_Id[refine0]: "S \<le> \<Down> Id S"
  by auto


lemma refine_TId[refine0]:
  fixes S :: "(_,(_,enat)acost) nrest"
  shows  "S \<le> \<Down> Id (\<Down>\<^sub>C TId S)"
  unfolding timerefine_id
  by auto





lemma SPEC_refine[refine]:
  fixes T :: "_ \<Rightarrow> ((_,enat)acost)"
  assumes *: "\<And>x. \<Phi> x \<Longrightarrow> \<exists>s'. \<Phi>' s' \<and> (x, s') \<in> R \<and> T x \<le> T' s'"
  shows "SPEC \<Phi> T \<le> \<Down>R (SPEC \<Phi>' T')"
  unfolding SPEC_def
  by (auto simp: pw_acost_le_iff refine_pw_simps dest!: * intro: order.trans[OF _ the_acost_mono])

    
lemma SPEC_both_refine:
  fixes T :: "_ \<Rightarrow> ((_,enat)acost)"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> \<exists>s'. \<Phi>' s' \<and> (x, s') \<in> R \<and> T x \<le> timerefineA TR (T' s')"
  shows "SPEC \<Phi> T \<le> \<Down> R (\<Down>\<^sub>C TR (SPEC \<Phi>' T'))"
  apply(rule order.trans) 
  defer
   apply(rule nrest_Rel_mono)
   apply(rule SPEC_timerefine[where A=\<Phi>'])
    prefer 3 apply(rule SPEC_refine[where T=T])
    defer apply simp apply(rule order_refl)
  by (fact assms)

lemma ASSERT_D5_leI[refine0]: 
  fixes S' :: "(_,(_,enat)acost) nrest"
  shows "(\<Phi> \<Longrightarrow> \<Down> R (\<Down>\<^sub>C F S) \<le> \<Down> R (\<Down>\<^sub>C E S')) \<Longrightarrow> \<Down> R (\<Down>\<^sub>C F ( do { _ \<leftarrow> ASSERT \<Phi>; S })) \<le> \<Down> R (\<Down>\<^sub>C E (do {
                                     _ \<leftarrow> ASSERT \<Phi>;
                                     S'
                                   }))"
  by (auto simp: pw_acost_le_iff refine_pw_simps)

declare consume_refine[refine0]


lemma RETURNT_refine_t[refine]:
  assumes "(x,x')\<in>R"
  shows "RETURNT x \<le> \<Down>R (\<Down>\<^sub>C E (RETURNT x'))"
  apply(subst timerefine_RETURNT)
  apply(rule RETURNT_refine) by (fact assms)


declare RETURNT_refine_t[refine0]
declare timerefineA_TId[refine0]


lemma SPECT_refine_t[refine]:
  fixes t :: "(_,enat) acost"
  assumes "(x,x')\<in>R"
    and "t\<le> timerefineA E t'"
  shows "SPECT [x\<mapsto>t] \<le> \<Down>R (\<Down>\<^sub>C E (SPECT [x'\<mapsto>t']))"
  apply(subst timerefine_SPECT_map)
  using assms apply(auto simp: pw_acost_le_iff refine_pw_simps)
  apply(cases t) apply (auto simp: less_eq_acost_def)
  subgoal for b ta xa apply(rule order.trans[where b="xa b"]) by auto
  done

lemma RECT_refine_t:
  assumes M: "mono2 body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (\<Down>\<^sub>C E (f' x')); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (\<Down>\<^sub>C E (body' f' x'))"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (\<Down>\<^sub>C E (RECT (\<lambda>f' x'. body' f' x') x'))"
  unfolding RECT_flat_gfp_def
  apply (clarsimp simp add: M) 
  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp body" 
    and B'=body 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD_flatf_ge)
  by (rule RS)

lemma RECT'_refine_t:
  fixes body :: "('b \<Rightarrow> ('c, (char list, enat) acost) nrest)
   \<Rightarrow> 'b \<Rightarrow> ('c, (char list, enat) acost) nrest"
  assumes M: "mono2 body"
  assumes wfRE: "wfR'' E"
  assumes spE: "struct_preserving E"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (\<Down>\<^sub>C E (f' x')); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (\<Down>\<^sub>C E (body' f' x'))"
  shows "RECT' (\<lambda>f x. body f x) x \<le>\<Down>S (\<Down>\<^sub>C E (RECT' (\<lambda>f' x'. body' f' x') x'))"
  unfolding RECT'_def
  apply(rule consume_refine[OF wfRE])
  subgoal using spE[THEN struct_preservingD(1)] by simp
  unfolding RECT_flat_gfp_def
  apply (clarsimp simp add: M[THEN RECT'_unfold_aux])
  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp ((\<lambda>D. body (\<lambda>x. NREST.consume (D x) (cost ''call'' 1))))" 
    and B'="(\<lambda>D. body (\<lambda>x. NREST.consume (D x) (cost ''call'' 1)))" 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN RECT'_unfold_aux, THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD_flatf_ge)
  apply (rule RS)
   apply(rule consume_refine[OF wfRE])
  subgoal using spE[THEN struct_preservingD(1)] by simp
   apply simp apply simp
  done

lemma monadic_WHILEIT_refine_t[refine]:  
  fixes b :: "'c \<Rightarrow> (bool, (char list, enat) acost) nrest"
  assumes wfR[simp]:  "wfR'' E"
  assumes sp_E: "struct_preserving E"
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (\<Down>\<^sub>C E (b s))"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; nofailT (b s);
                    \<exists>t e. inresT (project_acost  e (b s)) True t \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (\<Down>\<^sub>C E (f s))"
  shows "monadic_WHILEIT I' b' f' s' \<le> \<Down>R (\<Down>\<^sub>C E (monadic_WHILEIT I b f s))"
  unfolding monadic_WHILEIT_def unfolding MIf_def 
  apply (refine_rcg bindT_refine_conc_time2 RECT_refine_t IdI wfR struct_preservingD[OF sp_E]) 
  apply simp  
  subgoal by refine_mono
  apply (assumption?; auto)+
  apply (refine_rcg consume_refine_easy bindT_refine_conc_time2 wfR struct_preservingD[OF sp_E] RETURNT_refine_t )
       apply (assumption?; auto)+
  apply(rule RETURNT_refine_t) 
  apply (assumption?; auto)+ 
  done

lemma monadic_WHILEIT_refine':  
  fixes b :: "'c \<Rightarrow> (bool, (char list, enat) acost) nrest"
  assumes wfR[simp]:  "wfR'' E"
  assumes sp_E: "struct_preserving E"
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (\<Down>\<^sub>C E (b s))"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (\<Down>\<^sub>C E (f s))"
  shows "monadic_WHILEIT I' b' f' s' \<le> \<Down>R (\<Down>\<^sub>C E (monadic_WHILEIT I b f s))"
  apply(rule monadic_WHILEIT_refine_t[OF assms(1-5)])
  by(auto intro: assms(6) inres_if_inresT_acost)

subsection \<open>mop call\<close>

definition mop_call where
  "mop_call m = consume m (cost ''call'' 1)"

lemma gwp_call[vcg_rules']:
  fixes m :: "(_,(_,enat) acost) nrest"
  assumes "Some (cost ''call'' 1 + t) \<le> gwp m Q"
  shows  "Some t \<le> gwp (mop_call m) Q"
  unfolding mop_call_def
  apply(rule gwp_consume) by(rule assms)

lemma mop_call_refine:
  fixes M :: "('e, (string, enat) acost) nrest"
  assumes "wfR'' E"
    "struct_preserving E"
  shows "\<lbrakk> M \<le> \<Down> R (\<Down>\<^sub>C E M')\<rbrakk> \<Longrightarrow> mop_call M \<le> \<Down>R (\<Down>\<^sub>C E (mop_call M'))"
  unfolding mop_call_def
  apply(subst timerefine_consume)
  subgoal using assms(1) .
  apply(subst conc_fun_consume)
  apply(rule consume_mono) 
  using assms(2)[THEN struct_preservingD(1)]  
  by auto    

subsection \<open>Shortcuts for specifications of operations\<close>

  definition "SPECc1' c aop == (\<lambda>a. SPECT ( [(aop a)\<mapsto>c]))"
  definition "SPECc1 name aop == (\<lambda>a. SPECT ( [(aop a)\<mapsto>(cost name 1)]))"
  definition "SPECc2 name aop == ( (\<lambda>a b. SPECT ( [(aop a b)\<mapsto>(cost name 1)])))"


lemma RETURNT_eq_SPECc2_iff[simp]: "RETURNTecost v \<le> SPECc2 n f a b
      \<longleftrightarrow> (f a b = v)"
  unfolding SPECc2_def apply (auto simp: pw_acost_le_iff refine_pw_simps)
  using zero_enat_def by(auto simp: )  

lemma inres_SPECc2: "inres (SPECc2 n op a b) t \<longleftrightarrow> (op a b = t)"
  by(auto simp: inres_def SPECc2_def)

lemma SPECc2_alt: "SPECc2 name aop = ( (\<lambda>a b. consume (RETURNT (aop a b)) (cost name 1)))"
  unfolding SPECc2_def consume_def by(auto simp: RETURNT_def intro!: ext)

lemma SPECc1_alt: "SPECc1 name aop = ( (\<lambda>a. consume (RETURNT (aop a)) (cost name 1)))"
  unfolding SPECc1_def consume_def by(auto simp: RETURNT_def intro!: ext)

lemma gwp_SPECc2:
  assumes "Some (t + cost c 1) \<le> Q (op a b)"
  shows "Some t \<le> gwp (SPECc2 c op a b) Q"
  unfolding SPECc2_def 
  apply(refine_vcg \<open>-\<close>)
  using assms by auto

lemma SPECc2_refine':
  fixes TR :: "'h \<Rightarrow> ('h, enat) acost"
  shows "(op x y, op' x' y')\<in>R \<Longrightarrow> preserves_curr TR n  \<Longrightarrow> SPECc2 n op x y \<le> \<Down> R (\<Down>\<^sub>C TR (SPECc2 n op' x' y'))"
  unfolding SPECc2_def    
  apply(subst SPECT_refine_t) by (auto simp: preserves_curr_def timerefineA_cost_apply) 
  
lemma SPECc2_refine:
  "(op x y, op' x' y')\<in>R \<Longrightarrow> cost n (1::enat) \<le> TR n'  \<Longrightarrow> SPECc2 n op x y \<le> \<Down> R (\<Down>\<^sub>C TR (SPECc2 n' op' x' y'))"
  unfolding SPECc2_def    
  apply(subst SPECT_refine_t) apply auto
  apply(rule order.trans) apply (simp add: )
  apply(subst timerefineA_cost) by simp


subsection \<open>normalize blocks\<close>

text \<open>The idea of the following tactic is to normalize all straight line blocks,
      such that they have the form (doN { [ASSUMEs]; consumea T; [RETURNs]; FURTHER }.      
      To that end, it assumes that most operations are unfolded and only contain consumea, RETURN
      or consume (RETURN _) _. The RETURNs will be propagated with @{thm nres_bind_left_identity},
      ASSERTIONs will be pulled to the front, consumeas will be shrinked and assoc rule is applied.

      It then is assumed, that FURTHER statements in the concrete and abstract are in lock step.

      [ Then refine_block will split products, collect and discharge ASSUME statements, 
      pay for the consumea; and then stop at a FURTHER statement.
      One can then give "rules" that process the FURTHER statements. ]
      This process is way better done by refine_rcg!
      
      This allows that not only lockstep refinement is possible, but that by unfolding certain
      operations, their effects get 
        \<close>

lemma consumea_refine:
  fixes t :: "(_,enat) acost"
  shows "((), ()) \<in> R \<Longrightarrow> t \<le> timerefineA F t' \<Longrightarrow> consumea t \<le> \<Down> R (\<Down>\<^sub>C F (consumea t'))"
  unfolding consumea_def
  apply(rule SPECT_refine_t) by auto

lemma consumea_Id_refine:
  fixes t :: "(_,enat) acost"
  shows "t \<le> timerefineA F t' \<Longrightarrow> consumea t \<le> \<Down> Id (\<Down>\<^sub>C F (consumea t'))"
  unfolding consumea_def
  apply(rule SPECT_refine_t) by auto
    

lemma swap_consumea_ASSERT: "do { consumea t; ASSERT P; M:: ('c, ('d, enat) acost) nrest} = do {ASSERT P; consumea t; M}"
  apply(auto simp: pw_acost_eq_iff refine_pw_simps consumea_def)
  apply (metis zero_enat_def zero_le)
  using le_Suc_ex zero_enat_def by force


lemma consumea_0_noop:
  fixes m :: "('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows "do { consumea 0; m } = m"
  apply(auto simp: consumea_def bindT_def split: nrest.splits intro!: ext) 
  subgoal for x2 x apply(cases "x2 x") by auto
  done

thm refine0              

lemma forget_inresT_project_acos: "\<exists>t b. inresT (project_acost b (consumea tt)) x' t \<Longrightarrow> True"
  by simp

lemma forget_nofailT_consumea: "nofailT (consumea tt) \<Longrightarrow> True"
  by simp

lemmas normalize_inres_precond = forget_nofailT_consumea forget_inresT_project_acos
                                  inresT_consumea_D EX_inresT_SPECTONE_D

method normalize_blocks = (simp only: swap_consumea_ASSERT nres_acost_bind_assoc consume_alt consumea_shrink nres_bind_left_identity)
method refine_block uses rules = (drule normalize_inres_precond |split prod.splits | intro allI impI
                                    | rule refine0 consumea_Id_refine SPECT_refine_t bindT_refine_conc_time_my rules)
method refine_blocks uses rules = repeat_all_new \<open>refine_block rules: rules\<close>


subsection \<open>Simple bind rule with inres\<close>


lemma bindT_refine_conc_time_my_inres:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (\<Down>\<^sub>C E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'; inres m' x'\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (\<Down>\<^sub>C E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2) using assms
  by (auto dest: inres_if_inresT_acost)

lemma bindT_refine_conc_time_easy:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR E" " m \<le> \<Down>R' (\<Down>\<^sub>C E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R' \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (\<Down>\<^sub>C E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
  apply(rule bindT_refine_conc_time)
    apply fact
   apply fact
  apply(rule assms(3)) apply simp
  done

lemma bindT_refine_easy:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  fixes m' :: "('e2,('c2,enat)acost) nrest"
  assumes "wfR'' E" " m \<le> \<Down>R' (\<Down>\<^sub>C E m')"
  "(\<And>x x'. \<lbrakk>(x,x')\<in>R'\<rbrakk>
         \<Longrightarrow> f x \<le> \<Down> R (\<Down>\<^sub>C E (f' x') ))"
shows "bindT m f \<le>  \<Down> R (\<Down>\<^sub>C E (bindT m' f'))"
  apply(rule bindT_refine_conc_time2) using assms
  by (auto dest: inres_if_inresT_acost)





definition "project_all T =  (Sum_any (the_enat o the_acost T))"

lemma  project_all_is_Sumany_if_lifted:
  "f = lift_acost g \<Longrightarrow> project_all f = (Sum_any (the_acost g))"
  unfolding project_all_def lift_acost_def
  by simp


definition "norm_cost_tag a b = (a=b)"

lemma norm_cost_tagI: "norm_cost_tag a a"
  unfolding norm_cost_tag_def
  by simp


lemma the_acost_mult_eq_z_iff: "the_acost (n *m c) a = 0 \<longleftrightarrow> the_acost c a = 0 \<or> n=0" for n :: nat 
  apply (cases c)
  apply (auto simp: costmult_def)
  done
  
lemma finite_the_acost_mult_nonzeroI: "finite {a. the_acost c a \<noteq> 0} \<Longrightarrow> finite {a. the_acost (n *m c) a \<noteq> 0}" for n :: nat 
  apply (erule finite_subset[rotated])
  by (auto simp: the_acost_mult_eq_z_iff)
  
  


end