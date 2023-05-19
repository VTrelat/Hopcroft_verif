\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
section \<open>Basic Definitions\<close>
theory Sepref_Basic
imports 
  "../ds/LLVM_DS_NArray"
  "HOL-Eisbach.Eisbach"
  "Lib/Sepref_Misc"
  "Lib/Structured_Apply"
  "../nrest/NREST_Main"
  Sepref_Id_Op
  "../lib/More_Refine_Util"
begin

paragraph \<open>Summary\<close>
text \<open>This theory introduces the synthesishn predicate and basic rules for it.\<close>


paragraph \<open>Main Theorems/Definitions\<close>
text \<open>
\<^item> hn_refine: the synthesise predicate hnr
\<^item> hnr_bind: the hnr rule for @{term bindT}
\<^item> ht_from_hnr: with this rule one can extract a Hoare Triple from a hnr with special form: the
    running time may not depend on the result but only on the input parameters.
\<close>

no_notation i_ANNOT (infixr ":::\<^sub>i" 10)
no_notation CONST_INTF (infixr "::\<^sub>i" 10)

no_notation pred_K ("\<langle>_\<rangle>")


type_synonym assn = ll_assn
translations
  (type) "assn" \<leftharpoondown> (type) "llvm_amemory \<times> (char list, enat) acost \<Rightarrow> bool"


abbreviation (input) "RETURN \<equiv> RETURNT" (* FIXME ! *)
text \<open>
  In this theory, we define the basic concept of refinement 
  from a nondeterministic program specified in the 
  Isabelle Refinement Framework to an imperative deterministic one 
  specified in Imperative/HOL.
\<close>

subsection \<open>Values on Heap\<close>
text \<open>We tag every refinement assertion with the tag @{text hn_ctxt}, to
  avoid higher-order unification problems when the refinement assertion 
  is schematic.\<close>
definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  \<comment> \<open>Tag for refinement assertion\<close>
  where
  "hn_ctxt P a c \<equiv> P a c"

definition pure :: "('b \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> assn"
  \<comment> \<open>Pure binding, not involving the heap\<close>
  where "pure R \<equiv> (\<lambda>a c. \<up>((c,a)\<in>R))"

lemma pure_app_eq: "pure R a c = \<up>((c,a)\<in>R)" by (auto simp: pure_def)

lemma pure_eq_conv[simp]: "pure R = pure R' \<longleftrightarrow> R=R'"
  unfolding pure_def 
  apply (rule iffI)
  apply safe
  apply (meson pure_assn_eq_conv)
  apply (meson pure_assn_eq_conv)
  done

lemma pure_rel_eq_false_iff: "pure R x y = sep_false \<longleftrightarrow> (y,x)\<notin>R"
  by (auto simp: pure_def sep_algebra_simps)
    
lemma pure_part_pure[simp]: "pure_part (pure R a c) \<longleftrightarrow> (c,a)\<in>R"  
  by (simp add: pure_app_eq)
  
definition is_pure :: "(_ \<Rightarrow> _ \<Rightarrow> assn) \<Rightarrow> bool" where "is_pure P \<equiv> \<exists>P'. \<forall>x x'. P x x'=\<up>(P' x x')"
lemma is_pureI[intro?]: 
  assumes "\<And>x x'. P x x' = \<up>(P' x x')"
  shows "is_pure P"
  using assms unfolding is_pure_def by blast

lemma is_pureE:
  assumes "is_pure P"
  obtains P' where "\<And>x x'. P x x' = \<up>(P' x x')"
  using assms unfolding is_pure_def by blast

lemma pure_pure[simp]: "is_pure (pure P)"
  unfolding pure_def by rule blast
lemma pure_hn_ctxt[intro!]: "is_pure P \<Longrightarrow> is_pure (hn_ctxt P)"
  unfolding hn_ctxt_def[abs_def] .


definition the_pure :: "('b \<Rightarrow> 'a \<Rightarrow> assn) \<Rightarrow> ('a \<times> 'b) set" 
  where "the_pure P \<equiv> THE P'. \<forall>x x'. P x x'=\<up>((x',x)\<in>P')"

lemma the_pure_pure[simp]: "the_pure (pure R) = R"
  unfolding pure_def the_pure_def
  by (rule theI2[where a=R]) auto

lemma is_pure_alt_def: "is_pure R \<longleftrightarrow> (\<exists>Ri. \<forall>x y. R x y = \<up>((y,x)\<in>Ri))"
  unfolding is_pure_def
  apply auto
  apply (rename_tac P')
  apply (rule_tac x="{(x,y). P' y x}" in exI)
  apply auto
  done

lemma pure_the_pure[simp]: "is_pure R \<Longrightarrow> pure (the_pure R) = R"
  unfolding is_pure_alt_def pure_def the_pure_def
  apply (intro ext)
  apply clarsimp
  apply (rename_tac a c Ri)
  apply (rule_tac a=Ri in theI2)
  apply auto
  done
  
lemma is_pure_conv: "is_pure R \<longleftrightarrow> (\<exists>R'. R = pure R')"
  unfolding pure_def is_pure_alt_def by force

lemma is_pure_the_pure_id_eq[simp]: "is_pure R \<Longrightarrow> the_pure R = Id \<longleftrightarrow> R=pure Id"  
  by (auto simp: is_pure_conv)

lemma is_pure_iff_pure_assn: "is_pure P = (\<forall>x x'. sep_is_pure_assn (P x x'))"
  unfolding is_pure_def 
  apply (rule iffI)
  apply auto []
  apply (rule exI[where x="\<lambda>a c. pure_part (P a c)"])
  apply auto
  done


abbreviation "hn_val R \<equiv> hn_ctxt (pure R)"

lemma hn_val_unfold: "hn_val R a b = \<up>((b,a)\<in>R)"
  by (simp add: hn_ctxt_def pure_def)


definition "invalid_assn R x y \<equiv> \<up>(pure_part (R x y))"

abbreviation "hn_invalid R \<equiv> hn_ctxt (invalid_assn R)"

lemma invalidate_clone: "R x y = (invalid_assn R x y ** R x y)"
  unfolding invalid_assn_def
  by (metis (mono_tags, lifting) pure_partI pure_part_pure_eq pure_part_split_conj pure_true_conv sep.add.right_neutral sep_conj_commute sep_is_pure_assn_def)

lemma invalidate_clone': "hn_ctxt R x y = (hn_invalid R x y ** hn_ctxt R x y)"
  unfolding hn_ctxt_def using invalidate_clone .

lemma invalid_pure_recover: "invalid_assn (pure R) x y = pure R x y"
  unfolding invalid_assn_def pure_def by auto

lemma hn_invalidI: "hn_ctxt P x y s \<Longrightarrow> hn_invalid P x y = \<box>"
  by (auto simp: invalid_assn_def hn_ctxt_def pure_partI pure_true_conv)

lemma invalid_assn_cong[cong]:
  assumes "x\<equiv>x'"
  assumes "y\<equiv>y'"
  assumes "R x' y' \<equiv> R' x' y'"
  shows "invalid_assn R x y = invalid_assn R' x' y'"
  using assms unfolding invalid_assn_def
  by simp

subsection \<open>Constraints in Refinement Relations\<close>

definition rdomp :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" where
  "rdomp R a \<equiv> \<exists>h c. R a c h"

(*abbreviation "rdom R \<equiv> Collect (rdomp R)"*)

lemma rdomp_ctxt[simp]: "rdomp (hn_ctxt R) = rdomp R"
  by (simp add: hn_ctxt_def[abs_def])  

lemma rdomp_pure[simp]: "rdomp (pure R) a \<longleftrightarrow> a\<in>Range R"
  unfolding rdomp_def pure_def by (auto simp: pred_lift_extract_simps)

(*lemma rdom_pure[simp]: "rdom (pure R) = Range R"
  unfolding rdomp_def[abs_def] pure_def by (auto simp: pred_lift_extract_simps)
*)  

lemma rdomp_invalid_simp[simp]: "rdomp (invalid_assn P) x = rdomp P x"
  by (auto simp: invalid_assn_def rdomp_def pure_part_def pred_lift_extract_simps)

lemma Range_of_constraint_conv[simp]: "Range (A\<inter>UNIV\<times>C) = Range A \<inter> C"
  by auto


subsection \<open>Heap-Nres Refinement Calculus\<close>

subsubsection \<open>Definition of hnr\<close>

text \<open> Predicate that expresses refinement. Given a heap
  @{text "\<Gamma>"}, program @{text "c"} produces a heap @{text "\<Gamma>'"} and
  a concrete result that is related with predicate @{text "R"} to some
  abstract result from @{text "m"}\<close>

definition "hn_refine \<Gamma> c \<Gamma>' R m \<equiv>
  nofailT m \<longrightarrow>
  (\<forall>F s cr M. m = REST M \<longrightarrow>
      llSTATE (\<Gamma> \<and>* F) (s,cr) \<longrightarrow> 
      (\<exists>ra Ca. M ra \<ge> Some Ca
        \<and> wp c (\<lambda>r. llSTATE (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC)) (s, cr+Ca)
      )
  )"

lemma STATE_alt: "STATE \<alpha> P = (\<lambda>s. P (\<alpha> s))"
  by(auto simp: STATE_def)

(* For presentation in paper *)  
lemma "hn_refine \<Gamma> c \<Gamma>' R m = (
  nofailT m \<longrightarrow>
  (\<forall>F s cr M. m = REST M \<longrightarrow>
      (\<Gamma> \<and>* F) (llvm_\<alpha> s,cr) \<longrightarrow> 
      (\<exists>ra Ca. M ra \<ge> Some Ca
        \<and> wp c (\<lambda>r (s',cr'). (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC) (llvm_\<alpha> s',cr')) (s, cr+Ca)
      )
  ))"
  unfolding hn_refine_def STATE_alt lift_\<alpha>_cost_def ll_\<alpha>_def
  apply (simp split: prod.splits)
  by (smt case_prodD case_prodI2 wp_monoI)  

subsubsection \<open>Hnr Rules\<close>

lemma hn_refine_extract_pre_val: 
  "hn_refine (hn_val S xa xc ** \<Gamma>) c \<Gamma>' R m \<longleftrightarrow> ((xc,xa)\<in>S \<longrightarrow> hn_refine \<Gamma> c \<Gamma>' R m)"
  unfolding hn_refine_def hn_ctxt_def pure_def
  by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps htriple_extract_pre_pure)

lemma hn_refineI_SPECT: 
  assumes "llvm_htriple ($t ** \<Gamma>) c (\<lambda>r. \<Gamma>' ** R x r)"
  shows "hn_refine \<Gamma> c \<Gamma>' R (SPECT [x\<mapsto>t])"  
  apply (auto simp add: hn_refine_def STATE_alt)
  apply(rule exI[where x="t"]) apply simp
proof (goal_cases)
  fix F s cr
  assume "(\<Gamma> ** F) (ll_\<alpha> (s, cr))"
  then have "((\<Gamma> ** F) ** $(t)) (ll_\<alpha> (s, cr + t))"
  unfolding lift_\<alpha>_cost_def ll_\<alpha>_def
    apply(rule sep_conjI[where y="(0,t)"])
    subgoal by(simp add: time_credits_assn_def sep_algebra_simps)  
    subgoal by(simp add: sep_disj_enat_def sep_disj_acost_def sep_algebra_simps)  
    subgoal by(simp add: sep_disj_enat_def sep_disj_acost_def sep_algebra_simps)  
    done
  then have "(($t \<and>* \<Gamma>) \<and>* F) (ll_\<alpha> (s, cr + t))"
    by (simp add: sep_conj_c)

  from assms[unfolded htriple_def, rule_format, OF this]
  show "wp c (\<lambda>r s. (\<Gamma>' \<and>* R x r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + t)"
    by (simp add: sep_algebra_simps sep_conj_c) 
qed

lemma hn_refineI': 
  assumes "llvm_htriple \<Gamma> c (\<lambda>r. \<Gamma>' ** R x r)"
  shows "hn_refine \<Gamma> c \<Gamma>' R (RETURNT x)"  
  apply (auto simp add: hn_refine_def STATE_alt)
  apply(rule exI[where x=0]) apply simp
  using assms unfolding htriple_def
  by (simp add: sep_conj_c) 

lemma hn_refineI'': 
  assumes "\<Phi> \<Longrightarrow> llvm_htriple \<Gamma> c (\<lambda>r. \<Gamma>' ** R x r)"
  shows "hn_refine \<Gamma> c \<Gamma>' R (doN { _ \<leftarrow> ASSERT \<Phi>; RETURNT x })"  
  apply (auto simp add: hn_refine_def STATE_alt ASSERT_def iASSERT_def)
  apply(rule exI[where x=0]) apply simp
  using assms unfolding htriple_def
  by (simp add: sep_conj_c) 

lemma hn_refineI[intro]: 
  assumes "\<And>F s cr M. \<lbrakk> m = REST M; (\<Gamma>**F) (ll_\<alpha>(s,cr)) \<rbrakk>
          \<Longrightarrow> (\<exists>ra Ca. M ra \<ge> Some Ca \<and>
                     (wp c (\<lambda>r s.  (\<Gamma>' ** R ra r ** F ** GC) (ll_\<alpha> s)) (s,cr+Ca)))"
  shows "hn_refine \<Gamma> c \<Gamma>' R m"  
  apply (auto simp add: hn_refine_def STATE_alt)  
  apply(rule assms) by auto

lemma hnr_vcgI_aux: 
  assumes "\<And>F s cr M. \<lbrakk> m = REST M; llSTATE (\<Gamma>**F) (s,cr) \<rbrakk>
          \<Longrightarrow> (\<exists>ra Ca. M ra \<ge> Some Ca \<and>
                     EXTRACT (wp c (\<lambda>r. POSTCOND ll_\<alpha> (\<Gamma>' ** R ra r ** F ** GC)) (s,cr+Ca)))"
  shows "hn_refine \<Gamma> c \<Gamma>' R m"  
  using assms by (simp add: hn_refine_def vcg_tag_defs) 


lemma hnr_vcg_aux1:
  "P (s, cr) \<Longrightarrow> (P \<and>* $Ca) (s, cr + Ca)"
  apply(rule sep_conjI[where y="(0,Ca)"])
     apply (simp_all add: time_credits_assn_def sep_disj_prod_def sep_algebra_simps)
  by (auto simp add: sep_disj_acost_def sep_disj_enat_def sep_algebra_simps)

lemma hnr_vcg_aux2:
  "(P \<and>* $(lift_acost Ca)) (s, cr + (lift_acost Ca)) \<Longrightarrow> P (s, cr)"
  apply(drule sep_conjD) apply (auto simp:  lift_acost_def time_credits_assn_def sep_algebra_simps)
  by (metis add.commute cost_ecost_add_minus_cancel lift_acost_def) 

lemma hnr_vcgI: 
  assumes "\<And>F s cr M. \<lbrakk> m = REST M \<rbrakk>
          \<Longrightarrow> (\<exists>ra Ca. (llSTATE (\<Gamma>**F**$(lift_acost Ca)) (s,cr+(lift_acost Ca)) \<longrightarrow> (M ra \<ge> Some (lift_acost Ca) \<and>
                     EXTRACT (wp c (\<lambda>r. POSTCOND ll_\<alpha> (\<Gamma>' ** R ra r ** F ** GC)) (s,cr+lift_acost Ca)))))"
  shows "hn_refine \<Gamma> c \<Gamma>' R m"  
  apply(rule hnr_vcgI_aux)
  subgoal premises prems for F s cr M
    using assms[OF prems(1), where F=F and s=s and cr=cr] apply -
    apply(elim exE) 
    subgoal for ra Ca apply(rule exI[where x=ra])
      apply(rule exI[where x="lift_acost Ca"])
      apply(erule mp)
      using  prems(2)   
      unfolding STATE_def ll_\<alpha>_def lift_\<alpha>_cost_def apply simp
      apply(rule hnr_vcg_aux1[of "(\<Gamma> \<and>* F)", simplified]) .
    done
  done




lemma hn_refine_consume_return:
  "hn_refine \<Gamma> c \<Gamma>' R m =
  nofailT m \<longrightarrow>
  (\<forall>F s cr . 
      llSTATE (\<Gamma> \<and>* F) (s,cr) \<longrightarrow> 
      (\<exists>ra Ca. consume (RETURNT ra) Ca \<le> m
        \<and> wp c (\<lambda>r. llSTATE (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC)) (s, cr+Ca)
      )
  )"
  unfolding hn_refine_def
  apply auto 
  apply(cases m)
   apply auto
  subgoal premises p for F x cr x2
    using p(2)[rule_format, OF p(1)]
    apply safe
    subgoal for ra Ca
      apply(rule exI[where x=ra])
      apply(rule exI[where x=Ca])
      unfolding consume_def RETURNT_def apply simp
      by (auto simp: le_fun_def)
    done
  done


lemma hn_refineD:
  assumes "hn_refine \<Gamma> c \<Gamma>' R m"
  assumes "m = REST M" "(\<Gamma> \<and>* F) (ll_\<alpha> (s,cr))"
  shows  "(\<exists>ra Ca. M ra \<ge> Some Ca
        \<and> wp c (\<lambda>r s. (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr+Ca)
      )"
  using assms by(auto simp: hn_refine_def STATE_alt nofailT_def)


lemma hn_refine_preI: 
  assumes "\<And>h. \<Gamma> h \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  apply(rule hn_refineI) 
  using sep_conjD assms  hn_refineD  by blast 

lemma hn_refine_nofailI: 
  assumes "nofailT a \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"  
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  using assms by (auto simp: hn_refine_def)

lemma hn_refine_false[simp]: "hn_refine sep_false c \<Gamma>' R m"
  by rule auto

lemma hnr_FAIL[simp, intro!]: "hn_refine \<Gamma> c \<Gamma>' R FAILT"
  by rule auto
thm sep_conj_impl1 wp_monoI  frame_rule


(* Consequence rule for hn-refine *)
(* TODO: Move *)
lemma STATE_rev_mp: "STATE \<alpha> P s \<Longrightarrow> P\<turnstile>P' \<Longrightarrow> STATE \<alpha> P' s"
  unfolding STATE_def entails_def by blast

(* TODO: Move *)
lemma wp_post_cons: "wp m (\<lambda>r. STATE \<alpha> (Q r)) s \<Longrightarrow> (\<And>r. Q r \<turnstile> Q' r) \<Longrightarrow> wp m (\<lambda>r. STATE \<alpha> (Q' r)) s"  
  by (simp add: STATE_rev_mp wp_monoI)
  
lemma hn_refine_cons_complete:
  assumes R: "hn_refine P' c Q R m"
  assumes I: "P\<turnstile>P'"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes LE: "m\<le>m'"
  shows "hn_refine P c Q' R' m'"
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (drule STATE_rev_mp)
  apply (sep_drule I; rule entails_refl)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated])
  apply simp
  apply (elim exE conjE)
  apply (intro exI conjI)
  apply (rule order_trans, assumption, erule le_funD)
  apply (erule wp_post_cons)
  apply (sep_drule I')
  apply (sep_drule R')
  apply (rule ENTAILSD)
  apply fri
  done
  
lemmas hn_refine_cons = hn_refine_cons_complete[OF _ _ _ _ order_refl]  
lemmas hn_refine_cons_pre = hn_refine_cons_complete[OF _ _ entails_refl entails_refl order_refl]  
lemmas hn_refine_cons_post = hn_refine_cons_complete[OF _ entails_refl _ entails_refl order_refl]  
lemmas hn_refine_cons_res = hn_refine_cons_complete[OF _ entails_refl entails_refl _ order_refl]  
lemmas hn_refine_ref = hn_refine_cons_complete[OF _ entails_refl entails_refl entails_refl]


lemma zz: "(P \<and>* Q) s \<Longrightarrow> P \<turnstile> P' ** F \<Longrightarrow> (P' ** Q ** F) s"
  unfolding entails_def   
  apply(subst (2) sep_conj_commute)
  apply(subst sep_conj_assoc[symmetric])
  apply (drule sep_conjD)
  apply safe
  apply(rule sep_conjI)
  by(auto simp add: sep_algebra_simps ) 

thm frame_rule
lemma hn_refine_frame:
  assumes hnr: "hn_refine P' c Q' R m"
  assumes ent: "P \<turnstile> P' ** F"
  shows "hn_refine P c (Q' ** F) R m"
  apply (rule hn_refineI)
  subgoal for Fa s cr M
    apply(drule zz[OF _ ent])
    apply(drule hnr[THEN hn_refineD, where F="Fa**F"])
     apply simp
    apply(auto simp add: sep_conj_aci sep_algebra_simps pred_lift_extract_simps) 
    done
  done 

lemma hn_refine_frame': "hn_refine \<Gamma> c \<Gamma>' R m \<Longrightarrow> hn_refine (\<Gamma>**F) c (\<Gamma>'**F) R m"  
  by (simp add: hn_refine_frame) 
lemma hn_refine_frame'': "hn_refine \<Gamma> c \<Gamma>' R m \<Longrightarrow> hn_refine (F**\<Gamma>) c (F**\<Gamma>') R m"  
  using hn_refine_frame' sep_conj_c by smt 
 

lemma hn_refine_augment_res:
  assumes A: "hn_refine \<Gamma> f \<Gamma>' R g"
  assumes B: "g \<le>\<^sub>n SPEC \<Phi> t"
  shows "hn_refine \<Gamma> f \<Gamma>' (\<lambda>a c. R a c ** \<up>(\<Phi> a)) g"
  apply (rule hn_refineI)
proof -
  fix F s cr M
  assume g: "g = SPECT M" and h:"(\<Gamma> \<and>* F) (ll_\<alpha> (s, cr))"

  from A[THEN hn_refineD, OF this] obtain ra Ca
    where s: "Some Ca \<le> M ra"
      and w: "wp f (\<lambda>r s. (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)"
    by blast

  from B g have "\<And>x. M x \<le> (if \<Phi> x then Some (t x) else None)"
    by(auto simp: le_or_fail_def SPEC_def le_fun_def)
  from this[of ra] have *: "\<Phi> ra"
    using s apply(auto split: if_splits simp: less_eq_option_None_is_None )
    using less_eq_option_Some_None order.trans by blast

  show "\<exists>ra Ca.
              Some Ca \<le> M ra \<and>
              wp f (\<lambda>r s. (\<Gamma>' \<and>* (R ra r \<and>* \<up>\<Phi> ra) \<and>* F \<and>* GC) (ll_\<alpha> s))
               (s, cr + Ca)"
    apply(rule exI[where x=ra])
    apply(rule exI[where x=Ca])
    apply safe
     apply fact
    apply(simp add: pure_def pred_lift_def * sep_algebra_simps)
    by fact
qed
  
subsection \<open>Product Types\<close>
text \<open>Some notion for product types is already defined here, as it is used 
  for currying and uncurrying, which is fundamental for the sepref tool\<close>
definition prod_assn :: "('a1\<Rightarrow>'c1\<Rightarrow>assn) \<Rightarrow> ('a2\<Rightarrow>'c2\<Rightarrow>assn) 
  \<Rightarrow> 'a1*'a2 \<Rightarrow> 'c1*'c2 \<Rightarrow> assn" where
  "prod_assn P1 P2 a c \<equiv> case (a,c) of ((a1,a2),(c1,c2)) \<Rightarrow>
  P1 a1 c1 ** P2 a2 c2"

notation prod_assn (infixr "\<times>\<^sub>a" 70)
  
lemma prod_assn_pure_conv[simp]: "prod_assn (pure R1) (pure R2) = pure (R1 \<times>\<^sub>r R2)"
  by (auto simp: pure_def prod_assn_def pred_lift_extract_simps intro!: ext)

lemma prod_assn_pair_conv[simp]: 
  "prod_assn A B (a1,b1) (a2,b2) = (A a1 a2 ** B b1 b2)"
  unfolding prod_assn_def by auto

lemma prod_assn_true[simp]: "prod_assn (\<lambda>_ _. sep_true) (\<lambda>_ _. sep_true) = (\<lambda>_ _. sep_true)"
  by (auto intro!: ext simp: hn_ctxt_def prod_assn_def)

  
subsection "Convenience Lemmas"

lemma hn_refine_guessI:
  assumes "hn_refine P f P' R f'"
  assumes "f=f_conc"
  shows "hn_refine P f_conc P' R f'"
  \<comment> \<open>To prove a refinement, first synthesize one, and then prove equality\<close>
  using assms by simp


lemma imp_correctI:
  assumes R: "hn_refine \<Gamma> c \<Gamma>' R a"
  assumes C: "a \<le> SPECT (emb \<Phi> T)"
  shows "llvm_htriple (\<Gamma> ** $T) c (\<lambda>r'. EXS r. \<Gamma>' ** R r r' ** \<up>(\<Phi> r))" (*
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF R])
  apply (rule le_RES_nofailI[OF C])
  apply (force simp: sep_algebra_simps pred_lift_extract_simps dest: order_trans[OF _ C])
  done *) oops

lemma hnr_pre_ex_conv: 
  shows "hn_refine (EXS x. \<Gamma> x) c \<Gamma>' R a \<longleftrightarrow> (\<forall>x. hn_refine (\<Gamma> x) c \<Gamma>' R a)"
proof -
  have *: "\<And>x \<Gamma> F s cr. llSTATE (\<Gamma> x \<and>* F) (s, cr) \<Longrightarrow> llSTATE ((\<lambda>s. \<exists>x. \<Gamma> x s) \<and>* F) (s, cr)" 
    by (metis (no_types, lifting) STATE_def sep_conj_impl1)  
  have **: "\<And>x \<Gamma> F s cr.  llSTATE ((\<lambda>s. \<exists>x. \<Gamma> x s) \<and>* F) (s, cr) \<Longrightarrow> \<exists>x. llSTATE (\<Gamma> x \<and>* F) (s, cr)" 
    by (smt STATE_def sep_conjE sep_conjI)

  show ?thesis
    unfolding hn_refine_def
    apply (safe; clarsimp?)
    subgoal premises prems for x F s cr
      using prems(1)[rule_format] *[of \<Gamma>, OF prems(3)] by blast
    subgoal premises prems for x F s cr
      using prems(1)[rule_format] **[of \<Gamma>, OF prems(3)] by blast
    done
qed

lemma hnr_pre_pure_conv:  
  shows "hn_refine (\<up>P ** \<Gamma>) c \<Gamma>' R a \<longleftrightarrow> (P \<longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a)"
  unfolding hn_refine_def
  apply (auto simp: sep_algebra_simps htriple_extract_pre_pure STATE_def)
  using pred_lift_extract_simps(2) by blast

lemma hn_refine_split_post:
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c (\<Gamma>' or \<Gamma>'') R a"
  apply (rule hn_refine_cons_post[OF assms])
  apply (auto simp: entails_def)
  done

lemma hn_refine_post_other: 
  assumes "hn_refine \<Gamma> c \<Gamma>'' R a"
  shows "hn_refine \<Gamma> c (\<Gamma>' or \<Gamma>'') R a"
  apply (rule hn_refine_cons_post[OF assms])
  apply (auto simp: entails_def)
  done


subsubsection \<open>Return\<close>

lemma hnr_RETURN_pass:
  "hn_refine (hn_ctxt R x p) (return p) (hn_invalid R x p) R (RETURNT x)"
  \<comment> \<open>Pass on a value from the heap as return value\<close>
  apply (subst invalidate_clone')
  unfolding hn_ctxt_def
  apply(rule hnr_vcgI_aux)
  apply(simp add: ecost_le_zero) 
  apply vcg
  done

lemma hnr_RETURN_pure:
  assumes "(c,a)\<in>R"
  shows "hn_refine emp (return c) emp (pure R) (RETURNT a)"
  \<comment> \<open>Return pure value\<close>
  apply(rule hnr_vcgI_aux) using assms
  apply(simp add: ecost_le_zero) 
  supply [simp] = pure_def
  by vcg
  
subsubsection \<open>Assertion\<close>

lemma hnr_ASSERT:
  assumes "\<Phi> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R c'"
  shows "hn_refine \<Gamma> c \<Gamma>' R (do { ASSERT \<Phi>; c'})"
  using assms
  apply (cases \<Phi>)
  by auto

subsubsection \<open>Bind\<close>
lemma bind_det_aux:
  fixes m :: "(_,(_,enat)acost) nrest"
  shows  "\<lbrakk> RETURN x \<le> m; RETURN y \<le> f x \<rbrakk> \<Longrightarrow> RETURN y \<le> m \<bind> f"
  apply (rule order_trans[rotated])
  apply (rule bindT_acost_mono')
  apply assumption
  apply (rule order_refl)
  apply simp
  done
  
definition "MK_FREE R f \<equiv> \<forall>a c. llvm_htriple (R a c) (f c) (\<lambda>_::unit. \<box>)"  

lemma MK_FREEI[intro?]: "\<lbrakk>\<And>a c. llvm_htriple (R a c) (f c) (\<lambda>_. \<box>)\<rbrakk> \<Longrightarrow> MK_FREE R f"
  by (auto simp: MK_FREE_def)

lemma MK_FREED: "MK_FREE R f \<Longrightarrow> llvm_htriple (R a c) (f c) (\<lambda>_. \<box>)"
  by (auto simp: MK_FREE_def)
  
lemma mk_free_pure: "MK_FREE (pure R) (\<lambda>_. return ())"
  apply rule unfolding pure_def
  by vcg

(*
  TODO: Should be synthesized once relations are known
*)
lemma mk_free_is_pure: "is_pure A \<Longrightarrow> MK_FREE A (\<lambda>_. return ())"
  apply rule unfolding pure_def is_pure_def
  by vcg

  
  
lemma mk_free_invalid: "MK_FREE (invalid_assn R) (\<lambda>_. return ())"
  apply rule unfolding invalid_assn_def
  by vcg


lemma mk_free_pair: 
  assumes "MK_FREE R\<^sub>1 f\<^sub>1" 
  assumes "MK_FREE R\<^sub>2 f\<^sub>2"  
  shows "MK_FREE (R\<^sub>1\<times>\<^sub>aR\<^sub>2) (\<lambda>(c\<^sub>1,c\<^sub>2). doM {f\<^sub>1 c\<^sub>1; f\<^sub>2 c\<^sub>2})"
  supply [vcg_rules] = assms[THEN MK_FREED]
  apply (rule)
  by vcg

lemma acost_plus_assoc: "a + (b + c) = (a + b) + (c::(char list, enat) acost)"
  apply(cases a; cases b; cases c) by auto

lemma "le_cost_ecost c (cr + Ca) \<Longrightarrow> le_cost_ecost c (cr + (Ca + Ca'))"
  apply(simp add: acost_plus_assoc) apply(rule cost_ecost_add_increasing2) .
  
lemma hnr_bind:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURNT x \<le> m \<Longrightarrow> hn_refine (hn_ctxt Rh x x' ** \<Gamma>1) (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<turnstile> hn_ctxt Rx x x' ** \<Gamma>'"
  assumes MKF: "MK_FREE Rx fr"
  shows "hn_refine \<Gamma> (doM {x\<leftarrow>m'; r \<leftarrow> f' x; fr x; return r}) \<Gamma>' R (m\<bind>f)"
  apply rule
  supply [vcg_rules] = D1[THEN hn_refineD]
  supply [simp] = pw_bindT_nofailT
proof goal_cases
  case C: (1 F s cr M)
  hence "nofailT (m \<bind> f)" by auto
  hence nfm: "nofailT m" and nff: "\<And>x t b. inresT (project_acost b m) x t \<Longrightarrow> nofailT (f x)"
    by (auto simp: g_pw_bindT_nofailT)

  from nfm obtain Mm where M: "m = SPECT Mm" by fastforce

  from D1[THEN hn_refineD, OF M C(2)] obtain ra Ca where Mra: "Some Ca \<le> Mm ra"
    and wp1: "wp m' (\<lambda>r s. (\<Gamma>1 \<and>* Rh ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)"
    by blast
  term "(run m' s)"
  from wp1[unfolded wp_def mwp_def] obtain s' r c
    where mH: "(\<Gamma>1 \<and>* Rh ra r \<and>* F \<and>* GC) (ll_\<alpha> (s', minus_ecost_cost (cr + Ca) c))"
      and mle: "le_cost_ecost c (cr + Ca)"
      and r1: "run m' s = SUCC r c s'"
    by (auto split: mres.splits)

  from M Mra have ram: "RETURNT ra \<le> m" apply(auto simp: le_fun_def RETURNT_def)
    by (simp add: dual_order.trans needname_nonneg)
  have noff: "nofailT (f ra)" apply(rule nff[where t=0]) using Mra M unfolding inresT_def
    by (metis RETURNT_alt \<open>RETURNT ra \<le> m\<close> project_acost_RETURNT pw_acost_le_project zero_enat_def)
  then obtain fM where fMra: "f ra = SPECT fM" by fastforce

  from mH have mH': "((Rh ra r \<and>* \<Gamma>1) \<and>* F \<and>* GC) (ll_\<alpha> (s', minus_ecost_cost (cr + Ca) c))"
    by (simp add: sep_conj_c)

  from D2[OF ram, THEN hn_refineD, OF fMra, of r, unfolded hn_ctxt_def, OF mH'] obtain ra' Ca'
    where fMra': "Some Ca' \<le> fM ra'"
      and wp2: "wp (f' r) (\<lambda>rb s. (\<Gamma>2 ra r \<and>* R ra' rb \<and>* (F \<and>* GC) \<and>* GC) (ll_\<alpha> s))
                      (s', minus_ecost_cost (cr + Ca) c + Ca')"
    by blast

  from wp2[unfolded wp_def mwp_def] obtain s'' r' c'
    where mH2: "(\<Gamma>2 ra r \<and>* R ra' r' \<and>* F \<and>* GC) (ll_\<alpha> (s'', minus_ecost_cost (minus_ecost_cost (cr + Ca) c + Ca') c'))"
      and mle2: "le_cost_ecost c' (minus_ecost_cost (cr + Ca) c + Ca')"
      and r2: "run (f' r) s' = SUCC r' c' s''"
    by (auto split: mres.splits)

  from mH2 IMP have mH2': "(Rx ra r \<and>* (\<Gamma>' \<and>* R ra' r' \<and>* F \<and>* GC))
                            (ll_\<alpha> (s'', minus_ecost_cost (minus_ecost_cost (cr + Ca) c + Ca') c'))"
    by (smt entails_def hn_ctxt_def sep.mult_assoc sep_conj_impl1)

  note wp3 = MKF[unfolded MK_FREE_def  htriple_def, rule_format, OF mH2']

  from wp3[unfolded wp_def mwp_def] obtain s''' r'' c''
    where mH3: "(GC \<and>* \<Gamma>' \<and>* R ra' r' \<and>* F \<and>* GC) (ll_\<alpha> (s''', minus_ecost_cost (minus_ecost_cost (minus_ecost_cost (cr + Ca) c + Ca') c') c''))"
      and mle3: "le_cost_ecost c'' (minus_ecost_cost (minus_ecost_cost (cr + Ca) c + Ca') c')"
      and r3: "run (fr r) s'' = SUCC r'' c'' s'''"
    by (auto split: mres.splits)
  from mH3 have  mH3': "(\<Gamma>' \<and>* R ra' r' \<and>* F \<and>* GC) (ll_\<alpha> (s''', minus_ecost_cost (minus_ecost_cost (minus_ecost_cost (cr + Ca) c + Ca') c') c''))"
    by (metis (no_types, lifting) GC_move_left(3) sep_conj_left_commute)
  
  from Mra fMra' obtain Car Car' where PF: "Mm ra = Some Car" "fM ra' = Some Car'" by fastforce+

  have "Some (Ca+Ca') \<le> Some (Car+Car')"
    using PF Mra fMra' add_mono by fastforce
  also
  from  C(1) fMra M have
    "Some ((Car+Car')) \<le> M ra' "
    unfolding bindT_def  apply simp apply(drule nrest_Sup_SPECT_D[where x=ra'])
    apply simp apply(rule Sup_upper) apply auto
    apply(rule exI[where x="(map_option ((+) (Car)) \<circ> fM)"])
    using PF
    apply simp apply(rule exI[where x=ra]) apply(rule exI[where x="Car"])
    by auto
  finally have "Some (Ca+Ca') \<le> M ra' " .

  have **: "minus_ecost_cost (cr + Ca) c + Ca'
      = minus_ecost_cost (cr + (Ca + Ca')) c"
    using mle
    by (simp add: acost_plus_assoc cost_ecost_minus_add_assoc2)

  show ?case
    apply(rule exI[where x=ra'])
    apply(rule exI[where x="Ca+Ca'"])
    apply safe
    subgoal apply fact done
    apply(simp add: wp_bind)
    apply(subst wp_def) apply(subst mwp_def)
    apply (simp add: r1)
    apply(simp add: wp_bind)
    apply(subst wp_def) apply(subst mwp_def)
    apply (simp add: r2)
    apply(simp add: wp_bind)
    apply(subst wp_def) apply(subst mwp_def)
    apply (simp add: r3)
    apply(simp add: wp_return)
    apply safe
    subgoal using mH3' unfolding ** .
    subgoal using mle3 unfolding ** .
    subgoal using mle2 unfolding ** .
    subgoal using mle apply(simp add: acost_plus_assoc) apply(rule cost_ecost_add_increasing2) .
    done
qed  
 
  

text \<open>Version fro manual synthesis, if freeing of bound variable has been inserted manually\<close>
lemma hnr_bind_manual_free:
  fixes m' :: "_ llM"
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURN x \<le> m \<Longrightarrow> hn_refine (hn_ctxt Rh x x' ** \<Gamma>1) (f' x') (\<Gamma>') R (f x)"
  shows "hn_refine \<Gamma> (m'\<bind>f') \<Gamma>' R (m\<bind>f)"
  apply(rule hnr_bind[OF D1 _ entails_refl, of f' "\<lambda>x x'. hn_invalid Rh x x'" \<Gamma>' R f "\<lambda>_. return ()", simplified])
  subgoal for x x' apply(subst invalidate_clone')  
    apply(drule D2[THEN hn_refine_frame'', where F=" (hn_invalid Rh) x x'", of _ x']) unfolding hn_ctxt_def using sep_conj_ac by smt
  subgoal unfolding MK_FREE_def invalid_assn_def hn_ctxt_def by vcg
  done

subsubsection \<open>Recursion\<close>
(*
definition "hn_rel P m \<equiv> \<lambda>r. EXS x. \<up>(RETURN x \<le> m) ** P x r"

lemma hn_refine_alt: "hn_refine Fpre c Fpost P m \<equiv> nofailT m \<longrightarrow>
  llvm_htriple Fpre c (\<lambda>r. hn_rel P m r ** Fpost)"
  apply (rule eq_reflection)
  unfolding hn_refine_def hn_rel_def
  by (auto simp: sep_conj_commute)
*)

term "Monad.REC  "
find_theorems "Monad.REC"
  
lemma hnr_RECT:
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px ** F) (cf px) (F' ax px) Ry (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px ** F) (cB cf px) (F' ax px) Ry (aB af ax)"
  assumes M: "(\<And>x. M.mono_body (\<lambda>f. cB f x))"
  shows "hn_refine 
    (hn_ctxt Rx ax px ** F) (Monad.REC cB px) (F' ax px) Ry (RECT aB ax)"
  unfolding RECT_flat_gfp_def Monad.REC_def
proof (simp, intro conjI impI)
  assume "mono2 aB"
  hence "flatf_mono_ge aB" by (simp add: trimonoD_flatf_ge)
  have "\<forall>ax px. 
    hn_refine (hn_ctxt Rx ax px ** F) (M.fixp_fun cB px) (F' ax px) Ry 
      (flatf_gfp aB ax)"
      
    apply (rule flatf_ord.fixp_induct[OF _ \<open>flatf_mono_ge aB\<close>])  

    apply (rule flatf_admissible_pointwise)
    apply simp

    apply (auto simp: hn_refine_def) []

    apply clarsimp
    apply (subst M.mono_body_fixp[of cB, OF M])
    apply (rule S)
    apply blast
    done
  thus "hn_refine (hn_ctxt Rx ax px ** F) (M.fixp_fun cB px) (F' ax px) Ry (flatf_gfp aB ax)" 
    by simp
qed

subsubsection \<open>Merging\<close>

definition "MERGE \<Gamma>1 f1 \<Gamma>2 f2 \<Gamma>' \<equiv> llvm_htriple \<Gamma>1 f1 (\<lambda>_. \<Gamma>') \<and> llvm_htriple \<Gamma>2 f2 (\<lambda>_. \<Gamma>')"

lemma MERGED: 
  assumes "MERGE \<Gamma>1 f1 \<Gamma>2 f2 \<Gamma>'"
  shows "llvm_htriple \<Gamma>1 f1 (\<lambda>_. \<Gamma>')" "llvm_htriple \<Gamma>2 f2 (\<lambda>_. \<Gamma>')"
  using assms by (auto simp: MERGE_def)

lemma MERGEI[intro?]: 
  assumes "llvm_htriple \<Gamma>1 f1 (\<lambda>_. \<Gamma>')" "llvm_htriple \<Gamma>2 f2 (\<lambda>_. \<Gamma>')"
  shows "MERGE \<Gamma>1 f1 \<Gamma>2 f2 \<Gamma>'"
  using assms by (auto simp: MERGE_def)

definition "MERGE1 R1 f1 R2 f2 R' \<equiv> \<forall> a c. MERGE (R1 a c) (f1 c) (R2 a c) (f2 c) (R' a c)"

lemma MERGE1I[intro?]: 
  assumes "\<And>a c. llvm_htriple (R1 a c) (f1 c) (\<lambda>_. R' a c)" 
      and "\<And>a c. llvm_htriple (R2 a c) (f2 c) (\<lambda>_. R' a c)"
  shows "MERGE1 R1 f1 R2 f2 R'"
  using assms by (auto simp: MERGE1_def MERGE_def)

lemma MERGE1D: 
  assumes "MERGE1 R1 f1 R2 f2 R'"
  shows "\<And>a c. llvm_htriple (R1 a c) (f1 c) (\<lambda>_. R' a c)" 
    and "\<And>a c. llvm_htriple (R2 a c) (f2 c) (\<lambda>_. R' a c)"
  using assms by (auto simp: MERGE1_def MERGE_def)
  
lemma MERGE_STAR:
  assumes "MERGE1 R1 f1 R2 f2 R'" "MERGE \<Gamma>1 fs1 \<Gamma>2 fs2 \<Gamma>'" 
  shows "MERGE (hn_ctxt R1 a c ** \<Gamma>1) (doM {f1 c;fs1}) (hn_ctxt R2 a c ** \<Gamma>2) (doM {f2 c;fs2}) (hn_ctxt R' a c ** \<Gamma>')"
proof -
  note [vcg_rules] = MERGE1D[OF assms(1)] MERGED[OF assms(2)]

  show ?thesis unfolding hn_ctxt_def by rule vcg
qed  

lemma MERGE_triv: "MERGE \<Gamma> (return ()) \<Gamma> (return ()) \<Gamma>"
  apply (rule) unfolding FRI_END_def by vcg

lemma MERGE_END: "MERGE FRI_END (return ()) FRI_END (return ()) \<box>"
  apply (rule) unfolding FRI_END_def by vcg

lemma MERGE1_eq: "MERGE1 P (\<lambda>_. return ()) P (\<lambda>_. return ()) P"  
  by rule vcg
  
lemma MERGE1_invalids: 
  assumes "MK_FREE R f"  
  shows "MERGE1 (invalid_assn R) (\<lambda>_. return ()) R f (invalid_assn R)" (is ?left)
    and "MERGE1 R f (invalid_assn R) (\<lambda>_. return ()) (invalid_assn R)" (is ?right)
proof -
  note [vcg_rules] = MK_FREED[OF assms]

  show ?left
    apply rule
    apply vcg []
    apply (subst invalidate_clone[of R])
    unfolding invalid_assn_def
    by vcg
    
  show ?right
    apply rule
    apply (subst invalidate_clone[of R])
    unfolding invalid_assn_def
    by vcg
    
qed  



subsubsection \<open>Extracting a Hoare Triple from a HNR rule\<close>

(* TODO: rework and structure this proof *)
lemma ht_from_hnr: 
  assumes "hn_refine \<Gamma> c \<Gamma>' R (timerefine E (do {_ \<leftarrow> ASSERT \<Phi>; SPECT (emb Q T) }))"
  and "\<Phi>"
shows " llvm_htriple ($(timerefineA E T) ** \<Gamma>) c (\<lambda>r. (EXS ra. \<up>(Q ra) ** R ra r) ** \<Gamma>')"
proof -

  from  assms(1)[unfolded hn_refine_def]
  have *: "\<And>F s cr. llSTATE (\<Gamma> \<and>* F) (s, cr) \<Longrightarrow> (\<exists>ra Ca. Some Ca \<le> (emb Q (timerefineA E T)) ra \<and> wp c (\<lambda>r. llSTATE (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC)) (s, cr + Ca))"
    using assms(2) apply (simp add: nofailT_timerefine)
    unfolding SPEC_REST_emb'_conv[symmetric]
    apply (simp add: SPEC_timerefine_conv)
    unfolding SPEC_REST_emb'_conv by auto

  show ?thesis
    unfolding htriple_def
    apply safe
  proof -
    fix F a b
    assume "(($timerefineA E T \<and>* \<Gamma>) \<and>* F) (ll_\<alpha> (a, b))"
    then have G:"($timerefineA E T ** (\<Gamma> ** F)) (ll_\<alpha> (a, b))"
      by(simp add: sep_conj_aci)
    obtain b' where  G':"(\<Gamma> ** F) (ll_\<alpha> (a, b'))" and b: "b= b'+ (timerefineA E T)"
      using G[THEN sep_conjD] apply (simp add: dollar_aux_conv )
      unfolding ll_\<alpha>_def lift_\<alpha>_cost_def
      apply auto
      using c_simps(5) by blast
     from *[unfolded STATE_def,OF G'] obtain ra Ca where
         i:  "Some Ca \<le> emb Q (timerefineA E T) ra" 
        and  wp: "wp c (\<lambda>r s. (\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (a, b' + Ca)"
       by auto
     from i have Q: "Q ra" unfolding emb'_def by (auto split: if_splits)   
     from i have "\<exists>delta. (timerefineA E T) = delta + Ca"
       apply(intro get_delta) by(auto simp: emb'_def split: if_splits)
     then obtain delta where tet: "(timerefineA E T) = delta + Ca" by blast

     have b_alt: "b = (b' + Ca) + delta"
       unfolding b tet 
       by (simp add: add.commute c_simps(6))


     show "wp c (\<lambda>r s'. ((((\<lambda>s. \<exists>x. (\<up>Q x \<and>* R x r) s) \<and>* \<Gamma>') \<and>* GC) \<and>* F) (ll_\<alpha> s')) (a, b)"
       unfolding b_alt 
       apply(rule wp_monoI)
        apply(rule wp_time_mono)
        apply(rule wp)
       apply safe
       apply auto
       unfolding ll_\<alpha>_def lift_\<alpha>_cost_def
       apply simp
     proof -
       fix r a cc'
       assume l: "(\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC) (llvm_\<alpha> a, cc') "
       have "((\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC)\<and>* GC) ((llvm_\<alpha> a, cc')+(0,delta))"
         apply(rule sep_conjI[where y="(0,delta)"])
            apply (rule l)
         subgoal unfolding GC_def SND_def by auto
         subgoal apply (auto simp: sep_disj_prod_def ) 
           using sep_disj_acost_def sep_disj_enat_def by blast
         apply simp
         done
       then have k: "((\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC)\<and>* GC) ((llvm_\<alpha> a, cc'+delta))"
         by(simp)
       then have k': "(R ra r ** (\<Gamma>' \<and>* GC \<and>* F)) ((llvm_\<alpha> a, cc'+delta))"
         apply simp
         by(simp add: sep_conj_aci)
          

       have R: "R ra r \<turnstile> (\<lambda>s. \<exists>x. (\<up>Q x \<and>* R x r) s)"
         using Q
         by (smt entails_def pure_true_conv sep.add.right_neutral sep_conj_commute)

       show "((\<lambda>s. \<exists>x. (\<up>Q x \<and>* R x r) s) \<and>* (\<Gamma>' \<and>* GC \<and>* F)) (llvm_\<alpha> a, cc' + delta)"
         apply(rule entailsD[rotated])
          apply(rule k')  
         apply(rule conj_entails_mono[OF R])
         apply simp
         done
     qed
   qed
 qed


lemma llvm_htriple_more_time: "a\<le>b \<Longrightarrow> llvm_htriple ($a ** F) c Q \<Longrightarrow> llvm_htriple ($b ** F) c Q"
proof -
  assume ll: "llvm_htriple ($a ** F) c Q"
  assume p: "a\<le>b"
  obtain c where "b=c+a"
    using get_delta[OF p] by blast
  then have *: "$b = ($a ** $c)"
    by (simp add: add.commute time_credits_add)   
  show ?thesis
    unfolding *
    unfolding htriple_def
    apply safe
    subgoal for F h1 h2
      apply(rule wp_monoI)
      apply(rule ll[unfolded htriple_def, rule_format, where F="$c ** F"])
       apply(simp add: sep_conj_aci )
      apply simp
      subgoal premises p for r x 
        apply(rule entailsD[rotated])
         apply(rule p(2))
        apply(rule conj_entails_mono)
         apply simp
        apply(simp only: sep_conj_assoc[symmetric])
        apply(rule conj_entails_mono)
        subgoal
          by (metis consume_credits_fri_end_rule entails_eq_iff sep.add_ac(2))
        subgoal by simp
        done
      done
    done
qed




subsubsection \<open>Payday: move Time Credits between Heap and Monadic Costs\<close>

text \<open>In the following we prove two rules that allow to move time credits in an hnr rule between
       the pre-heap and the advertised costs in the abstract algorithm. \<close>

lemma hn_refine_pay_aux: "NREST.consume m t = SPECT M
  \<Longrightarrow> \<exists>M'. m = SPECT M' \<and> M = (map_option ((+) t) \<circ> M')"
  unfolding consume_def apply(cases m) by auto


lemma hnr_vcg_aux4:
  "P (s, cr) \<Longrightarrow> ($Ca \<and>* P) (s, cr + Ca)"
  apply(rule sep_conjI[where x="(0,Ca)"])
     apply (simp_all add: time_credits_assn_def sep_disj_prod_def sep_algebra_simps)
  by (auto simp add: sep_disj_acost_def sep_disj_enat_def sep_algebra_simps)

lemma hnr_vcg_aux3:
  "($Ca \<and>* P) (s, cr) \<Longrightarrow> \<exists>cr'. P (s, cr') \<and> cr=cr'+Ca"
  apply(erule sep_conjE)
  by (auto simp: time_credits_assn_def SND_def add.commute) 

lemma hn_refine_payday_aux2:
  fixes t:: ecost
  shows "Some Ca \<le> m \<Longrightarrow> Some (Ca + t) \<le> map_option ((+) t) m"
  apply(cases m) 
  by( auto simp add: add.commute add_mono)

lemma hn_refine_payday_aux3:
  fixes t:: ecost
  shows "Some Ca \<le> map_option ((+) t) m \<Longrightarrow> Ca \<ge> t \<and>  Some (Ca - t) \<le> m "
  apply(cases m) apply auto
  oops

text \<open>Time Credits can always be pushed from the Heap to the advertised costs.\<close>

lemma hn_refine_payday:
  fixes m :: " ('d, (char list, enat) acost) nrest"
  shows "hn_refine ($t \<and>* \<Gamma>) c \<Gamma>' R m \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R (consume m t)"
  unfolding hn_refine_def
  apply auto
  subgoal apply(cases m) by auto
  subgoal premises p for F s cr M
    using p(1)[THEN hn_refine_pay_aux]
    apply safe
    subgoal premises p2 for M'
      using p(3)[rule_format, where s=s and cr="cr+t" and M=M', OF p2(1), unfolded ll_\<alpha>_def lift_\<alpha>_cost_def STATE_def,
              simplified, OF p(2)[ unfolded ll_\<alpha>_def lift_\<alpha>_cost_def STATE_def, simplified, THEN hnr_vcg_aux4[where P="(\<Gamma> \<and>* F)"]]]
      apply safe
      subgoal for ra Ca
        apply(rule exI[where x="ra"])
        apply(rule exI[where x="Ca+t"])
        unfolding STATE_def  ll_\<alpha>_def lift_\<alpha>_cost_def
        by (simp add: hn_refine_payday_aux2 add.assoc add.commute add.left_commute)
      done
    done
  done

lemma
  fixes t:: nat
  shows "Some Ca \<le> map_option ((+) t) m
    \<Longrightarrow> Some (Ca - t) \<le> m"
  by(cases m, auto)

lemma hn_refine_payday_reverse_aux1:
  "Ca \<le> (lift_acost t) + (Ca - (lift_acost t))"
  apply(cases t; cases Ca)
  unfolding lift_acost_def minus_acost_alt less_eq_acost_def 
  apply auto
  by (metis add.commute add_diff_assoc_enat linear needname_cancle) 
  

lemma hn_refine_payday_reverse_aux2:
  shows "Some Ca \<le> map_option ((+) (lift_acost t)) m
    \<Longrightarrow> Some (Ca - (lift_acost t)) \<le> m"
  apply(cases m, auto)
  unfolding less_eq_acost_def lift_acost_def
  apply(cases Ca; cases t) apply simp
  by (metis (mono_tags, lifting) acost.sel add_diff_cancel_enat comp_apply drm_class.diff_right_mono enat.distinct(2) the_acost_propagate)
  

text \<open>Time credits can be pulled from the advertised costs to the Heap if it is finite.\<close>

lemma hn_refine_payday_reverse:
  fixes m :: " ('d, (char list, enat) acost) nrest"
  shows "hn_refine \<Gamma> c \<Gamma>' R (consume m (lift_acost t)) \<Longrightarrow> hn_refine ($(lift_acost t) \<and>* \<Gamma>) c \<Gamma>' R m"
  unfolding hn_refine_def
  apply auto
  subgoal apply(cases m) by (auto simp: nofailT_consume)
  subgoal premises p for F s cr M
    using p(2)[unfolded ll_\<alpha>_def lift_\<alpha>_cost_def STATE_def, simplified, THEN hnr_vcg_aux3]
    apply safe
    subgoal premises p2 for cr'
      using p(3)[rule_format, where s=s and cr="cr'" and M="(map_option ((+) (lift_acost t)) \<circ> M)", unfolded ll_\<alpha>_def lift_\<alpha>_cost_def STATE_def,
          simplified, OF _ p2(1)]
      apply (simp add: consume_def)
      apply safe
      subgoal for ra Ca
        apply(rule exI[where x="ra"])
        apply(rule exI[where x="Ca-(lift_acost t)"])
        apply(frule hn_refine_payday_reverse_aux2)
        apply simp
        using p2(2)
        unfolding STATE_def  ll_\<alpha>_def lift_\<alpha>_cost_def
        apply (auto simp add: hn_refine_payday_aux2 add.assoc add.commute add.left_commute)
        using  get_delta[OF hn_refine_payday_reverse_aux1, of t Ca]
        apply safe
        subgoal premises p for delta
          using p(2)[THEN wp_time_mono, where d=delta]
          apply(subst p(5))
          apply(rule wp_monoI)
           apply (simp add: add.assoc add.commute add.left_commute)
          apply auto
          subgoal premises p2 for r a cc' 
            apply (rule entailsD)
             defer 
             apply(rule  p2(2)[THEN hnr_vcg_aux4[where P="(\<Gamma>' \<and>* R ra r \<and>* F \<and>* GC)" and Ca=delta and s="llvm_\<alpha> a" and cr=cc']])
            apply(rule entails_trans)
             apply(rule conj_entails_mono)
              apply(rule entails_GC)
             apply(rule entails_refl)
            apply (rule ENTAILSD)
            apply fri 
            done
          done
        done
      done
    done
  done



subsection \<open>ML-Level Utilities\<close>
ML \<open>
  signature SEPREF_BASIC = sig
    (* Destroy lambda term, return function to reconstruct. Bound var is replaced by free. *)
    val dest_lambda_rc: Proof.context -> term -> ((term * (term -> term)) * Proof.context)
    (* Apply function under lambda. Bound var is replaced by free. *)
    val apply_under_lambda: (Proof.context -> term -> term) -> Proof.context -> term -> term

    (* 'a nres type *)
    val is_nresT: typ -> bool
    val mk_nresT: typ -> typ
    val dest_nresT: typ -> typ

    (* Make certified == *)
    val mk_cequals: cterm * cterm -> cterm
    (* Make \<Longrightarrow>\<^sub>A *)
    val mk_entails: term * term -> term


    (* Operations on pre-terms *)
    val constrain_type_pre: typ -> term -> term (* t::T *)

    val mk_pair_in_pre: term -> term -> term -> term (* (c,a) \<in> R *)

    val mk_compN_pre: int -> term -> term -> term  (* f o...o g*)

    val mk_curry0_pre: term -> term                (* curry0 f *) 
    val mk_curry_pre: term -> term                 (* curry f *) 
    val mk_curryN_pre: int -> term -> term         (* curry (...(curry f)...) *) 

    val mk_uncurry0_pre: term -> term              (* uncurry0 f *)       
    val mk_uncurry_pre: term -> term               (* uncurry f *)
    val mk_uncurryN_pre: int -> term -> term       (* uncurry (...(uncurry f)...) *)



    (* Conversion for hn_refine - term*)
    val hn_refine_conv: conv -> conv -> conv -> conv -> conv -> conv

    (* Conversion on abstract value (last argument) of hn_refine - term *)
    val hn_refine_conv_a: conv -> conv

    (* Conversion on abstract value of hn_refine term in conclusion of theorem *)
    val hn_refine_concl_conv_a: (Proof.context -> conv) -> Proof.context -> conv

    (* Destruct hn_refine term *)
    val dest_hn_refine: term -> term * term * term * term * term 
    (* Make hn_refine term *)
    val mk_hn_refine: term * term * term * term * term -> term
    (* Check if given term is Trueprop (hn_refine ...). Use with CONCL_COND'. *)
    val is_hn_refine_concl: term -> bool

    (* Destruct abs-fun, returns RETURN-flag, (f, args) *)
    val dest_hnr_absfun: term -> bool * (term * term list)
(*
    (* Make abs-fun. *)
    val mk_hnr_absfun: bool * (term * term list) -> term
    (* Make abs-fun. Guess RETURN-flag from type. *)
    val mk_hnr_absfun': (term * term list) -> term
*)    
    (* Prove permutation of *. To be used with f_tac_conv. *)
    val star_permute_tac: Proof.context -> tactic

    (* Make separation conjunction *)
    val mk_star: term * term -> term
    (* Make separation conjunction from list. "[]" yields "\<box>". *)
    val list_star: term list -> term
    (* Decompose separation conjunction. "\<box>" yields "[]". *)
    val strip_star: term -> term list

    (* Check if true-assertion *)
    val is_true: term -> bool

    (* Check if term is hn_ctxt-assertion *)
    val is_hn_ctxt: term -> bool 
    (* Decompose hn_ctxt-assertion *)
    val dest_hn_ctxt: term -> term * term * term
    (* Decompose hn_ctxt-assertion, NONE if term has wrong format *)
    val dest_hn_ctxt_opt: term -> (term * term * term) option
      

    type phases_ctrl = {
      trace: bool,            (* Trace phases *)
      trace_goals: bool,      (* Trace intermediate goal states *)
      int_res: bool,          (* Stop with intermediate result *)
      start: string option,   (* Start with this phase. NONE: First phase *)
      stop: string option     (* Stop after this phase. NONE: Last phase *)
    }

    (* No tracing or intermediate result, all phases *)
    val dflt_phases_ctrl: phases_ctrl 
    (* Tracing, intermediate result, all phases *)
    val dbg_phases_ctrl: phases_ctrl
    (* Tracing, goal-tracing, intermediate result, all phases *)
    val full_dbg_phases_ctrl: phases_ctrl
    
    val cfg_trace_phase_goals: bool Config.T
    val flag_phases_ctrl: Proof.context -> bool -> phases_ctrl

    (* Name, tactic, expected number of created goals (may be negative for solved goals) *)
    type phase = string * (Proof.context -> tactic') * int

    (* Perform sequence of tactics (tac,n), each expected to create n new goals, 
       or solve goals if n is negative. 
       Debug-flag: Stop with intermediate state after tactic 
       fails or produces less/more goals as expected. *)   
    val PHASES': phase list -> phases_ctrl -> Proof.context -> tactic'

  end

  structure Sepref_Basic: SEPREF_BASIC = struct

    fun is_nresT (Type (@{type_name nrest},[_,_])) = true | is_nresT _ = false
    fun mk_nresT T = Type(@{type_name nrest},[T,@{typ ecost}])
    fun dest_nresT (Type (@{type_name nrest},[T,_])) = T | dest_nresT T = raise TYPE("dest_nresT",[T],[])


    fun dest_lambda_rc ctxt (Abs (x,T,t)) = let
        val (u,ctxt) = yield_singleton Variable.variant_fixes x ctxt
        val u = Free (u,T)
        val t = subst_bound (u,t)
        val reconstruct = Term.lambda_name (x,u)
      in
        ((t,reconstruct),ctxt)
      end
    | dest_lambda_rc _ t = raise TERM("dest_lambda_rc",[t])

    fun apply_under_lambda f ctxt t = let
      val ((t,rc),ctxt) = dest_lambda_rc ctxt t
      val t = f ctxt t
    in
      rc t
    end


    (* Functions on pre-terms *)
    fun mk_pair_in_pre x y r = Const (@{const_name Set.member}, dummyT) $
      (Const (@{const_name Product_Type.Pair}, dummyT) $ x $ y) $ r


    fun mk_uncurry_pre t = Const(@{const_name uncurry}, dummyT)$t
    fun mk_uncurry0_pre t = Const(@{const_name uncurry0}, dummyT)$t
    fun mk_uncurryN_pre 0 = mk_uncurry0_pre
      | mk_uncurryN_pre 1 = I
      | mk_uncurryN_pre n = mk_uncurry_pre o mk_uncurryN_pre (n-1)

    fun mk_curry_pre t = Const(@{const_name curry}, dummyT)$t
    fun mk_curry0_pre t = Const(@{const_name curry0}, dummyT)$t
    fun mk_curryN_pre 0 = mk_curry0_pre
      | mk_curryN_pre 1 = I
      | mk_curryN_pre n = mk_curry_pre o mk_curryN_pre (n-1)


    fun mk_compN_pre 0 f g = f $ g
      | mk_compN_pre n f g = let
          val g = fold (fn i => fn t => t$Bound i) (n-2 downto 0) g
          val t = Const(@{const_name "Fun.comp"},dummyT) $ f $ g

          val t = fold (fn i => fn t => Abs ("x"^string_of_int i,dummyT,t)) (n-1 downto 1) t
        in
          t
        end

    fun constrain_type_pre T t = Const(@{syntax_const "_type_constraint_"},T-->T) $ t




    local open Conv in
      fun hn_refine_conv c1 c2 c3 c4 c5 ct = case Thm.term_of ct of
        @{mpat "hn_refine _ _ _ _ _"} => let
          val cc = combination_conv
        in
          cc (cc (cc (cc (cc all_conv c1) c2) c3) c4) c5 ct
        end
      | _ => raise CTERM ("hn_refine_conv",[ct])
  
      val hn_refine_conv_a = hn_refine_conv all_conv all_conv all_conv all_conv
  
      fun hn_refine_concl_conv_a conv ctxt = Refine_Util.HOL_concl_conv 
        (fn ctxt => hn_refine_conv_a (conv ctxt)) ctxt
  
    end

    (* FIXME: Strange dependency! *)
    val mk_cequals = uncurry SMT_Util.mk_cequals
  
    val mk_entails = HOLogic.mk_binrel @{const_name "entails"}
  
    val mk_star = HOLogic.mk_binop @{const_name "sep_conj"}

    fun list_star [] = @{term "\<box>::assn"}
      | list_star [a] = a
      | list_star (a::l) = mk_star (a,list_star l)

    fun strip_star @{mpat "?a**?b"} = strip_star a @ strip_star b
      | strip_star @{mpat "\<box>"} = []
      | strip_star t = [t]

    fun is_true @{mpat "sep_true"} = true | is_true _ = false
  
    fun is_hn_ctxt @{mpat "hn_ctxt _ _ _"} = true | is_hn_ctxt _ = false
    fun dest_hn_ctxt @{mpat "hn_ctxt ?R ?a ?p"} = (R,a,p) 
      | dest_hn_ctxt t = raise TERM("dest_hn_ctxt",[t])
  
    fun dest_hn_ctxt_opt @{mpat "hn_ctxt ?R ?a ?p"} = SOME (R,a,p) 
      | dest_hn_ctxt_opt _ = NONE
  
    fun strip_abs_args (t as @{mpat "PR_CONST _"}) = (t,[])
      | strip_abs_args @{mpat "?f$?a"} = (case strip_abs_args f of (f,args) => (f,args@[a]))
      | strip_abs_args t = (t,[])
  
    fun dest_hnr_absfun @{mpat "RETURN$?a"} = (true, strip_abs_args a)
      | dest_hnr_absfun f = (false, strip_abs_args f)
  (*
    fun mk_hnr_absfun (true,fa) = Autoref_Tagging.list_APP fa |> (fn a => @{mk_term "RETURNT$?a"})
      | mk_hnr_absfun (false,fa) = Autoref_Tagging.list_APP fa
  
    fun mk_hnr_absfun' fa = let
      val t = Autoref_Tagging.list_APP fa
      val T = fastype_of t
    in
      case T of
        Type (@{type_name nrest},_) => t
      | _ => @{mk_term "RETURN$?t"}
  
    end  *)
  
    fun dest_hn_refine @{mpat "hn_refine ?P ?c ?Q ?R ?a"} = (P,c,Q,R,a)
      | dest_hn_refine t = raise TERM("dest_hn_refine",[t])
  
    fun mk_hn_refine (P,c,Q,R,a) = @{mk_term "hn_refine ?P ?c ?Q ?R ?a"}
  
    val is_hn_refine_concl = can (HOLogic.dest_Trueprop #> dest_hn_refine)
  
    fun star_permute_tac ctxt = ALLGOALS (
      VCG_Lib.simp_only_tac @{thms sep_conj_empty sep_conj_empty' sep_conj_ac} ctxt)
      

    type phases_ctrl = {
      trace: bool,            
      trace_goals: bool,
      int_res: bool,          
      start: string option,   
      stop: string option     
    }

    val dflt_phases_ctrl = {trace=false,trace_goals=false,int_res=false,start=NONE,stop=NONE} 
    val dbg_phases_ctrl = {trace=true,trace_goals=false,int_res=true,start=NONE,stop=NONE}
    val full_dbg_phases_ctrl = {trace=true,trace_goals=true,int_res=true,start=NONE,stop=NONE}
    
    val cfg_trace_phase_goals = Attrib.setup_config_bool @{binding sepref_trace_phase_goals} (K false)
    
    fun flag_phases_ctrl ctxt dbg =
      case (Config.get ctxt cfg_trace_phase_goals, dbg) of
        (_, false) => dflt_phases_ctrl
      | (false, true) => dbg_phases_ctrl
      | (true,true) => full_dbg_phases_ctrl

    type phase = string * (Proof.context -> tactic') * int

    local
      fun ph_range phases start stop = let
        fun find_phase name = let
          val i = find_index (fn (n,_,_) => n=name) phases
          val _ = if i<0 then error ("No such phase: " ^ name) else ()
        in
          i
        end

        val i = case start of NONE => 0 | SOME n => find_phase n
        val j = case stop of NONE => length phases - 1 | SOME n => find_phase n

        val phases = take (j+1) phases |> drop i

        val _ = case phases of [] => error "No phases selected, range is empty" | _ => ()
      in
        phases
      end
    in  
  
      fun PHASES' phases ctrl ctxt = let
        val phases = ph_range phases (#start ctrl) (#stop ctrl)
        val phases = map (fn (n,tac,d) => (n,tac ctxt,d)) phases
  
        fun r [] _ st = Seq.single st
          | r ((name,tac,d)::tacs) i st = let
              val n = Thm.nprems_of st
              val bailout_tac = if #int_res ctrl then all_tac else no_tac
              fun trace_tac msg st = (if #trace ctrl then tracing msg else (); Seq.single st)
              
              val trace_goal_tac = if #trace_goals ctrl then print_tac ctxt "Proof state" else all_tac
              
              val trace_start_tac = trace_tac ("Phase " ^ name)
            in
              K trace_goal_tac THEN' K trace_start_tac THEN' IF_EXGOAL (tac)
              THEN_ELSE' (
                fn i => fn st => 
                  (* Bail out if a phase does not solve/create exactly the expected subgoals *)
                  if Thm.nprems_of st = n+d then
                    ((trace_tac "  Done" THEN r tacs i) st)
                  else
                    (trace_tac "*** Wrong number of produced goals" THEN bailout_tac) st
                
              , 
                K (trace_tac "*** Phase tactic failed" THEN bailout_tac))
            end i st
  
      in
        r phases
      end


    end

  end


  signature SEPREF_DEBUGGING = sig
    (*************************)
    (* Debugging *)
    (* Centralized debugging mode flag *)
    val cfg_debug_all: bool Config.T

    val is_debug: bool Config.T -> Proof.context -> bool
    val is_debug': Proof.context -> bool

    (* Conversion, trace errors if custom or central debugging flag is activated *)
    val DBG_CONVERSION: bool Config.T -> Proof.context -> conv -> tactic'

    (* Conversion, trace errors if central debugging flag is activated *)
    val DBG_CONVERSION': Proof.context -> conv -> tactic'

    (* Tracing message and current subgoal *)
    val tracing_tac': string -> Proof.context -> tactic'
    (* Warning message and current subgoal *)
    val warning_tac': string -> Proof.context -> tactic'
    (* Error message and current subgoal *)
    val error_tac': string -> Proof.context -> tactic'

    (* Trace debug message *)
    val dbg_trace_msg: bool Config.T -> Proof.context -> string -> unit
    val dbg_trace_msg': Proof.context -> string -> unit
    
    val dbg_trace: bool Config.T -> Proof.context -> (Proof.context -> string) -> unit
    val dbg_trace': Proof.context -> (Proof.context -> string) -> unit

    val dbg_msg_tac: bool Config.T -> (Proof.context -> int -> thm -> string) -> Proof.context -> tactic'
    val dbg_msg_tac': (Proof.context -> int -> thm -> string) -> Proof.context -> tactic'

    val msg_text: string -> Proof.context -> int -> thm -> string
    val msg_subgoal: string -> Proof.context -> int -> thm -> string
    val msg_from_subgoal: string -> (term -> Proof.context -> string) -> Proof.context -> int -> thm -> string
    val msg_allgoals: string -> Proof.context -> int -> thm -> string

  end

  structure Sepref_Debugging: SEPREF_DEBUGGING = struct

    val cfg_debug_all = 
      Attrib.setup_config_bool @{binding sepref_debug_all} (K false)

    fun is_debug cfg ctxt = Config.get ctxt cfg orelse Config.get ctxt cfg_debug_all
    fun is_debug' ctxt = Config.get ctxt cfg_debug_all

    fun dbg_trace cfg ctxt obj = 
      if is_debug cfg ctxt then  
        tracing ((obj ctxt))
      else ()

    fun dbg_trace' ctxt obj = 
      if is_debug' ctxt then  
        tracing ((obj ctxt))
      else ()

    fun dbg_trace_msg cfg ctxt msg =   
      if is_debug cfg ctxt then  
        tracing msg
      else ()
    fun dbg_trace_msg' ctxt msg = 
      if is_debug' ctxt then  
        tracing msg
      else ()

    fun DBG_CONVERSION cfg ctxt cv i st = 
      Seq.single (Conv.gconv_rule cv i st)
      handle e as THM _   => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty)
           | e as CTERM _ => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty)
           | e as TERM _  => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty)
           | e as TYPE _  => (dbg_trace cfg ctxt (K (@{make_string} e)); Seq.empty);

    fun DBG_CONVERSION' ctxt cv i st = 
      Seq.single (Conv.gconv_rule cv i st)
      handle e as THM _   => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty)
           | e as CTERM _ => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty)
           | e as TERM _  => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty)
           | e as TYPE _  => (dbg_trace' ctxt (K (@{make_string} e)); Seq.empty);


    local 
      fun gen_subgoal_msg_tac do_msg msg ctxt = IF_EXGOAL (fn i => fn st => let
        val t = nth (Thm.prems_of st) (i-1)
        val _ = Pretty.block [Pretty.str msg, Pretty.fbrk, Syntax.pretty_term ctxt t]
          |> Pretty.string_of |> do_msg

      in
        Seq.single st
      end)
    in       
      val tracing_tac' = gen_subgoal_msg_tac tracing
      val warning_tac' = gen_subgoal_msg_tac warning
      val error_tac' = gen_subgoal_msg_tac error
    end


    fun dbg_msg_tac cfg msg ctxt =
      if is_debug cfg ctxt then (fn i => fn st => (tracing (msg ctxt i st); Seq.single st))
      else K all_tac
    fun dbg_msg_tac' msg ctxt =
      if is_debug' ctxt then (fn i => fn st => (tracing (msg ctxt i st); Seq.single st))
      else K all_tac

    fun msg_text msg _ _ _ = msg

    fun msg_from_subgoal msg sgmsg ctxt i st = 
      case try (nth (Thm.prems_of st)) (i-1) of
        NONE => msg ^ "\n" ^ "Subgoal out of range"
      | SOME t => msg ^ "\n" ^ sgmsg t ctxt

    fun msg_subgoal msg = msg_from_subgoal msg (fn t => fn ctxt =>
      Syntax.pretty_term ctxt t |> Pretty.string_of
    )

    fun msg_allgoals msg ctxt _ st = 
      msg ^ "\n" ^ Pretty.string_of (Pretty.chunks (Goal_Display.pretty_goals ctxt st))

  end
\<close>


ML \<open>
  (* Tactics for produced subgoals *)
  infix 1 THEN_NEXT THEN_ALL_NEW_LIST THEN_ALL_NEW_LIST'
  signature STACTICAL = sig
    (* Apply first tactic on this subgoal, and then second tactic on next subgoal *)
    val THEN_NEXT: tactic' * tactic' -> tactic'
    (* Apply tactics to the current and following subgoals *)
    val APPLY_LIST: tactic' list -> tactic'
    (* Apply list of tactics on subgoals emerging from tactic. 
      Requires exactly one tactic per emerging subgoal.*)
    val THEN_ALL_NEW_LIST: tactic' * tactic' list -> tactic'
    (* Apply list of tactics to subgoals emerging from tactic, use fallback for additional subgoals. *)
    val THEN_ALL_NEW_LIST': tactic' * (tactic' list * tactic') -> tactic'

  end

  structure STactical : STACTICAL = struct
    infix 1 THEN_WITH_GOALDIFF
    fun (tac1 THEN_WITH_GOALDIFF tac2) st = let
      val n1 = Thm.nprems_of st
    in
      st |> (tac1 THEN (fn st => tac2 (Thm.nprems_of st - n1) st ))
    end

    fun (tac1 THEN_NEXT tac2) i = 
      tac1 i THEN_WITH_GOALDIFF (fn d => (
        if d < ~1 then 
          (error "THEN_NEXT: Tactic solved more than one goal"; no_tac) 
        else 
          tac2 (i+1+d)
      ))

    fun APPLY_LIST [] = K all_tac
      | APPLY_LIST (tac::tacs) = tac THEN_NEXT APPLY_LIST tacs
            
    fun (tac1 THEN_ALL_NEW_LIST tacs) i = 
      tac1 i 
      THEN_WITH_GOALDIFF (fn d =>
        if d+1 <> length tacs then (
          error "THEN_ALL_NEW_LIST: Tactic produced wrong number of goals"; no_tac
        ) else APPLY_LIST tacs i
      )

    fun (tac1 THEN_ALL_NEW_LIST' (tacs,rtac)) i =  
      tac1 i 
      THEN_WITH_GOALDIFF (fn d => let
        val _ = if d+1 < length tacs then error "THEN_ALL_NEW_LIST': Tactic produced too few goals" else ();
        val tacs' = tacs @ replicate (d + 1 - length tacs) rtac
      in    
        APPLY_LIST tacs' i
      end)


  end


  open STactical
\<close>

end
