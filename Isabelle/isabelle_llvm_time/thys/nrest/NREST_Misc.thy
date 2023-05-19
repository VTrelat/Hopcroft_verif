\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
\<^marker>\<open>contributor "Peter Lammich"\<close>
section \<open>Additional Lemmas for NREST\<close>
theory NREST_Misc
  imports
 "HOL-Library.Extended_Nat" "Refine_Monadic.RefineG_Domain"  Refine_Monadic.Refine_Misc  
  "HOL-Library.Monad_Syntax"   "HOL-Library.Groups_Big_Fun"
  Complex_Main 
 "../cost/Abstract_Cost"
begin

paragraph \<open>Summary\<close>
text \<open>This theory contains auxiliary lemmas needed for the theory in NREST.\<close>

declare [[coercion_enabled = false]]




subsection "Auxiliaries for option"

lemma less_eq_option_None_is_None': "x \<le> None \<longleftrightarrow> x = None" by(auto simp: less_eq_option_None_is_None)

lemma everywhereNone: "(\<forall>x\<in>X. x = None) \<longleftrightarrow> X = {} \<or> X = {None}"
  by auto


lemma my_these_def: "Option.these M = {f. Some f \<in> M}"
  unfolding  Option.these_def by (auto intro: rev_image_eqI)  

lemma option_Some_image: 
    "A \<noteq> {} \<Longrightarrow> A \<noteq> {None} \<Longrightarrow> case_option None (Some \<circ> f) ` A \<noteq> {None}" 
  by (metis (mono_tags) comp_apply empty_iff everywhereNone
                  imageI in_these_eq option.exhaust option.simps(5) these_insert_None)



lemma Option_these_case_option_eq_image: "Option.these (case_option None (\<lambda>e. Some (f e)) ` A)
        = f `(Option.these A)"
  unfolding Option.these_def apply (auto split: option.splits)
   apply force   
  using image_iff by fastforce 

subsection "Auxiliaries for enat"


abbreviation (input) "SUPREMUM S f \<equiv> Sup (f ` S)" 


lemma helper: "x2 \<le> x2a \<Longrightarrow> \<not> x2 < a \<Longrightarrow> \<not> x2a < a \<Longrightarrow>  x2 - (a::enat) \<le> x2a - a"
  apply(cases x2; cases x2a) apply auto apply(cases a) by auto

lemma helper2: "x2b \<le> x2 \<Longrightarrow> \<not> x2a < x2  \<Longrightarrow> \<not> x2a < x2b \<Longrightarrow> x2a - (x2::enat) \<le> x2a - x2b"
  apply(cases x2; cases x2a) apply auto apply(cases x2b) by auto

lemma Sup_finite_enat: "Sup X = Some (enat a) \<Longrightarrow> Some (enat a) \<in> X"
  by (auto simp: Sup_option_def Sup_enat_def these_empty_eq Max_eq_iff in_these_eq split: if_splits)

lemma Sup_enat_less2: " Sup X = \<infinity> \<Longrightarrow> (\<exists>x\<in>X. enat t < x)"
  unfolding  Sup_enat_def using    finite_enat_bounded linear 
  apply(auto split: if_splits)  
   apply (smt Max_in empty_iff enat_ord_code(4))
  by (smt not_less)  


lemma le_Some_infinity_enat[simp]: "t \<le> Some (\<infinity>::enat)"
  by (cases t, auto)


lemma Sup_image_emult1_aux1: "n\<noteq>0 \<Longrightarrow> xa * enat n = y * enat n \<Longrightarrow> xa = y"
  apply(cases xa; cases y) by auto
 

lemma mult_Max_commute:
  fixes k :: enat
  assumes "finite N" and "N \<noteq> {}"
  shows "k * Max N = Max {k * m | m. m \<in> N}"
proof -
  have "\<And>x y. k * max x y = max (k * x) (k * y)"
    apply (simp add: max_def not_le)
    apply(cases k) apply auto
    subgoal  
      by (metis distrib_left leD le_iff_add)  
    subgoal  
      using \<open>\<And>y x nat. \<lbrakk>k = enat nat; x \<le> y; enat nat * y < enat nat * x\<rbrakk> \<Longrightarrow> enat nat * y = enat nat * x\<close> le_less by blast  
    subgoal  
      by (simp add: leD mult_left_mono)  
    subgoal  
      by (metis antisym enat_ord_code(3) imult_is_infinity not_le zero_le)  
    done
  with assms show ?thesis
    using hom_Max_commute [of "times k" N]
    by simp (blast intro: arg_cong [where f = Max])
qed


lemma image_is_singleton_iff: "f`X={y} \<longleftrightarrow> (X\<noteq>{} \<and> (\<forall>x\<in>X. f x = y))" by auto

(* inspired by Sup_image_eadd1 *)
lemma Sup_image_emult1:
  assumes "Y \<noteq> {}"
  shows "Sup ((\<lambda>y :: enat. x * y) ` Y) = x * Sup Y"
proof(cases "finite Y")
  case True
  have "(*) x ` Y = {x * m |m. m \<in> Y}" by auto
  thus ?thesis using True by(simp add: Sup_enat_def mult_Max_commute assms)
next
  case False
  thus ?thesis
  proof(cases x)
    case (enat x')
    show ?thesis
      proof (cases "x'=0")
        case True
        then show ?thesis using enat apply (auto simp add: zero_enat_def[symmetric] )  
          by (metis SUP_bot bot_enat_def)  
      next
        case f: False
        with enat have "\<not> finite ((*) x ` Y)" using False
            apply(auto dest!: finite_imageD intro!: inj_onI)  
            by (simp add: mult.commute Sup_image_emult1_aux1)  
        with False f enat show ?thesis by(simp add: Sup_enat_def assms) 
      qed       
  next
    case infinity
    from False have i: "Sup Y \<noteq> 0"  
      by (simp add: Sup_enat_def assms) 
    from infinity False have "(*) x ` Y = {\<infinity>} \<or> (*) x ` Y = {\<infinity>,0}" using assms  
      by (smt image_is_singleton_iff finite.simps image_insert imult_is_infinity insert_commute mk_disjoint_insert mult_zero_right)  
    thus ?thesis using i infinity assms
      apply auto
      subgoal by (metis imult_is_infinity) 
      subgoal  
        by (metis Sup_enat_def ccSup_empty imult_is_infinity sup_bot.right_neutral)   
      done
  qed
qed


lemma enat_mult_cont: "Sup A * (c::enat) = Sup ((\<lambda>x. x*c)`A)"
  apply(cases "A={}")
  subgoal unfolding Sup_enat_def by simp
  using Sup_image_emult1
  by (metis mult_commute_abs)

lemma enat_mult_cont':
  fixes f :: "'a \<Rightarrow> enat"
  shows 
  "(Sup (f ` A)) * c = Sup ((\<lambda>x. f x * c) ` A)"
  using enat_mult_cont[of "f`A" c] 
  by (metis (mono_tags, lifting) SUP_cong   image_image)


lemma enat_add_cont':
  fixes f g :: "'a \<Rightarrow> enat"
  shows "(SUP b\<in>B. f b) + (SUP b\<in>B. g b) \<ge> (SUP b\<in>B. f b + g b)"  
  by (auto intro: Sup_least add_mono Sup_upper) 

lemma enat_Sum_any_cont:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> enat"
  assumes f: "finite {x. \<exists>y. f x y \<noteq> 0}"
  shows 
  "SUPREMUM B (\<lambda>y. Sum_any (\<lambda>x. f x y)) \<le> Sum_any (\<lambda>x. (SUPREMUM B (f x)))"
proof - 
  have "{a. SUPREMUM B (f a) \<noteq> 0} \<subseteq> {x. \<exists>y. f x y \<noteq> 0}"
    apply auto by (metis SUP_eqI i0_lb le_zero_eq) 


  { fix S :: "'a set"
    assume "finite S"
    then have "(SUP y\<in>B. \<Sum>x\<in>S. f x y) \<le> (\<Sum>x\<in>S. SUPREMUM B (f x))"
    proof (induct rule: finite_induct)
      case empty
      then show ?case apply auto  
      by (metis SUP_bot_conv(2) bot_enat_def) 
    next
      case (insert a A) 
      have "(SUP y\<in>B. (\<Sum>x\<in>insert a A. f x y)) =  (SUP y\<in>B. f a y + (\<Sum>x\<in>A. f x y))"
        using sum.insert insert by auto   
      also have "\<dots> \<le> (SUP b\<in>B. f a b) + (SUP y\<in>B. \<Sum>x\<in>A. f x y)"
        apply(subst enat_add_cont') by simp
      also have "\<dots> \<le> (SUP b\<in>B. f a b) + (\<Sum>x\<in>A. SUP b\<in>B. f x b)" using insert by auto
      also have "\<dots> = (\<Sum>x\<in>insert a A. SUP a\<in>B. f x a)" 
        using sum.insert insert by auto                          
      finally show ?case .
    qed
  } note finite_SUP_sum = this

  thm Sum_any.expand_set
  show ?thesis
    apply(subst (1) Sum_any.expand_superset[of "{x. \<exists>y. f x y \<noteq> 0}"])
    subgoal by fact subgoal apply auto done
    apply(subst (1) Sum_any.expand_superset[of "{x. \<exists>y. f x y \<noteq> 0}"])
    subgoal by fact subgoal apply fact done
    using f by(rule finite_SUP_sum)
qed 


lemma enat_plus_Sup_distrib:
  "A\<noteq>{} \<Longrightarrow> (a::enat) + Sup A = Sup ((+) a ` A)"
  apply(cases a)
  subgoal 
  unfolding Sup_enat_def apply auto
   apply (metis Max.hom_commute empty_iff enat_add_left_cancel_le max_def plus_enat_simps(2))
  apply(subst (asm) finite_image_iff)
  subgoal unfolding inj_on_def by auto
  subgoal apply simp done
  done
  subgoal by simp
  done

lemma ecost_plus_Sup_distrib:
  "A\<noteq>{} \<Longrightarrow> (a::(_,enat) acost) + Sup A = Sup ((+) a ` A)"
  unfolding Sup_acost_def apply(cases a)
  unfolding plus_acost_alt apply simp
  apply(rule ext)
proof (goal_cases)
  case (1 x xa)
  have "x xa + (SUP f\<in>A. the_acost f xa) = x xa + (SUP f\<in>the_acost `A. f xa)"
    apply simp  by (metis SUP_apply Sup_apply)  
  also have "\<dots> = x xa + (SUP v\<in>{f xa|f. f \<in> the_acost `A}. v)"
    by (simp add: setcompr_eq_image)  
  also have "\<dots> = Sup ((+) (x xa) ` {f xa|f. f \<in> the_acost `A})"
    apply(subst enat_plus_Sup_distrib) using 1(1) by auto
  also have "\<dots> = (SUP x\<in>case_acost (\<lambda>b. acostC (\<lambda>xa. x xa + b xa)) ` A. the_acost x xa) "
    apply(rule arg_cong[where f=Sup])
    apply auto
    subgoal for xb apply(cases xb) apply (auto simp: )
      apply(rule image_eqI) by auto 
    subgoal for xb apply(cases xb) apply (auto simp: )
      apply(rule image_eqI) apply(rule refl) apply auto  
      by force
    done
  finally show ?case .
qed



lemma map_option_case_option_conv: "map_option f = case_option None (\<lambda>x. Some (f x))"
  apply (rule ext) 
  unfolding map_option_case by simp
                                              
   
lemma map_option_plus_ecost_continuous:
  fixes t :: "(_,enat) acost"
  shows "(\<lambda>a. map_option ((+) t) a) (Sup A) = Sup ((\<lambda>a. map_option ((+) (t)) a) ` A)"
  unfolding map_option_case_option_conv
  unfolding Sup_option_def[unfolded my_these_def] 
  apply (simp add: option_Some_image  )
  apply rule+
  subgoal  
    by (metis empty_is_image Option_these_case_option_eq_image these_empty_eq)  
  subgoal apply(subst ecost_plus_Sup_distrib)
    subgoal
        using everywhereNone by fastforce  
  apply(rule arg_cong[where f=Sup]) 
    by  (auto split: option.splits  intro: rev_image_eqI)  
  done

lemma map_option_plus_enat_continuous:
  fixes t :: enat
  shows "(\<lambda>a. map_option ((+) t) a) (Sup A) = Sup ((\<lambda>a. map_option ((+) (t)) a) ` A)"
  unfolding map_option_case_option_conv
  unfolding Sup_option_def[unfolded my_these_def] 
  apply (simp add: option_Some_image  )
  apply rule+
  subgoal  
    by (metis empty_is_image Option_these_case_option_eq_image these_empty_eq)  
  subgoal apply(subst enat_plus_Sup_distrib)
    subgoal
        using everywhereNone by fastforce  
  apply(rule arg_cong[where f=Sup]) 
    by  (auto split: option.splits  intro: rev_image_eqI)  
  done

lemma conc_fun_consume_aux:
  fixes x2 :: "_ \<Rightarrow> (_,enat) acost option"
  shows "Sup ((\<lambda>a. map_option ((+) t) a) ` {x2 a| a. (c, a) \<in> R})
         = (\<lambda>a. map_option ((+) t) a) (Sup {x2 a |a. (c, a) \<in> R})"
  apply(subst map_option_plus_ecost_continuous)
  apply simp done


subsection "Auxiliary (for Sup and Inf)"



 
lemma aux2: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {None} \<longleftrightarrow> (M x = None \<and> M\<noteq>Map.empty)"
  apply (cases "M x"; auto simp: image_is_singleton_iff)
  by force

lemma aux3: "(\<lambda>f. f x) ` {[x \<mapsto> t1] |x t1. M x = Some t1} = {Some t1 | t1. M x = Some t1} \<union> ({None | y. y\<noteq>x \<and> M y \<noteq> None })"
  by (fastforce split: if_splits simp: image_iff) 

lemma Sup_pointwise_eq_fun: "(SUP f\<in>{[x \<mapsto> t1] |x t1. M x = Some t1}. f x) = M x"
  unfolding Sup_option_def  
  apply (simp add: aux2) 
  apply (auto simp: aux3)
  by (metis (mono_tags, lifting) Some_image_these_eq Sup_least in_these_eq mem_Collect_eq sup_absorb1 these_image_Some_eq)


lemma SUP_eq_None_iff: "(SUP f\<in>X. f x) = None \<longleftrightarrow> X={} \<or> (\<forall>f\<in>X. f x = None)"
  by (smt SUP_bot_conv(2) SUP_empty Sup_empty empty_Sup)

lemma SUP_eq_Some_iff: "(SUP f\<in>X. f x) = Some t \<longleftrightarrow> (\<exists>f\<in>X. f x \<noteq> None) \<and> (t=Sup {t' | f t'. f\<in>X \<and> f x = Some t' })"
  apply auto
  subgoal 
    by (smt Sup_bot_conv(1) Sup_empty Sup_option_def Sup_pointwise_eq_fun imageE option.distinct(1))
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  subgoal 
    unfolding Sup_option_def
    apply (clarsimp split: if_splits; safe)
    subgoal by (force simp: image_iff)
    apply (fo_rule arg_cong)
    apply (auto simp: Option.these_def)
    apply (metis (mono_tags, lifting) image_iff mem_Collect_eq option.sel)
    done
  done  



lemma Sup_enat_less: "X \<noteq> {} \<Longrightarrow> enat t \<le> Sup X \<longleftrightarrow> (\<exists>x\<in>X. enat t \<le> x)"
  apply rule
  subgoal 
  by (metis Max_in Sup_enat_def finite_enat_bounded linear) 
  subgoal apply auto
    by (simp add: Sup_upper2)
  done


(* 
  This is how implication can be phrased with an Inf operation.
  Generalization from boolean to enat can be explained this way.
 *)

lemma fixes Q P  shows
    "Inf { P x \<le> Q x |x. True}  \<longleftrightarrow> P \<le> Q" unfolding le_fun_def by simp


subsection \<open>continuous\<close>
term sup_continuous  

text \<open>That might by Scott continuity;
      
     https://en.wikipedia.org/wiki/Scott_continuity \<close>


text \<open>There is scott_continuous in Complete_Non_Orders.Fixed_Points\<close>

definition continuous :: "('a::{Sup} \<Rightarrow> 'b::{Sup}) \<Rightarrow> bool"  where
  "continuous f \<longleftrightarrow> (\<forall>A. Sup (f ` A) = f (Sup A) )"

definition continuousInf :: "('a::{Inf} \<Rightarrow> 'b::{Inf}) \<Rightarrow> bool"  where
  "continuousInf f \<longleftrightarrow> (\<forall>A. A\<noteq>{} \<longrightarrow> Inf (f ` A) = f (Inf A) )"


term sup_continuous
thm continuous_at_Sup_mono

lemma "continuous (f::'a::{complete_lattice}\<Rightarrow>'b::{complete_lattice})
         \<longleftrightarrow> (\<forall>A. Inf (f ` A) = f (Inf A) )" (* wrong conjecture *) oops
  
lemma continuousI: "(\<And>A. f (Sup A) = Sup (f ` A)) \<Longrightarrow> continuous f" by (auto simp: continuous_def)
lemma continuousD: "continuous f \<Longrightarrow> f (Sup A) = Sup (f ` A)" by (auto simp: continuous_def)


lemma continuousInfI: "(\<And>A. A\<noteq>{} \<Longrightarrow> f (Inf A) = Inf (f ` A)) \<Longrightarrow> continuousInf f" by (auto simp: continuousInf_def)
lemma continuousInfD: "continuousInf f \<Longrightarrow> A\<noteq>{} \<Longrightarrow> f (Inf A) = Inf (f ` A)" by (auto simp: continuousInf_def)


lemma continuous_Domain: "continuous Domain"
  apply(rule continuousI) by (fact Domain_Union)

lemma continuous_Range: "continuous Range"
  apply(rule continuousI) by (fact Range_Union)
  


subsubsection \<open>combinations are continuous\<close>


lemma continuousInf_funs:
  assumes *: "\<And>x. continuousInf (\<lambda>s. f s x)"
  shows "continuousInf (\<lambda>s. f (s x) (m x))"
  apply(rule continuousInfI)
  unfolding Inf_fun_def
  apply(subst continuousInfD[OF *]) apply simp
  apply(subst image_image) by simp

lemma continuousInf_Map_empty: "continuousInf Map.empty"
  apply(rule continuousInfI)
  by simp


lemma continuous_app: "continuous (\<lambda>f. f x)"
  apply(rule continuousI)
  by simp


lemma 
  continuous_fun:
  assumes *: "continuous f" shows "continuous  (\<lambda>X x. (f (X x)))"
  apply(rule continuousI)
  unfolding Sup_fun_def  apply(rule ext) 
  apply(subst continuousD[OF *]) apply(subst image_image) apply(subst image_image) ..



lemma 
  continuousInf_fun:
  assumes *: "continuousInf f" shows "continuousInf  (\<lambda>X x. (f (X x)))"
  apply(rule continuousInfI)
  unfolding Inf_fun_def  apply(rule ext) 
  apply(subst continuousInfD[OF *]) subgoal apply simp done
    apply(subst image_image) apply(subst image_image) ..


lemma SupD: "Sup A = Some f \<Longrightarrow> A \<noteq> {} \<and> A\<noteq>{None}"
  unfolding Sup_option_def by auto


lemma zzz: "Option.these A \<noteq> {}
 \<Longrightarrow> Sup ( (\<lambda>x. case x of None \<Rightarrow> None | Some e \<Rightarrow> Some (f e)) ` A)
        = Some (Sup ( f ` Option.these A))"
  apply(subst Sup_option_def)
  apply simp
  apply safe
  subgoal  
    by simp  
  subgoal  
    by (metis SupD image_is_singleton_iff empty_Sup in_these_eq option.simps(5))  
  subgoal apply(subst Option_these_case_option_eq_image) by simp 
  done


lemma assumes "continuous f"
  shows "continuous (case_option None (Some o f))" (* TODO: generalize to adding top/bottom element *)
  apply(rule continuousI)
  apply(auto split: option.splits)
  subgoal unfolding Sup_option_def by (auto split: if_splits)
proof -
  fix A   and a :: "'a::{complete_lattice}"
  assume a: "Sup A = Some a"
  with SupD have A: "A \<noteq> {} \<and> A \<noteq> {None}" by auto

  then have a': "a= Sup (Option.these A)"  
    by (metis Sup_option_def a option.inject)

  from A have oA: "Option.these A \<noteq> {}" unfolding Option.these_def by auto

  have *: "\<And>x. Some (f x) = (Some o f) x" by simp
  have "(SUP x\<in>A. case x of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> f) x)
        = (SUP x\<in>A. case x of None \<Rightarrow> None | Some s \<Rightarrow> Some (f s))"
    by(simp only: *) 
  also have "\<dots> = Some (SUP s\<in>(Option.these A). (f s))"
   using oA zzz by metis 
        
  also have "(SUP s\<in>(Option.these A). (f s)) = f a"
    using a' assms(1)[THEN continuousD] by metis 

  finally show "Some (f a) = (SUP x\<in>A. case x of None \<Rightarrow> None | Some x \<Rightarrow> (Some \<circ> f) x)"  by simp
qed  
  
text \<open>a shorter proof\<close>

lemma continuous_option: (* or generally, adding a bottom element *)
  assumes *: "continuous f"
  shows "continuous (case_option None (Some o f))"
  apply(rule continuousI)
  unfolding Sup_option_def[unfolded my_these_def] 
  apply (simp add: option_Some_image)
  apply (simp add:  continuousD[OF *])
  apply rule+
  apply(rule arg_cong[where f=Sup]) 
    by  (auto split: option.splits  intro: rev_image_eqI)   

lemma continuous_option': 
  assumes *: "continuous f"
  shows "continuous (case_option None (\<lambda>x. Some (f x)))"
  using continuous_option[OF *, unfolded comp_def]  .


lemma continuousInf_option: (* or generally, adding a bottom element *)
  assumes *: "continuousInf f"
  shows "continuousInf (case_option None (\<lambda>x. Some (f x)))"
  apply(rule continuousInfI)
  unfolding Inf_option_def[unfolded my_these_def] 
  apply (simp add: option_Some_image )
  apply safe
  subgoal by force
  subgoal by(auto split: option.splits) 
  subgoal apply(subst continuousInfD[OF *]) subgoal  
    by (metis Collect_empty_eq Inf_lower \<open>\<And>A. Inf A = (if None \<in> A then None else Some (Inf {f. Some f \<in> A}))\<close> le_some_optE)  
    apply(rule arg_cong[where f=Inf]) 
    by  (auto split: option.splits  intro: rev_image_eqI)  
  done

               
lemma continuous_map_option: "continuous f \<Longrightarrow> continuous (map_option f)"
  unfolding map_option_case_option_conv apply(intro continuous_option') .




definition myminus where "myminus x y = (if x=\<infinity> \<and> y=\<infinity> then 0 else x - y)"
lemma "(a::enat) + x \<ge> b  \<longleftrightarrow> x \<ge> myminus b a "
  unfolding myminus_def
  apply(cases a; cases b; cases x) apply auto oops



end