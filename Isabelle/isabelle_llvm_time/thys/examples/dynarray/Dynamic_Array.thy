theory Dynamic_Array
  imports "../../sepref/Hnr_Primitives_Experiment" "../../nrest/Refine_Heuristics"
  "../../nrest/NREST_Automation" "../sorting/Sorting_Setup"
  "../../nrest/Synth_Rate"
begin



definition "hide a b = (a=b)"
lemma hideI: "a=b \<Longrightarrow> hide a b" unfolding hide_def by simp
lemma hide: "hide a b \<Longrightarrow> a = b" unfolding hide_def by simp


(* TODO: Move *)
lemma wfR''_zero[simp]: "wfR'' 0"
  unfolding wfR''_def by (auto simp: zero_acost_def)

(* TODO: Move *)
lemma nrest_C_relI:
  fixes a :: "(_,ecost) nrest"
  shows "a \<le> \<Down>R (\<Down>\<^sub>C TId b) \<Longrightarrow> (a,b) \<in> \<langle>R\<rangle>nrest_rel"
  apply(rule nrest_relI) by (auto simp: timerefine_id)

(* TODO: Move *)
definition mop_list_length :: "_ \<Rightarrow> (_,ecost) nrest" where
  "mop_list_length xs = RETURNT (length xs)"


(* TODO: move *)
lemma one_time_SPECT_map[OT_intros]: "one_time (SPECT [x\<mapsto>t])"
  unfolding one_time_def by auto


lemma one_time_bind_assert[OT_intros]: "one_time m \<Longrightarrow> one_time (doN { ASSERT P; m})"
  unfolding one_time_def
  apply(cases P) by auto

(* TODO: Move *)
lemma one_time_uncurry[OT_intros]:
  "(\<And>a b. x=(a,b) \<Longrightarrow> one_time (f a b)) \<Longrightarrow> one_time (uncurry f x)"
  unfolding uncurry_def 
  by (metis old.prod.case old.prod.exhaust) 

lemma one_time_mop_list_get[OT_intros]: "one_time (mop_list_get T a b)"
  unfolding mop_array_nth_def mop_list_get_def by (intro OT_intros)

lemma one_time_mop_array_nth[OT_intros]: "one_time (mop_array_nth a b)"
  unfolding mop_array_nth_def by (intro OT_intros)


lemma one_time_PR_CONST[OT_intros]: "one_time x \<Longrightarrow> one_time (PR_CONST x)"
         "one_time (y b) \<Longrightarrow> one_time (PR_CONST y b)"
         "one_time (z c d) \<Longrightarrow> one_time (PR_CONST z c d)"
  unfolding PR_CONST_def by simp



subsection \<open>Array Copy\<close>

definition "array_copy_impl dst src n = doM {
          return dst      
      }"


definition list_copy_spec where
  "list_copy_spec T dst src n = doN {
       ASSERT (n\<le>length dst \<and> n\<le>length src);
       REST [take n src @ drop n dst \<mapsto> T n]
    }"

definition "list_copy_body_cost = (cost ''if'' 1 + cost ''call'' 1 +  mop_array_nth_cost + 
                                         mop_array_upd_cost + cost ''add'' 1 + cost ''icmp_slt'' 1)"
definition list_copy :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a list, ecost) nrest" where
  "list_copy dst src n = doN {
          (dst,_) \<leftarrow> monadic_WHILEIET (\<lambda>(dst',n'). n'\<le>n \<and> length dst' = length dst \<and> dst' = take n' src @ drop n' dst)
              (\<lambda>(_::'a list,n'). (n-n') *m list_copy_body_cost )
            (\<lambda>(_,n'). SPECc2 ''icmp_slt'' (<) n' n)
            (\<lambda>(dst',n'). doN {
              x \<leftarrow> mop_array_nth src n';
              dst'' \<leftarrow> mop_array_upd dst' n' x;
              ASSERT (n'+1\<le>n);
              n'' \<leftarrow> SPECc2 ''add'' (+) n' 1;
              RETURNT (dst'',n'')
            })
          (dst,0);
          RETURNT dst
      }"

definition "list_copy_spec_time n = (enat (n)) *m (lift_acost list_copy_body_cost)
           + cost ''if'' 1 + cost ''call'' 1 + cost ''icmp_slt'' 1"

lemma list_copy_correct: "(uncurry2 list_copy, uncurry2 (list_copy_spec list_copy_spec_time))
       \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nrest_rel"
  apply rule
  apply (rule nrest_relI)    
  unfolding uncurry_def 
  unfolding list_copy_spec_def 
  apply (auto simp add: le_fun_def)    
  apply(rule le_acost_ASSERTI) 
  unfolding list_copy_def
  unfolding list_copy_body_cost_def
  unfolding SPECc2_def mop_array_nth_def mop_list_get_def mop_array_upd_def  mop_list_set_def
  apply(rule gwp_specifies_I)
  apply(refine_vcg \<open>-\<close> rules: gwp_monadic_WHILEIET If_le_rule)
  subgoal
    unfolding wfR2_def
    apply (auto simp:  costmult_add_distrib costmult_cost the_acost_propagate zero_acost_def)
      by(auto simp: cost_def zero_acost_def)
  subgoal apply(rule loop_body_conditionI)
    subgoal apply (auto simp: norm_cost) apply(sc_solve) by auto
    subgoal apply (auto simp: norm_cost) apply(sc_solve) by (auto simp: one_enat_def)
    subgoal apply (auto simp: norm_cost) by(simp add: upd_conv_take_nth_drop take_Suc_conv_app_nth)
    done
  subgoal apply auto done
  subgoal apply auto done
  subgoal apply auto done
  subgoal
    apply(rule loop_exit_conditionI)
    apply(refine_vcg \<open>-\<close> rules:)
    unfolding list_copy_spec_time_def list_copy_body_cost_def
    apply (auto simp: norm_cost lift_acost_propagate cost_zero)
    apply(sc_solve) by auto
  subgoal apply auto done
  done


(*
declare hnr_array_upd[sepref_fr_rules del] 
lemma hnr_array_upd_ohne_sc[sepref_fr_rules]:
  "CONSTRAINT is_pure A \<Longrightarrow>(uncurry2 array_upd, uncurry2 mop_array_upd) \<in> (array_assn A)\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a array_assn A"
  apply(rule hnr_array_upd)
   apply simp 
  unfolding SC_attains_sup_def
  apply safe
  apply(rule one_time_attains_sup)
  unfolding mop_array_upd_def mop_list_set_def
  unfolding uncurry_def apply simp
  by(intro OT_intros) *)


context size_t_context
begin

  thm hnr_array_upd
  thm hnr_eoarray_upd'

  thm hnr_array_upd

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "array_assn A" for A]

   sepref_def list_copy_impl is "uncurry2 list_copy"  
     :: "(array_assn (pure R))\<^sup>d *\<^sub>a (array_assn (pure R))\<^sup>k *\<^sub>a size_assn\<^sup>k  \<rightarrow>\<^sub>a array_assn (pure R)"
     unfolding  list_copy_def PR_CONST_def  
     unfolding monadic_WHILEIET_def
     apply (annot_snat_const "TYPE('size_t)")
     by sepref 


lemmas list_copy_impl_refine = list_copy_impl.refine 

  thm list_copy_impl.refine

end

thm size_t_context.list_copy_impl_refine
thm size_t_context.list_copy_impl_def

section \<open>Misc\<close>




lemma timerefineA_mono:
    assumes "wfR'' R"
    shows "t \<le> t' \<Longrightarrow> timerefineA R t \<le> timerefineA R (t'::ecost)"
  apply (auto simp: less_eq_acost_def timerefineA_def split: nrest.splits option.splits simp: le_fun_def)
  proof (goal_cases)
    case (1 ac)
    then have l: "\<And>ac. the_acost t ac \<le>  the_acost t' ac"
      apply(cases t; cases t') unfolding less_eq_acost_def  
      by auto
    show ?case
      apply(rule Sum_any_mono)
      subgoal using l apply(rule ordered_semiring_class.mult_right_mono) by (simp add: needname_nonneg)
      apply(rule wfR_finite_mult_left2) by fact
  qed 



lemma SPECT_assign_emb': "SPECT [x\<mapsto>t] = SPECT (emb' (\<lambda>y. y=x) (\<lambda>_.t))"
  unfolding emb'_def apply auto done

lemma 
  SPEC_leq_SPEC_I_even_stronger:
  "A \<le> A' \<Longrightarrow> (\<And>x. A x \<Longrightarrow> B x \<le> (B' x)) \<Longrightarrow> SPEC A B \<le> (SPEC A' B')"
  apply(auto simp: SPEC_def)
  by (simp add: le_fun_def)  


lemma consume_SPEC_eq: "consume (SPEC \<Phi> T) (t::ecost)= SPEC \<Phi> (\<lambda>x. T x + t)"
  unfolding SPEC_def consume_def
  apply auto
  apply(rule ext) apply auto 
  using ecost_add_commute by blast

 
lemma meh_special: "b \<ge> lift_acost a \<Longrightarrow> Ca \<le> b - lift_acost a\<Longrightarrow> Ca + lift_acost a \<le> b"
  apply(cases b; cases Ca; cases a) apply auto
  using plus_minus_adjoint_ecost by blast 


lemma plus_minus_adjoint_ecost_I: "b \<ge> (a::ecost) \<Longrightarrow> Ca \<le> b - a\<Longrightarrow> Ca + a \<le> b"
  apply(subst plus_minus_adjoint_ecost[symmetric]) by simp_all

lemma enat_minusrule: "b<\<infinity> \<Longrightarrow> (a+b)-b = (a::enat)"
  by(cases a; cases b; auto simp: ) 

lemma zz: "(\<And>x. the_acost b x < \<infinity>) \<Longrightarrow> (a+b)-b = (a::ecost)"
  apply(cases a; cases b; auto simp: )
  apply(rule ext) apply(rule enat_minusrule)
  by auto

lemma acost_move_sub_le: "b\<ge>c \<Longrightarrow> (a+b)-c \<ge> (a::(string,nat) acost)"
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)
  by (simp add: nat_move_sub_le)


lemma zz3: "b\<ge>c \<Longrightarrow> (b+a)-c \<ge> (a::(string,nat) acost)"
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)
  by (simp add: nat_move_sub_le)


lemma add_diff_assoc_ncost: "b\<ge>c \<Longrightarrow> (a+b)-c = (a::(string,nat) acost) + (b-c)"
  apply(cases a; cases b; cases c) 
  by (auto simp: less_eq_acost_def)


lemma costmult_add_distrib_left:
  fixes a :: "'b::semiring"
  shows "a *m A + b *m A = (a+b) *m A "
  apply(cases A) by (auto simp: costmult_def plus_acost_alt ring_distribs)

lemma costmult_right_mono:
  fixes a :: nat
  shows "a \<le> a' \<Longrightarrow> a *m c \<le> a' *m c"
  unfolding costmult_def less_eq_acost_def
  by (auto simp add: mult_right_mono)  


lemma cost_mult_zero_enat[simp]:"(0::enat) *m m = (0) "
  by(auto simp: zero_acost_def costmult_def) 
lemma cost_mult_zero_nat[simp]: "(0::nat) *m m = (0) "
  by(auto simp: zero_acost_def costmult_def) 
 


lemma costmult_left_cong: "a=b \<Longrightarrow> a *m A = b *m A"
  by simp

subsection \<open>Stuff about Sum_any\<close>


lemma finite_nonzero_minus: "finite {a. g a \<noteq> 0} \<Longrightarrow> finite {a. h a \<noteq> (0::enat)} \<Longrightarrow> finite {a. g a - h a \<noteq> 0}"
  by (metis (mono_tags, lifting) Collect_mono_iff idiff_0 rev_finite_subset)

lemma sum_minus_distrib_enat:
  assumes "\<And>a. g a \<ge> (h a::enat)"
  shows "finite A \<Longrightarrow> sum (\<lambda>a. g a - h a) A = sum g A - sum h A" 
proof (induct rule: finite_induct)
  case (insert x F)
  have *: "sum g F \<ge> sum h F"
    apply(rule sum_mono) using assms by auto
  have "(\<Sum>a\<in>insert x F. g a - h a)
      = (g x - h x) + (\<Sum>a\<in>F. g a - h a)"  
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "\<dots> = (g x - h x) + (sum g F - sum h F)"
    by (simp add: insert.hyps(3))
  also have "\<dots> = (g x + sum g F) - (h x + sum h F)"
    using assms[of x] * 
    by (metis add.commute add_diff_assoc_enat assms minus_plus_assoc2) 
  also have "\<dots> = sum g (insert x F) - sum h (insert x F)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case .
qed simp  

lemma Sum_any_minus_distrib_enat:
  assumes "finite {a. g a \<noteq> 0}" "finite {a. h a \<noteq> 0}"
  assumes "\<And>a. g a \<ge> (h a :: enat)"
  shows "Sum_any (\<lambda>a. g a - h a) = Sum_any g - Sum_any h"
proof -
  have z: "{a. g a - h a \<noteq> 0} \<subseteq> {a. g a \<noteq> (0::enat)}"
    by auto

  have "Sum_any (\<lambda>a. g a - h a) = sum (\<lambda>a. g a - h a)  {a. g a \<noteq> 0}"
    apply  (rule Sum_any.expand_superset) 
    apply(rule assms(1))
    apply(rule z)
    done
  also have "\<dots> = sum g {a. g a \<noteq> 0} - sum h {a. g a \<noteq> 0}"
    apply(subst sum_minus_distrib_enat) 
      apply(rule assms(3))
    apply(rule assms(1))
    apply simp done 
  also have "\<dots> = Sum_any g - Sum_any h"
    apply(subst Sum_any.expand_set)
    apply(subst Sum_any.expand_superset[OF assms(1)])
    subgoal using assms(3)  apply auto 
      by (metis ile0_eq) 
    apply simp 
    done
  finally show ?thesis .
qed    

lemma diff_mult_sub_distrib_enat:
  shows "(a - b) * (c::enat) \<le> a * c - b * c"
  apply(cases a; cases b; cases c; auto)
  using diff_mult_distrib by simp


(* TODO: move improved version upstream *)
lemma wfR''_finite_mult_left:
  assumes "wfR'' R"
  shows "finite {ac. x ac * the_acost (R ac) cc \<noteq> 0}"
proof - 
  from assms have "finite {s. the_acost (R s) cc \<noteq> 0}" unfolding wfR''_def by auto
  show ?thesis
    apply(rule finite_subset[where B="{ac. the_acost (R ac) cc \<noteq> 0}"])
    subgoal by auto
    subgoal apply fact done
    done
qed 

lemma timerefineA_propagate_minus:
  assumes "wfR'' E"
  fixes a b :: "('a, enat) acost"
  assumes "a\<ge>b"
  shows "timerefineA E (a - b) \<le> timerefineA E a - timerefineA E b"
  unfolding timerefineA_def
  apply(auto simp: less_eq_acost_def minus_acost_alt timerefine_def consume_def timerefineA_def split: nrest.splits option.splits)
  apply(cases a, cases b) 
  apply auto
  unfolding  ring_distribs 
  apply(rule order.trans)
   apply(rule Sum_any_mono)
    apply(rule diff_mult_sub_distrib_enat) 
   apply(rule finite_nonzero_minus)
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  apply(subst Sum_any_minus_distrib_enat)
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  subgoal apply(rule wfR''_finite_mult_left) by(rule assms(1))
  subgoal apply(rule mult_right_mono) using assms(2) unfolding le_fun_def  by (auto simp: less_eq_acost_def  )
  apply simp
  done

lemma add_increasing2_nat_acost: "(a::(_,nat)acost)\<le>b \<Longrightarrow> a\<le>b+c" 
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)  
  by (simp add: add_increasing2)  
lemma add_increasing2_ecost: "(a::ecost)\<le>b \<Longrightarrow> a\<le>b+c" 
  apply(cases a; cases b; cases c) apply (auto simp: less_eq_acost_def)  
  by (simp add: add_increasing2)  


subsection \<open>reclaim\<close>


fun reclaim where
  "reclaim FAILi t = FAILT"
| "reclaim (SPECT M) t = Sup { if t'\<ge>t x then SPECT [x\<mapsto>t' - t x] else FAILT | t' x. M x = Some t' }"




lemma reclaim_nofailT[simp]: "reclaim FAILT t = FAILT"
  unfolding top_nrest_def apply(subst reclaim.simps) by simp

lemma blaD1: "nofailT (reclaim m t) \<Longrightarrow> nofailT m \<and> (\<forall>M. m=SPECT M \<longrightarrow> (\<forall>x t'. M x = Some t' \<longrightarrow> t' \<ge> t x))"
  apply(cases m)
   apply auto
  unfolding pw_Sup_nofail 
  by force 

lemma blaD2: " nofailT m \<and> (\<forall>M. m=SPECT M \<longrightarrow> (\<forall>x t'. M x = Some t' \<longrightarrow> t' \<ge> t x)) \<Longrightarrow> nofailT (reclaim m t)"
  apply(cases m)
   apply auto
  unfolding pw_Sup_nofail  
  by auto

lemma nofailT_reclaim:
 "nofailT (reclaim m t) \<longleftrightarrow> (nofailT m \<and> (\<forall>M. m=SPECT M \<longrightarrow> (\<forall>x t'. M x = Some t' \<longrightarrow> t' \<ge> t x)))"
  apply(cases m)
   apply auto
  unfolding pw_Sup_nofail  
  apply force
  by auto
 

lemma reclaim_SPEC: "(\<And>x. Q x \<Longrightarrow> T x \<ge> \<Phi> x) \<Longrightarrow> reclaim (SPEC Q T) (\<Phi>::_\<Rightarrow>ecost) = SPEC Q (\<lambda>x. T x - \<Phi> x)"
  apply(rule antisym)
  subgoal
    by (auto simp: le_fun_def SPEC_def split: if_splits intro!: Sup_least)
  subgoal    
    by (auto simp: SPEC_def Sup_nrest_def le_fun_def intro!: Sup_upper2)
  done

lemma reclaim_SPEC_le: "SPEC Q (\<lambda>x. T x - \<Phi> x) \<le> reclaim (SPEC Q T) (\<Phi>::_\<Rightarrow>ecost)"
  apply(cases "nofailT (reclaim (SPEC Q T) (\<Phi>::_\<Rightarrow>ecost))")
  subgoal
    apply(subst (asm) nofailT_reclaim)
    apply (auto simp: nofailT_SPEC )
    apply(subst (asm) SPEC_def) apply (auto split: if_splits) 
    subgoal    
      by (auto simp: SPEC_def Sup_nrest_def le_fun_def intro!: Sup_upper2)
    done
  subgoal unfolding nofailT_def by auto
  done



lemma pull_timerefine_through_reclaim:
  fixes TR :: "_\<Rightarrow>ecost"
  assumes *: "wfR'' TR"
      and ineq: "\<And>x. \<Psi> x \<Longrightarrow> \<Phi>' x \<le> T x + \<Phi>"
  shows "\<Down>\<^sub>C TR (reclaim (consume (SPEC \<Psi> (T::_\<Rightarrow>ecost)) \<Phi>) \<Phi>') \<le>
         (reclaim (consume (SPEC \<Psi> (\<lambda>x. timerefineA TR ((T::_\<Rightarrow>ecost) x))) (timerefineA TR \<Phi>)) (timerefineA TR o \<Phi>'))"
  apply(subst consume_SPEC_eq)
  apply(subst consume_SPEC_eq)  
  apply(subst reclaim_SPEC) 
    subgoal apply(rule ineq) by simp
  apply(subst reclaim_SPEC) 
    subgoal
     apply(subst timerefineA_propagate[symmetric])
       apply(rule *)     apply simp
      apply(rule timerefineA_mono)
      subgoal by(rule *)   
    subgoal apply(rule ineq) by simp
      done
  apply(subst SPEC_timerefine_conv)
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  subgoal apply auto done
  subgoal apply (subst timerefineA_propagate[symmetric])
     apply(rule *)       apply simp
    apply(rule order.trans[rotated])
     apply(rule timerefineA_propagate_minus)
    subgoal by(rule *)     
    subgoal apply(rule ineq) by simp
    subgoal 
      apply(rule timerefineA_mono)
      subgoal by(rule *)     
      apply simp
      done
    done
  done   

subsection \<open>augment_amor_assn\<close>

definition "augment_amor_assn \<Phi> A = (\<lambda>ra r. $\<Phi> ra ** A ra r)"
lemma amor_orthogonal:
  assumes "(C, A) \<in> (assn)\<^sup>k *\<^sub>a S \<rightarrow>\<^sub>a R"
  shows "(C, A) \<in> (augment_amor_assn PHI assn)\<^sup>k *\<^sub>a S \<rightarrow>\<^sub>a R"
  unfolding augment_amor_assn_def
  apply(rule hfrefI)
  apply (auto)
  apply(rule hn_refine_frame'') 
  using assms[THEN hfrefD] by auto


lemma amor_orthogonal_empt:
  assumes "(C, A) \<in> (assn)\<^sup>k \<rightarrow>\<^sub>a R"
  shows "(C, A) \<in> (augment_amor_assn PHI assn)\<^sup>k \<rightarrow>\<^sub>a R"
  unfolding augment_amor_assn_def
  apply(rule hfrefI)
  apply (auto)
  apply(rule hn_refine_frame'') 
  using assms[THEN hfrefD] by auto


lemma invalid_assn_augment_amor_assn: "invalid_assn (augment_amor_assn \<Phi> A) = invalid_assn A"
  unfolding augment_amor_assn_def invalid_assn_def
  unfolding pure_part_def 
  apply auto apply(rule ext) apply(rule ext)
  apply auto
  subgoal  
    using hnr_vcg_aux3 by blast
  subgoal
    by (metis hnr_vcg_aux1 sep_conj_commute) 
  done

subsection \<open>finite cost\<close>

definition "finite_cost t \<equiv> \<forall>x. the_acost t x < \<infinity>"

lemma finite_costD: "finite_cost t \<Longrightarrow> the_acost t x < \<infinity>"
  unfolding finite_cost_def by auto
   
lemma finite_costI: "(\<And>x. the_acost t x < \<infinity>) \<Longrightarrow> finite_cost t"
  unfolding finite_cost_def by auto


lemma finite_cost_lift_acost: "finite_cost (lift_acost x)"
  unfolding finite_cost_def lift_acost_def by auto

lemma extract_lift_acost_if_less_infinity:
  assumes
    less_infinity: "finite_cost t" 
  obtains t' where "lift_acost t' = t"
proof 
  show "lift_acost (acostC (\<lambda>x. the_enat (the_acost t x))) = t"
    unfolding lift_acost_def
    apply(cases t)
    apply simp
    using less_infinity[THEN finite_costD]
    by (metis (mono_tags) acost.sel acost_eq_I comp_apply less_infinityE the_enat.simps)
qed


subsection \<open>wp can frame time through\<close>


text \<open>Is this property specific to wp of LLVM, or is this general?\<close>

thm wp_time_mono text \<open>is this morally the same lemma? it was also proven with unfolding mwp\<close>

lemma wp_time_frame: "wp c (\<lambda>r s. (G r) (ll_\<alpha> s)) (s,tc)
  \<Longrightarrow> wp c (\<lambda>r s. ($t ** G r) (ll_\<alpha> s)) (s,tc+t)"
  unfolding wp_def apply auto
  unfolding mwp_def apply(cases "run c s")
     apply auto
  unfolding ll_\<alpha>_def
  subgoal for x y z
    apply(rule sep_conjI[where x="(0,t)" and y="(lift_\<alpha>_cost llvm_\<alpha> (z, minus_ecost_cost tc y))"]) 
    subgoal unfolding time_credits_assn_def SND_def by auto 
    subgoal apply simp done
    subgoal by (simp add: sep_disj_acost_def sep_disj_enat_def sep_disj_prod_def) 
    subgoal
      by (smt \<open>\<lbrakk>run c s = SUCC x y z; G x (lift_\<alpha>_cost llvm_\<alpha> (z, minus_ecost_cost tc y)); le_cost_ecost y tc\<rbrakk> \<Longrightarrow> (0, t) ## lift_\<alpha>_cost llvm_\<alpha> (z, minus_ecost_cost tc y)\<close>
              add.commute cost_ecost_minus_add_assoc2 lift_\<alpha>_cost_def old.prod.case plus_prod_eqI prod.sel(1) sep_disj_prod_def unique_zero_simps(3))
    done
  subgoal
    using cost_ecost_add_increasing2 by blast
  done

subsection \<open>more HNR rules\<close>

lemma hn_refineI2: 
  assumes "\<And>F s cr M. \<lbrakk> nofailT m ; m = REST M; (\<Gamma>**F) (ll_\<alpha>(s,cr)) \<rbrakk>
          \<Longrightarrow> (\<exists>ra Ca. M ra \<ge> Some Ca \<and>
                     (wp c (\<lambda>r s.  (\<Gamma>' ** R ra r ** F ** GC) (ll_\<alpha> s)) (s,cr+Ca)))"
  shows "hn_refine \<Gamma> c \<Gamma>' R m"  
  apply (auto simp add: hn_refine_def STATE_alt)  
  apply(rule assms) by auto

lemma hn_refine_payday_reverse_alt:
  fixes m :: " ('d, (char list, enat) acost) nrest"
  assumes 
    a: "finite_cost t" 
  and "hn_refine \<Gamma> c \<Gamma>' R (consume m t)"
  shows "hn_refine ($t \<and>* \<Gamma>) c \<Gamma>' R m"
proof -
  from extract_lift_acost_if_less_infinity[OF a]
  obtain t' where t: "t = lift_acost t'" by blast


  show ?thesis
    unfolding t apply(rule hn_refine_payday_reverse)
    apply(fold t)
    apply(fact)
    done
qed



lemma hn_refine_reclaimday: 
   assumes
     nofail: "nofailT m \<Longrightarrow> nofailT (reclaim m \<Phi>)"
     and as: "hn_refine \<Gamma> c \<Gamma>' G (reclaim m \<Phi>)"
   shows "hn_refine \<Gamma> c \<Gamma>' (augment_amor_assn \<Phi> G) m"
proof (rule hn_refineI2)
  fix F s cr M
  assume n: "nofailT m"
      and m: "m = SPECT M" and H: "(\<Gamma> \<and>* F) (ll_\<alpha> (s, cr))"

  from n nofail have z: "nofailT (reclaim m \<Phi>)" by simp
  then obtain M' where kl: " (reclaim m \<Phi>) = SPECT M'"   
    unfolding nofailT_def 
    by force

  from z m have Z: "(\<forall>x t'. M x = Some t' \<longrightarrow> \<Phi> x \<le> t')" apply(simp only: nofailT_reclaim) by auto

  from as[unfolded hn_refine_def STATE_def, rule_format, OF z, OF kl H] obtain ra Ca where
    ff: "Some Ca \<le> M' ra" and wp: "wp c (\<lambda>r s. (\<Gamma>' \<and>* G ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)" by blast

  from ff have "M' ra \<noteq> None"
    by (metis less_eq_option_Some_None)
  with kl[symmetric] have mra: "M ra \<noteq> None" unfolding m
    apply(cases "M ra") apply auto unfolding Sup_nrest_def apply (auto split: if_splits) 
    by (smt SUP_bot_conv(2) Sup_empty empty_Sup fun_upd_apply mem_Collect_eq option.distinct(1))

  then obtain mra where Mra: "M ra = Some mra" by auto

  have nene: "M' ra \<le> Some (mra - \<Phi> ra)"
    using kl unfolding m  apply (auto split: if_splits)
    unfolding Sup_nrest_def apply (auto split: if_splits)
    apply(rule Sup_least) apply auto 
    by (simp add: Mra) 

  with ff have ff': " Some Ca \<le>Some (mra - \<Phi> ra)" by(rule order.trans)

  show "\<exists>ra Ca. Some Ca \<le> M ra \<and> wp c (\<lambda>r s. (\<Gamma>' \<and>* augment_amor_assn \<Phi> G ra r \<and>* F \<and>* GC) (ll_\<alpha> s)) (s, cr + Ca)"
    apply(rule exI[where x=ra])
    apply(rule exI[where x="Ca+\<Phi> ra"])
    apply safe
    subgoal        
      using ff' unfolding Mra apply simp
      apply(rule plus_minus_adjoint_ecost_I) 
      using Z[rule_format, of ra mra] Mra
      by simp
    subgoal using wp_time_frame[OF wp, where t="\<Phi> ra"] unfolding augment_amor_assn_def
      by (auto simp:  sep_conj_left_commute sep_conj_commute add.assoc add.left_commute add.commute)
    done
qed


lemma hn_refine_amortization: 
   assumes
     nofail: "\<And>x r. nofailT (m x r) \<Longrightarrow> nofailT (reclaim (consume (m x r) (\<Phi> x)) \<Phi>)"
  and finite: "\<And>x. finite_cost (\<Phi> x)" 
     and as: "hn_refine (G x x' ** F' r r') (c x' r') (invalid_assn G x x' ** F' r r') G (reclaim (consume (m x r) (\<Phi> x)) \<Phi>)"
   shows
  "hn_refine ((augment_amor_assn \<Phi> G) x x' ** F' r r') (c x' r') (invalid_assn (augment_amor_assn \<Phi> G) x x' ** F' r r') (augment_amor_assn \<Phi> G) (m x r)"
  unfolding invalid_assn_augment_amor_assn
  unfolding augment_amor_assn_def
  apply(subst sep_conj_assoc) apply simp
  apply(fold augment_amor_assn_def)
  apply(rule hn_refine_payday_reverse_alt[OF finite])
  apply(rule hn_refine_reclaimday)
  subgoal apply (simp add: nofailT_consume) using nofail by simp
  subgoal using as by simp
  done





section \<open>Specification of List Operations\<close>


(* TODO: it is not append but snoc ! *)

context fixes T :: ecost begin
definition mop_list_snoc where
 [simp]: "mop_list_snoc  xs x = SPECT [xs @ [x] \<mapsto> T]"
sepref_register mop_list_snoc


definition mop_list_emptylist where
  [simp]: "mop_list_emptylist = SPECT [ [] \<mapsto> T ]"
sepref_register mop_list_emptylist

end



text \<open>The abstract program A for empty list:\<close>






section \<open>Dynamic Lists\<close>

subsection \<open>Dynamic Lists refine lists\<close>

definition "dyn_list_rel = {( ((bs,l,c)) , as) | bs l c  as. take l bs = as \<and> l \<le> c \<and> c = length bs \<and> length bs > 0 }"


lemma dyn_list_rel_alt: "dyn_list_rel = br (\<lambda>(bs,l,c). take l bs) (\<lambda>(bs,l,c). l \<le> c \<and> c = length bs \<and> length bs > 0)"
  unfolding dyn_list_rel_def br_def by auto


lemma dyn_list_rel_sv[relator_props]: "single_valued dyn_list_rel"
  unfolding dyn_list_rel_alt by(rule br_sv)  


subsection \<open>Specification of Dynamic List Operations\<close>

definition "dyn_list_empty_spec T = SPEC (\<lambda>(ls,l,c). l=0 \<and> c=8 \<and> c = length ls) (\<lambda>_. T)"

context
  fixes  T :: "(nat \<times> nat) \<Rightarrow> (char list, enat) acost"
begin
  definition dyn_list_get_spec  :: "('a list*_*_) \<Rightarrow> nat \<Rightarrow> ('a, _) nrest"
    where [simp]: "dyn_list_get_spec \<equiv> \<lambda>(xs,l,_) i. do { ASSERT (i<length xs); consume (RETURNT (xs!i)) (T (l,i)) }"
  sepref_register "dyn_list_get_spec"
end


definition dyn_list_push_spec where
  "dyn_list_push_spec T \<equiv> \<lambda>(bs,l,c) x. SPEC (\<lambda>(bs',l',c'). l'\<le>c' \<and> c'=length bs' \<and> l'=l+1 \<and> length bs' \<ge> length bs
                                                          \<and> take l bs' = take l bs \<and> bs' ! l = x) (\<lambda>_. T)"



text \<open>timerefine commutes with specifications\<close>

lemma timerefine_dyn_list_empty_spec: "timerefine TR (dyn_list_empty_spec T) = dyn_list_empty_spec (timerefineA TR T)"
  unfolding dyn_list_empty_spec_def
  by (auto split: prod.splits simp: SPEC_timerefine_conv)

lemma timerefine_dyn_list_push_spec: "timerefine TR (dyn_list_push_spec T dl x) = dyn_list_push_spec (timerefineA TR T) dl x"
  unfolding dyn_list_push_spec_def
  by (auto split: prod.splits simp: SPEC_timerefine_conv)

text \<open>dynamic list opertions refine the list operations\<close>
 

lemma 
  shows "(uncurry (dyn_list_get_spec T), uncurry (mop_list_get T)) \<in> dyn_list_rel \<times>\<^sub>r Id  \<rightarrow>\<^sub>f \<langle>Id\<rangle>nrest_rel"
  apply(rule frefI)
  apply(rule nrest_relI)
  unfolding uncurry_def dyn_list_get_spec_def mop_list_get_def dyn_list_rel_alt 
  apply (auto simp: in_br_conv consume_RETURNT)
  apply(rule le_acost_ASSERTI)
  apply(rule gwp_specifies_I)
  apply(refine_vcg \<open>-\<close>)
  by auto 





lemma "((bs,l,c),as)\<in>dyn_list_rel \<Longrightarrow> (x',x) \<in> Id
 \<Longrightarrow> dyn_list_push_spec T (bs,l,c) x'
         \<le> \<Down>dyn_list_rel (timerefine (0(''list_append'':=T)) (mop_list_snoc (cost ''list_append'' 1) as x))"
  unfolding dyn_list_push_spec_def mop_list_snoc_def
  apply(subst timerefine_SPECT_map)
  apply(subst SPECT_assign_emb')
  unfolding dyn_list_rel_alt
    apply(subst conc_fun_br)
  apply(subst SPEC_REST_emb'_conv[symmetric])
  apply safe
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  subgoal by (auto simp: in_br_conv take_Suc_conv_app_nth)
  subgoal apply auto 
    by(simp add: norm_cost ) 
  done



lemma dyn_list_push_spec_refines_one_step: 
  "((bs,l,c),as)\<in> dyn_list_rel \<Longrightarrow> (r',r)\<in>Id
   \<Longrightarrow> dyn_list_push_spec T (bs, l, c) r' \<le> \<Down>dyn_list_rel (mop_list_snoc T  as r)"
  unfolding mop_list_snoc_def dyn_list_rel_alt
  apply(subst SPECT_assign_emb')
  unfolding conc_fun_br
  apply(subst SPEC_REST_emb'_conv[symmetric])
  unfolding dyn_list_push_spec_def  apply simp
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  unfolding in_br_conv
  by (auto simp add: take_Suc_conv_app_nth norm_cost) 

lemma dyn_list_push_spec_refines_fref: "(uncurry (PR_CONST (dyn_list_push_spec T)), uncurry (PR_CONST (mop_list_snoc T)))
        \<in> dyn_list_rel \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>dyn_list_rel\<rangle>nrest_rel" 
  apply(rule frefI)
  apply(rule nrest_relI)
  apply(auto split: prod.splits simp del: mop_list_snoc_def simp add: PR_CONST_def uncurry_def)
  apply(rule dyn_list_push_spec_refines_one_step) by auto



subsection \<open>Raw Refinements Dynamic List Operations\<close>


subsubsection \<open>dynamic List init\<close>

text \<open>The abstract program B for empty dynamic list, (in dynamic array currencies) :\<close>

definition dyn_list_new_raw where
  "dyn_list_new_raw = do {
       dst \<leftarrow> mop_list_init_raw (\<lambda>n. cost ''list_init_c'' 8) 8;
       RETURNT (dst,0,8)
    }"

definition dyn_list_new where
  "dyn_list_new ini = do {
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' 8) ini 8;
       RETURNT (dst,0,8)
    }"

text \<open>Refinement THEOREM A-B\<close>

abbreviation "TR_dyn_list_new ==  (0(''list_empty'':=cost ''list_init_c'' 8))"

lemma dyn_list_new_refines:
 "dyn_list_new ini \<le> \<Down>dyn_list_rel (\<Down>\<^sub>C TR_dyn_list_new (mop_list_emptylist (cost ''list_empty'' 1)))"
  unfolding mop_list_emptylist_def dyn_list_new_def dyn_list_rel_alt
  apply (simp add: timerefine_SPECT_map norm_cost )                   
  apply (simp add: SPECT_assign_emb' conc_fun_br)
  apply(rule gwp_specifies_I)
  apply(refine_vcg \<open>-\<close>)    by(auto simp: emb'_def)

subsubsection \<open>dynamic list lookup\<close>

definition dyn_list_get where
  "dyn_list_get \<equiv> \<lambda>(bs,l,c) i. doN {
    mop_list_get (\<lambda>_. cost ''list_get'' 1) bs i
  }"

lemma "( (bs,l,c), as)\<in>dyn_list_rel \<Longrightarrow> dyn_list_get (bs,l,c) i \<le> mop_list_get (\<lambda>_. cost ''list_get'' 1) as i"
  oops


subsubsection \<open>Refinement of dynamic List push\<close>

paragraph \<open>Specification of Dynamic List Double\<close>

term mop_list_init
term mop_list_init_raw
thm hnr_raw_array_new refine_mop_list_init_raw
term mop_array_new
thm hnr_array_new
thm hnr_array_new


text \<open>an dynamic list is a triple (bs,l,c) with the carrier list bs which has capacity \<open>c\<close>, 
      and length \<open>l\<close>, i.e. the first \<open>l\<close> elements are valid. \<close>

definition dyn_list_double_spec where
  "dyn_list_double_spec \<equiv> \<lambda>(bs,l,c). doN {
       ASSERT (l\<le>c \<and> c=length bs);
       SPEC (\<lambda>(bs',l',c'). take l bs' = take l bs \<and> 
              length bs' = 2 * length bs \<and> l' = l \<and> l\<le>c' \<and> c'=length bs')
        (\<lambda>(bs',l',c'). cost ''dyn_list_double_c'' (enat c)) 
  }"


paragraph \<open>Specification of dynamic List basic append\<close>

definition dyn_list_push_basic_spec where
  "dyn_list_push_basic_spec \<equiv> \<lambda>(bs,l,c) x. doN {
      ASSERT (l < length bs \<and> length bs = c);
      bs' \<leftarrow> mop_list_set (\<lambda>_. cost ''list_set'' 1) bs l x;
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      RETURNT (bs',l',c)
  }"


paragraph \<open>Implementation Sketch for dynamic List append:\<close>

definition dyn_list_push where
  "dyn_list_push \<equiv> \<lambda>(bs,l,c) x. doN {
      ASSERT (l\<le>c \<and> c=length bs \<and> 0<length bs);
      if\<^sub>N SPECc2 ''less'' (<) l c then doN {
        dyn_list_push_basic_spec (bs,l,c) x
      } else doN {          
        (bs',l',c') \<leftarrow> dyn_list_double_spec (bs,l,c);
        ASSERT (l'=l \<and> l<c' \<and> c'=length bs' \<and> take l bs = take l bs' );
        dyn_list_push_basic_spec (bs',l',c') x
      }
  }"



paragraph \<open>Amortization proof\<close>
  

definition "push_amortized_cost \<equiv> cost ''dyn_list_double_c'' (1::nat)"
definition "push_overhead_cost \<equiv> cost ''add'' 1 + (cost ''list_set'' 1 + (cost ''if'' 1 + (cost ''less'' 1 + cost ''list_length'' 1)))"
definition "\<Phi>_push \<equiv> (\<lambda>(xs,l,c). (((2*l -length xs)) *m push_amortized_cost))"
abbreviation "\<Phi>_push' \<equiv> lift_acost o \<Phi>_push"

text \<open>The program @{term dyn_list_push} has two cases,
       either the capacity is reached, then we have to resize (at @{term push_amortized_cost} cost per element in the list)
       and push (with cost bounded by @{term push_overhead_cost}),
       or there is still space, then we can push right away (with cost bounded by @{term push_overhead_cost}). 

      We now level out the advertised cost of push by introducing a potential. We will lower the `advertised cost`
      of the resize-case, and increase the `advertised cost` of the push-case.
      The potential is @{term "(\<lambda>(xs,l,c). (((2*l -length xs)) *m push_amortized_cost))"}, which is positive
      if the dynamic list is more than half full. Then we collect @{term push_amortized_cost} credits with
      each push, until we reach capacity, when @{term \<Phi>_push} will get @{term "length xs *m push_amortized_cost"}
      and can be used to pay for the resize.

      To fill up the potential we have to pay 2 x @{term push_amortized_cost} in the advertised cost of all pushs,
      additional to the @{term push_overhead_cost} for inserting an element.

      Note, in this operation the overhead cost is in both cases @{term push_overhead_cost}. If it was not, one has to
      chose the supremum over both to incorporate into the advertised cost.
    \<close>


text\<open>The amortization inequality is: 
  RAW COST \<le>     (  PREPOTENTIAL + ADVERTISED COST ) - POSTPOTENTIAL

  we now prove:
      raw_operation \<le> reclaim ( consume advertised_opertion PREPOTENTIAL) POSTPOTENTIAL
 \<close>


lemma  dyn_list_push_spec_refines_sketch:
    \<comment> \<open>This lemma collects the inequalities of the advertised cost ACC and the potential \<Phi>\<close>
  assumes a: "l \<le> c" "c=length bs" "0<length bs"
  shows "dyn_list_push (bs,l,c) x \<le> reclaim (consume (dyn_list_push_spec ACC (bs,l,c) x) (\<Phi> (bs,l,c))) \<Phi>"
  unfolding dyn_list_push_spec_def
  unfolding dyn_list_push_def
  apply simp
  apply(subst consume_SPEC_eq)
  apply(rule order.trans[rotated])
  apply(rule reclaim_SPEC_le)
  unfolding SPEC_def
  apply(rule gwp_specifies_I)
  unfolding SPECc2_alt dyn_list_push_basic_spec_def mop_list_set_def
    dyn_list_double_spec_def SPEC_REST_emb'_conv
  apply(refine_vcg \<open>-\<close>)
  using a
          defer
         apply auto[1]
         apply auto [1]
  defer
      apply auto [1]
     apply auto [1]
  subgoal by force
  using assms  
   apply auto    
  oops


lemma  dyn_list_push_spec_refines:
  assumes a: "l \<le> c" "c=length bs" "0<length bs"
  shows "dyn_list_push (bs,l,c) x \<le> reclaim (consume (dyn_list_push_spec (lift_acost (2 *m push_amortized_cost + push_overhead_cost)) (bs,l,c) x) (\<Phi>_push' (bs,l,c))) \<Phi>_push'"
  unfolding dyn_list_push_spec_def
  unfolding dyn_list_push_def
  apply simp
  apply(subst consume_SPEC_eq)
  apply(subst reclaim_SPEC)
  subgoal
    unfolding \<Phi>_push_def push_amortized_cost_def push_overhead_cost_def
    apply (auto simp: norm_cost) apply(subst add.commute) apply(subst (2) add.assoc) apply(subst cost_same_curr_add)
    apply(simp add: add.assoc)  
      apply sc_solve  by auto
  unfolding SPEC_def
  apply(rule gwp_specifies_I)
  unfolding SPECc2_alt dyn_list_push_basic_spec_def mop_list_set_def
        dyn_list_double_spec_def SPEC_REST_emb'_conv
  apply(refine_vcg \<open>-\<close>)
  using a 
  subgoal apply auto
    unfolding \<Phi>_push_def apply (simp add: lift_acost_propagate[symmetric] lift_acost_minus)
    apply(subst (4) add.commute)
    apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)  
    apply(rule order.trans[rotated])
     apply(rule lift_acost_mono)
     apply(rule acost_move_sub_le)
     apply(rule costmult_right_mono) apply simp 
    unfolding push_overhead_cost_def  apply(simp add: norm_cost) apply(sc_solve) by (simp add: one_enat_def)
         apply auto[1]
        apply auto [1]
  subgoal apply simp (* can't see why auto would loop here *)
    unfolding \<Phi>_push_def apply (simp add: lift_acost_propagate[symmetric] lift_acost_minus add.assoc)
    apply(subst (5) add.commute)
    apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)
    apply(subst add_diff_assoc_ncost)
    subgoal apply(rule costmult_right_mono) by auto

    apply(subst costmult_minus_distrib)
    apply simp
    unfolding push_overhead_cost_def push_amortized_cost_def
    apply(simp add: norm_cost)
    apply sc_solve  by(simp add: one_enat_def)
      apply auto [1]
     apply auto [1]
  subgoal by force
  using assms  
   apply auto 
  done


subsubsection \<open>Refinement of dynamic List emptylist\<close>

definition "E_dlas \<equiv> cost ''list_init_c'' 8" (* the cost to initialize the empty list *)

lemma  dyn_list_new_raw_refines:
  shows "dyn_list_new_raw \<le> reclaim (consume (dyn_list_empty_spec (lift_acost E_dlas)) 0) \<Phi>_push'"
  unfolding dyn_list_new_raw_def mop_list_init_raw_def
  unfolding dyn_list_empty_spec_def
  apply(subst consume_SPEC_eq)
  apply(subst reclaim_SPEC)
  subgoal unfolding \<Phi>_push_def  by (auto simp: lift_acost_def less_eq_acost_def zero_acost_def)
  unfolding SPEC_def
  unfolding autoref_tag_defs
  apply(rule gwp_specifies_I)
  apply(refine_vcg \<open>-\<close>)
  subgoal 
    unfolding \<Phi>_push_def  apply (auto simp: lift_acost_zero E_dlas_def lift_acost_cost needname_minus_absorb) 
    apply sc_solve by auto
  subgoal by simp
  done


section \<open>Implementing Dynamic Lists\<close>

text \<open>We introduce a locale that expects implementations of the operations of dynamic lists,
    then composes this, to obtain amortized implementations of list operations \<close>


locale dyn_list_assn = 
  fixes 
    TR_dynarray :: "string \<Rightarrow> ecost"
    and dyn_array_raw_assn :: " 'e list \<times> nat \<times> nat \<Rightarrow> 'f \<Rightarrow> assn"
begin


text \<open>We lift the raw_assn to contain the Potential Time Credits.\<close>

abbreviation "\<Phi>_d == \<lambda>x. timerefineA TR_dynarray  (\<Phi>_push' x)"

definition dyn_array_raw_armor_assn where
  "dyn_array_raw_armor_assn \<equiv> \<lambda>(bs, l, c) da'.  $\<Phi>_d (bs, l, c) \<and>* dyn_array_raw_assn (bs, l, c) da'"

lemma dyn_array_raw_armor_assn_alt: "dyn_array_raw_armor_assn = augment_amor_assn \<Phi>_d (dyn_array_raw_assn)"
  unfolding augment_amor_assn_def dyn_array_raw_armor_assn_def 
  apply (rule ext) 
  apply (rule ext) by simp


text \<open>and combining it with the refinement relation between dynamic lists and lists\<close>

definition "dyn_array_assn A = hr_comp (hr_comp (dyn_array_raw_armor_assn) dyn_list_rel) (\<langle>the_pure A\<rangle>list_rel)"

definition "b_aux = hr_comp (dyn_array_raw_armor_assn) dyn_list_rel"
lemma b_aux_unf: "hr_comp (dyn_array_raw_armor_assn) dyn_list_rel = b_aux"
  unfolding b_aux_def by auto
declare b_aux_unf[fcomp_norm_unfold]
thm b_aux_unf
lemma dyn_array_raw_armor_aux: "hr_comp (b_aux) (\<langle>the_pure A\<rangle>list_rel)
           = dyn_array_assn A"
  unfolding b_aux_def dyn_array_assn_def by auto
declare dyn_array_raw_armor_aux[fcomp_norm_unfold]
thm dyn_array_raw_armor_aux
lemma dyn_array_raw_armor_: "hr_comp (hr_comp (dyn_array_raw_armor_assn) dyn_list_rel) (\<langle>the_pure A\<rangle>list_rel)
           = dyn_array_assn A"
  unfolding dyn_array_assn_def by auto
 (*TODO: is this the right way to instrument FCOMP in order to fold the hr_comp ?*)
declare dyn_array_raw_armor_[fcomp_norm_unfold]

end

locale dyn_list_impl = dyn_list_assn TR_dynarray dyn_array_raw_assn 
    for TR_dynarray and dyn_array_raw_assn :: "('e::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> 'f \<Rightarrow> assn" + 
    fixes
      push_size_bound  :: "nat \<Rightarrow> bool"
    and  dyn_array_push
    and dyn_array_push_impl :: "'f \<Rightarrow> 'e \<Rightarrow> 'f llM" 

    and dynamiclist_empty2 :: "((('e) list \<times> nat \<times> nat),ecost) nrest"
    and dynamiclist_empty_impl :: "'f llM"

  assumes 
        wfR_TR_dynarray: "wfR'' TR_dynarray"                           
    and TR_dynarray_keeps_finite: "\<And>\<Phi>. finite {x. the_acost \<Phi> x \<noteq>0} \<Longrightarrow> finite_cost \<Phi> \<Longrightarrow> finite_cost (timerefineA TR_dynarray \<Phi>)"
    and dyn_array_push_refine: "dyn_array_push dl x \<le> \<Down>\<^sub>C TR_dynarray (dyn_list_push dl x)"

    and dyn_array_push_impl_refines: "push_size_bound l \<Longrightarrow> hn_refine (dyn_array_raw_assn (bs,l,c) da' ** id_assn x x')
                        (dyn_array_push_impl da' x')
                      (invalid_assn (dyn_array_raw_assn) (bs,l,c) da' ** id_assn x x')
                        (dyn_array_raw_assn) (dyn_array_push (bs,l,c) x)"

    and emptylist2_real: "(uncurry0 dynamiclist_empty_impl, uncurry0 dynamiclist_empty2) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a  dyn_array_raw_assn"
    and emptylist2_refine: "dynamiclist_empty2 \<le> \<Down>\<^sub>C TR_dynarray dyn_list_new_raw"
begin 




subsection \<open>Combining the Push operation\<close>

abbreviation "push_abstract_advertised_cost == lift_acost (2 *m push_amortized_cost + push_overhead_cost)"
abbreviation "push_concrete_advertised_cost == timerefineA TR_dynarray push_abstract_advertised_cost"


text \<open>this is the operation that is used in abstract programs when already decided which 
      data structure to use here: array_lists\<close>
definition "dyn_array_push_spec = mop_list_snoc push_concrete_advertised_cost"



lemma dyn_list_push_spec_leq_pull_TR:
  fixes TR :: "_\<Rightarrow>ecost"
  assumes *: "wfR'' TR"
  shows "\<Down>\<^sub>C TR (reclaim (NREST.consume (dyn_list_push_spec push_abstract_advertised_cost (bs, l, c) x) (\<Phi>_push' (bs, l, c))) \<Phi>_push') \<le>
         (reclaim (NREST.consume ((dyn_list_push_spec (timerefineA TR push_abstract_advertised_cost) (bs, l, c) x)) (timerefineA TR (\<Phi>_push' (bs, l, c)))) (timerefineA TR o \<Phi>_push'))"
  unfolding dyn_list_push_spec_def
  apply simp
  supply [[unify_trace_failure]]
  apply(rule pull_timerefine_through_reclaim)
   apply(rule *) 
  subgoal apply(auto simp: \<Phi>_push_def) apply(subst lift_acost_propagate[symmetric])
    apply(rule lift_acost_mono)
    apply(subst add.commute) apply(subst add.assoc)
    apply(subst costmult_add_distrib_left)
    apply(subst add.commute)
    apply(rule add_increasing2_nat_acost) 
    apply(rule costmult_right_mono) by auto 
  done


text \<open>Now we combine two refinements:
  \<^item> the refinement of the dynamic list push specification @{term dyn_list_push_spec} incurring the
      advertised cost with the algorithm sketch @{term dyn_list_push} based on the real cost:
      @{thm dyn_list_push_spec_refines} contains the amortization proof. 
     Both programs use currencies of the dynamic list!
  \<^item> the refinement of the algorithm sketch @{term dyn_list_push} to the NREST program @{term dyn_array_push}
     which is a timerefinement using the exchange rate @{term TR_dynarray} to exchange from currencies
     of the dynamic list into LLVM currencies\<close>

lemma dyn_array_push_refines:
  "\<lbrakk>l \<le> c; c = length bs; 0 < length bs\<rbrakk> \<Longrightarrow> dyn_array_push (bs,l,c) x
    \<le> reclaim
          (NREST.consume (dyn_list_push_spec push_concrete_advertised_cost (bs, l, c) x)
            (\<Phi>_d (bs, l, c)))
          \<Phi>_d"
  apply(rule order.trans)   
  apply(rule dyn_array_push_refine)
  apply(rule order.trans)
   apply(rule timerefine_mono2)
  apply(rule wfR_TR_dynarray)
   apply(rule dyn_list_push_spec_refines)
     apply simp_all [3]
  apply(rule order.trans)
   apply(rule dyn_list_push_spec_leq_pull_TR)
  apply(rule wfR_TR_dynarray)
  apply(simp add: timerefine_dyn_list_push_spec)
  unfolding comp_def
  by auto

text \<open>Now we combine the raw hnr-rule @{thm dyn_array_push_impl_refines} with the
  amortization refinement @{thm dyn_array_push_refines}}\<close>

lemma dyn_array_push_impl_refines_dyn_list_push_spec: "\<lbrakk>l \<le> c; c = length bs; 0 < length bs; push_size_bound l\<rbrakk>
\<Longrightarrow> hn_refine (hn_ctxt (dyn_array_raw_armor_assn) (bs, l, c) da' \<and>* hn_ctxt id_assn r r')
     (dyn_array_push_impl $ da' $ r')
     (hn_invalid (dyn_array_raw_armor_assn) (bs, l, c) da' \<and>* hn_ctxt id_assn r r')
       (dyn_array_raw_armor_assn)
      (PR_CONST (dyn_list_push_spec push_concrete_advertised_cost) $ (bs, l, c) $ r) "
  unfolding hn_ctxt_def APP_def PR_CONST_def
  unfolding dyn_array_raw_armor_assn_alt apply (simp only: prod.case)        
  apply(rule hn_refine_amortization[where m="dyn_list_push_spec push_concrete_advertised_cost" and c=dyn_array_push_impl and \<Phi>="\<Phi>_d"])
  subgoal 
    apply(simp add: nofailT_reclaim nofailT_consume)
    unfolding dyn_list_push_spec_def apply (auto simp: SPEC_def consume_def split: prod.splits)
    unfolding \<Phi>_push_def
    apply(subst timerefineA_propagate[OF wfR_TR_dynarray, symmetric])
    apply(rule timerefineA_mono[OF wfR_TR_dynarray])
    apply auto
    unfolding lift_acost_propagate[symmetric]
    apply(rule lift_acost_mono) 
    apply(subst add.assoc[symmetric])
    apply(subst costmult_add_distrib_left) 
    apply(rule add_increasing2_nat_acost) 
    apply(rule costmult_right_mono) by auto
  subgoal 
    apply(rule TR_dynarray_keeps_finite)
    subgoal apply (auto simp: \<Phi>_push_def lift_acost_def push_amortized_cost_def norm_cost split: prod.splits)
      apply(rule finite_subset[where B="{''dyn_list_double_c''}"])
       apply auto
      apply(rule ccontr) unfolding cost_def zero_acost_def zero_enat_def by auto
    by(auto intro: finite_cost_lift_acost)
  apply(rule hn_refine_ref)
   apply(rule dyn_array_push_impl_refines) apply simp
  apply(rule dyn_array_push_refines)
    apply auto
  done




lemma dyn_array_push_impl_refines_dyn_list_push_spec':
"\<lbrakk>(case x of (bs,l,c) \<Rightarrow> l \<le> c \<and> c = length bs \<and> 0 < length bs \<and> push_size_bound l)\<rbrakk>
  \<Longrightarrow> hn_refine (hn_ctxt (dyn_array_raw_armor_assn) x x' \<and>* hn_ctxt id_assn r r')
     (dyn_array_push_impl $ x' $ r')
     (hn_invalid (dyn_array_raw_armor_assn) x x' \<and>* hn_ctxt id_assn r r')
       (dyn_array_raw_armor_assn)
      (PR_CONST (dyn_list_push_spec push_concrete_advertised_cost) $ x $ r) "
  apply(cases x)
  apply (simp only:)
  apply(rule dyn_array_push_impl_refines_dyn_list_push_spec)
  by auto

lemmas dyn_array_push_impl_refines_dyn_list_push_spec_hfref = dyn_array_push_impl_refines_dyn_list_push_spec'[to_hfref]

thm dyn_array_push_impl_refines_dyn_list_push_spec' dyn_list_push_spec_refines_fref[where T="lift_acost (2 *m push_amortized_cost + push_overhead_cost)"]







text \<open>this makes the tactic \<open>solve_attains_sup\<close> solve the supattains sidecondition, 
  because \<open>tagged_solver\<close> can then solve the single_valued goal. \<close>

thm auto_weaken_pre_comp_PRE_I
(*
lemma "(\<And>a aa. push_size_bound (a, aa, length a)) \<Longrightarrow>
  comp_PRE (dyn_list_rel \<times>\<^sub>r Id) (\<lambda>_. True) (\<lambda>x (a, b). case a of (bs, l, c) \<Rightarrow> l \<le> c \<and> c = length bs \<and> 0 < length bs \<and> push_size_bound (bs, l, c))
   (\<lambda>x. nofailT (uncurry (PR_CONST (mop_list_snoc push_concrete_advertised_cost)) x)) (a, b)"
  apply(rule auto_weaken_pre_comp_PRE_I)
   apply simp 
  apply (simp_all add: dyn_list_rel_def )
  apply safe    
  subgoal apply simp done
  subgoal apply simp done
  subgoal apply simp done
  subgoal apply simp
    oops
lemma "\<lbrakk>\<And>a aa. X (a, aa, length a); (((aa, aaa, ba), baa), a, b) \<in> {((bs, l, length bs), take l bs) |bs l. l \<le> length bs \<and> bs \<noteq> []} \<times>\<^sub>r Id\<rbrakk>
    \<Longrightarrow> X (aa, aaa, ba)" apply simp

lemma zzz: "\<lbrakk>\<And>a aa. push_size_bound (a, aa, length a); ((aa, aaa, b), a) \<in> dyn_list_rel\<rbrakk> \<Longrightarrow> push_size_bound (aa, aaa, b)"
  sorry

*)

 
thm dyn_array_push_impl_refines_dyn_list_push_spec_hfref dyn_list_push_spec_refines_fref

lemma XXX[fcomp_prenorm_simps]: "((as,l,c),x)\<in> dyn_list_rel \<Longrightarrow> push_size_bound l = push_size_bound (length x)"
  unfolding dyn_list_rel_def by auto

lemma dyn_array_push_fcomp_prenorm[fcomp_prenorm_simps]:
  "((bs,l,c),x)\<in> dyn_list_rel \<Longrightarrow> l \<le> c \<and> c = length bs \<and> bs \<noteq> []"
  by(auto simp: dyn_list_rel_def)

lemmas dyn_array_push_impl_refines_dyn_array_push_spec
  = dyn_array_push_impl_refines_dyn_list_push_spec_hfref[FCOMP dyn_list_push_spec_refines_fref, folded dyn_array_push_spec_def]


thm dyn_array_push_impl_refines_dyn_array_push_spec



lemma taaaa: "(uncurry (PR_CONST dyn_array_push_spec), uncurry (PR_CONST dyn_array_push_spec))
        \<in>  \<langle>R\<rangle>list_rel \<times>\<^sub>r R \<rightarrow>\<^sub>f \<langle>\<langle>R\<rangle>list_rel\<rangle>nrest_rel" 
  apply rule
  unfolding nrest_rel_def dyn_array_push_spec_def   
  apply auto
  unfolding conc_fun_RES apply auto 
  apply (simp add: le_fun_def)  
  apply(rule Sup_upper) apply auto  
  by (meson list_rel_append2 list_rel_simp(4) refine_list(1))  


lemma one_time_dyn_array_push_spec[OT_intros]: "one_time (dyn_array_push_spec a b)"
  apply(auto simp:  dyn_array_push_spec_def) by (intro OT_intros)

(* TODO: Move! *)  
lemmas [fcomp_prenorm_simps] = list_rel_imp_same_length  
  
  
lemmas G_push =  dyn_array_push_impl_refines_dyn_array_push_spec[FCOMP taaaa] 
 





subsubsection \<open>obsolete\<close>


abbreviation "specify_cost == 0(''list_append'':= push_concrete_advertised_cost)"

lemma dyn_list_push_spec_refines: 
  "((bs,l,c),as)\<in> dyn_list_rel \<Longrightarrow> (r',r)\<in>Id
   \<Longrightarrow> dyn_list_push_spec push_concrete_advertised_cost (bs, l, c) r' \<le> \<Down>dyn_list_rel (\<Down>\<^sub>C specify_cost  (mop_list_snoc (cost ''list_append'' 1)  as r))"
  unfolding mop_list_snoc_def dyn_list_rel_alt
  apply(subst timerefine_SPECT_map)
  apply(subst SPECT_assign_emb')
  unfolding conc_fun_br
  apply(subst SPEC_REST_emb'_conv[symmetric])
  unfolding dyn_list_push_spec_def  apply simp
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  unfolding in_br_conv
  by (auto simp add: take_Suc_conv_app_nth norm_cost) 



subsection \<open>Combining the Emptylist operation\<close>

abbreviation "el_abstract_advertised_cost == lift_acost E_dlas"
abbreviation "el_concrete_advertised_cost == timerefineA TR_dynarray el_abstract_advertised_cost"

definition "dynamiclist_empty_spec = mop_list_emptylist el_concrete_advertised_cost"

lemma dyn_list_empty2_refines:
  "dynamiclist_empty2
    \<le> reclaim (dyn_list_empty_spec el_concrete_advertised_cost) \<Phi>_d"
  apply(rule order.trans)
  apply(rule emptylist2_refine)
  apply(rule order.trans)
   apply(rule timerefine_mono2)
  apply(rule wfR_TR_dynarray)
   apply(rule dyn_list_new_raw_refines)
  apply(rule order.trans)
  unfolding dyn_list_empty_spec_def
   apply(rule pull_timerefine_through_reclaim[OF wfR_TR_dynarray])
  subgoal by (auto simp: \<Phi>_push_def lift_acost_zero ecost_nneg)
  apply(simp add: timerefine_dyn_list_empty_spec consume_0)
  unfolding comp_def            
  by auto
  
(* declare [[unify_trace_failure]] *)

thm emptylist2_real
thm emptylist2_real[to_hnr]
thm emptylist2_refine

lemma YEAH32: "hn_refine \<box> dynamiclist_empty_impl \<box>
       (dyn_array_raw_armor_assn)
      (PR_CONST (dyn_list_empty_spec el_concrete_advertised_cost) ) "
  unfolding hn_ctxt_def APP_def PR_CONST_def
  unfolding dyn_array_raw_armor_assn_alt
  apply(rule hn_refine_reclaimday)
  subgoal                                    
    apply(simp add: nofailT_reclaim nofailT_consume)
    unfolding dyn_list_empty_spec_def apply (auto simp: SPEC_def consume_def split: prod.splits)
    unfolding \<Phi>_push_def apply auto
    apply(rule timerefineA_mono[OF wfR_TR_dynarray])
    by (auto simp: lift_acost_zero ecost_nneg) 
  apply(rule hn_refine_ref) 
   apply(rule emptylist2_real[to_hnr])
  apply(rule dyn_list_empty2_refines)
  done

lemmas RICHTIGCOOL2 = YEAH32[to_hfref]

lemma dynamiclist_empty_refines_fref: "(uncurry0 (PR_CONST (dyn_list_empty_spec (T::ecost))), uncurry0 (PR_CONST (mop_list_emptylist T)))
        \<in> unit_rel \<rightarrow>\<^sub>f \<langle>dyn_list_rel\<rangle>nrest_rel" 
  apply(rule frefI)
  apply(rule nrest_relI)
  unfolding mop_list_emptylist_def dyn_list_empty_spec_def dyn_list_rel_alt
  apply (simp add: timerefine_SPECT_map norm_cost )                   
  apply (simp add: SPECT_assign_emb' conc_fun_br)
  apply(subst SPEC_REST_emb'_conv[symmetric])
  apply(rule SPEC_leq_SPEC_I_even_stronger)
  by auto

lemmas GGG = RICHTIGCOOL2[FCOMP dynamiclist_empty_refines_fref, folded dynamiclist_empty_spec_def]



lemma taaaa_emp: "(uncurry0 (PR_CONST  (dynamiclist_empty_spec)), uncurry0 (PR_CONST  (dynamiclist_empty_spec)))
        \<in> unit_rel \<rightarrow>\<^sub>f \<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>nrest_rel" 
  apply rule
  unfolding nrest_rel_def dynamiclist_empty_spec_def mop_list_emptylist_def 
  apply auto
  unfolding conc_fun_RES apply auto 
  by (simp add: le_fun_def)  

lemmas GGG' = GGG[FCOMP taaaa_emp]


lemma GGG_empty: "(uncurry0 dynamiclist_empty_impl, uncurry0 (PR_CONST dynamiclist_empty_spec)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a dyn_array_assn A"
  apply(rule GGG')
  apply(intro allI SC_attains_supI) 
  apply(rule one_time_attains_sup)
  unfolding uncurry0_def dynamiclist_empty_spec_def mop_list_emptylist_def apply simp
  apply(intro OT_intros)
  done

end

context size_t_context begin

definition dyn_array_raw_assn  :: "('x::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> 'x ptr \<times> ('size_t) word \<times> 'size_t word \<Rightarrow> assn" where
  "dyn_array_raw_assn  \<equiv> (array_assn id_assn \<times>\<^sub>a snat_assn' TYPE('size_t) \<times>\<^sub>a snat_assn' TYPE('size_t))"
(*
     \<lambda>(bs,l,c) (p,l',c'). array_assn id_assn bs p ** snat_assn' TYPE('size_t) l l' ** snat_assn' TYPE('size_t) c c'"
*)





subsection \<open>implement nth\<close>


(* TODO *)

subsection  \<open>implement push\<close>


definition "TR_doublec = 0(''dyn_list_double_c'':=   cost'_narray_new 2
                               + lift_acost list_copy_body_cost
                                + cost ''icmp_slt'' 1 + cost ''call'' 1 + cost ''if'' 1
                                + cost ''mul'' 1
                                          )"

lemma wfR''_TR_doublec[simp]: "wfR'' TR_doublec"
  unfolding TR_doublec_def
  by auto 


term   dyn_list_double_spec

definition dyn_list_double :: "('x::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> ('x list \<times> nat \<times> nat, (char list, enat) acost) nrest"  where
  "dyn_list_double  \<equiv> \<lambda>(bs,l,c). doN {
       ASSERT (l=c \<and> c=length bs);
       c' \<leftarrow> SPECc2 ''mul'' (*) c 2;
       bs' \<leftarrow> mop_array_new id_assn init c';
       bs'' \<leftarrow> list_copy_spec list_copy_spec_time bs' bs l;
       RETURNT (bs'',l,c')
  }"


lemma dyn_list_double_correct:
    "c>0 \<Longrightarrow> l=c \<Longrightarrow> dyn_list_double (bs,l,c) \<le> \<Down> Id ( \<Down>\<^sub>C TR_doublec (dyn_list_double_spec (bs,l,c)))"
  unfolding dyn_list_double_spec_def 
  apply(split prod.splits)+ apply (rule)+
  apply(rule ASSERT_D3_leI) 
  apply (auto simp add: le_fun_def SPEC_timerefine_conv split: prod.splits)  
  unfolding SPEC_def 
  apply(rule gwp_specifies_I) 
  unfolding dyn_list_double_def SPECc2_def mop_array_new_def mop_list_init_def
  unfolding list_copy_spec_def
  apply(refine_vcg \<open>-\<close> rules:)
  subgoal for a b ca
     apply(rule If_le_Some_rule2)
    unfolding list_copy_spec_time_def list_copy_body_cost_def TR_doublec_def
     apply (auto simp: norm_cost)
    apply(sc_solve) 
    apply (auto simp: numeral_eq_enat one_enat_def)
    apply(rule order.trans[where b="1+(1+1)"]) apply simp apply(rule add_mono) apply simp
      apply(rule add_mono) apply simp_all done
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done


definition dyn_list_double2 :: "('x::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> ('x list \<times> nat \<times> nat, (char list, enat) acost) nrest"  where
  "dyn_list_double2  \<equiv> \<lambda>(bs,l,c). doN {
       ASSERT (l=c \<and> c=length bs);
       c' \<leftarrow> SPECc2 ''mul'' (*) c 2;
       bs' \<leftarrow> mop_array_new id_assn init c';
       bs'' \<leftarrow> list_copy bs' bs l;
       mop_free bs;
       RETURNT (bs'',l,c')
  }"

 (*
lemma "(dyn_list_double2, dyn_list_double) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nrest_rel"
  apply rule
  apply (rule nrest_C_relI)   
  unfolding dyn_list_double2_def dyn_list_double_def
  unfolding SPECc2_alt
    apply normalize_blocks
  apply(refine_rcg consumea_Id_refine bindT_refine_easy) *)

term "TTId {''malloc'', ''free'' , ''if'' , ''if'' , ''icmp_eq'' , ''ptrcmp_eq''}" 

lemma TTId_simps: "x \<in> S \<Longrightarrow> TTId S x = cost x 1"
      "x \<notin> S \<Longrightarrow> TTId S x = 0"
  unfolding TTId_def by auto

lemma
  mop_array_new_minimal_Trefinement:
   "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> mop_array_new R a b \<le> \<Down> Id (timerefine (TTId {''malloc'', ''free'' , ''if'' , ''if'' , ''icmp_eq'' , ''ptrcmp_eq''}) (mop_array_new R a' b'))"
  unfolding mop_array_new_def mop_list_init_def 
  apply(simp del: conc_Id)
  apply(rule consume_refine)
  subgoal apply(rule wfR''_TTId_if_finite) by simp
  subgoal apply(auto simp add: norm_cost intro!: wfR''_TTId_if_finite)
    apply(subst timerefineA_propagate) apply(intro wfR''_TTId_if_finite) apply simp
    apply(subst timerefineA_propagate) apply(intro wfR''_TTId_if_finite) apply simp
    apply(subst timerefineA_propagate) apply(intro wfR''_TTId_if_finite) apply simp
    apply(subst timerefineA_propagate) apply(intro wfR''_TTId_if_finite) apply simp
    apply(subst timerefineA_propagate) apply(intro wfR''_TTId_if_finite) apply simp
    by(auto simp add: norm_cost TTId_simps)
  subgoal  apply(rule RETURNT_refine_t) by simp
  done

lemma
  mop_array_new_Trefinement:
   "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> mop_array_new R a b \<le> \<Down> Id (timerefine TId (mop_array_new R a' b'))"
  by (auto simp: timerefine_id)

thm selfrefine_TTId_currs_of_M_both

lemma pff: "list_copy a b c \<le>  list_copy_spec list_copy_spec_time a b c"
  using list_copy_correct[THEN frefD, THEN nrest_relD, unfolded uncurry_def, simplified]
  by auto 

lemma list_copy_self_refine: "(a,a')\<in>Id \<Longrightarrow> (b,b')\<in>Id \<Longrightarrow> (c,c')\<in>Id
    \<Longrightarrow> list_copy a b c \<le> \<Down>Id (\<Down>\<^sub>C TId (list_copy_spec list_copy_spec_time a' b' c'))"
  using list_copy_correct[THEN frefD, THEN nrest_relD, unfolded uncurry_def, simplified]
  by (auto simp: timerefine_id) 

lemma zzz: "(nofailT (list_copy_spec list_copy_spec_time dst src n))
    \<Longrightarrow> currs_of_M (list_copy_spec list_copy_spec_time dst src n) = currs_of (list_copy_spec_time n)"
  unfolding list_copy_spec_def 
  unfolding currs_of_M_def
  by (auto simp: nofailT_bindT_ASSERT_iff split: if_splits)

lemma currs_of_add:
  fixes a :: ecost
  shows "currs_of (a+b) = currs_of a \<union> currs_of b"
  apply(cases a; cases b)
  by (auto simp:  currs_of_def)

lemma currs_of_costmult:
  fixes b :: ecost
  shows "currs_of (a *m b) \<subseteq> currs_of b"
  apply(cases b)
  by (auto simp: costmult_def currs_of_def) 

lemma currs_of_costmult_gt:
  fixes b :: ecost
  shows "a>0 \<Longrightarrow> currs_of (a *m b) = currs_of b"
  apply(cases b)
  by (auto simp: costmult_def currs_of_def) 

lemma uu: "(\<Union>n. currs_of (list_copy_spec_time n)) = currs_of (list_copy_spec_time 1)"
  unfolding list_copy_spec_time_def
  apply (auto simp: list_copy_body_cost_def norm_cost )   
  subgoal for x n
    apply(cases "n=0") 
     apply(simp add: currs_of_add cost_zero zero_enat_def[symmetric])
    by (auto simp:  currs_of_add pff2 zero_enat_def) 
  done

 
  

lemma tta: "currs_of (list_copy_spec_time n) \<subseteq> (\<Union>n. currs_of (list_copy_spec_time n))"
  unfolding list_copy_spec_time_def
  by (auto simp: list_copy_body_cost_def norm_cost )    


lemma list_copy_tight: "(dsti,dst)\<in>Id \<Longrightarrow> (srci,src)\<in>Id \<Longrightarrow> (ni,n)\<in>Id \<Longrightarrow>
          list_copy dsti srci ni \<le> \<Down> Id (\<Down>\<^sub>C (TTId (\<Union>n. currs_of (list_copy_spec_time n)))
                                         (list_copy_spec list_copy_spec_time dst src n))"
  apply auto
  apply(rule order.trans)
   apply(rule pff)
  apply(rule order.trans[rotated])
   apply(rule timerefine_TTId_mono)
  apply(rule tta[where n=n]) defer
   apply(subst selfrefine_TTId_currs_of_M_both_yeah)
  supply [[show_types]]
    apply(rule zzz) apply simp apply auto 
  unfolding uu 
  unfolding list_copy_spec_time_def list_copy_body_cost_def
  by(auto simp: norm_cost currs_of_add intro: finite_subset[OF currs_cost] )
 


lemma pff3: "currs_of (cost x (i::enat)) \<subseteq> {x}"
  unfolding currs_of_def cost_def  by (auto simp: zero_acost_def)

lemma finite_currs_of_lcst[simp]: "finite (currs_of (list_copy_spec_time l))"
  unfolding list_copy_spec_time_def list_copy_body_cost_def
  by(auto simp add: norm_cost currs_of_add pff2 intro: finite_subset[OF pff3])    

declare RETURNT_refine_t[refine0 del]

lemma RETURNT_refine_tight[refine0]: "(c,a)\<in>R \<Longrightarrow> RETURNT c \<le> \<Down>R (\<Down>\<^sub>C 0 (RETURNT a))"
  by (rule RETURNT_refine_t)

term mop_free

schematic_goal dyn_list_double2_refine_tight: 
  "(bs,bs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (c,c')\<in>Id
    \<Longrightarrow> dyn_list_double2 (bs, l, c) \<le> \<Down> Id (\<Down>\<^sub>C (?E) (dyn_list_double (bs', l', c')))"
  unfolding dyn_list_double2_def dyn_list_double_def mop_free_def
  apply normalize_blocks (* TODO: rule for mop_free refine *)
  apply(refine_rcg) apply auto[1]
  apply(refine_rcg  bindT_refine_conc_time_my_inres_sup
          SPECc2_refine_exch mop_array_new_minimal_Trefinement
          list_copy_tight)
                 apply refine_dref_type 
  by (auto simp: TId_apply uu intro!: wfR''_supI wfR''_TTId_if_finite )

concrete_definition TR_dld2 is dyn_list_double2_refine_tight uses "_ \<le> \<Down> Id (\<Down>\<^sub>C \<hole> _)" 
lemmas dyn_list_double2_refine = TR_dld2.refine
thm TR_dld2.refine TR_dld2_def

lemma II:
  fixes A :: "_ \<Rightarrow> ecost"
  shows "sup A 0 = A" 
  apply (auto simp: sup_fun_def sup_acost_def zero_acost_def) apply(rule ext)  
  by (simp add: complete_linorder_sup_max)  


lemma  III:
  shows "sup ( (TTId A) :: _ \<Rightarrow> ecost) (TTId B) = TTId (A\<union>B)" 
  unfolding TTId_def apply(auto simp: sup_acost_def sup_fun_def)
  apply(rule ext) by (auto simp: zero_acost_def complete_linorder_sup_max)

lemma h: "(\<lambda>_. 0)(''mul'' := cost ''mul'' 1) = TTId {''mul''}"
  unfolding TTId_def by auto

schematic_goal TR_dld2_alt: "TR_dld2 = ?A"
  apply(rule hide)
  unfolding TR_dld2_def
  unfolding list_copy_spec_time_def
  apply(simp only: II III h )
  apply(auto simp: currs_of_add)
  apply(subst currs_of_costmult_gt) apply (simp add: zero_enat_def)
  unfolding list_copy_body_cost_def
  apply(auto simp: currs_of_add norm_cost)
  apply(auto simp: currs_of_cost_gt zero_enat_def) 
  apply(subst currs_of_cost_gt, simp)+ 
  apply simp
  apply(rule hideI) apply simp done

(* obsolete *)
lemma dyn_list_double2_refine_coarse: "dyn_list_double2 (bs, l, c) \<le> \<Down> Id (\<Down>\<^sub>C TId (dyn_list_double (bs, l, c)))"
  unfolding dyn_list_double2_def dyn_list_double_def
  unfolding mop_free_def
  apply normalize_blocks
  apply(refine_rcg bindT_refine_easy SPECc2_refine mop_array_new_Trefinement
        list_copy_self_refine
       )
  apply refine_dref_type
  by (auto simp: TId_apply)


  thm bindT_refine_conc_time_my_inres_sup

lemma wfR''_TR_dld2[simp]: "wfR'' TR_dld2"
  unfolding TR_dld2_alt apply(rule wfR''_TTId_if_finite)
  by simp


  thm dyn_list_double2_refine dyn_list_double_correct

lemma dyn_list_double2_correct:"\<lbrakk>0 < c; l = c; (bs,bs')\<in>Id; (l,l')\<in>Id; (c,c')\<in>Id \<rbrakk> \<Longrightarrow>
  dyn_list_double2 (bs', l', c') \<le> \<Down> Id (\<Down>\<^sub>C (pp TR_dld2 TR_doublec) (dyn_list_double_spec (bs, l, c))) "
  apply(rule order.trans)
   apply(rule dyn_list_double2_refine) apply simp apply simp apply simp
  apply (simp add: timerefine_id timerefine_iter2[symmetric])
  apply(rule timerefine_mono2)
  subgoal  by simp 
  apply(rule order.trans[rotated])
   apply(rule dyn_list_double_correct[simplified])
  by auto


lemma "pp TR (F(x:=l)) = (pp TR F)(x:=timerefineA TR l)"
  using pp_fun_upd by metis

lemma pp_0: "pp TR 0 = (0::_ \<Rightarrow> ecost)"
  unfolding pp_def by(auto simp: zero_acost_def)

schematic_goal TR_dld2_dynaaray_simp: "(pp TR_dld2 TR_doublec) = ?gg"
  apply(rule hide)
  unfolding TR_doublec_def 
  apply(simp only: pp_fun_upd pp_0)
  unfolding list_copy_body_cost_def
  apply(auto simp: norm_cost )
  apply(auto simp: TR_dld2_alt TTId_simps)
  apply(auto simp: costmult_cost)
  apply(rule hideI)
  apply(rule refl) done

thm TR_dld2_dynaaray_simp


term dyn_list_push_basic_spec
                               
definition dyn_list_push_basic :: "'a::llvm_rep list \<times> nat \<times> nat \<Rightarrow> 'a \<Rightarrow> ('a list \<times> nat \<times> nat, (char list, enat) acost) nrest" where
  "dyn_list_push_basic \<equiv> \<lambda>(bs,l,c) x. doN {
      ASSERT (l < length bs \<and> length bs = c);
      bs' \<leftarrow> mop_array_upd  bs l x;
      l' \<leftarrow> SPECc2 ''add'' (+) l 1;
      RETURNT (bs',l',c)
  }"

lemma mop_array_upd_refines:
  "(bs,bs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (x,x')\<in>Id 
     \<Longrightarrow> mop_array_upd bs l x \<le>  \<Down>Id (\<Down>\<^sub>C (0(''list_set'':=lift_acost mop_array_upd_cost)) (mop_list_setN bs' l' x'))"
  unfolding mop_array_upd_def mop_list_set_def
  apply(refine_rcg) by (auto simp: norm_cost)
  

schematic_goal dyn_list_push_basic_refine_tight:
  "(bs,bs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> (x,x')\<in>Id
    \<Longrightarrow> dyn_list_push_basic (bs,l,c) x  \<le> \<Down>Id (\<Down>\<^sub>C ?TR (dyn_list_push_basic_spec (bs',l',c') x'))"
  unfolding dyn_list_push_basic_def dyn_list_push_basic_spec_def
  apply(refine_rcg) apply auto[1]
  apply(refine_rcg  bindT_refine_conc_time_my_inres_sup
          SPECc2_refine_exch mop_array_upd_refines)
                 apply refine_dref_type 
  by (auto simp: TId_apply intro!: wfR''_supI wfR''_TTId_if_finite )

concrete_definition TR_dlpc is dyn_list_push_basic_refine_tight uses "_ \<le> \<Down> Id (\<Down>\<^sub>C \<hole> _)" 
thm TR_dlpc.refine
thm TR_dlpc.refine[no_vars]
lemma dyn_list_push_basic_refine: 
  "(dl,dl')\<in>Id \<Longrightarrow> (x,x')\<in>Id \<Longrightarrow> dyn_list_push_basic dl x \<le> \<Down> Id (\<Down>\<^sub>C TR_dlpc (dyn_list_push_basic_spec dl' x'))"
  apply(cases dl; cases dl')
  apply(simp del: conc_Id) apply(rule TR_dlpc.refine) by auto

lemma wfR''_TR_dlpc[simp]: "wfR'' TR_dlpc"
  unfolding TR_dlpc_def
  apply(intro wfR''_supI wfR''_upd)
  by(auto)

definition has_enough_space  :: "('a::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> (bool, (char list, enat) acost) nrest" where
  "has_enough_space = (\<lambda>(bs,l,c).  SPECc2 ''icmp_slt'' (<) l c)"

sepref_def has_enough_space_impl is "has_enough_space"
  :: "(dyn_array_raw_assn:: ('x::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> 'x ptr \<times> ('size_t) word \<times> 'size_t word \<Rightarrow> assn)\<^sup>k \<rightarrow>\<^sub>a (bool1_assn::bool\<Rightarrow>_\<Rightarrow>assn)"
  unfolding has_enough_space_def
  unfolding dyn_array_raw_assn_def
  by sepref

(* aktuelles design: if *)
(* besser: ensure_capacity ; push_back_basic *)
definition dynamiclist_append2 where
  "dynamiclist_append2 \<equiv> \<lambda>dl x. doN {
      if\<^sub>N has_enough_space dl then doN {
        dyn_list_push_basic dl x
      } else doN {          
        dl' \<leftarrow> dyn_list_double2 dl;
        dyn_list_push_basic dl' x
      }
  }"

lemma dynamiclist_append2_refines_tight_aux: 
    "(\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel) = Id"
  apply simp done

schematic_goal dynamiclist_append2_refines_tight:
  "(bs,bs')\<in>Id \<Longrightarrow> (l,l')\<in>Id \<Longrightarrow> (c,c')\<in>Id \<Longrightarrow> (x,x')\<in>Id \<Longrightarrow>
      dynamiclist_append2 (bs,l,c) x \<le>  \<Down>Id (\<Down>\<^sub>C ?TR (dyn_list_push (bs',l',c') x'))"
  unfolding dynamiclist_append2_def dyn_list_push_def has_enough_space_def
  apply(refine_rcg) 
  apply(refine_rcg  bindT_refine_conc_time_my_inres_sup
          SPECc2_refine_exch mop_array_upd_refines
          MIf_refine_sup dyn_list_push_basic_refine
          dyn_list_double2_refine
        )
                apply refine_dref_type 
                     apply(auto)[2]
  apply(simp only: dynamiclist_append2_refines_tight_aux)
            apply(rule dyn_list_double2_correct)
  apply (auto simp: TId_apply   intro!: wfR''_supI wfR''_TTId_if_finite wfR''_ppI )
        apply(auto simp: inres_SPECc2)
  apply(auto intro!: wfR''_upd)
  done

concrete_definition TR_da is dynamiclist_append2_refines_tight uses "_ \<le> \<Down> Id (\<Down>\<^sub>C \<hole> _)" 
thm TR_da_def
lemmas dynamiclist_append2_refines_aux = TR_da.refine
lemma wfR''_TR_da[simp]: "wfR'' TR_da"
  unfolding TR_da_def
  apply(intro wfR''_supI wfR''_upd wfR''_ppI) by simp_all

lemma dynamiclist_append2_refines:
    "dynamiclist_append2 dl x \<le> \<Down> Id (\<Down>\<^sub>C TR_da (dyn_list_push dl x))"
  apply(cases dl) apply (simp del: conc_Id)
  apply(rule dynamiclist_append2_refines_aux) by auto
 


sepref_def dyn_list_double_impl is "dyn_list_double2 :: ('a::llvm_rep) list \<times> _ \<Rightarrow> _"
  :: "[\<lambda>(ls,l,c). l * 2 < max_snat LENGTH('size_t)]\<^sub>a
     (dyn_array_raw_assn :: ('a) list \<times> nat \<times> nat \<Rightarrow> ('a) ptr \<times> 'size_t word \<times> 'size_t word \<Rightarrow> assn)\<^sup>d
        \<rightarrow> (dyn_array_raw_assn :: ('a) list \<times> _ \<Rightarrow> _)"
  unfolding dyn_list_double2_def
  unfolding dyn_array_raw_assn_def
  apply (annot_snat_const "TYPE('size_t)")  
  by sepref 

find_theorems rdomp array_assn
 

sepref_def dyn_list_push_basic_impl is "uncurry dyn_list_push_basic"
  :: "(dyn_array_raw_assn :: ('a::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> ('a) ptr \<times> 'size_t word \<times> 'size_t word \<Rightarrow> assn)\<^sup>d
          *\<^sub>a id_assn\<^sup>d
        \<rightarrow>\<^sub>a (dyn_array_raw_assn :: ('a) list \<times> _ \<Rightarrow> _)"
  unfolding dyn_list_push_basic_def
  unfolding dyn_array_raw_assn_def
  apply (annot_snat_const "TYPE('size_t)")  
  by sepref 

sepref_def dyn_array_push_impl is "uncurry (dynamiclist_append2 :: ('a::llvm_rep) list \<times> _ \<Rightarrow> _)"
    :: "[\<lambda>((dl,l,c),_). l * 2 < max_snat LENGTH('size_t)]\<^sub>a
          (dyn_array_raw_assn :: ('a) list \<times> nat \<times> nat \<Rightarrow> ('a) ptr \<times> 'size_t word \<times> 'size_t word \<Rightarrow> assn)\<^sup>d
             *\<^sub>a id_assn\<^sup>k \<rightarrow> (dyn_array_raw_assn :: ('a) list \<times> _ \<Rightarrow> _)"
  unfolding dynamiclist_append2_def 
  by sepref 

thm dyn_array_push_impl.refine[]

lemmas prepare = dyn_array_push_impl.refine[to_hnr, unfolded hn_ctxt_def APP_def]

definition "push_size_bound TYPE('size_t) l \<equiv> l * (2::nat) < max_snat LENGTH('size_t)"

lemma dyn_array_push_impl_refines: "
        push_size_bound TYPE('size_t) l \<Longrightarrow>
          hn_refine (dyn_array_raw_assn (bs,l,c) da' ** id_assn x x')
                        (dyn_array_push_impl da' x')
                      (invalid_assn (dyn_array_raw_assn) (bs,l,c) da' ** id_assn x x')
                        (dyn_array_raw_assn) (dynamiclist_append2 (bs,l,c) x)"
  apply(rule prepare)
  unfolding push_size_bound_def
  by auto


subsection  \<open>implement empty\<close>

definition  dynamiclist_empty2 :: "('a::llvm_rep list \<times> nat \<times> nat, ecost) nrest"   where
  "dynamiclist_empty2 = do {
       dst \<leftarrow> mop_array_new id_assn init 8 ;
       RETURNT (dst,0,8)
    }"

thm  hnr_raw_array_new
term "mop_list_init_raw (\<lambda>n. lift_acost (cost'_narray_new n))"
 

lemma consumea_bind_return_is_SPECT: "do {
      _ \<leftarrow> consumea t;
      RETURNTecost x
    } = SPECT [x\<mapsto>t]"
  unfolding consumea_def bindT_def by (auto simp add: RETURNT_def)

definition "TR_de = 0(''list_init_c'':=lift_acost (cost'_narray_new 1))"
lemma wfR''_TR_de[simp]: "wfR'' TR_de"
  unfolding TR_de_def
  by(auto intro!: wfR''_upd)

lemma emptylist2_refine_aux: "dynamiclist_empty2 \<le> \<Down>\<^sub>C TR_de dyn_list_new_raw"
  unfolding dyn_list_new_raw_def dynamiclist_empty2_def mop_array_new_def
  apply(rule order.trans)
   defer apply(rule timerefine_bindT_ge2)  
   apply (simp_all add: timerefine_consume timerefine_RETURNT) 
  apply normalize_blocks
  unfolding consumea_bind_return_is_SPECT  apply auto
  apply(auto simp: le_fun_def)
  unfolding TR_de_def apply (simp add: timerefineA_cost_apply_costmult costmult_add_distrib costmult_cost norm_cost)
  apply sc_solve by (auto simp: numeral_eq_enat )


definition "TR_dynarray =  sup TR_de TR_da"
lemma wfR''_TR_dynarray: "wfR'' TR_dynarray"
  unfolding TR_dynarray_def
  by(auto intro: wfR''_supI)


lemma sup_upd: "sup (F(x:=y::ecost)) G = (sup F G)(x:=sup y (G x))"
  unfolding fun_upd_def 
  by fastforce 

lemma sup_0:
  fixes x y z :: "_ \<Rightarrow> ecost"
  shows "sup 0 x = x" "sup (\<lambda>_. 0) y = y"
      "sup z 0 = z" "sup y (\<lambda>_. 0) = y"
  subgoal using II   sup.commute 
    by metis
  subgoal using II[unfolded zero_fun_def]   sup.commute 
    by metis
  subgoal using II 
    by metis
  subgoal using II[unfolded zero_fun_def] 
    by metis
  done

lemma sup_0_enat:
  fixes x y z :: "ecost"
  shows "sup 0 x = x" "sup z 0 = z" 
  by (simp_all add: needname_nonneg sup_absorb2 sup.commute)

thm TR_da_def

thm fun_upd_apply
lemma f_upd_app: "x\<noteq>y \<Longrightarrow>(f(x:=t)) y = f y"
    "x=y \<Longrightarrow>  (f(x:=t)) y = t"
  by simp_all

schematic_goal TR_dynarray_aux: "sup (pp TR_dld2 TR_doublec) TR_dlpc = ?x"
  apply(rule hide)
  unfolding TR_dld2_dynaaray_simp TR_dlpc_def 
  apply(simp add: sup_0_enat sup_upd sup_0 norm_cost f_upd_app del: fun_upd_apply )
  apply summarize_same_cost
  apply(rule hideI)
  by simp

schematic_goal TR_dynarray_aux2: "sup TR_dlpc (sup (pp TR_dld2 TR_doublec) TR_dlpc) = ?x"
  apply(rule hide)
  unfolding TR_dynarray_aux
  unfolding TR_dlpc_def 
  apply(simp add: sup_0_enat sup_upd sup_0 norm_cost f_upd_app del: fun_upd_apply )
  apply summarize_same_cost
  apply(rule hideI)
  by simp

lemma one_enat_fold: "enat (Suc 0) = 1"
  by (simp add: one_enat_def)
schematic_goal TR_dynarray_simplified: "TR_dynarray = ?x"
  apply(rule hide)
  unfolding TR_dynarray_def 
  unfolding TR_da_def   TR_dynarray_aux2 TR_de_def
  apply(simp add: sup_0_enat sup_upd sup_0 norm_cost f_upd_app del: fun_upd_apply )
  unfolding one_enat_fold  apply simp
  apply(rule hideI)
  by simp


lemma emptylist2_refine: "dynamiclist_empty2 \<le> \<Down>\<^sub>C TR_dynarray dyn_list_new_raw"
  unfolding TR_dynarray_def
  apply(rule timerefine_supI2[OF emptylist2_refine_aux])
  by simp_all


lemma dyn_array_push_refine: "dynamiclist_append2 dl x \<le> \<Down>\<^sub>C TR_dynarray (dyn_list_push dl x)"
  unfolding TR_dynarray_def
  apply(rule timerefine_supI[OF dynamiclist_append2_refines[simplified]])
  using dynamiclist_append2_refines
  by simp_all

 

 
(* declare [[show_types,show_consts]]
*)

  thm SIZE_T

  find_in_thms mop_list_init_raw hn_refine in sepref_fr_rules

sepref_def dynamiclist_empty_impl is "(uncurry0 (dynamiclist_empty2 :: ('a::llvm_rep list \<times> nat \<times> nat, ecost) nrest) )"
  :: "(unit_assn)\<^sup>k \<rightarrow>\<^sub>a (dyn_array_raw_assn :: ('a::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> ('a::llvm_rep) ptr \<times> 'size_t word \<times> 'size_t word \<Rightarrow> assn)"
  unfolding dynamiclist_empty2_def dyn_array_raw_assn_def
  apply (annot_snat_const "TYPE('size_t)")  
  by sepref 
   
 
   

thm dynamiclist_empty_impl.refine


definition finite_cost_preserves  :: "(_ \<Rightarrow> ecost) \<Rightarrow> bool" where
  "finite_cost_preserves TR = (\<forall>\<Phi>. finite {x. the_acost \<Phi> x \<noteq> 0} \<longrightarrow> finite_cost \<Phi> \<longrightarrow> finite_cost (timerefineA TR \<Phi>))"   

lemma finite_cost_preservesI:
    "(\<And>\<Phi>. finite {x. the_acost \<Phi> x \<noteq> 0} \<Longrightarrow> finite_cost \<Phi> \<Longrightarrow> finite_cost (timerefineA TR \<Phi>))
    \<Longrightarrow> finite_cost_preserves TR "
  unfolding finite_cost_preserves_def by auto

lemma finite_cost_preservesD:
    "finite_cost_preserves TR \<Longrightarrow> 
        finite {x. the_acost \<Phi> x \<noteq> 0} \<Longrightarrow> finite_cost \<Phi> \<Longrightarrow> finite_cost (timerefineA TR \<Phi>)"
  unfolding finite_cost_preserves_def by auto

lemma finite_cost_preserves_sup:
  assumes "finite_cost \<Phi> \<Longrightarrow> finite_cost (timerefineA A \<Phi>)"      
       "finite_cost \<Phi> \<Longrightarrow> finite_cost (timerefineA B \<Phi>)"
      and f: "finite_cost \<Phi>"
    shows "finite_cost (timerefineA (sup A B) \<Phi>)"
  apply(rule finite_costI)
  subgoal for x
  using assms(1,2)[OF f, THEN finite_costD, of x]
  unfolding finite_cost_def timerefineA_def apply auto
  oops

lemma timerefineA_if_finite_support:
  "finite  {x. the_acost \<Phi> x \<noteq> 0}
  \<Longrightarrow> timerefineA TR \<Phi> = acostC (\<lambda>cc. sum (\<lambda>ac. the_acost \<Phi> ac * the_acost (TR ac) cc) {x. the_acost \<Phi> x \<noteq> 0})"
  unfolding timerefineA_def apply auto
  apply(rule ext)
  apply(subst Sum_any.expand_superset[of "{x. the_acost \<Phi> x \<noteq> 0}"]) by auto


lemma finite_cost_sup:
  fixes A :: "ecost"
  shows "finite_cost A \<Longrightarrow> finite_cost B \<Longrightarrow> finite_cost (sup A B)"
  unfolding finite_cost_def apply (auto simp: sup_acost_def) 
  by (simp add: max_def sup_enat_def) 

thm wfR''_def


lemma finite_sum_iff: "finite S \<Longrightarrow> sum f S < (\<infinity>::enat) \<longleftrightarrow> (\<forall>x\<in>S. f x < \<infinity>)"
  apply(induct S rule: finite_induct)
  apply simp apply auto
  by (metis add.commute enat.exhaust plus_enat_simps(3)) 

lemma finite_cost_timerefineA:
  assumes "finite  {x. the_acost \<Phi> x \<noteq> (0::enat)}"
  shows "finite_cost (timerefineA A \<Phi>) \<longleftrightarrow> (\<forall>ac\<in>{x. the_acost \<Phi> x \<noteq> 0}. (\<forall>cc. the_acost \<Phi> ac * the_acost (A ac) cc < \<infinity>))"
  unfolding timerefineA_if_finite_support[OF assms(1)] finite_cost_def
  apply (simp del: enat_ord_simps(4))
  apply(subst finite_sum_iff) apply(subst assms(1))
  apply (simp del: enat_ord_simps(4)) by auto


lemma finite_cost_preserves_sup:
  fixes A :: "'a \<Rightarrow> ecost"
  assumes A: "finite_cost_preserves A"
  assumes B: "finite_cost_preserves B"
  shows "finite_cost_preserves (sup A B)"
proof (rule finite_cost_preservesI)
  fix \<Phi> :: "('a, enat) acost"
  assume f: "finite {x. the_acost \<Phi> x \<noteq> 0}" "finite_cost \<Phi>"
  show "finite_cost (timerefineA (sup A B) \<Phi>)"
    unfolding finite_cost_timerefineA[OF f(1)]
    apply safe
    subgoal premises p for ac cc 
    using A[THEN finite_cost_preservesD, OF f, unfolded  finite_cost_timerefineA[OF f(1)], rule_format, of ac cc]
    using B[THEN finite_cost_preservesD, OF f,  unfolded  finite_cost_timerefineA[OF f(1)], rule_format, of ac cc]
    using p apply simp
    by (simp add: max_def sup_acost_def sup_max)
  done
qed


lemma finite_cost_preserves_upd:
  assumes  "finite_cost_preserves F " " finite_cost a"
  shows "finite_cost_preserves (F(x:=a))"
  apply(rule finite_cost_preservesI)  
  subgoal premises p for \<Phi>
  apply(subst finite_cost_timerefineA)
  apply (simp add: p)
  using assms(1)[THEN finite_cost_preservesD, OF p]
  apply(subst (asm) finite_cost_timerefineA)
   apply (simp add: p)
  apply auto
  using assms(2)[unfolded finite_cost_def] 
  by (metis finite_costD less_infinityE p(2) times_enat_simps(1)) 
  done

lemma finite_cost_zero: "finite_cost (0::ecost)"
  unfolding finite_cost_def by (auto simp: zero_acost_def) 

lemma timerefineA_zero_acost[simp]: "timerefineA 0 \<Phi> = 0"
  unfolding timerefineA_def by (auto simp: zero_acost_def)
lemma timerefineA_zero_acost'[simp]: "timerefineA (\<lambda>_. 0) \<Phi> = 0"
  unfolding timerefineA_def by (auto simp: zero_acost_def)

lemma finite_cost_cost_enat[simp]: "x < \<infinity> \<Longrightarrow> finite_cost (cost n (x::enat))"
  apply(rule finite_costI)
  by (auto simp: cost_def zero_acost_def zero_enat_def ) 

lemma finite_cost_preserves_zero[simp]:
  "finite_cost_preserves (0::_\<Rightarrow>ecost)"
  apply(rule finite_cost_preservesI) 
  by (auto simp: finite_cost_zero) 
lemma finite_cost_preserves_zero'[simp]:
  "finite_cost_preserves ((\<lambda>_. 0)::_\<Rightarrow>ecost)"
  apply(rule finite_cost_preservesI) 
  by (auto simp: finite_cost_zero) 

(* finite_cost_preserves_pp may even be wrong 
lemma finite_Sum_any_comp: 
  fixes  R :: "'a \<Rightarrow> ecost"
  assumes "\<forall>f. finite {s. the_acost (B s) f \<noteq> 0}" "finite {x. the_acost \<Phi> x \<noteq> 0}"
  shows "finite {x. ((Sum_any (\<lambda>ac. (the_acost Mc ac * (the_acost (R ac) x)))) \<noteq> 0)}"
proof - 
  thm finite_cartesian_product

  have "\<And>f. G ( {x. the_acost \<Phi> x \<noteq> 0} \<times> {s. the_acost (B s) f \<noteq> 0})" sorry

  {fix x
    have "((Sum_any (\<lambda>ac. ((the_acost Mc ac) * (the_acost (R ac) x)))) \<noteq> 0)
      \<Longrightarrow> \<exists>ac. (the_acost Mc ac) * (the_acost (R ac) x) \<noteq> 0"
      using Sum_any.not_neutral_obtains_not_neutral by blast 
  } then 
  have "{x. ((Sum_any (\<lambda>ac. ((the_acost Mc ac) * (the_acost (R ac) x)))) \<noteq> 0)}
          \<subseteq> {x. \<exists>ac. ((the_acost Mc ac) * (the_acost (R ac) x)) \<noteq> 0}" by blast
  also have "\<dots> \<subseteq> snd ` {(ac,x). ((the_acost Mc ac) * (the_acost (R ac) x)) \<noteq> 0}" by auto 
  also have "\<dots> \<subseteq> snd ` {(ac,x).  (the_acost (R ac) x) \<noteq> 0 \<and> (the_acost Mc ac) \<noteq> 0}" by auto


  finally  show ?thesis 
    apply(rule finite_subset ) apply auto
    apply(rule finite_imageI) 
    apply(rule finite_subset )
    
qed 


lemma finite_cost_preserves_pp:
  fixes A :: "string \<Rightarrow> ecost"
  and  B :: "string \<Rightarrow> ecost"
  assumes A: "finite_cost_preserves A"
      and B:  "finite_cost_preserves B"
      and "wfR'' A" "wfR'' B"
      shows "finite_cost_preserves (pp A B)"
proof (rule finite_cost_preservesI)
  fix \<Phi> :: "ecost"
  assume T: "finite {x. the_acost \<Phi> x \<noteq> 0}" "finite_cost \<Phi>"  
  have "finite {x. the_acost (timerefineA B \<Phi>) x \<noteq> 0}" "finite_cost (timerefineA B \<Phi>)"
    subgoal using assms(4)[unfolded wfR''_def] T 
      unfolding timerefineA_def
      apply simp apply(rule wfR_finite_Sum_any)
      unfolding wfR_def 
      sorry
    subgoal
      using B[THEN finite_cost_preservesD, OF T] .
    done
  from A[THEN finite_cost_preservesD, OF this]
  have "finite_cost (timerefineA A (timerefineA B \<Phi>))" .

  show "finite_cost (timerefineA (pp A B) \<Phi>)"
    apply(subst timerefineA_iter2[symmetric])
    by fact+ 
qed *)


lemma finite_cost_preserves_TTId:
  "finite A \<Longrightarrow> finite_cost_preserves (TTId A)"
  apply(rule finite_cost_preservesI)
  unfolding finite_cost_def 
  apply(subst timerefineA_if_finite_support) apply simp
  apply (simp del: enat_ord_simps(4)) apply safe
  apply(subst finite_sum_iff)
  by (auto simp: TTId_def zero_acost_def norm_cost cost_def simp del: enat_ord_simps(4))

lemma finite_cost_addI:
  fixes a b :: ecost
  shows "finite_cost a \<Longrightarrow> finite_cost b \<Longrightarrow> finite_cost (a+b)"
  unfolding finite_cost_def apply (cases a; cases b; auto simp: plus_acost_alt)
  by (metis plus_enat_simps(1)) 

lemma finite_cost_preserves_TR_dlpc: "finite_cost_preserves TR_dlpc"
  unfolding TR_dlpc_def
  apply(intro finite_cost_preserves_sup)
  subgoal 
    apply(intro finite_cost_preserves_upd)
    by (simp_all add: finite_cost_lift_acost)
  subgoal 
    apply(intro finite_cost_preserves_upd)
    by (simp_all add: finite_cost_lift_acost)
  by (simp_all add: finite_cost_lift_acost)

lemma finite_cost_preserves_TR_dynarray: "finite_cost_preserves TR_dynarray"
  unfolding TR_dynarray_def
  apply(rule finite_cost_preserves_sup)
  subgoal 
    unfolding TR_de_def  
    apply(rule finite_cost_preserves_upd) by (simp_all add: finite_cost_lift_acost)
  subgoal 
    unfolding TR_da_def  
    apply(intro finite_cost_preserves_sup)
    subgoal 
      apply(rule finite_cost_preserves_upd) by (simp_all add: finite_cost_lift_acost)
    subgoal 
      apply(intro finite_cost_preserves_upd) by (simp_all add: finite_cost_lift_acost)
    subgoal  
      by (fact finite_cost_preserves_TR_dlpc)
    subgoal 
      unfolding TR_dld2_dynaaray_simp
      apply(intro finite_cost_addI finite_cost_preserves_sup finite_cost_preserves_upd finite_cost_preserves_TTId)       
      by (simp_all add: norm_cost) 
    subgoal 
      by (fact finite_cost_preserves_TR_dlpc)
    done
  done

interpretation dyn_array: dyn_list_impl TR_dynarray dyn_array_raw_assn
                            "push_size_bound TYPE('size_t)" dynamiclist_append2 dyn_array_push_impl
                            dynamiclist_empty2 dynamiclist_empty_impl
      (*                       
    defines dynamic_array_append_spec = "dyn_array.dyn_array_push_spec"
      and dynamic_array_empty_spec = "dyn_array.dynamiclist_empty_spec" 
      and dynamic_array_assn = dyn_array.dyn_array_assn *)
  apply standard (* TODO: provide the implementations *)
  subgoal by (fact wfR''_TR_dynarray)
  subgoal
    apply(rule finite_cost_preservesD) apply auto
    apply(rule finite_cost_preserves_TR_dynarray) done
  subgoal by(fact dyn_array_push_refine)
  subgoal apply(rule dyn_array_push_impl_refines) by simp
  subgoal by (fact dynamiclist_empty_impl.refine)
  subgoal by (fact emptylist2_refine) 
  done 


sepref_register dyn_array.dyn_array_push_spec
lemmas da_push_rule  = dyn_array.G_push
declare dyn_array.G_push[sepref_fr_rules]
thm dyn_array.G_push

term dynamic_array_empty_spec
sepref_register dyn_array.dynamiclist_empty_spec
lemmas da_empty_rule = dyn_array.GGG_empty 
declare dyn_array.GGG_empty[sepref_fr_rules]
thm dyn_array.GGG_empty  

lemmas dyn_array_dyn_array_push_spec_def = dyn_array.dyn_array_push_spec_def
lemmas  dyn_array_dynamiclist_empty_spec_def =  dyn_array.dynamiclist_empty_spec_def
lemmas  dyn_array_dynamic_array_assn_def =  dyn_array.dyn_array_assn_def

term dyn_array.dyn_array_assn

thm dyn_array.dyn_array_push_impl_refines_dyn_array_push_spec dyn_array.GGG


concrete_definition dynamic_array_assn2 is dyn_array_dynamic_array_assn_def

definition  "da \<equiv> dyn_array.dyn_array_assn"


thm FREE_array_assn(*
lemma FREE_dynarray_assn[sepref_frame_free_rules]:
  assumes PURE: "is_pure A"
  shows "MK_FREE (dyn_array.dyn_array_assn A) dynarray_free" 
  apply rule
  unfolding dyn_array.dyn_array_assn_def
  unfolding
    dyn_list_assn.dyn_array_raw_armor_assn_def
  apply(subst hr_comp_assoc)
  unfolding dyn_array_raw_assn_def
  sorry
*)
term mop_array_nth


subsection \<open>Nth operation\<close>

definition dyn_array_nth :: "('a list \<times> nat \<times> nat) \<Rightarrow> nat \<Rightarrow> ('a, (char list, enat) acost) nrest"
  where "dyn_array_nth = (\<lambda>(dl,_,_) n. (mop_array_nth dl n))"

sepref_def dyn_array_nth_impl is "uncurry dyn_array_nth"
     :: "(dyn_array_raw_assn :: ('a::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> ('a) ptr \<times> 'size_t word \<times> 'size_t word \<Rightarrow> assn)\<^sup>k *\<^sub>a (snat_assn' TYPE('size_t) )\<^sup>k \<rightarrow>\<^sub>a (id_assn::'a \<Rightarrow> 'a \<Rightarrow> assn)"
  unfolding dyn_array_raw_assn_def dyn_array_nth_def
  by sepref

term dyn_array.dyn_array_assn

term nrest_rel
lemma dyn_array_nth_dyn_list_refine: "(uncurry dyn_array_nth, uncurry mop_array_nth) \<in> dyn_list_rel \<times>\<^sub>r Id \<rightarrow>\<^sub>f  \<langle>Id\<rangle>nrest_rel "
  apply(rule)
  apply(rule nrest_C_relI)
  unfolding dyn_array_nth_def mop_array_nth_def mop_list_get_def uncurry_def
  apply(refine_rcg bindT_refine_easy)
  by(auto simp: dyn_list_rel_def)  

lemma mop_array_nth_refine_R: "(uncurry mop_array_nth, uncurry mop_array_nth) \<in> \<langle>R\<rangle>list_rel \<times>\<^sub>r Id \<rightarrow>\<^sub>f  \<langle>R\<rangle>nrest_rel"
  apply(rule)
  apply(rule nrest_C_relI)
  unfolding mop_array_nth_def mop_list_get_def uncurry_def
  apply(refine_rcg bindT_refine_easy)
  by(auto simp: param_nth list_rel_imp_same_length)

thm dyn_array_dynamic_array_assn_def
thm dyn_array.dyn_array_raw_armor_assn_def
thm dyn_array.dyn_array_raw_armor_assn_alt
(* TODO: move *) 

lemmas dyn_array_nth_aux1 = dyn_array_nth_impl.refine[THEN amor_orthogonal[where PHI=dyn_array.\<Phi>_d], folded dyn_array.dyn_array_raw_armor_assn_alt]


thm dyn_array_nth_aux1 dyn_array_nth_dyn_list_refine
lemmas dyn_array_nth_aux2 = dyn_array_nth_aux1[FCOMP dyn_array_nth_dyn_list_refine]
thm dyn_array_nth_aux2 mop_array_nth_refine_R
thm fcomp_norm_unfold
thm fcomp_norm_norm
lemmas dyn_array_nth_rule = dyn_array_nth_aux2[FCOMP mop_array_nth_refine_R]



subsection \<open>length operation\<close>

definition dyn_array_length :: "(('a::llvm_rep) list \<times> nat \<times> nat) \<Rightarrow> (nat, (char list, enat) acost) nrest"
  where "dyn_array_length = (\<lambda>(_,l,_) . RETURNT l)"



sepref_def dyn_array_length_impl is "dyn_array_length"
     :: "(dyn_array_raw_assn :: ('a::llvm_rep) list \<times> nat \<times> nat \<Rightarrow> ('a) ptr \<times> 'size_t word \<times> 'size_t word \<Rightarrow> assn)\<^sup>k \<rightarrow>\<^sub>a  (snat_assn' TYPE('size_t) )"
  unfolding dyn_array_raw_assn_def dyn_array_length_def
  by sepref

lemmas dyn_array_length_aux1 = dyn_array_length_impl.refine[THEN amor_orthogonal_empt[where PHI=dyn_array.\<Phi>_d], folded dyn_array.dyn_array_raw_armor_assn_alt]

lemma dyn_array_length_dyn_list_refine: "(dyn_array_length, mop_list_length) \<in> dyn_list_rel \<rightarrow>\<^sub>f  \<langle>nat_rel\<rangle>nrest_rel "
  apply(rule)
  apply(rule nrest_C_relI)
  unfolding dyn_array_length_def mop_list_length_def
  apply(refine_rcg bindT_refine_easy)
  by(auto simp: dyn_list_rel_def)  

lemma mop_array_length_refine_R: "(mop_list_length, mop_list_length) \<in> \<langle>R\<rangle>list_rel \<rightarrow>\<^sub>f  \<langle>nat_rel\<rangle>nrest_rel"
  apply(rule)
  apply(rule nrest_C_relI)
  unfolding mop_list_length_def
  apply(refine_rcg bindT_refine_easy)
  by(auto simp: param_nth list_rel_imp_same_length)

thm mop_array_length_refine_R mop_array_nth_refine_R

lemmas dyn_array_length_aux2 = dyn_array_length_aux1[FCOMP dyn_array_length_dyn_list_refine]
thm dyn_array_length_aux2  dyn_array_nth_aux2
thm dyn_array_length_aux2 mop_array_length_refine_R

thm dyn_array.dyn_array_raw_armor_
thm dyn_array.dyn_array_raw_armor_aux
thm fcomp_norm_unfold
lemmas dyn_array_length_rule = dyn_array_length_aux2[FCOMP mop_array_length_refine_R[where R="the_pure R" for R]]
(* TODO: IDG 
lemma dyn_array_length_rule:
  "\<^cancel>\<open>Sepref_Constraints.CONSTRAINT Sepref_Basic.is_pure U
       \<Longrightarrow> \<close>(dyn_array_length_impl, mop_list_length) \<in> (dyn_array.dyn_array_assn U)\<^sup>k \<rightarrow>\<^sub>a snat_assn"
  sorry *)



term dyn_array.push_concrete_advertised_cost


concrete_definition dynamic_array_append_spec_cost is dyn_array_dyn_array_push_spec_def
  uses "_ = mop_list_snoc \<hole>"

schematic_goal dynamic_array_append_spec_cost_simplified: "dynamic_array_append_spec_cost = ?x"
  apply(rule hide)
  unfolding dynamic_array_append_spec_cost_def 
  unfolding push_amortized_cost_def push_overhead_cost_def
  apply(simp add: norm_cost wfR''_TR_dynarray)
  unfolding TR_dynarray_simplified
  apply(simp add: norm_cost )
  apply summarize_same_cost
  apply (simp add: numeral_eq_enat )  
  apply(rule hideI)
  by simp


schematic_goal dynamic_array_append_spec_cost_simplified2: "dyn_array.push_concrete_advertised_cost = ?x"
  apply(rule hide)
  unfolding push_amortized_cost_def unfolding push_overhead_cost_def
  apply(simp add: norm_cost wfR''_TR_dynarray)
  unfolding TR_dynarray_simplified
  apply(simp add: norm_cost )
  apply summarize_same_cost
  apply (simp add: numeral_eq_enat )  
  apply(rule hideI)
  by simp


thm dynamic_array_append_spec_cost_simplified

end

 


concrete_definition dynamiclist_empty_impl is size_t_context.dynamiclist_empty_impl_def
concrete_definition dyn_array_push_impl is size_t_context.dyn_array_push_impl_def

concrete_definition dynamic_array_append_spec is size_t_context.dyn_array_dyn_array_push_spec_def

concrete_definition dynamic_array_empty_spec is size_t_context.dyn_array_dynamiclist_empty_spec_def
thm dynamic_array_empty_spec.refine

definition [simp]: "dynamic_array_empty_spec_a TYPE('l::len2)\<equiv> dynamic_array_empty_spec"

concrete_definition dynamic_array_assn is size_t_context.dyn_array_dynamic_array_assn_def

abbreviation "al_assn' TYPE('l::len2) R \<equiv> dynamic_array_assn R :: (_ \<Rightarrow> _ \<times> 'l word \<times> 'l word \<Rightarrow> _)"

 
thm hnr_array_nth 

term "(\<lambda>((dl,_,_),n). mop_array_nth dl n)"
term "(dynamic_array_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A"

(* TODO: Move *)
lemma pull_cond_hfref: "(P \<Longrightarrow>  p \<in> x \<rightarrow>\<^sub>a y) \<Longrightarrow> p \<in> [\<lambda>_. P]\<^sub>a x \<rightarrow> y"
  unfolding hfref_def by auto


concrete_definition dyn_array_nth_impl is size_t_context.dyn_array_nth_impl_def

(* TODO one could move the definition of dyn_array_nth_impl out of the size context and
  thus avoid the precondition with the length *)
sepref_register dyn_array_nth_impl
lemma dyn_array_nth[sepref_fr_rules]:
  "Sepref_Constraints.CONSTRAINT Sepref_Basic.is_pure A
  \<Longrightarrow> (uncurry dyn_array_nth_impl, uncurry mop_array_nth) \<in> [\<lambda>_. 8\<le>LENGTH('l)]\<^sub>a (al_assn' TYPE('l::len2) A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> A"
  apply(rule pull_cond_hfref)
  apply(subgoal_tac "size_t_context TYPE('l)")
  subgoal premises p
    supply f = size_t_context.dyn_array_nth_rule[where 'size_t='l, unfolded 
                    dynamic_array_assn.refine[OF p(3)]
                    dyn_array_nth_impl.refine[OF p(3)]
                   ]
    thm f
    apply(rule f) using p by auto
  apply standard apply simp done


(*
lemma dyn_array_nth_old[sepref_fr_rules]:
  "Sepref_Constraints.CONSTRAINT Sepref_Basic.is_pure A \<Longrightarrow> (uncurry dyn_array_nth, uncurry mop_array_nth)
     \<in> (dynamic_array_assn A)\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a A" 
  sorry

thm dyn_array_nth dyn_array_nth_old
*)



concrete_definition dyn_array_length_impl is size_t_context.dyn_array_length_impl_def
sepref_register dyn_array_length_impl
(* TODO one could move the definition of dyn_array_nth_impl out of the size context and
  thus avoid the precondition with the length *)
lemma dyn_array_length[sepref_fr_rules]:
  "\<^cancel>\<open>Sepref_Constraints.CONSTRAINT Sepref_Basic.is_pure A
  \<Longrightarrow>\<close> ( dyn_array_length_impl,  mop_list_length) \<in> [\<lambda>_. 8\<le>LENGTH('l)]\<^sub>a (al_assn' TYPE('l::len2) A)\<^sup>k \<rightarrow> snat_assn"
  apply(rule pull_cond_hfref)
  apply(subgoal_tac "size_t_context TYPE('l)")
  subgoal premises p
    supply f = size_t_context.dyn_array_length_rule[where 'size_t='l, unfolded 
                    dynamic_array_assn.refine[OF p(2)]
                    dyn_array_length_impl.refine[OF p(2)]
                   ]
    thm f
    apply(rule f) using p by auto
  apply standard apply simp done




sepref_register dynamic_array_empty_spec
sepref_register "dynamic_array_empty_spec_a TYPE('l::len2)"
lemma pf: "(uncurry0 dynamiclist_empty_impl, uncurry0 (PR_CONST (dynamic_array_empty_spec_a TYPE('l::len2))))
   \<in> [\<lambda>_. 8\<le>LENGTH('l)]\<^sub>a  unit_assn\<^sup>k \<rightarrow> al_assn' TYPE('l) A"
  apply(rule pull_cond_hfref)
  apply(subgoal_tac "size_t_context TYPE('l)")
  subgoal premises p 
    supply f= size_t_context.da_empty_rule[where 'size_t='l, unfolded 
                    dynamic_array_assn.refine[OF p(2)]
                    dynamic_array_empty_spec.refine[OF p(2)]
                    dynamiclist_empty_impl.refine[OF p(2)] ]
    unfolding dynamic_array_empty_spec_a_def
    apply(rule f) by fact
  apply standard apply simp done
declare pf[sepref_fr_rules]


lemma annot: "dynamic_array_empty_spec = dynamic_array_empty_spec_a TYPE('l::len2)"
  apply simp done
thm annot

lemma hfrefD_precond: "(f,g) \<in> [\<lambda>_. P]\<^sub>a S \<rightarrow> R \<Longrightarrow> P  \<Longrightarrow> (f,g) \<in> S \<rightarrow>\<^sub>a R"
  unfolding hfref_def by auto   

lemma hfrefD_precond2: "(f,g) \<in> [\<lambda>_. P]\<^sub>a S \<rightarrow> R\<Longrightarrow> True"
  by auto    


lemma weaken_cond_hfref: "(p \<in> [\<lambda>a. P' a]\<^sub>a x \<rightarrow> y) \<Longrightarrow> (\<And>a. P a \<Longrightarrow> P' a)   \<Longrightarrow> p \<in> [\<lambda>a. P a]\<^sub>a x \<rightarrow> y"
  unfolding hfref_def by auto


lemma pull_cond_hfref': "(\<And>a. R a \<Longrightarrow> P) \<Longrightarrow>(P \<Longrightarrow> p \<in> [R]\<^sub>a x \<rightarrow> y) \<Longrightarrow>  p \<in> [R]\<^sub>a x \<rightarrow> y"
  unfolding hfref_def by auto

thm size_t_context.push_size_bound_def

sepref_register dynamic_array_append_spec
lemma dyn_array_push_impl_rule: "
Sepref_Constraints.CONSTRAINT Sepref_Basic.is_pure A
   \<Longrightarrow> (uncurry dyn_array_push_impl, uncurry dynamic_array_append_spec)
     \<in> [\<lambda>(ls,_). 2 * length ls < max_snat LENGTH('l) \<and> 8\<le>LENGTH('l)]\<^sub>a  (al_assn' TYPE('l::len2) A)\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow> al_assn' TYPE('l) A"
  apply(rule pull_cond_hfref'[where P="8\<le>LENGTH('l)"]) apply auto[1]
  apply(subgoal_tac "size_t_context TYPE('l)")
  subgoal premises p 
    supply f= size_t_context.da_push_rule[where 'size_t='l, unfolded 
                    dynamic_array_assn.refine[OF p(3)]
                    dynamic_array_append_spec.refine[OF p(3)]
                    dyn_array_push_impl.refine[OF p(3)], unfolded PR_CONST_def ] 
    apply(rule weaken_cond_hfref[OF f] ) 
    unfolding size_t_context.push_size_bound_def size_t_context.push_size_bound_def[OF p(3)]
    using p by auto
  apply standard apply simp done 
declare dyn_array_push_impl_rule[sepref_fr_rules]


thm dynamic_array_append_spec_def


thm size_t_context.TR_dynarray_def

thm size_t_context.TR_dynarray_simplified

lemma ht_from_hnr_triv: 
  assumes "hn_refine \<Gamma> c \<Gamma>' R (SPECT (emb Q T))"
  shows " llvm_htriple ($T ** \<Gamma>) c (\<lambda>r. (EXS ra. \<up>(Q ra) ** R ra r) ** \<Gamma>')" 
  apply(rule ht_from_hnr[where \<Phi>=True and E="TId", simplified timerefineA_TId_eq])
  using assms by (auto simp: timerefine_id)  



concrete_definition da_append_spec_cost is size_t_context.dynamic_array_append_spec_cost_simplified2
  uses "_ = \<hole>"



lemma assumes "Sepref_Basic.is_pure A"
  and "2 * length a < max_snat LENGTH('c::len2)"
  and "8 \<le> LENGTH('c)"
shows dyn_array_push_impl_ht': "llvm_htriple ($da_append_spec_cost \<and>* al_assn' TYPE('c) A a ai \<and>* A b bi) (dyn_array_push_impl ai bi)
     (\<lambda>r. (\<lambda>s. \<exists>x. (\<up>(x = a @ [b]) \<and>* dynamic_array_assn A x r) s) \<and>* hn_invalid (dynamic_array_assn A) a ai \<and>* A b bi)"
proof - 
  from assms(3) have S: "size_t_context TYPE('c)"
    apply unfold_locales .

  note f = size_t_context.dynamic_array_append_spec_cost_simplified2[OF S, folded da_append_spec_cost_def]

  from dyn_array_push_impl_rule[to_hnr, unfolded dynamic_array_append_spec_def f APP_def mop_list_snoc_def SPECT_assign_emb'
               , THEN  ht_from_hnr_triv]
  show ?thesis
    unfolding Sepref_Constraints.CONSTRAINT_def hn_ctxt_def using assms by fast
qed


(* TODO: Move *)
lemma sep_conj_pred_lift: "(A \<and>* (pred_lift B)) s = (A s \<and> B)"
  apply(cases B) by (auto simp: pure_true_conv)

lemma introsort_final_hoare_triple:assumes "Sepref_Basic.is_pure A"
  and "2 * length a < max_snat LENGTH('c::len2)"
  and "8 \<le> LENGTH('c)"
shows dyn_array_push_impl_ht: "llvm_htriple ($da_append_spec_cost \<and>* al_assn' TYPE('c) A a ai \<and>* A b bi) (dyn_array_push_impl ai bi)
     (\<lambda>r. (\<lambda>s. \<exists>x. (\<up>(x = a @ [b]) \<and>* dynamic_array_assn A x r) s) \<and>* A b bi)"
  apply(rule cons_post_rule) (* TODO: very ugly proof to get rid of the invalid_assn! *)
   apply (rule dyn_array_push_impl_ht'[OF assms, unfolded hn_ctxt_def]) 
  apply(simp add: pred_lift_extract_simps  invalid_assn_def pure_part_def)
  apply(subst (asm) (2) sep_conj_commute)
  apply(subst (asm) (1) sep_conj_assoc[symmetric])
  apply(subst (asm) sep_conj_pred_lift) by simp

lemma Sum_any_cost: "Sum_any (the_acost (cost n x)) = x"
  unfolding cost_def by (simp add: zero_acost_def)
lemma sum_any_push_costmul: "Sum_any (the_acost (n *m c)) = n * (Sum_any (the_acost c))" for n :: nat 
  apply (cases c) subgoal for x
  apply (auto simp: costmult_def algebra_simps) 
  apply (cases "finite {a. x a \<noteq> 0}"; cases "n=0")
  apply (simp_all add: Sum_any_right_distrib)
  done done
  

schematic_goal all_da_append_spec_cost: "project_all da_append_spec_cost = ?x"
  apply (fold norm_cost_tag_def)
  unfolding da_append_spec_cost_def
  apply(subst project_all_is_Sumany_if_lifted )
  apply(simp only: lift_acost_cost[symmetric] lift_acost_propagate[symmetric]) 
  apply(simp add: the_acost_propagate add.assoc) 
  
  supply acost_finiteIs = finite_sum_nonzero_cost finite_sum_nonzero_if_summands_finite_nonzero finite_the_acost_mult_nonzeroI
  
  apply (subst Sum_any.distrib, (intro acost_finiteIs;fail), (intro acost_finiteIs;fail))+
  apply (simp only: Sum_any_cost sum_any_push_costmul)
  apply (simp add: add_ac)

  by (rule norm_cost_tagI)



definition "algorithm = doN {
    (s::nat list) \<leftarrow> dynamic_array_empty_spec;
    s \<leftarrow> dynamic_array_append_spec s (0::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    s \<leftarrow> dynamic_array_append_spec s (42::nat);
    s \<leftarrow> dynamic_array_append_spec s (42::nat);
    s \<leftarrow> dynamic_array_append_spec s (32::nat);
    s \<leftarrow> dynamic_array_append_spec s (31::nat);
    s \<leftarrow> dynamic_array_append_spec s (42::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    len \<leftarrow> mop_list_length s;
    s \<leftarrow> dynamic_array_append_spec s len;
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    s \<leftarrow> dynamic_array_append_spec s (1::nat);
    RETURNT s
  }"


term "dynamic_array_assn (snat_assn' TYPE(32))"
term "(snat_assn' TYPE(32))"

term unat_assn'

term narray_new

thm sepref_fr_rules

(* TODO: I GUESS registering those lemmas as simp is TOO eager,
    they should help solving the size side conditions in the following sepref call *)
lemmas [simp] = dynamic_array_empty_spec_def dynamic_array_append_spec_def

lemma [simp]:
  fixes t::ecost
  shows "RETURNT x \<le> SPECT [y \<mapsto> t] \<longleftrightarrow> x = y"
  by (auto simp: RETURNT_def le_fun_def  ecost_nneg)  

sepref_def algorithm_impl is "uncurry0 algorithm"
  :: "(unit_assn)\<^sup>k \<rightarrow>\<^sub>a al_assn' TYPE(32) (snat_assn' TYPE(32))"
  unfolding algorithm_def
    supply [[goals_limit = 2]]
  apply (annot_snat_const "TYPE(32)")
  apply(rewrite annot[where 'l=32])
  by sepref (*
  apply sepref_dbg_trans_keep
             apply sepref_dbg_trans_step_keep 
  apply(rule sepref_fr_rules(1)[unfolded PR_CONST_def])
  using sepref_fr_rules(1)

         apply sepref_dbg_trans_step
  apply(rule sepref_fr_rules(2)[unfolded PR_CONST_def])

  oops (*
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done *)
  *)
\<^cancel>\<open>


section \<open>Array with Length\<close>


definition "mop_list_length T xs = SPECT [ length xs \<mapsto> T  ]"



definition "llist_rel = br snd (\<lambda>(l,cs). l = length cs)"

definition "llist_new ini n = doN {
        cs \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init'' (enat n)) ini n;
        RETURNT (n,cs)
      }"

lemma "llist_new ini n \<le> \<Down>llist_rel (mop_list_init (\<lambda>n. cost ''list_init'' (enat n)) ini n)"
  sorry

definition "llist_nth T  \<equiv> \<lambda>(l,cs) n. doN {
              mop_list_get T cs n
          }"

lemma "llist_nth T lcs i \<le> \<Down>llist_rel (mop_list_get T cs i)"


 





section \<open>Implementation of Dynamic List Operations\<close>

subsection \<open>Implementation of Dynamic List Double\<close>

definition dyn_list_double where
  "dyn_list_double ini  \<equiv> \<lambda>(bs,l,c). doN {
       ASSERT (l\<le>length bs);
       bsl \<leftarrow> SPECc2 ''mul'' (*) 2 c;
       dst \<leftarrow> mop_list_init (\<lambda>n. cost ''list_init_c'' (enat n)) ini bsl;
       list_copy dst bs l; 
       RETURNT (dst,l,bsl)
      }"


lemma "dyn_list_double ini (bs,l,c) \<le> dyn_list_double_spec (bs,l,c)"
  unfolding dyn_list_double_def dyn_list_double_spec_def
  sorry


\<close>

end