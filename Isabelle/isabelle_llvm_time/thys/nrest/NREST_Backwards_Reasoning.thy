\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
\<^marker>\<open>contributor "Peter Lammich"\<close>
section \<open>Generalized Weakest Precondition - gwp\<close>
theory NREST_Backwards_Reasoning
imports NREST NREST_Type_Classes "../cost/Enat_Cost" Time_Refinement
begin


paragraph \<open>Summary\<close>
text \<open>This theory introduces backwards reasoning for NREST. It generalizes weakest precondition
    to resources and forms a syntax directed VCG.\<close>
 
subsection \<open>Auxiliary Definitions\<close>


definition mm3 where
  "mm3 t A = (case A of None \<Rightarrow> None | Some t' \<Rightarrow> if t'\<le>t then Some (t-t') else None)"


lemma Some_eq_mm3_Some_conv: "Some t = mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> enat t = enat (t' - t''))"
  by (simp add: mm3_def)

lemma Some_eq_mm3_Some_conv': "mm3 t' (Some t'') = Some t \<longleftrightarrow> (t'' \<le> t' \<and> enat t = enat (t' - t''))"
  using Some_eq_mm3_Some_conv by metis

lemma mm3_acost_Some_conv: "mm3 (lift_acost A) (Some (lift_acost B)) = Some t \<longleftrightarrow> (B\<le>A \<and> t=lift_acost (A-B))"
  apply(cases A; cases B)
  unfolding mm3_def by (auto simp: lift_acost_def less_eq_acost_def minus_acost_alt split: nrest.splits)


lemma mm3_Some_is_Some:
  fixes t0 :: "(_,nat) acost"
  shows "mm3 t0 (Some t0) = Some 0"  by (auto simp: less_eq_acost_def mm3_def zero_acost_def)

lemma mm3_Some_is_Some_enat:
  fixes t0 :: "(_,enat) acost"
  assumes "\<forall>x. the_acost t0 x < \<infinity>"
  shows "mm3 t0 (Some t0) = Some 0"
  using assms by (auto simp: less_eq_acost_def minus_acost_alt mm3_def zero_acost_def
                          split: acost.splits)



lemma mm3_Some_conv: "(mm3 t0 A = Some t) = (\<exists>t'. A = Some t' \<and> t0 \<ge> t' \<and> t=t0-t')"
  unfolding mm3_def by(auto split: option.splits)

lemma Some_le_mm3_Some_conv: "Some t \<le> mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t \<le> (t' - t''))"
  by (simp add: mm3_def)
  

lemma Some_le_emb'_conv: "Some t \<le> emb' Q ft x \<longleftrightarrow> Q x \<and> t \<le> ft x"
  by (auto simp: emb'_def)


lemma Some_eq_emb'_conv: "Some t = emb' Q ft x \<longleftrightarrow> Q x \<and> t = ft x"
        "emb' Q ft x = Some t  \<longleftrightarrow> Q x \<and> t = ft x"
  by (auto simp: emb'_def)

subsubsection "minus potential"

definition minus_potential :: "( 'a \<Rightarrow> ('d::{minus,ord,top}) option) \<Rightarrow> ( 'a \<Rightarrow> 'd option) \<Rightarrow> ( 'a \<Rightarrow> 'd option)" where
  "minus_potential R m = (\<lambda>x. (case m x of None \<Rightarrow> Some top
                                | Some mt \<Rightarrow>
                                  (case R x of None \<Rightarrow> None | Some rt \<Rightarrow> (if mt \<le> rt then  Some (rt - mt) else None))))"

definition minus_cost :: "(  ('d::{minus,ord,top}) option) \<Rightarrow> (   _ option) \<Rightarrow> (   _ option)" where
  "minus_cost r m = (case m  of None \<Rightarrow> Some top
                                | Some mt \<Rightarrow>
                                  (case r of None \<Rightarrow> None | Some rt \<Rightarrow> (if mt \<le> rt then Some (rt - mt) else None)))"

lemma minus_cost_None: "minus_cost r None = Some top" unfolding minus_cost_def by auto 


lemma f: "(t::_::complete_lattice) \<le> Some top \<longleftrightarrow> True" 
  unfolding less_eq_option_def top_option_def apply(cases t) by auto 

lemma minus_cost_mono: 
  fixes q q' :: "'b::{complete_lattice,minus,ord,top,drm} option"
  shows "(m \<noteq> None \<Longrightarrow> q' \<le> q) \<Longrightarrow> minus_cost q m \<ge> minus_cost q' m"
  unfolding minus_cost_def 
  by (auto split: option.splits simp: drm_class.diff_right_mono)  

lemma minus_cost_antimono: 
  fixes x y :: "'b::{complete_lattice,minus,ord,top,drm} option"
  shows "x \<le> y \<Longrightarrow> minus_cost q x \<ge> minus_cost q y"
  unfolding minus_cost_def by (auto split: option.splits simp: diff_left_mono)  

lemma Option_these_non_empty_if_Sup_Some: "Sup X = Some t \<Longrightarrow> Option.these X \<noteq> {}"
  by (simp add: SupD these_empty_eq)

lemma Sup_option_these: "Sup X = Some b \<Longrightarrow> Sup (Option.these X) = (b::'a::complete_lattice)" 
    by (metis SupD Sup_option_def option.sel)   

lemma minus_cost_contiuous2:
  fixes t :: "'a::{complete_lattice,minus,drm} option" 
  shows "\<forall>x\<in>X. t \<le> minus_cost q x \<Longrightarrow> t \<le> minus_cost q (Sup X)"  
  unfolding minus_cost_def
  apply(auto simp: everywhereNone   less_eq_option_None_is_None' split: option.splits if_splits)
     apply(simp add: top_option_def[symmetric]) 
  subgoal by (metis Sup_bot_conv(1) Sup_empty empty_Sup option.distinct(1) option.exhaust)
  subgoal for b c
    apply(cases t)
     apply(auto simp add: f)  
  proof (goal_cases)
    case prems: (1 a)
  
    from prems(1)[rule_format, rule_format, of _ _ c, simplified]
    have "\<And>x B. \<lbrakk>x \<in> X; x = Some B\<rbrakk> \<Longrightarrow> a \<le> c - B" by auto

    then have **: "\<forall>B\<in>Option.these X. a \<le> c - B" unfolding Ball_def in_these_eq by blast

    have *: "Option.these X \<noteq> {}"
      using prems apply(simp add: Option_these_non_empty_if_Sup_Some) done

    show ?case unfolding Sup_option_these[symmetric, OF prems(4)]
      apply(rule minus_continuousSup)
      apply(rule *)
      by(rule **)
  qed 
  subgoal  
    by (metis Sup_le_iff Sup_option_def in_these_eq option.sel option.simps(3))  
  done 


abbreviation "minus_option rt mt \<equiv> (if mt \<le> rt then Some (rt - mt) else None)"

lemma "minus_cost r m = case_option (Some top) (\<lambda>mt. case_option None (\<lambda>rt. minus_option rt mt) r) m"
  unfolding minus_cost_def by simp

lemma minus_potential_alt: "minus_potential r m = (\<lambda>x. minus_cost (r x) (m x))"
  unfolding minus_potential_def minus_cost_def by simp

lemma diff_right_mono_enat: "a \<le> b \<Longrightarrow> a - c \<le> b - (c::enat)"
  apply(cases a; cases b; cases c) by auto

lemma minus_potential_mono: 
  fixes q q' :: "_ \<Rightarrow> 'b::{complete_lattice,minus,ord,top,drm} option"
  shows "(\<And>x. m x \<noteq> None \<Longrightarrow> q x \<le> q' x) \<Longrightarrow> minus_potential q m \<le> minus_potential q' m"
  unfolding minus_potential_alt 
  apply(rule le_funI) apply(rule minus_cost_mono) 
  by(simp add: le_fun_def)

lemma minus_potential_antimono: 
  fixes x y :: "_ \<Rightarrow> 'b::{complete_lattice,minus,ord,top,drm} option"
  shows "x \<le> y \<Longrightarrow> minus_potential q x \<ge> minus_potential q y"
  unfolding minus_potential_alt 
  apply(rule le_funI) apply(rule minus_cost_antimono) 
  by(simp add: le_fun_def)

lemma extract_hard_case:
  fixes infi :: "'b::{complete_lattice,drm}"
  assumes "r \<in> R" "mt \<le> infi" "Inf R = Some infi" "m = Some mt" "Some infi \<notin> R"
    shows " (INF x\<in>R. case x of None \<Rightarrow> None | Some rt \<Rightarrow> minus_option rt mt) \<le> Some (infi - mt)"
proof -
  from `Inf R = Some infi` have "\<And>r. r\<in>R \<Longrightarrow> Some infi \<le> r"  
    using Inf_lower by fastforce
  with `mt \<le> infi` have a: "\<And>r. r\<in>R \<Longrightarrow> Some mt \<le> r"  
    using order_subst2 by fastforce  
  have ii: "Inf R = Some infi \<Longrightarrow> None \<notin> R" 
    by force  
  with assms(3) have "None \<notin> R" by simp
  then have "{x \<in> R. x \<noteq> None} = R" apply(intro antisym) apply auto  
    using not_None_eq by fastforce 

  from a ii have *: "\<And>r. r\<in>R \<Longrightarrow> mt \<le> the r"  
    by (metis (full_types) antisym less_eq_option_None less_eq_option_Some option.exhaust_sel)  

  have pr: "{f. Some f \<in> (\<lambda>r. Some (the r - mt)) ` R} = (\<lambda>r. the r - mt) ` R"
    apply(rule antisym)
    by auto

  have "infi = the (Inf R)" using assms(3) by auto
  also have "\<dots> = Inf (the ` R)"  
    by (metis (full_types) Inf_option_def Option.these_def \<open>None \<notin> R\<close> \<open>{x \<in> R. x \<noteq> None} = R\<close> option.sel)  
  finally have brum: "infi = Inf (the ` R)" .

  show ?thesis 
    apply(rule order.trans)
     apply(rule Inf_superset_mono[where B="(\<lambda>r. Some (the r - mt))`R"])
    subgoal apply auto  
      by (smt "*" a less_eq_option_Some_None option.case_eq_if rev_image_eqI)  
    subgoal 
      unfolding Inf_option_def  apply auto unfolding my_these_def unfolding pr
      unfolding brum 
        apply(rule minus_continuousInf[where R="(the ` R)",unfolded image_image]) using assms by auto
    done
qed
  

lemma mm_continousInf':
  fixes m :: "('d::{minus,ord,top,complete_lattice,drm}) option"
  shows "R\<noteq>{} \<Longrightarrow> minus_cost (Inf R) m = Inf ((\<lambda>r. minus_cost r m)`R)"
  apply(rule antisym)
  subgoal 
    apply(rule Inf_greatest)
    unfolding minus_cost_def
    apply (auto split: option.splits)
    subgoal using not_None_eq by fastforce  
    subgoal apply(rule diff_right_mono) using Inf_lower by force
    subgoal using Inf_lower order_trans by fastforce
    done
  subgoal 
    unfolding minus_cost_def 
    apply (auto split: option.splits)
    subgoal
      by (smt INF_lower Inf_option_def option.distinct(1) option.simps(4))
    subgoal  for mt r infi
      apply(cases "Some infi\<in>R")
      subgoal by (simp add: Inf_lower rev_image_eqI)
      subgoal apply(rule extract_hard_case[where r=r]) by auto
      done
    subgoal for mt r infi
      apply(cases "Some infi\<in>R")
      subgoal apply(rule Inf_lower) apply(rule image_eqI[where x="Some infi"]) by auto
      subgoal by (smt Inf_lower Inf_option_def in_these_eq le_Inf_iff option.case(2) option.simps(1) rev_image_eqI)
      done
    done
  done


lemma mm_continuousInf:
  fixes m :: "('d::{minus,ord,top,complete_lattice,drm}) option"
  shows "continuousInf (\<lambda>s. minus_cost s m)"
  apply(rule continuousInfI)
  apply(rule mm_continousInf') .
 

lemma minus_potential_continuousInf:
  fixes m :: "_ \<Rightarrow> ('d::{minus,ord,top,complete_lattice,drm}) option"
  shows "continuousInf (\<lambda>s. minus_potential s m x)"
  unfolding minus_potential_alt
  apply(rule continuousInf_funs)
  by (rule mm_continuousInf) 


subsubsection "mii"


definition minus_p_m :: "('a \<Rightarrow> ('b::{minus,complete_lattice,monoid_add}) option) \<Rightarrow> ('a,'b) nrest \<Rightarrow> 'a \<Rightarrow> 'b option" where 
  "minus_p_m Qf M x =  (case M of FAILi \<Rightarrow> None | REST Mf \<Rightarrow> (minus_potential Qf Mf) x)"
                                                           

lemma minus_p_m_alt: "minus_p_m Q M x = (case M of FAILi \<Rightarrow> None | REST Mf \<Rightarrow> minus_cost (Q x) (Mf x))"
  unfolding minus_p_m_def minus_potential_alt ..

lemma minus_p_m_Failt: "minus_p_m Q FAILT x = None" unfolding minus_p_m_def by auto


lemma minus_p_m_flip:
  fixes P :: "_ \<Rightarrow> ((_,enat) acost) option"
  shows "Some (T + t) \<le> minus_p_m Q (SPECT P) x \<Longrightarrow> Some t \<le> minus_p_m Q (SPECT (map_option ((+) T) \<circ> P)) x"
  unfolding minus_p_m_def
  apply (auto simp: minus_potential_def split: option.splits)
  subgoal
    by (smt add.commute less_eq_option_Some less_eq_option_Some_None minus_plus_assoc2 needname_adjoint)
  subgoal
    apply(auto simp: if_splits)
    by (metis add.commute add_le_if_le_diff needname_adjoint needname_cancle)
  done


lemma minus_p_m_mono: 
  fixes q q' :: "'a \<Rightarrow> 'b::{complete_lattice,minus,ord,top,drm,monoid_add} option"
  shows "(\<And>P x . m = SPECT P \<Longrightarrow> P x \<noteq> None \<Longrightarrow> q x \<le> q' x) \<Longrightarrow> minus_p_m q m \<le> minus_p_m q' m"
  unfolding minus_p_m_def 
  apply(rule le_funI)
  apply(auto split: nrest.splits) 
    apply(rule minus_potential_mono[THEN le_funD]) 
  by blast

lemma minus_p_m_antimono: 
  fixes x y :: "('a,'b::{complete_lattice,minus,ord,top,drm,monoid_add}) nrest"
  shows "x \<le> y \<Longrightarrow> minus_p_m q x \<ge> minus_p_m q y"
  unfolding minus_p_m_def 
  apply(rule le_funI)
  apply(auto split: nrest.splits) 
  apply(rule minus_potential_antimono[THEN le_funD]) 
  by(simp add: le_fun_def)



lemma continuousInf_minus_p_m:
  fixes m :: "(_ ,'d::{minus,ord,top,complete_lattice,drm,monoid_add}) nrest"
  shows "continuousInf (\<lambda>s. minus_p_m s m x)"
  unfolding minus_p_m_def 
  apply(cases m)
  by (auto intro: continuousInf_Map_empty minus_potential_continuousInf) 
 
 
lemma minus_p_m_continuousInf:
  fixes m :: "(_ ,'d::{minus,ord,top,complete_lattice,drm,monoid_add}) nrest"
  shows  "minus_p_m (\<lambda>x. Inf {f y x|y. True}) m x = Inf {minus_p_m (%x. f y x) m x|y. True}"
proof - 
  have *: "\<And>x. Inf {f y x|y. True} = Inf ((\<lambda>y. f y x)`UNIV)" 
    apply(rule arg_cong[where f=Inf]) by auto
  have **: "\<And>x. Inf {f y x|y. True} = (Inf ((\<lambda>y. f y )`UNIV)) x"
    unfolding * unfolding Inf_fun_def[symmetric] 
    by (metis INF_apply) 
  
  have A: "minus_p_m (\<lambda>x. Inf {f y x|y. True})
        = minus_p_m (Inf {f y |y. True})"
    apply(rule arg_cong[where f=minus_p_m])
    apply(rule ext)  unfolding **  
    by (simp add: full_SetCompr_eq)  

  show ?thesis
    unfolding A  
    apply(subst continuousInf_minus_p_m[THEN continuousInfD])
     apply auto
    apply(rule arg_cong[where f=Inf]) by auto
qed
              

lemma minus_p_m_continuous:
  fixes t :: "'b::{complete_lattice,minus,ord,top,drm,monoid_add} option"
  shows "(minus_p_m Q (Sup {F x t1 |x t1. P x t1}) x \<ge> t) = (\<forall>y t1. P y t1 \<longrightarrow> minus_p_m Q (F y t1) x \<ge> t)"
  unfolding minus_p_m_alt apply auto apply (auto simp: nrest_Sup_FAILT less_eq_option_None_is_None' split: nrest.splits)
  subgoal by (smt nrest_Sup_FAILT(2) mem_Collect_eq nres_order_simps(1) top_greatest) 
  subgoal for y t1 x2 x2a
    apply(drule nrest_Sup_SPECT_D[where x=x])
    apply(rule order.trans[where b="minus_cost (Q x) (x2 x)"])
    subgoal by simp
    subgoal 
      apply(rule minus_cost_antimono) by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq)
    done
  subgoal 
    apply(drule nrest_Sup_SPECT_D[where x=x])
    by (auto intro: minus_cost_contiuous2) 
  done 


subsection \<open>gwp\<close>


definition gwp :: "('a,'b) nrest \<Rightarrow> ('a \<Rightarrow> ('b::{complete_lattice,minus,ord,top,drm,monoid_add}) option) \<Rightarrow> 'b option" 
  where "gwp M Qf  = Inf { minus_p_m Qf M x | x. True}"


definition "gwp\<^sub>n m Q \<equiv> (if nofailT m then gwp m Q else Some top)"

lemma gwp_FAILT[simp]: "gwp FAILT Q  = None"
  by(auto simp: gwp_def minus_p_m_Failt)

lemma gwp_mono:
  fixes q q' :: "'a \<Rightarrow> 'b::{complete_lattice,minus,ord,top,drm,monoid_add} option"
  assumes "\<And>P x. \<lbrakk>m = SPECT P; P x \<noteq> None\<rbrakk> \<Longrightarrow> q x \<le> q' x"
  shows "gwp m q \<le> gwp m q'"
proof -
  from assms minus_p_m_mono
    have *: "minus_p_m q m \<le> minus_p_m q' m" by blast

  show ?thesis
  unfolding gwp_def
  apply(rule Inf_mono) 
  using "*" le_fun_def by force 
qed


lemma gwp_antimono: "M \<le> M' \<Longrightarrow> gwp M Qf \<ge> gwp M' Qf"
  unfolding gwp_def
  apply(rule Inf_mono) apply auto
  subgoal for x apply(rule exI[where x="minus_p_m Qf M' x"])
    by (auto intro!: minus_p_m_antimono[THEN le_funD])
  done


lemma gwp_pw: "gwp M Q \<ge> t  \<longleftrightarrow> (\<forall>x. minus_p_m Q M x \<ge> t)"
  unfolding gwp_def minus_p_m_def apply(cases M) apply auto
  subgoal  
    by (metis (mono_tags, lifting) le_Inf_iff mem_Collect_eq) 
  subgoal by (auto intro: Inf_greatest)
  done

lemma gwp_specifies_I: 
  shows "gwp m Q \<ge> Some 0 \<Longrightarrow> (m \<le> SPECT Q)"
  unfolding gwp_pw apply (cases m)
   apply (auto simp: minus_p_m_Failt le_fun_def minus_p_m_def minus_potential_def split: option.splits)
  subgoal for M x apply(cases "Q x"; cases "M x")
    subgoal by (auto split: if_splits)[1]
    subgoal by force 
    subgoal by (auto split: if_splits)[1]
    subgoal by (auto split: if_splits)
    done
  done

lemma gwp_specifies_rev_I: 
  fixes m :: "('b, 'a::{complete_lattice,minus,ord,top,drm,monoid_add,needname_zero}) nrest"
  shows "(m \<le> SPECT Q) \<Longrightarrow> gwp m Q \<ge> Some 0 "
  unfolding gwp_pw apply (cases m)
   apply (auto simp: minus_p_m_Failt le_fun_def minus_p_m_def minus_potential_def split: option.splits)
  subgoal for M x apply(cases "Q x"; cases "M x")
    subgoal by (auto split: if_splits)[1]
    subgoal by (metis less_eq_option_Some_None) 
    subgoal by (auto split: if_splits)[1]
    subgoal by (auto split: if_splits)
    done
  subgoal using needname_nonneg by blast
  subgoal by (metis less_eq_option_Some) 
  done



lemma gwp_specifies_rev_I_bot: 
  fixes m :: "('b, 'a::{complete_lattice,minus,ord,top,drm,monoid_add}) nrest"
  shows "(m \<le> SPECT Q) \<Longrightarrow> gwp m Q \<ge> Some bot "
  unfolding gwp_pw apply (cases m)
   apply (auto simp: minus_p_m_Failt le_fun_def minus_p_m_def minus_potential_def split: option.splits)
  subgoal for M x apply(cases "Q x"; cases "M x")
    subgoal by (auto split: if_splits)[1]
    subgoal by (metis less_eq_option_Some_None) 
    subgoal by (auto split: if_splits)[1]
    subgoal by (auto split: if_splits)
    done
  subgoal by (metis less_eq_option_Some) 
  done


lemma gwp_specifies_time_I: 
  shows "gwp m (timerefineF E Q) \<ge> Some 0 \<Longrightarrow> (m \<le> timerefine E (SPECT Q))"
  unfolding timerefine_SPECT
  apply(rule gwp_specifies_I) .

subsection "pointwise reasoning about gwp via nres3"


definition nres3 where "nres3 Q M x t \<longleftrightarrow> minus_p_m Q M x \<ge> t"


lemma le_if_le_imp_le: "(\<forall>t. gwp M Q \<ge> t \<longrightarrow> gwp M' Q' \<ge> t) \<Longrightarrow> gwp M Q \<le> gwp M' Q'"
  by simp

lemma pw_gwp_le:
  assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
  shows "gwp M Q \<le> gwp M' Q'"
  apply(rule le_if_le_imp_le)
  using assms unfolding gwp_pw nres3_def by metis

lemma pw_gwp_eq_iff:
  assumes "\<And>t. (\<forall>x. nres3 Q M x t) = (\<forall>x. nres3 Q' M' x t)" 
  shows "gwp M Q = gwp M' Q'"
  apply (rule antisym)
   apply(rule pw_gwp_le) using assms apply metis
  apply(rule pw_gwp_le) using assms apply metis
  done 

lemma pw_gwp_eqI: 
  assumes "\<And>t. (\<forall>x. nres3 Q M x t) \<Longrightarrow> (\<forall>x. nres3 Q' M' x t)"
    "\<And>t. (\<forall>x. nres3 Q' M' x t) \<Longrightarrow> (\<forall>x. nres3 Q M x t)"
  shows "gwp M Q = gwp M' Q'"
  apply (rule antisym)
   apply(rule pw_gwp_le) apply fact
  apply(rule pw_gwp_le) apply fact
  done 


lemma lem:
  fixes t :: "('b::{minus,complete_lattice,plus,needname,monoid_add}) option"
  shows
    "\<forall>t1. M y = Some t1 \<longrightarrow> t \<le> minus_p_m Q (SPECT (map_option ((+) t1) \<circ> x2)) x \<Longrightarrow> f y = SPECT x2 \<Longrightarrow> t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) (SPECT M) y"
  unfolding minus_p_m_def apply (auto split: nrest.splits)
  unfolding minus_potential_def apply (auto split: nrest.splits)
  apply(cases "M y")
  subgoal by (auto simp: top_option_def[symmetric]) 
  apply(auto split: option.splits if_splits simp: le_None)
  subgoal for a using top_absorb[of a] by simp
  subgoal apply(rule order.trans) apply assumption by(simp add: minus_plus_assoc2)
  subgoal using le_diff_if_add_le by auto
  subgoal using add_leD2 by auto
  done

lemma le_top_option: "t \<le> Some (top::'a::complete_lattice)"
    apply(cases t) by(auto simp: less_eq_option_def )  

lemma lem2:
  fixes t :: "('b::{minus,complete_lattice,plus,needname,monoid_add}) option"
  shows "t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) (SPECT M) y \<Longrightarrow> M y = Some t1 \<Longrightarrow> f y = SPECT fF \<Longrightarrow> t \<le> minus_p_m Q (SPECT (map_option ((+) t1) \<circ> fF)) x"
  apply (simp add: minus_p_m_def minus_potential_def) apply(cases "fF x") apply auto 
  apply(cases "Q x") apply (auto simp: le_top_option le_None split: if_splits option.splits) 
  subgoal for a b  apply(cases t) apply auto
    apply(rule order.trans) apply assumption by(simp add: minus_plus_assoc2) 
  subgoal for a b  apply(cases t) apply auto using add_le_if_le_diff[of t1 b a] by simp
  done

  

lemma minus_p_m_bindT: 
  fixes t :: "('b::{minus,complete_lattice,plus,needname,zero,monoid_add,drm}) option"
  shows "(t \<le> minus_p_m Q (bindT m f) x) \<longleftrightarrow> (\<forall>y. t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) m y)"
proof -
  { fix M
    assume mM: "m = SPECT M"
    let ?P = "%x t1. M x = Some t1"
    let ?F = "%x t1. case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (map_option ((+) t1) \<circ> m2)"
    let ?Sup = "(Sup {?F x t1 |x t1. ?P x t1})" 

    { fix y 
      have "(\<forall>t1. ?P y t1 \<longrightarrow> minus_p_m Q (?F y t1) x \<ge> t)
              = (t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) m y)"
        apply safe
        subgoal apply(cases "f y")
          subgoal apply (auto simp: minus_p_m_Failt le_None)
            subgoal using mM top_enat_def top_greatest top_option_def  
              by (metis (mono_tags, lifting) minus_p_m_def minus_potential_def nrest.case(2) option.case(1))  
            done
          subgoal apply (simp add: mM) using lem  by metis

          done
        subgoal for t1 apply(cases "f y")
          subgoal by (auto simp: minus_p_m_Failt minus_potential_def mM minus_p_m_def) 
          subgoal for fF apply(simp add: mM)
            using lem2 by metis
          done
        done
    } note blub=this


    from mM have "minus_p_m Q (bindT m f) x = minus_p_m Q ?Sup x" by (auto simp: bindT_def)
    then have "(t \<le> minus_p_m Q (bindT m f) x) = (t \<le> minus_p_m Q ?Sup x)" by simp
    also have "\<dots> = (\<forall>y t1. ?P y t1 \<longrightarrow> minus_p_m Q (?F y t1) x \<ge> t)" by (rule minus_p_m_continuous)  
    also have "\<dots> = (\<forall>y. t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) m y)" by(simp only: blub)
    finally have ?thesis .
  } note bl=this

  show ?thesis apply(cases m)
    subgoal by (simp add: minus_p_m_def)
    subgoal apply(rule bl) .
    done
qed


lemma t: "(\<forall>y. (t::('b::complete_lattice) option) \<le> f y) \<longleftrightarrow> (t\<le>Inf {f y|y. True})"  
  using le_Inf_iff by fastforce   

lemma nres3_bindT: 
  fixes t :: "('b::{needname_zero,drm}) option"
  shows "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>y. nres3 (\<lambda>y. gwp (f y) Q ) m y t)"
proof -
  have "(\<forall>x. nres3 Q (bindT m f) x t) = (\<forall>x.  t \<le> minus_p_m Q (bindT m f) x)" unfolding nres3_def by auto
  also have "\<dots> = (\<forall>x. (\<forall>y. t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) m y))" by(simp only: minus_p_m_bindT)
  also have "\<dots> = (\<forall>y. (\<forall>x. t \<le> minus_p_m (\<lambda>y. minus_p_m Q (f y) x) m y))" by blast
  also have "\<dots> = (\<forall>y.  t \<le> minus_p_m (\<lambda>y. Inf {minus_p_m Q (f y) x|x. True}) m y)" 
    apply(simp only: minus_p_m_continuousInf) using t by fast
  also have "\<dots> = (\<forall>y.  t \<le> minus_p_m (\<lambda>y. gwp (f y) Q) m y)" unfolding gwp_def by auto
  also have "\<dots> = (\<forall>y. nres3 (\<lambda>y. gwp (f y) Q) m y t)" unfolding nres3_def by auto
  finally show ?thesis .
  have "(\<forall>y.  t \<le> minus_p_m (\<lambda>y. gwp (f y) Q) m y) = (t \<le> Inf{ minus_p_m (\<lambda>y. gwp (f y) Q) m y|y. True})" using t by metis
qed


subsection \<open>Automation\<close>

subsubsection \<open>Progress prover\<close>


definition "progress m \<equiv> \<forall>s' M. m = SPECT M \<longrightarrow> M s' \<noteq> None \<longrightarrow> M s' > Some 0"

lemma progressD: "progress m \<Longrightarrow> m=SPECT M \<Longrightarrow> M s' \<noteq> None \<Longrightarrow> M s' > Some 0"
  by (auto simp: progress_def)


text \<open>Progress rules\<close>

named_theorems progress_rules

lemma progress_SELECT_iff: "progress (SELECT P t) \<longleftrightarrow> t > 0"
  unfolding progress_def SELECT_def emb'_def by (auto split: option.splits)

lemmas [progress_rules] = progress_SELECT_iff[THEN iffD2]

lemma progress_REST_iff: "progress (REST [x \<mapsto> t]) \<longleftrightarrow> t>0"
  by (auto simp: progress_def)

lemmas [progress_rules] = progress_REST_iff[THEN iffD2]

lemma progress_ASSERT_bind[progress_rules]:
  fixes f :: "unit \<Rightarrow> ('b,'c::{complete_lattice,zero,monoid_add}) nrest"
  shows "\<lbrakk>\<Phi> \<Longrightarrow> progress (f ()) \<rbrakk> \<Longrightarrow> progress (ASSERT \<Phi>\<bind>f)"
  by (cases \<Phi>) (auto simp: progress_def less_fun_def) 


lemma progress_SPECT_emb[progress_rules]: "t > 0 \<Longrightarrow> progress (SPECT (emb P t))" by(auto simp: progress_def emb'_def)


lemma Sup_Some: "Sup (S::('c::complete_lattice) option set) = Some e \<Longrightarrow> \<exists>x\<in>S. (\<exists>i. x = Some i)"
  unfolding Sup_option_def by (auto split: if_splits)


lemma progress_bind_aux1:
  fixes a b :: "'a::{ordered_comm_monoid_add,nonneg}" shows
 "0<a \<Longrightarrow> 0<a+b"  
    "0<a \<Longrightarrow> 0<b+a"  
  by (simp_all add: needname_nonneg add_pos_nonneg add.commute) 
 


lemma progress_bind[progress_rules]:
  fixes f :: "'a \<Rightarrow> ('b,'c::{complete_lattice,zero,ordered_comm_monoid_add,nonneg}) nrest"
  assumes "progress m \<or> (\<forall>x. progress (f x))"
  shows "progress (m\<bind>f)"
proof  (cases m)
  case FAILi
  then show ?thesis by (auto simp: progress_def)
next
  case (REST x2)   
  then show ?thesis unfolding  bindT_def progress_def apply safe
  proof (goal_cases)
    case (1 s' M y)
    let ?P = "\<lambda>fa. \<exists>x. f x \<noteq> FAILT \<and>
             (\<exists>t1. \<forall>x2a. f x = SPECT x2a \<longrightarrow> fa = map_option ((+) t1) \<circ> x2a \<and> x2 x = Some t1)"
    from 1 have A: "Sup {fa s' |fa. ?P fa} = Some y" apply simp
      apply(drule nrest_Sup_SPECT_D[where x=s']) by (auto split: nrest.splits)
    from Sup_Some[OF this] obtain fa i where P: "?P fa" and 3: "fa s' = Some i"   by blast 
    then obtain   x t1 x2a  where  a3: "f x = SPECT x2a"
      and "\<forall>x2a. f x = SPECT x2a \<longrightarrow> fa = map_option ((+) t1) \<circ> x2a" and a2: "x2 x = Some t1"  
      by fastforce 
    then have a1: " fa = map_option ((+) t1) \<circ> x2a" by auto
    have "progress m \<Longrightarrow> t1 > 0" apply(drule progressD)
      using 1(1) a2 a1 a3 by auto  
    moreover
    have "progress (f x) \<Longrightarrow> x2a s' > Some 0"  
      using   a1 1(1) a2 3  by (auto dest!: progressD[OF _ a3])   
    ultimately
    have " t1 > 0 \<or> x2a s' > Some 0" using assms by auto

    then have "Some 0 < fa s'" using   a1  3  progress_bind_aux1  
      by fastforce  
    also have "\<dots> \<le> Sup {fa s'|fa. ?P fa}" 
      apply(rule Sup_upper) using P by blast
    also have "\<dots> = M s'" using A 1(3) by simp
    finally show ?case .
  qed 
qed


method progress methods solver = 
  (rule asm_rl[of "progress _"] , (simp add: le_fun_def less_fun_def split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> | rule disjI1; progress \<open>solver\<close>; fail | rule disjI2; progress \<open>solver\<close>; fail | solver)+) []



subsubsection \<open>VCG splitter\<close>



ML \<open>

  structure VCG_Case_Splitter = struct
    fun dest_case ctxt t =
      case strip_comb t of
        (Const (case_comb, _), args) =>
          (case Ctr_Sugar.ctr_sugar_of_case ctxt case_comb of
             NONE => NONE
           | SOME {case_thms, ...} =>
               let
                 val lhs = Thm.prop_of (hd (case_thms))
                   |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
                 val arity = length (snd (strip_comb lhs));
                 (*val conv = funpow (length args - arity) Conv.fun_conv
                   (Conv.rewrs_conv (map mk_meta_eq case_thms));*)
               in
                 SOME (nth args (arity - 1), case_thms)
               end)
      | _ => NONE;
    
    fun rewrite_with_asm_tac ctxt k =
      Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
        Local_Defs.unfold0_tac ctxt' [nth prems k]) ctxt;
    
    fun split_term_tac ctxt case_term = (
      case dest_case ctxt case_term of
        NONE => no_tac
      | SOME (arg,case_thms) => let 
            val stac = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps case_thms) 
          in 
          (*CHANGED o stac
          ORELSE'*)
          (
            Induct.cases_tac ctxt false [[SOME arg]] NONE []
            THEN_ALL_NEW stac
          ) 
        end 1
    
    
    )

    fun split_tac ctxt = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} => ALLGOALS (
        SUBGOAL (fn (t, _) => case Logic.strip_imp_concl t of
          @{mpat "Trueprop (Some _ \<le> gwp ?prog _)"} => split_term_tac ctxt prog
         | @{mpat "Trueprop (Some _ \<le> gwp\<^sub>n ?prog _)"} => split_term_tac ctxt prog
         | @{mpat "Trueprop (progress ?prog)"} => split_term_tac ctxt prog  
     (*   | @{mpat "Trueprop (Case_Labeling.CTXT _ _ _ (valid _ _ ?prog))"} => split_term_tac ctxt prog *)
        | _ => no_tac
        ))
      ) ctxt 
      THEN_ALL_NEW TRY o Hypsubst.hyp_subst_tac ctxt

  end
\<close>

subsubsection \<open>VCG\<close>

method_setup refine_vcg_split_case = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (CHANGED o (VCG_Case_Splitter.split_tac ctxt)))\<close>


named_theorems vcg_rules' 
method refine_vcg_step methods solver uses rules =
    (intro rules vcg_rules' | refine_vcg_split_case 
        | (progress simp;fail)  | (solver; fail))

method refine_vcg methods solver uses rules = repeat_all_new \<open>refine_vcg_step solver rules: rules\<close>


subsection "rules for gwp"

lemma gwp_bindT:                       
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero,drm}) option"
  shows "gwp (bindT M f) Q = gwp M (\<lambda>y. gwp (f y) Q)" (* only need \<ge> *)
  apply (rule pw_gwp_eq_iff) 
  apply (rule nres3_bindT)
  done

lemma gwp_bindT_I[vcg_rules']:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option"
  shows "\<And>t. Some t \<le>  gwp  M (\<lambda>y. gwp (f y) Q ) \<Longrightarrow>  Some t \<le> gwp (M \<bind> f) Q"
  by (simp add: gwp_bindT)

lemma gwp_SPECT_emb_I[vcg_rules']: 
  fixes t' :: "'b:: {needname_zero}"
  assumes "(\<And> x. X x \<Longrightarrow> (Some (t' + t x ) \<le> Q x))"
  shows "Some t' \<le> gwp (SPECT (emb' X t)) Q"
  unfolding gwp_pw
  unfolding minus_p_m_def minus_potential_def emb'_def
  apply (auto split: option.splits)
  subgoal using assms by force
  subgoal for x tx using assms[of x] by (simp add: needname_adjoint le_fun_def)  
  subgoal for x tx using assms[of x] by (simp add: needname_cancle)    
  done


lemma gwp_consume[vcg_rules']:
  fixes m :: "(_,(_,enat) acost) nrest"
  shows "Some (T+t) \<le> gwp m Q \<Longrightarrow> Some t \<le> gwp (consume m T) Q"
  unfolding consume_def
  apply(cases m) by (auto simp: gwp_pw minus_p_m_Failt intro: minus_p_m_flip)  

lemma gwp_RETURNT_I[vcg_rules']:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option"
  shows "t \<le> Q x \<Longrightarrow> t  \<le> gwp (RETURNT x) Q" 
  apply (auto intro!: Inf_greatest intro:   
            simp: RETURNT_def needname_adjoint minus_p_m_def gwp_def minus_potential_def split: option.splits)
  subgoal using le_top_option by blast 
  subgoal by (simp add: needname_minus_absorb)  
  subgoal using le_top_option by blast  
  subgoal by (simp add: needname_nonneg)  
  done

lemma gwp_SPECT_I[vcg_rules']:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option" and t
  assumes "(Some (t' + t ) \<le> Q x)"
  shows "Some t' \<le> gwp (SPECT [ x \<mapsto> t]) Q"
  using assms
  by (auto intro: Inf_greatest intro:  add_leD2 elim: le_some_optE
            simp: needname_adjoint minus_p_m_def gwp_def minus_potential_def split: option.splits)


lemma gwp_If_I[vcg_rules']: "(b \<Longrightarrow> t \<le> gwp Ma Q) \<Longrightarrow> (\<not>b \<Longrightarrow> t \<le> gwp Mb Q) \<Longrightarrow> t  \<le> gwp (if b then Ma else Mb) Q"
   by (simp add: split_def)


lemma gwp_MIf_I[vcg_rules']:
  fixes c1 :: "(_,(_,enat) acost) nrest"
  assumes "(b \<Longrightarrow> Some (cost ''if'' 1 + t) \<le> gwp c1 Q)"
    "(\<not>b \<Longrightarrow> Some (cost ''if'' 1 + t) \<le> gwp c2 Q)"
  shows "Some t \<le> gwp (MIf b c1 c2) Q"
  unfolding MIf_def
  apply(rule gwp_consume)
  apply(rule gwp_If_I[OF assms]) by simp_all


lemma gwp_ASSERT_I[vcg_rules']:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option"
  shows "(\<Phi> \<Longrightarrow> Some t \<le> Q ()) \<Longrightarrow> \<Phi> \<Longrightarrow> Some t \<le> gwp (ASSERT \<Phi>) Q"
  apply(cases \<Phi>)
  by (auto intro: vcg_rules' )

lemma gwp_SELECT_I[vcg_rules']: 
  assumes "\<forall>x. \<not> P x \<Longrightarrow> Some tt \<le> gwp (SPECT [None \<mapsto> tf]) Q"
    and p: "(\<And>x. P x \<Longrightarrow> Some tt \<le> gwp (SPECT [Some x \<mapsto> tf]) Q )"
  shows "Some tt \<le> gwp (SELECT P tf) Q"
proof(cases "\<exists>x. P x")
  case True
  have *: "P x \<Longrightarrow> Some tt \<le> minus_cost (Q (Some x)) (Some tf)" for x
    using p[of x] unfolding gwp_pw minus_p_m_alt by(auto split: if_splits) 

  show ?thesis
    unfolding SELECT_def emb'_def gwp_pw minus_p_m_alt
    using True
    by(auto simp: * minus_cost_None split: nrest.splits option.splits if_splits)   
next
  case False
  then show ?thesis using assms(1) unfolding SELECT_def emb'_def by auto
qed 



lemma gwp_ASSERT_bind_I[vcg_rules']:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option"
  shows "(\<Phi> \<Longrightarrow> Some t \<le> gwp M Q) \<Longrightarrow> \<Phi> \<Longrightarrow> Some t \<le> gwp (do { ASSERT \<Phi>; M}) Q"
  apply(cases \<Phi>)
  by (auto intro: vcg_rules' )



  lemma gwp_specifies_acr_I: 
    fixes m :: "(_,(_,enat) acost) nrest"
    shows "(\<Phi> \<Longrightarrow> gwp m [x \<mapsto> T] \<ge> Some 0) \<Longrightarrow> (m \<le> doN { ASSERT \<Phi>; consume (RETURNT x) T })"
    apply(rule le_acost_ASSERTI)
    unfolding consume_RETURNT
    apply(rule gwp_specifies_I) by simp



subsubsection \<open>Consequence Rules\<close>

lemma gwp_conseq_aux1: 
  fixes Q :: "('b::{needname_zero}) option"
  shows "Some t \<le> minus_cost Q (Some t') \<longleftrightarrow> Some (t+t') \<le> Q"
  apply (auto simp: minus_cost_def split: option.splits)
  subgoal for t''
    using add_le_if_le_diff by auto
  subgoal for t''
    by (simp add: needname_adjoint) 
  subgoal for t''
    using needname_cancle by auto 
  done

lemma gwp_conseq_0:
  fixes f :: "('b, 'a::{needname_zero}) nrest"
  assumes 
    "gwp f Q' \<ge> Some 0"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some (t + t'')" 
  shows "gwp f Q \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded gwp_pw] have i: "Some 0 \<le> minus_p_m Q' f x" by auto
    from assms(2) have ii: "\<And>t'' M.  f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some (t + t'')" by auto
    from i ii have "Some t \<le> minus_p_m Q f x"
      unfolding minus_p_m_alt apply(auto split: nrest.splits)
      subgoal for x2
        apply(cases "x2 x")
        subgoal  by (simp add: minus_cost_None)
        subgoal
          apply(simp add: gwp_conseq_aux1)  
          apply(cases "Q' x")
          subgoal by simp  
          apply(cases "Q x")
          subgoal by auto 
          subgoal premises prems for qv' qv
            using prems(1)[of x2 qv'] prems(2-6) apply auto
             apply(rule order.trans) defer apply assumption
            by(simp add: needname_plus_absorb plus_left_mono)
          done
        done
      done
  } 
  thus ?thesis
    unfolding gwp_pw ..
qed


lemma gwp_conseq:
  fixes f :: "('b, 'a::{complete_lattice,minus,ord,top,drm,monoid_add,needname_zero}) nrest"
  assumes 
    "gwp f Q' \<ge> Some t"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')" 
  shows "gwp f Q \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded gwp_pw] have i: "Some t \<le> minus_p_m Q' f x" by auto
    from assms(2) have ii: "\<And>t'' M.  f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some t''" by auto
    from i ii have "Some t \<le> minus_p_m Q f x"
      unfolding minus_p_m_alt apply(auto split: nrest.splits)
      subgoal for x2
        apply(cases "x2 x")
        subgoal  by (simp add: minus_cost_None)
        subgoal
          apply(simp add: gwp_conseq_aux1)  
          apply(cases "Q' x")
          subgoal by simp  
          apply(cases "Q x")
          subgoal by auto 
          subgoal using le_add2 by force
          done
        done
      done
  } 
  thus ?thesis
    unfolding gwp_pw ..
qed


lemma gwp_conseq4_aux2: "t - t' + b \<le> c \<Longrightarrow> t' + a \<le> b \<Longrightarrow> t + a \<le> (c::enat)"
  apply(cases t; cases t'; cases b; cases c; cases a) by auto

lemma gwp_conseq4_aux3: "t - t' + b \<le> c \<Longrightarrow> t' + a \<le> b \<Longrightarrow> t + a \<le> (c::('a,enat)acost)"  
  apply(cases t; cases t'; cases b; cases c; cases a)
  unfolding less_eq_acost_def le_fun_def apply simp
  apply safe apply(rule gwp_conseq4_aux2) by auto



lemma gwp_conseq4:
  fixes f :: "('b, ('a,enat) acost) nrest"
  assumes 
    "gwp f Q' \<ge> Some t'"
    "\<And>x t'' M. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" 
  shows "gwp f Q  \<ge> Some t"
proof -
  {
    fix x
    from assms(1)[unfolded gwp_pw] have i: "Some t' \<le> minus_p_m Q' f x" by auto
    from assms(2) have ii: "\<And>t''. Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ((t - t') + t'')" by auto
    from i ii have "Some t \<le> minus_p_m Q f x"
      unfolding minus_p_m_alt apply(auto split: nrest.splits)
      subgoal for x2 apply(cases "x2 x") apply (simp add: minus_cost_None)
        apply(simp add: gwp_conseq_aux1)  
        apply(cases "Q' x") apply simp
        apply auto 
        apply(cases "Q x") apply auto 
        subgoal for a aa ab apply(rule gwp_conseq4_aux3[where t'=t' and b=aa]) by auto 
        done
      done
  } 
  thus ?thesis
    unfolding gwp_pw ..
qed

subsubsection \<open>Rules for While\<close>

lemma gwp_whileT_rule_wf: 
  fixes r :: "('a,(_,enat)acost) nrest"
  assumes "whileT b c s = r"
  assumes IS: "\<And>s t'. I s = Some t' \<Longrightarrow> b s 
           \<Longrightarrow> Some t' \<le>  gwp (c s) (\<lambda>s'. if (s',s)\<in>R then I s' else None)"
  assumes "I s = Some t"
  assumes wf: "wf R"
  shows "gwp r (\<lambda>x. if b x then None else I x) \<ge> Some t"
  using assms(1,3)
  unfolding whileT_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp
    apply safe 
    subgoal apply (refine_vcg \<open>-\<close> rules: IH IS[THEN gwp_conseq]) by (auto split: if_splits)
    subgoal apply (refine_vcg \<open>-\<close>) by (auto split: if_splits)
    done

qed

lemma Inf_option_Some_aux1: "Inf {uu. \<exists>xa. (xa = x \<longrightarrow> uu = Some (a - T)) \<and> (xa = x \<or> uu = Some top)} = Some (a-T)"
proof -
  consider "{uu. \<exists>xa. (xa = x \<longrightarrow> uu = Some (a - T)) \<and> (xa = x \<or> uu = Some top)}
        = { Some (a-T) }" | "{uu. \<exists>xa. (xa = x \<longrightarrow> uu = Some (a - T)) \<and> (xa = x \<or> uu = Some top)}
        = { Some (a-T) , Some top }" by auto
  then show ?thesis
    apply(cases) apply simp apply simp done
qed

 
lemma monadic_WHILE_rule''_aux1:
  fixes T :: "(_,enat) acost"
  shows "gwp (SPECT [x\<mapsto>T]) Q = Some t \<Longrightarrow> Q x = Some (T+t)"
  unfolding gwp_def minus_p_m_def minus_potential_def apply simp
  apply(auto split: if_splits)
  apply(cases "Q x") apply simp apply auto 
  apply(auto split: if_splits)
  subgoal for a
  unfolding Inf_option_Some_aux1  apply simp apply(cases T; cases t; cases a)
    unfolding less_eq_acost_def minus_acost_alt plus_acost_alt apply simp
      apply(rule ext)  
    by (metis add_diff_assoc_enat add_diff_cancel_enat enat_ord_simps(4) leD plus_eq_infty_iff_enat) 
  done

lemma consume_alt3:
  fixes M :: "(_,(_,enat) acost) nrest" 
  shows "consume M T = do { r \<leftarrow> M; _ \<leftarrow> SPECT [()\<mapsto>T]; RETURNT r}"
  using consume_alt  apply (simp add: consumea_def)
  by blast



lemma
  fixes r :: "('a, (char list, enat) acost) nrest"
  assumes "monadic_WHILEIT' Inv bm c s = r" 
  assumes IS: "\<And>s t'. I s = Some t' 
           \<Longrightarrow>  gwp (bm s) (\<lambda>b. gwp (SPECT [()\<mapsto> (cost ''if'' 1)]) (\<lambda>_. if b then gwp (do { consume (c s) (cost ''call'' 1)  })  (\<lambda>s'. if (s',s)\<in>R then I s' else None) else Q s)) \<ge> Some t'"
  assumes "I s = Some t"
  assumes z: "\<And>t s. I s = Some t \<Longrightarrow> Inv s"
  assumes wf: "wf R"
  shows monadic_WHILE_rule'': "gwp r Q \<ge> Some t"
  using assms(1,3)
  unfolding monadic_WHILEIT'_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH[vcg_rules'] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply clarsimp  
    apply(rule gwp_ASSERT_bind_I)
    apply (rule gwp_bindT_I)
    apply(rule gwp_conseq)
      apply (rule IS) apply simp  
    unfolding MIf_def
     apply(auto split: if_splits)
      defer 
    subgoal 
      apply(rule gwp_consume)
      apply(rule vcg_rules')
      apply(drule monadic_WHILE_rule''_aux1) by simp
    subgoal
      apply(rule z) apply simp
      done
    subgoal
      apply(drule monadic_WHILE_rule''_aux1)
      apply(rule gwp_consume)
      unfolding consume_alt3
      apply(subst (asm) gwp_bindT)
      apply (rule gwp_bindT_I)
      subgoal premises pr
        apply(rule gwp_conseq) 
         apply(subst pr(6)) apply simp
        apply(subst (asm) gwp_bindT)
      apply(drule monadic_WHILE_rule''_aux1)
        unfolding RETURNT_alt
        apply(drule monadic_WHILE_rule''_aux1) apply (auto split: if_splits)
        apply(rule gwp_bindT_I)
        apply(rule gwp_SPECT_I) 
      apply(rule IH) apply simp by (simp add: add.commute)
      done
    done
qed
lemma
  fixes r :: "('a, (char list, enat) acost) nrest"
  assumes pi: "monadic_WHILEIT Inv bm c s = r" 
  assumes IS: "\<And>s t'. I s = Some t' 
           \<Longrightarrow>  gwp (bm s) (\<lambda>b. gwp (SPECT [()\<mapsto> (cost ''if'' 1)]) (\<lambda>_. if b then gwp (do { consume (c s) (cost ''call'' 1)  })  (\<lambda>s'. if (s',s)\<in>R then I s' else None) else Q s)) \<ge> Some t'"
  assumes "I s = Some (t + cost ''call'' 1)"
  assumes z: "\<And>t s. I s = Some t \<Longrightarrow> Inv s"
  assumes wf: "wf R"
  shows monadic_WHILE_rule_real: "gwp r Q \<ge> Some t"
  apply(subst pi[symmetric])
  unfolding monadic_WHILEIT_def
  apply(rule gwp_bindT_I)
  apply(rule gwp_SPECT_I)
  unfolding monadic_WHILEIT'_def[symmetric]
  apply(rule monadic_WHILE_rule''[OF refl])
     apply (rule IS)
     apply simp apply(fact)
   apply(fact z) apply fact 
  done



fun Someplus where
  "Someplus None _ = None"
| "Someplus _ None = None"
| "Someplus (Some a) (Some b) = Some (a+b)"

definition mm22 :: "( ('c,enat) acost option) \<Rightarrow> (   ('c,enat) acost option) \<Rightarrow> (   ('c,enat) acost option)" where
  "mm22 r m = (case m  of None \<Rightarrow> Some (acostC (\<lambda>_. \<infinity>))
                                | Some mt \<Rightarrow>
                                  (case r of None \<Rightarrow> None | Some rt \<Rightarrow> (if mt \<le> rt then Some (rt - mt) else None)))"





abbreviation "lift_acost_option I \<equiv> case_option None (\<lambda>m. Some (lift_acost m)) I"


thm gwp_conseq
lemma mm3_None[simp]: "mm3 t None = None"
  unfolding mm3_def by auto
term wfR

lemma wfR_D: "wfR (\<lambda>s. the (I s)) \<Longrightarrow> finite {(s,f). the_acost (the (I s)) f \<noteq> 0}"
  unfolding wfR_def by auto

lemma wfR_D2: "wfR (\<lambda>s. the (I s)) \<Longrightarrow> finite {f. the_acost (the (I s)) f \<noteq> 0}"
  apply(rule wfR_snd[where R="(\<lambda>s. the (I s))"]) .

lemma wfR_D3: "wfR (\<lambda>s. the (I s)) \<Longrightarrow> I s = Some c \<Longrightarrow> finite {f. the_acost c f \<noteq> 0}"
  apply(drule wfR_D2[where s=s]) by simp


lemma wfR_D4: "wfR (\<lambda>s. (case I s of None \<Rightarrow> 0 | Some t \<Rightarrow> t)) \<Longrightarrow> finite {x. the_acost (case I s of None \<Rightarrow> 0 | Some t \<Rightarrow> t) x \<noteq> 0}"
  apply(rule wfR_snd[where R="(\<lambda>s. (case I s of None \<Rightarrow> 0 | Some t \<Rightarrow> t))"]) .


definition ffS :: "(_\<Rightarrow>'a\<Rightarrow>nat) \<Rightarrow> ('a \<times> 'a) set"
  where "ffS f = {(s,s')| s s'. f s < f s'}"

definition ffSacost :: "('a \<Rightarrow> (_,nat) acost) \<Rightarrow> ('a \<times> 'a) set"
  where "ffSacost f = {(s,s')| s s'. the_acost (f s) < the_acost (f s')}"

lemma z:
  fixes f :: "_ \<Rightarrow> 'a::linorder"
  shows "(f \<le> g \<and> (\<exists>x. f x < g x)) \<longleftrightarrow> f < g"
  apply rule
  subgoal 
    unfolding le_fun_def less_fun_def apply auto
    subgoal for x apply(rule exI[where x=x]) by simp
    done
  subgoal 
    unfolding le_fun_def less_fun_def apply auto
    subgoal for x apply(rule exI[where x=x]) by simp
    done
  done
    

lemma za:
  fixes f g :: "'a\<Rightarrow>nat"
  assumes "finite {x. g x\<noteq>0 }"
  shows "f < g \<Longrightarrow>  Sum_any (\<lambda>b. f b) < Sum_any (\<lambda>b. g b)"
proof -
  assume fg: "f < g"
  then obtain x where f_le_g:"f \<le> g" and less: "f x < g x" unfolding z[symmetric] by blast
  then have gs0: "g x \<noteq> 0" by auto
  then have klo: "x  : {x. g x\<noteq>0 }" by auto
  have subs: "{x. f x\<noteq>0 } \<subseteq> {x. g x\<noteq>0 }" apply auto using f_le_g unfolding le_fun_def
    by (metis gr_zeroI leD)  
  from subs assms have fs: "finite {x. f x\<noteq>0 }"  
    using infinite_super by blast
  have "Sum_any f = sum f {x. f x\<noteq>0 }" by (simp add: Sum_any.expand_set)
  also have "\<dots> =  sum f (({x. f x\<noteq>0 }-{x})\<union>{x})"
    apply(cases "x \<in> {x. f x\<noteq>0 }")
     apply simp_all
    subgoal  
      by (simp add: insert_absorb)  
    subgoal  
      by (metis add.commute add.right_neutral finite_insert sum.infinite sum.insert_if)
  done
  also have "\<dots> \<le> sum f ({x. 0 < f x} - {x}) + f x"
    apply(subst sum.union_disjoint)
    subgoal apply simp using assms  fg fs by auto  
    subgoal apply auto done
    subgoal by simp
    apply simp
    done
  also have "\<dots> \<le> sum g ({x. 0 < f x} - {x}) + f x"
    apply simp apply(rule sum_mono) using f_le_g unfolding le_fun_def by auto
  also have "\<dots> < sum g ({x. 0 < f x} - {x}) + g x"
    apply simp using less .
  also have "\<dots> \<le> sum g ({x. 0 < g x} - {x}) + g x"
    apply simp  apply(rule sum_mono2) using assms apply simp
    using subs  by auto
  also have "\<dots> \<le> sum g ({x. 0 < g x} - {x} \<union> {x})"
    apply(subst sum.union_disjoint) using assms apply simp
      apply simp
     apply simp
    apply simp
    done
  also have "\<dots> = Sum_any g" using klo apply simp apply (simp add: Sum_any.expand_set)
    apply(rule arg_cong[where f="sum g"]) by auto
  finally
  show "Sum_any f < Sum_any g" .
qed

lemma wf_Sum_any: "wf (measure (\<lambda>s. Sum_any (\<lambda>b. (f s) b)))"
  apply(rule wf_measure) .

thm in_measure
lemma wf_ffS: "(\<And>s. finite {x. f s x\<noteq>0 }) \<Longrightarrow> wf (ffS f)"
  apply(rule wf_subset[OF wf_Sum_any[of f]])
  unfolding ffS_def 
  unfolding measure_def apply auto
  apply(rule za) apply simp
  apply simp done

lemma wf_ffSacost: "(\<And>s. finite {x. the_acost (f s) x\<noteq>0 }) \<Longrightarrow> wf (ffSacost f)"
  apply(rule wf_subset[OF wf_Sum_any[of "\<lambda>s. the_acost (f s)"]])
  unfolding ffSacost_def 
  unfolding measure_def  apply auto
  subgoal for a b 
  apply(rule za) unfolding less_fun_def apply simp
    apply simp done
  done

lemma lift_acost_option_some_finite:
  "lift_acost_option I = Some t0 \<Longrightarrow> (\<forall>x. the_acost t0 x <\<infinity>)"
  unfolding lift_acost_def by (auto split: option.splits)

lemma 
  the_acost_less_aux:
  "0 < D \<Longrightarrow> D \<le> lift_acost ti - lift_acost y \<Longrightarrow> lift_acost y \<le> lift_acost ti  \<Longrightarrow> the_acost y < the_acost ti"
  apply(cases D; cases y; cases ti) apply (auto simp: lift_acost_def less_eq_acost_def less_fun_def le_fun_def)
  by (metis acost.sel diff_is_0_eq' leD less_acost_def zero_acost_def zero_enat_def) 


definition "loopbody_cond b d = (if b then Some d else None)"
definition "loopexit_cond Qs t Es0 Es = mm22 Qs (Someplus (Some t) (mm3 (Es0) (Some (Es))))"

lemma lift_acost_cancel: "lift_acost x - lift_acost x = 0"
  by(auto simp: lift_acost_def zero_acost_def zero_enat_def)


lemma neueWhile_aux1: "Someplus (Some t) (mm3 (lift_acost (E s0)) (if I s then Some (lift_acost (E s)) else None)) = Some t'
  \<Longrightarrow> I s \<and> t' = t + (lift_acost (E s0) - lift_acost (E s)) \<and> lift_acost (E s) \<le> lift_acost (E s0)"
  unfolding mm3_def by (auto split: if_splits) 

lemma pff: "Someplus (Some t) R \<le> Q \<Longrightarrow> Some t \<le> mm22 Q R"
  unfolding mm22_def apply(auto split: option.splits)
  subgoal unfolding less_eq_acost_def by simp
  subgoal using needname_adjoint by blast
  subgoal using needname_cancle by blast
  done
lemma pff2: "Some t \<le> mm22 Q R \<Longrightarrow> Someplus (Some t) R \<le> Q"
  unfolding mm22_def apply(auto split: option.splits if_splits)
  using add_le_if_le_diff by blast



lemma Someplus_None: "Someplus Q None = None"
  by (cases Q; auto)

lemma minus_p_m_Map_empty: "minus_p_m Map.empty a b = 
     (case a of FAILi \<Rightarrow> None | REST Mf \<Rightarrow> case Mf b of None \<Rightarrow> Some top | Some mt \<Rightarrow> None)" 
  unfolding minus_p_m_def minus_potential_def by (auto split: nrest.splits option.splits )

lemma "mm22 (gwp c Q) (Some T) = gwp c (\<lambda>x. Someplus (Q x) (Some T))"
  unfolding mm22_def gwp_def 
  apply (simp add: Someplus_None minus_p_m_Map_empty)
  unfolding minus_p_m_def minus_potential_def
  apply(cases c) apply auto oops


lemma mm22_minus_cost: "mm22 c r = minus_cost c r"
  unfolding mm22_def unfolding minus_cost_def top_acost_def top_enat_def by simp

lemma "Inf {u. \<exists>x. u = minus_potential (\<lambda>x. case Q x of None \<Rightarrow> None | Some rt \<Rightarrow> minus_option rt T) x2 x}
          \<le> (case Inf {u. \<exists>x. u = minus_potential Q x2 x} of None \<Rightarrow> None | Some rt \<Rightarrow> minus_option rt T)"
  oops

lemma minus_cost_minus_p_m_commute:
  fixes T :: "(_,enat) acost"
  shows "minus_cost (minus_p_m Q c x) (Some T) = minus_p_m (\<lambda>x. minus_cost (Q x) (Some T)) c x"
  unfolding minus_cost_def minus_p_m_def minus_potential_def  apply(cases T)
  apply (auto split: nrest.splits option.splits) apply(auto simp: top_acost_def minus_acost_alt top_enat_def split: option.splits acost.splits intro!: ext)
  subgoal 
    by (metis add.commute minus_plus_assoc2) 
  subgoal 
    by (smt acost.sel add_diff_cancel_enat enat_add_left_cancel_le less_eqE less_eq_acost_def needname_adjoint)
  subgoal    
    by (metis (full_types) drm_class.diff_left_mono minus_acost.simps needname_minus_absorb needname_nonneg order_trans)
  subgoal 
    by (smt acost.sel add_diff_cancel_enat enat_add_left_cancel_le less_eqE less_eq_acost_def needname_adjoint) 
  subgoal 
    by (metis (full_types) drm_class.diff_left_mono minus_acost.simps needname_minus_absorb needname_nonneg order_trans) 
  done

lemma aaa1: "gwp c (\<lambda>x. mm22 (Q x) (Some T)) = mm22 (gwp c Q) (Some T)"
  unfolding  gwp_def           unfolding  mm22_minus_cost   
  apply(subst mm_continousInf')
  subgoal apply auto done
proof -
  have "(INF r\<in>{minus_p_m Q c x |x. True}. minus_cost r (Some T))
         = Inf  {minus_cost (minus_p_m Q c x) (Some T) |x. True}"
    apply(rule arg_cong[where f=Inf]) by auto
  also have "\<dots> = Inf {minus_p_m (\<lambda>x. minus_cost (Q x) (Some T)) c x |x. True}"
    apply(subst minus_cost_minus_p_m_commute) by simp
  finally show "Inf {minus_p_m (\<lambda>x. minus_cost (Q x) (Some T)) c x |x. True}
                = (INF r\<in>{minus_p_m Q c x |x. True}. minus_cost r (Some T))" by simp
qed
  
lemma aaa: "gwp c (\<lambda>x. mm22 (Q x) (Some T)) \<le> mm22 (gwp c Q) (Some T)"
  unfolding aaa1 by simp

thm mm_continousInf'

lemma lift_acost_mono: "A \<le> B \<Longrightarrow> lift_acost A \<le> lift_acost B"
  by (auto simp: less_eq_acost_def lift_acost_def)
lemma lift_acost_mono': "lift_acost A \<le> lift_acost B \<Longrightarrow> A \<le> B"
  by (auto simp: less_eq_acost_def lift_acost_def)

lemma blah:
  fixes T :: "(_,enat) acost"
    shows "consume (c s) T = SPECT x2
      \<Longrightarrow> \<exists>x3. c s = SPECT x3 \<and> (\<forall>x. x2 x = Someplus (x3 x) (Some T))"
  unfolding consume_def apply(auto split: nrest.splits)
  subgoal for x2a x apply(cases "x2a x") by (auto simp: add.commute)
  done

lemma argh: "b\<le>d \<Longrightarrow> c\<le>d \<Longrightarrow> a + d - (b + (a + d - (c::nat))) = c - b"
  by simp 

lemma 
  fixes s0 :: 'a and I :: "'a \<Rightarrow> bool" and E :: "'a \<Rightarrow> (string, nat) acost" and t :: "(string, enat) acost"
    and Q :: "'a \<Rightarrow>  (string, enat) acost option"
  assumes wf: "\<And>s. wfR2 (if I s then E s else 0)"
  assumes
  step: "(\<And>s. I s \<Longrightarrow> Some 0 \<le> gwp (bm s) (\<lambda>b. gwp (SPECT [()\<mapsto> (cost ''if'' 1)])
       (\<lambda>_. if b then gwp (do { consume (c s) (cost ''call'' 1)  })
                             (\<lambda>s'. loopbody_cond (I s' \<and> E s' \<le> E s) (lift_acost (E s - E s')))
                 else loopexit_cond (Q s) t (lift_acost (E s0)) (lift_acost (E s)))))"
(* and  progress: "\<And>s. progress (c s)" \<comment> \<open>This is actually not really needed, because ''call'' needs to decrease!
                                         As an improvement one could not look at ''call'' and ''if'' costs, by setting them to \<infinity>, then progress is needed again.\<close> *)
 and  i: "I s0"                                       
shows neueWhile_rule'': "Some t \<le> gwp (monadic_WHILEIET' I E bm c s0) Q"
proof  -


  show ?thesis unfolding monadic_WHILEIET'_def
    apply (rule monadic_WHILE_rule''[OF refl,
              where I="\<lambda>s. Someplus (Some t) (mm3 (lift_acost (E s0)) ((\<lambda>e. if I e
                then Some (lift_acost (E e)) else None) s))" 
                and R="ffSacost (\<lambda>s. if I s then E s else 0)", simplified])
    subgoal for s t' (* step *)
      apply(drule neueWhile_aux1)
      apply(rule gwp_conseq_0)
      apply(rule step)
       apply simp
      apply(rule gwp_SPECT_I)
      apply(drule monadic_WHILE_rule''_aux1) apply safe
    proof (goal_cases)
      case (1 x t'' M)
      have A1: "(\<lambda>s'. loopbody_cond (I s' \<and> E s' \<le> E s) (lift_acost (E s - E s')))
          = (\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (lift_acost (E s - E s')) else None)"
        unfolding loopbody_cond_def by simp
      have A2:  "loopexit_cond (Q s) t (lift_acost (E s0)) (lift_acost (E s)) 
            = mm22 (Q s) (Some (t + (lift_acost (E s0) - lift_acost (E s))))"
        unfolding loopexit_cond_def unfolding mm3_def using 1(5) by simp

      (* thm progress[THEN progressD] 1 gwp_pw *)
      { fix tt Q
        from pff2[where R="Some (t + (lift_acost (E s0) - lift_acost (E s)))", of tt Q]
        have faaa: "Some tt \<le> mm22 Q (Some (t + (lift_acost (E s0) - lift_acost (E s))))
                 \<Longrightarrow> (Some (t + (lift_acost (E s0) - lift_acost (E s)) +tt)) \<le> Q"
          apply simp apply(subst (2) add.commute) .
      } note faaa = this

        from 1(2)[symmetric]
        show ?case apply(simp only: A1 A2)
          apply(subst (2)add.assoc)
          apply(rule faaa)
          apply(subst (asm) add.commute)
          subgoal premises prems apply(subst prems)
            apply(cases x)
            subgoal apply simp
              apply(rule order.trans[OF _ aaa])
              unfolding ffSacost_def using 1(4) apply auto
              unfolding gwp_def
              apply(rule Inf_mono) apply auto
              subgoal for xa
                apply(rule exI[where x="minus_p_m (\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (lift_acost (E s - E s')) else None) (consume (c s) (cost ''call'' 1)) xa"])
                apply safe  apply(rule exI[where x=xa])
                 apply simp
                unfolding minus_p_m_def apply(auto split: nrest.splits)
                unfolding minus_potential_def apply(split option.splits) apply simp
                apply auto
                subgoal for x2 x3
                  subgoal unfolding mm3_def using 1(5) apply simp    apply auto unfolding mm22_def apply auto
                  proof -
                    assume I: "x" "I s" "consume (c s) (cost ''call'' 1) = SPECT x2" "the_acost (E xa) < the_acost (E s)" 
                            "I xa" "E xa \<le> E s" "x3 \<le> lift_acost (E s - E xa)" "x2 xa = Some x3"
                            "lift_acost (E s) \<le> lift_acost (E s0)" 
                    have A: "lift_acost (E xa) \<le> lift_acost (E s0)"
                      using I(6)[THEN lift_acost_mono] I(9) by simp

                    show "x3 \<le> t + (lift_acost (E s0) - lift_acost (E xa)) - (t + (lift_acost (E s0) - lift_acost (E s)))"
                      apply(cases t; cases "E s0"; cases "E xa"; cases "E s"; cases x3) apply simp
                      
                      using I(7) I(9) A
                      unfolding less_eq_acost_def lift_acost_def plus_acost_alt minus_acost_alt
                      apply auto
                      subgoal for x xaa xb xc xd xe apply(cases "x xe") apply simp_all apply(subst argh) by auto
                      done

                    show "t + (lift_acost (E s0) - lift_acost (E s)) \<le> t + (lift_acost (E s0) - lift_acost (E xa))"
                      apply(cases t; cases "E s0"; cases "E xa"; cases "E s"; cases x3) apply simp
                      
                      using I(7) I(9) A
                      unfolding less_eq_acost_def lift_acost_def plus_acost_alt minus_acost_alt
                      apply auto
                      subgoal for x xaa xb xc xd xe apply(cases "x xe") apply simp_all
                        by (metis I(6) acost.sel diff_le_mono2 less_eq_acost_def)
                      done
                    show "lift_acost (E s - E xa) - x3 \<le> t + (lift_acost (E s0) - lift_acost (E xa)) - (t + (lift_acost (E s0) - lift_acost (E s))) - x3"
                      apply(cases t; cases "E s0"; cases "E xa"; cases "E s"; cases x3) apply simp
                      
                      using I(7) I(9) A
                      unfolding less_eq_acost_def lift_acost_def plus_acost_alt minus_acost_alt
                      apply auto
                      subgoal for x xaa xb xc xd xe apply(cases "x xe") apply simp_all  
                        by (simp add: argh)
                      done         
                    { assume "\<not> lift_acost (E xa) \<le> lift_acost (E s0)"
                      with A show False by simp
                      }
                  qed
                done
              subgoal for x2 t
                
                apply(drule blah) apply auto 
               (*  apply(drule progress[THEN progressD, where s'=xa])
                subgoal for x3 apply(cases "x3 xa") by auto *)
                unfolding mm22_def apply auto
                subgoal for x4 proof (goal_cases)
                  case 1 
                  (* from 1(9) obtain tt where "x4 xa = Some tt"  apply(cases "x4 xa") by auto *)
                  with 1(7) have "t>0" apply(cases "x4 xa") apply auto unfolding less_acost_def  zero_acost_def apply auto 
                    subgoal for x apply(rule exI[where x="''call''"]) unfolding plus_acost_alt cost_def apply simp
                      apply(cases x) by simp
                    done
                  with 1(3,6) show ?case unfolding less_acost_def zero_acost_def lift_acost_def minus_acost_alt
                    apply(cases "E xa"; cases "E s"; cases t) unfolding less_eq_acost_def le_fun_def less_fun_def apply auto
                      subgoal 
                        by (metis "1"(5) acost.sel less_eq_acost_def) 
                      subgoal 
                        using zero_enat_def by auto 
                      done
                qed  
                done
              done
            done
            subgoal by simp
            done
          done
      qed
    subgoal (* init *) apply(simp add: i) unfolding mm3_def by (simp add: lift_acost_cancel)
    subgoal for ta s apply(cases "I s") by auto 
    subgoal apply(rule wf_ffSacost) using wf[unfolded wfR2_def] .
    done
qed



lemma 
  fixes s0 :: 'a and I :: "'a \<Rightarrow> bool" and E :: "'a \<Rightarrow> (string, nat) acost" and t :: "(string, enat) acost"
    and Q :: "'a \<Rightarrow>  (string, enat) acost option"
  assumes wf: "\<And>s. wfR2 (if I s then E s else 0)"
  assumes
  step: "(\<And>s. I s \<Longrightarrow> Some 0 \<le> gwp (bm s) (\<lambda>b. gwp (SPECT [()\<mapsto> (cost ''if'' 1)])
       (\<lambda>_. if b then gwp (do { consume (c s) (cost ''call'' 1)  })
                             (\<lambda>s'. loopbody_cond (I s' \<and> E s' \<le> E s) (lift_acost (E s - E s')))
                 else loopexit_cond (Q s) (t + cost ''call'' 1) (lift_acost (E s0)) (lift_acost (E s)))))"
(* and  progress: "\<And>s. progress (c s)" \<comment> \<open>This is actually not really needed, because ''call'' needs to decrease!
                                         As an improvement one could not look at ''call'' and ''if'' costs, by setting them to \<infinity>, then progress is needed again.\<close> *)
 and  i: "I s0"                                       
shows neueWhile_rule''_real: "Some t \<le> gwp (monadic_WHILEIET I E bm c s0) Q"
  unfolding monadic_WHILEIET_def monadic_WHILEIT_def
  apply(rule gwp_bindT_I)
  apply(rule gwp_SPECT_I)
  unfolding monadic_WHILEIT'_def[symmetric] monadic_WHILEIET'_def[symmetric, where E=E]
  apply(rule neueWhile_rule'')
     apply fact
    apply(rule step) using assms by auto
lemma lift_acost_leq_conv: "lift_acost (E s) \<le> lift_acost (E s0) \<longleftrightarrow> E s \<le> E s0"
  by(auto simp: less_eq_acost_def lift_acost_def)
lemma lift_acost_minus: " lift_acost A - lift_acost B =  lift_acost (A - B)"
  by(cases A; cases B; auto simp: lift_acost_def minus_acost_alt)

lemma neueWhile_rewrite: "mm22 (Q s) (Someplus (Some (t + cost ''call'' 1)) (mm3 (lift_acost (E s0)) (Some (lift_acost (E s)))))
    = (if E s \<le> E s0 then minus_cost (Q s) (Some (t + cost ''call'' 1 + (lift_acost (E s0 - E s)))) else Some top)"
  apply(auto simp: mm22_minus_cost[symmetric] top_acost_def lift_acost_minus top_enat_def lift_acost_leq_conv mm3_def mm22_def split: option.splits if_splits)
  done


definition "loop_body_condition Is' Es' Es = (if Is' \<and> Es' \<le> Es then Some (lift_acost (Es - Es')) else None)"
definition "loop_exit_condition Qs t Es Es0 = (if Es \<le> Es0 then minus_cost Qs (Some (t + cost ''call'' 1 + (lift_acost (Es0 - Es)))) else Some top)"


lemma plus_minus_adjoint_ecost: "A \<le> B \<Longrightarrow> t \<le> B - A \<longleftrightarrow> t + A \<le> (B::(_,enat) acost)"
  apply(cases t; cases B, cases A)
  apply(auto simp: less_eq_acost_def minus_acost_alt plus_acost_alt)
  subgoal by (smt ab_semigroup_add_class.add_ac(1) add.commute add_diff_cancel_enat le_iff_add plus_eq_infty_iff_enat)
  subgoal by (simp add: needname_adjoint)
  done

lemma loop_body_conditionI:
  assumes "lift_acost Es' \<le> lift_acost Es"
  assumes "t + lift_acost Es' \<le> lift_acost Es"
  assumes "Is'"
  shows  "Some t \<le> loop_body_condition Is' Es' Es"
  unfolding loop_body_condition_def
  using assms
  apply (auto simp: lift_acost_minus[symmetric] intro: lift_acost_mono') 
  apply(subst plus_minus_adjoint_ecost)
  by simp_all 

lemma le_minus_cost_if_gt_Someplus: 
  fixes Q :: "('b, enat) acost option"
  shows "Someplus (Some t) R \<le> Q \<Longrightarrow> Some t \<le> minus_cost Q R"
  by(rule pff[unfolded mm22_minus_cost]) 
                    
lemma le_minus_cost_Some_if_gt_Some: 
  fixes Q :: "('b, enat) acost option"
  shows "Some (t + R) \<le> Q \<Longrightarrow> Some t \<le> minus_cost Q (Some R)"
  apply(rule le_minus_cost_if_gt_Someplus) by simp

thm loop_exit_condition_def
lemma loop_exit_conditionI:
  assumes  "Es \<le> Es0 \<Longrightarrow>  Some ((lift_acost (Es0 - Es)) + (t' + (t + cost ''call'' 1 ))) \<le> Qs"
  shows "Some t' \<le> loop_exit_condition Qs t Es Es0"
  using assms unfolding loop_exit_condition_def
  apply simp apply safe
  apply(rule le_minus_cost_Some_if_gt_Some) by (simp add: add_ac)



lemma 
  fixes s0 :: 'a and I :: "'a \<Rightarrow> bool" and E :: "'a \<Rightarrow> (string, nat) acost" and t :: "(string, enat) acost"
    and Q :: "'a \<Rightarrow>  (string, enat) acost option"
  assumes wf: "\<And>s. wfR2 (if I s then E s else 0)"
  assumes
  step: "(\<And>s. I s \<Longrightarrow> Some 0 \<le> gwp (bm s) (\<lambda>b. gwp (SPECT [()\<mapsto> (cost ''if'' 1)])
       (\<lambda>_. if b then gwp (do { consume (c s) (cost ''call'' 1)  })
                             (\<lambda>s'. loop_body_condition (I s') (E s') (E s) )
                 else loop_exit_condition (Q s) t (E s) (E s0))))"
(* and  progress: "\<And>s. progress (c s)" \<comment> \<open>This is actually not really needed, because ''call'' needs to decrease!
                                         As an improvement one could not look at ''call'' and ''if'' costs, by setting them to \<infinity>, then progress is needed again.\<close>
*)
 and  i: "I s0"                                       
shows gwp_monadic_WHILEIET: "Some t \<le> gwp (monadic_WHILEIET I E bm c s0) Q"
  apply(rule neueWhile_rule''_real)
     apply (fact wf)
    unfolding loopbody_cond_def loopexit_cond_def neueWhile_rewrite
    apply(rule step[unfolded loop_body_condition_def loop_exit_condition_def])
    apply simp
  apply (fact i)
  done
  




thm RECT_mono 

lemma ASSERT_acost_refine:
  shows "(Q \<Longrightarrow> P) \<Longrightarrow> (ASSERT P::(_,(_,enat)acost)nrest) \<le> ASSERT Q"
  by(auto simp: pw_acost_le_iff refine_pw_simps)

lemma WHILEIT_weaken:
  fixes f :: "'c \<Rightarrow> ('c, (_,enat) acost) nrest"
  assumes IW: "\<And>x. I x \<Longrightarrow> I' x"
  shows "monadic_WHILEIT I' b f x \<le> monadic_WHILEIT I b f x"
  unfolding monadic_WHILEIT_def
  apply(rule bindT_acost_mono') apply simp
  apply (rule RECT_mono) apply refine_mono
  apply(rule bindT_acost_mono')
  by (auto intro!: ASSERT_acost_refine IW) 

lemma WHILEIET_weaken:
  fixes f :: "'c \<Rightarrow> ('c, (_,enat) acost) nrest"
  assumes IW: "\<And>x. I x \<Longrightarrow> I' x"
  shows "monadic_WHILEIET I' E b f x \<le> monadic_WHILEIET I E b f x"
  apply(subst monadic_WHILEIET_def)
  apply(subst monadic_WHILEIET_def)
  apply(rule WHILEIT_weaken[OF IW])
  .




lemma monadic_WHILEIT_unfold:
  fixes c :: "'b \<Rightarrow> ('b, (char list, enat) acost) nrest"
  shows "monadic_WHILEIT I bm c s
      = do {
      _ \<leftarrow> SPECT [() \<mapsto> cost ''call'' 1];
      _ \<leftarrow> ASSERT (I s);
      bv \<leftarrow> bm s;
      MIf bv (c s \<bind> monadic_WHILEIT I bm c) (RETURNT s)
    }"  
  unfolding monadic_WHILEIT_def
  apply(subst RECT_unfold) apply refine_mono
  apply(fold monadic_WHILEIT_def)
  by simp
   


lemma loop_body_condition_weaken: 
  "A \<le> A' \<Longrightarrow> loop_body_condition A B C \<le> loop_body_condition A' B C"
  unfolding loop_body_condition_def by auto

lemma
  EX_inresT_I:
  fixes P :: "_ \<Rightarrow> (_, enat) acost option"
  shows "M = SPECT P \<Longrightarrow> P x = Some t \<Longrightarrow> (\<exists>b t. inresT (project_acost b M) x t)"
  apply (auto simp: project_acost_SPECT)  
  by (metis zero_enat_def zero_le)  


thm neueWhile_rule''_real[unfolded loopbody_cond_def loopexit_cond_def]



lemma
  fixes I :: "_ \<Rightarrow> ('a,nat) acost option"
  assumes "whileT b c s0 = r"
  assumes wfR: "\<And>s. wfR2 (case I s of None \<Rightarrow> 0 | Some t \<Rightarrow> t)" 
  assumes progress: "\<And>s. progress (c s)" 
  assumes IS: "\<And>s t t'. lift_acost_option (I s) = Some t \<Longrightarrow>  b s  \<Longrightarrow> 
           gwp (c s) (\<lambda>s'. mm3 t (lift_acost_option (I s')) ) \<ge> Some 0"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes t0[simp]: "lift_acost_option (I s0) = Some (lift_acost t0)" 
    (*  assumes wf: "wf R" *)                         
  shows whileT_rule''': "gwp r (\<lambda>x. if b x then None else mm3 (lift_acost t0) (lift_acost_option (I x))) \<ge> Some 0"  
  apply(rule gwp_conseq4)
   apply(rule gwp_whileT_rule_wf[where I="\<lambda>s. mm3 (lift_acost t0) (lift_acost_option (I s))"
        and R="ffSacost (\<lambda>s. case (I s) of None \<Rightarrow> 0 | Some t \<Rightarrow> t )", OF assms(1)]) 
   apply auto       
  subgoal for s t'
    apply(cases "I s"; simp) 
    subgoal for ti
      using IS[of s "lift_acost ti"]
      apply (cases "c s"; simp)
      subgoal for M
        using progress[of s, THEN progressD, of M]
        apply(auto simp: gwp_pw ffSacost_def) 
        apply(auto simp: mm3_Some_conv minus_p_m_alt minus_cost_def mm3_def split: option.splits if_splits)
        subgoal 
          by fastforce 
        subgoal premises prems for x x2 x2b
          using prems(3)[rule_format, of x] prems(11) apply auto
          subgoal premises p2 for y using   p2(2)[rule_format, of y, simplified] p2(1,3) prems(1,2) prems(4-11)  
            apply auto subgoal premises p3 using p3(13)[rule_format, of x2b] apply simp
              using prems(5)[of x] prems(11) apply auto using p3(12) apply(intro the_acost_less_aux[where D=x2b]) by auto
            done
          done
        subgoal premises prems for x x2 x2b
          using prems(3)[rule_format, of x, simplified, THEN conjunct2, rule_format, of x2, rule_format] prems(1,2,4) prems(6-11)
          apply auto subgoal premises p2 using p2(1-10) p2(11)[rule_format, of x2b, simplified]
            apply(cases x2b; cases ti; cases x2; cases t0)
            apply (auto simp add: lift_acost_def less_eq_acost_def zero_acost_def le_fun_def minus_acost_alt split: nrest.splits)
            subgoal premises p3 for xa xaa xb xc xd 
              using p3(1-5)[rule_format, of xd]
                    p3(6-15) 
            using enat_ile by fastforce
          done
        done
          subgoal
            by (metis drm_class.diff_right_mono dual_order.trans option.discI)
        subgoal 
          using dual_order.trans by blast 
        done
      done
    done
    apply(rule mm3_Some_is_Some_enat[OF lift_acost_option_some_finite[OF t0]])
  subgoal apply(rule wf_ffSacost) using wfR unfolding wfR2_def  by simp
  subgoal  
    by (simp add: needname_minus_absorb)  
  done

thm whileT_rule'''[OF refl, where I="(\<lambda>e. if I e
                then Some (E e) else None)"]

lemma zz: "(if b then Some A else None) = Some t \<longleftrightarrow> (b \<and> t=A)" by auto
lemma aa: "(case if I s then Some (E s) else None of None \<Rightarrow> 0 | Some t \<Rightarrow> t)
          =   (if I s then E s else 0)" by auto
lemma  whileIET_rule:
  fixes E :: "_ \<Rightarrow> (_, nat) acost"
  assumes "\<And>s. wfR2 (if I s then E s else 0)" and
    "(\<And>s t t'.
    (if I s then Some (lift_acost (E s)) else None) = Some t \<Longrightarrow>
    b s \<Longrightarrow> Some 0 \<le> gwp (C s) (\<lambda>s'. mm3 t (lift_acost_option (if I s' then Some (E s') else None))))" 
  "\<And>s. progress (C s)"
  "I s0" 
shows "Some 0 \<le> gwp (whileIET I E b C s0) (\<lambda>x. if b x then None else mm3 (lift_acost (E s0)) (lift_acost_option (if I x then Some (E x) else None)))"
  unfolding whileIET_def  
  apply(rule whileT_rule'''[OF refl, where I="(\<lambda>e. if I e
                then Some (E e) else None)"])
  subgoal using assms(1) unfolding aa .  
  subgoal by fact
  using assms unfolding lift_acost_def by (auto simp: zz split: option.splits if_splits ) 

lemma  whileIET_rule':
  fixes E
  assumes  "\<And>s. wfR2 (if I s then E s else 0)" and
    "(\<And>s t t'. I s \<Longrightarrow>  b s \<Longrightarrow> Some 0 \<le> gwp (C s) (\<lambda>s'. mm3 (lift_acost (E s)) (lift_acost_option (if I s' then Some (E s') else None))))" 
  "\<And>s. progress (C s)"
  "I s0" 
shows "Some 0 \<le> gwp (whileIET I E b C s0) (\<lambda>x. if b x then None else mm3 (lift_acost (E s0)) (lift_acost_option (if I x then Some (E x) else None)))" 
  apply(rule whileIET_rule)
     apply fact   
  apply(simp only: zz)  using assms by auto  

lemma auxx: "(if b then Some (lift_acost (x)) else None)
          = (lift_acost_option (if b then Some (x) else None))"
  apply(cases "b") by auto 

lemma While[vcg_rules']:   
  assumes  "\<And>s. wfR2 (if I s then E s else 0)"                                               
  assumes  "I s0"  "(\<And>s. I s \<Longrightarrow> b s \<Longrightarrow> Some 0 \<le> gwp (C s) (\<lambda>s'. mm3 (lift_acost (E s)) 
                                                        (if I s' then Some (lift_acost (E s')) else None)))"
     "(\<And>s. progress (C s))"
     "(\<And>x. \<not> b x \<Longrightarrow>  I x \<Longrightarrow>  (E x) \<le> (E s0) \<Longrightarrow>   Some (t + lift_acost ((E s0) - E x)) \<le> Q x)"
   shows   "Some t \<le> gwp (whileIET I E b C s0) Q"
  apply(rule whileIET_rule'[THEN gwp_conseq4])
  subgoal using assms(1) by simp
  subgoal using assms(3) unfolding auxx by simp
  subgoal using assms(4) by simp
  subgoal using assms(2) by simp
  subgoal for x using assms(5) apply(cases "I x") apply (auto simp:split: if_splits)    
    apply(simp add: mm3_acost_Some_conv)
    subgoal premises prems using prems(1)[of x] prems(2-4) apply auto  
      by (simp add: needname_minus_absorb)  
    done   
  done



subsection \<open>inres - a monadic operation has a certain result\<close>

definition "inres M x = (\<exists>m t. M = SPECT m \<and> m x = Some t)"

lemma inres_alt: "inres m x \<longleftrightarrow> (\<exists>P. m = SPECT P \<and> P x \<noteq> None)"
  unfolding inres_def by auto

lemma inres_consume_conv: "inres (NREST.consume m t) x = inres m x"
  by(auto simp: inres_def consume_def split: nrest.splits)

lemma inres_if_inresT:
  "inresT M x t \<Longrightarrow> nofailT M \<Longrightarrow> inres M x"
  unfolding inresT_def inres_def nofailT_def apply (cases M) apply (auto simp: le_fun_def)
  by (metis (full_types) le_some_optE)

lemma inres_if_inresT_acost:
  "inresT (project_acost b M) x t \<Longrightarrow> nofailT M \<Longrightarrow> inres M x"
  unfolding inresT_def inres_def nofailT_def apply (cases M) apply (auto simp: le_fun_def project_acost_SPECT)
  subgoal premises p for m
    using p(1)[rule_format, of x] apply simp
    apply(cases "m x") by auto
  done

lemma nofailT_bindT:
  "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x. inres M x \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def nofailT_def inres_def
  apply(cases M) by (auto simp: nrest_Sup_FAILT split: nrest.splits)

lemma inres_SPECT: "inres (SPECT [x\<mapsto>t]) y \<longleftrightarrow> x = y"
  unfolding inres_def by auto 


lemma inres_bindT_SPECT_one[simp]: "inres (do {l' \<leftarrow> SPECT [x \<mapsto> t]; M l'}) r \<longleftrightarrow> inres (M x) r"
  by(auto simp: bindT_def inres_def split: nrest.splits)

declare inres_SPECT[simp]




lemma inres_consumea[simp]: "inres (do {_ \<leftarrow> consumea t; M}) r \<longleftrightarrow> inres M r"
  by (cases M) (auto simp: bindT_def inres_def consumea_def)

lemma inres_RETURNT[simp]: "inres (RETURNT x) y \<longleftrightarrow> (x=y)"
  by(auto simp: inres_def )

lemma inres_bind_ASSERT[simp]: "inres (do { ASSERT \<phi>; N }) r \<longleftrightarrow> (\<phi> \<and> inres N r)"
  by(auto simp: inres_def ASSERT_def iASSERT_def)

declare inres_consume_conv[simp]

lemma inres_bindT_consume_conv[simp]:
  fixes t :: "(_,enat) acost"
  shows "inres (do { x  \<leftarrow> NREST.consume m t; M x}) r = inres (do { x \<leftarrow> m; M x }) r"
  unfolding consume_alt2 by simp

lemma
  nofailT_bindT_SPEC_iff:
  shows "nofailT (do { _ \<leftarrow> SPECT [x\<mapsto>t]; M}) \<longleftrightarrow> nofailT M"
  by (auto simp add: nofailT_bindT inres_SPECT) 



lemma gwp_mono_alt:
  fixes q q' :: "'c \<Rightarrow> 'b::{complete_lattice,minus,ord,top,drm,monoid_add,needname_zero} option"
  assumes "\<And>x. inres m x \<Longrightarrow> q x \<le> q' x"
  shows "gwp m q \<le> gwp m q'"
  apply(rule gwp_mono)
  apply(rule assms) by(simp add: inres_alt)



subsection \<open>Rules for gwpn\<close>


lemma gwpn_specifies_I: "Some 0 \<le> gwp\<^sub>n m Q  \<Longrightarrow> m \<le>\<^sub>n SPECT Q"
  unfolding gwp\<^sub>n_def le_or_fail_def by (auto intro: gwp_specifies_I) 

lemma gwpn_RETURNT_I:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option"
  shows "Some t \<le> Q x \<Longrightarrow> Some t \<le> gwp\<^sub>n (RETURNT x) Q"
  unfolding gwp\<^sub>n_def  by(auto intro: gwp_RETURNT_I)

lemma gwpn_FAIL[simp]: "gwp\<^sub>n FAILT Q = Some top"
  by(auto simp: gwp\<^sub>n_def)

lemma gwpn_ASSERT_I: 
  fixes Q :: "unit \<Rightarrow> ('b::{complete_lattice,monoid_add,drm,needname_zero}) option"
  shows "(P \<Longrightarrow> Some t \<le> Q ()) \<Longrightarrow> Some t \<le> gwp\<^sub>n (ASSERT P) Q"
  apply(cases P)
  by(auto intro: gwpn_RETURNT_I)


lemma gwpn_ASSERT_bind_I:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option"
  shows "(\<Phi> \<Longrightarrow> Some t \<le> gwp\<^sub>n M Q) \<Longrightarrow> Some t \<le> gwp\<^sub>n (do { ASSERT \<Phi>; M}) Q"
  apply(cases \<Phi>)
  by(auto intro: gwpn_RETURNT_I)

thm gwp_SPECT_I

lemma gwpn_SPECT_I:
  fixes Q :: "_ \<Rightarrow> ('b::{needname_zero}) option" and t
  assumes "(Some (t' + t ) \<le> Q x)"
  shows "Some t' \<le> gwp\<^sub>n (SPECT [ x \<mapsto> t]) Q"
  unfolding gwp\<^sub>n_def using assms by (auto intro: gwp_SPECT_I)


lemma gwpn_bindT_I:
  fixes M :: "(_, (_,enat) acost) nrest"
  shows "Some t \<le> gwp\<^sub>n M (\<lambda>y. gwp\<^sub>n (f y) Q) \<Longrightarrow> Some t \<le> gwp\<^sub>n (M \<bind> f) Q"
  unfolding gwp\<^sub>n_def apply (auto intro!: gwp_bindT_I simp: g_pw_bindT_nofailT)
  apply(rule order.trans) apply simp
  apply(rule gwp_mono) apply auto 
  subgoal  premises prems for m x t using prems(2)[rule_format, where x=x] prems(5) prems(3) prems(4)
    apply(auto simp: inresT_def project_acost_def)
    unfolding inresT_def apply (auto simp: le_fun_def)  
    by (smt less_eq_option_None_code less_eq_option_Some option.simps(5) zero_enat_def zero_le)
  done


lemma gwpn_MIf_I:
  fixes c1 :: "(_,(_,enat) acost) nrest"
  assumes "(b \<Longrightarrow> Some (cost ''if'' 1 + t) \<le> gwp\<^sub>n c1 Q)"
    "(\<not>b \<Longrightarrow> Some (cost ''if'' 1 + t) \<le> gwp\<^sub>n c2 Q)"
  shows "Some t \<le> gwp\<^sub>n (MIf b c1 c2) Q"
  using assms 
  unfolding gwp\<^sub>n_def
  apply auto
  apply(rule gwp_MIf_I)
  by(auto simp: MIf_def nofailT_consume split: if_splits)


lemma gwpn_consume:
  fixes m :: "(_,(_,enat) acost) nrest"
  shows "Some (T+t) \<le> gwp\<^sub>n m Q \<Longrightarrow> Some t \<le> gwp\<^sub>n (consume m T) Q"
  unfolding gwp\<^sub>n_def
  apply auto apply(rule gwp_consume) apply (cases m) by auto


lemma gwpn_conseq:
  fixes Q :: "unit \<Rightarrow> ('b::{complete_lattice,monoid_add,drm,needname_zero}) option"
  assumes 
    "gwp\<^sub>n f Q' \<ge> Some t"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')" 
  shows "gwp\<^sub>n f Q \<ge> Some t"
  using assms
  unfolding gwp\<^sub>n_def apply auto
  apply(rule gwp_conseq[where Q'="Q'"]) by auto


lemma gwpn_monadic_WHILE_rule''_aux1:
  fixes T :: "(_,enat) acost"
  shows "gwp\<^sub>n (SPECT [x\<mapsto>T]) Q = Some t \<Longrightarrow> Q x = Some (T+t)"
  unfolding gwp\<^sub>n_def gwp_def minus_p_m_def minus_potential_def apply simp
  apply(auto split: if_splits)
  apply(cases "Q x") apply simp apply auto 
  apply(auto split: if_splits)
  subgoal for a
  unfolding Inf_option_Some_aux1  apply simp apply(cases T; cases t; cases a)
    unfolding less_eq_acost_def minus_acost_alt plus_acost_alt apply simp
      apply(rule ext)  
    by (metis add_diff_assoc_enat add_diff_cancel_enat enat_ord_simps(4) leD plus_eq_infty_iff_enat) 
  done



lemma
  fixes s0 :: 'a and I :: "'a \<Rightarrow> bool" and E :: "'a \<Rightarrow> (string, nat) acost" and t :: "(string, enat) acost"
    and Q :: "'a \<Rightarrow>  (string, enat) acost option"
  assumes wf: "\<And>s. wfR2 (if I s then E s else 0)"
  assumes
  step: "(\<And>s. I s \<Longrightarrow> Some 0 \<le> gwp\<^sub>n (bm s) (\<lambda>b. gwp\<^sub>n (SPECT [()\<mapsto> (cost ''if'' 1)])
       (\<lambda>_. if b then gwp\<^sub>n (do { consume (c s) (cost ''call'' 1)  })
                             (\<lambda>s'. loop_body_condition (I s') (E s') (E s) )
                 else loop_exit_condition (Q s) t (E s) (E s0))))"
 and  i: "I s0"                                       
shows gwpn_monadic_WHILEIET: "Some t \<le> gwp\<^sub>n (monadic_WHILEIET I E bm c s0) Q"
  unfolding gwp\<^sub>n_def apply clarsimp
  subgoal premises nofailT_WHILE
    apply(rule order.trans[OF _ ])
     defer
     apply(rule gwp_antimono)
     apply(rule WHILEIET_weaken[of "\<lambda>s. I s \<and> nofailT (monadic_WHILEIET I E bm c s)"])
     apply simp  
    apply(rule gwp_monadic_WHILEIET)
    subgoal  unfolding wfR2_def apply - apply(rule finite_subset[OF _ wf[unfolded wfR2_def]])
      by (auto simp: the_acost_zero_app) 
    subgoal for s 
      unfolding monadic_WHILEIET_def 
      apply(rule order.trans)
       apply(rule step[of s])
       apply simp
      apply(subst gwp\<^sub>n_def)
      apply(subst (asm) monadic_WHILEIT_unfold)  
      apply auto
      subgoal
        apply(rule gwp_mono_alt)
        apply(subst gwp\<^sub>n_def)        
        apply auto
        apply(rule gwp_mono_alt)
        apply(subst gwp\<^sub>n_def)
        apply (auto)
        subgoal                    
          by (auto simp add: nofailT_bindT inres_SPECT MIf_def nofailT_consume inres_consume_conv
                  intro!: gwp_mono_alt loop_body_condition_weaken split: if_splits) 
        subgoal     
          by (auto simp: nofailT_bindT inres_SPECT MIf_def nofailT_consume)  
        done
      subgoal   
        by (auto simp: nofailT_bindT inres_SPECT MIf_def nofailT_consume)  
      done
    subgoal using i nofailT_WHILE by simp
    done
  done


end