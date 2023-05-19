\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
\<^marker>\<open>contributor "Peter Lammich"\<close>
section \<open>Currency Refinement\<close>
theory Time_Refinement
imports NREST NREST_Type_Classes
begin

paragraph \<open>Summary\<close>
text \<open>This theory introduces currency refinement.\<close>

subsection "time refine" 

(* mult_zero for wfR_finite_mult_left *)
definition timerefine ::"('b \<Rightarrow> ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             \<Rightarrow> ('a, ('b,'d) acost) nrest \<Rightarrow> ('a, ('c,'d) acost) nrest" ("\<Down>\<^sub>C") 
  where "\<Down>\<^sub>C R m = (case m of FAILi \<Rightarrow> FAILi |
                REST M \<Rightarrow> REST (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc)))))"

lemma timerefine_alt3:
  assumes "TR =( \<lambda>cm.  (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc))))"
  shows 
 "\<Down>\<^sub>C R m = (case m of FAILi \<Rightarrow> FAILi |
                REST M \<Rightarrow> REST (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (TR cm) ))"
  unfolding assms unfolding timerefine_def by simp

definition "timerefine' TR m = (case m of FAILi \<Rightarrow> FAILi |
                REST M \<Rightarrow> REST (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (TR cm) ))"

lemma timerefine_alt4:
  fixes R
  defines "TR \<equiv> ( \<lambda>cm.  (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc))))"
  shows "\<Down>\<^sub>C R m = timerefine' TR m"
   unfolding timerefine_def timerefine'_def
  unfolding assms by simp



definition timerefineF ::"('b \<Rightarrow> ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             \<Rightarrow> ('a \<Rightarrow> ('b,'d) acost option) \<Rightarrow> ('a \<Rightarrow> ('c,'d) acost option)"
  where "timerefineF R M = (\<lambda>r. case M r of None \<Rightarrow> None |
                  Some cm \<Rightarrow> Some (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc))))"



definition timerefineA ::"('b \<Rightarrow> ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost)
                             \<Rightarrow> ( ('b,'d) acost) \<Rightarrow> ( ('c,'d) acost)"
  where "timerefineA R cm =  (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc)))"


lemma timerefineA_0[simp]: "timerefineA r 0 = 0"
  by(auto simp: timerefineA_def zero_acost_def)

lemma timerefine_alt: "\<Down>\<^sub>C R m = case_nrest FAILi (\<lambda>M. SPECT (timerefineF R M)) m"
  unfolding timerefine_def timerefineF_def ..

lemma timerefine_SPECT: "\<Down>\<^sub>C R (SPECT Q) = SPECT (timerefineF R Q)" 
  unfolding timerefine_alt by simp



lemma SPEC_timerefine_conv:
  "\<Down>\<^sub>C R (SPEC A B') = SPEC A (\<lambda>x. timerefineA R (B' x))"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT 
  apply auto
  unfolding timerefineF_def timerefineA_def
  by auto



lemma timerefineA_upd_aux: "(if a = m then x else (0::enat)) * b = (if a = m then x * b else 0)"
  by auto




lemma timerefineA_cost_apply: "timerefineA TR (cost n (t::enat)) = acostC (\<lambda>x. t * the_acost (TR n) x)"
  unfolding timerefineA_def cost_def zero_acost_def
  apply simp
  apply(subst timerefineA_upd_aux)
  apply(subst Sum_any.delta) by simp 


lemma timerefineA_update_apply_same_cost': 
  "timerefineA (F(n := y)) (cost n (t::enat)) = t *m y"
  by (auto simp: costmult_def timerefineA_def cost_def zero_acost_def timerefineA_upd_aux ) 

lemma timerefineA_cost_apply_costmult: "timerefineA TR (cost n (t::enat)) = t *m (TR n)"
  by (simp add: costmult_def timerefineA_cost_apply)  


lemma timerefineA_update_apply_same_cost: 
  "timerefineA (F(n := y)) (cost n (t::enat)) = acostC (\<lambda>x. t * the_acost y x)"
  by (auto simp: timerefineA_def cost_def zero_acost_def timerefineA_upd_aux ) 



lemma timerefineA_cost: "timerefineA TR (cost n (1::enat)) = TR n"
  unfolding timerefineA_def cost_def zero_acost_def
  apply simp
  apply(subst timerefineA_upd_aux)
  apply(subst Sum_any.delta) by simp 


lemma timerefineA_update_cost[simp]: 
  "n\<noteq>m \<Longrightarrow> timerefineA (F(n := y)) (cost m (t::enat)) = timerefineA F (cost m t)"
  by (auto simp: timerefineA_def cost_def zero_acost_def timerefineA_upd_aux ) 

lemma timerefineA_upd:
  fixes R :: "'b \<Rightarrow> ('c, enat) acost"
  shows "timerefineA (R(n:=y)) (cost m x) = (if n=m then acostC (\<lambda>z. x * the_acost y z) else timerefineA R (cost m x))"
  unfolding timerefineA_def
  by (auto simp: cost_def zero_acost_def timerefineA_upd_aux)


definition wfn :: "('a, ('c,'d::{complete_lattice,comm_monoid_add,times,mult_zero}) acost) nrest \<Rightarrow> bool" where
  "wfn m = (case m of FAILi \<Rightarrow> True |
                REST M \<Rightarrow> \<forall>r\<in>dom M. (case M r of None \<Rightarrow> True | Some cm \<Rightarrow> finite {x. the_acost cm x \<noteq> 0}))"

definition wfR :: "('b \<Rightarrow> ('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR R = (finite {(s,f). the_acost (R s) f \<noteq> 0})"


lemma wfR_sup:
  fixes A :: "('b \<Rightarrow> ('c, enat) acost)"
  shows "wfR A \<Longrightarrow> wfR B \<Longrightarrow> wfR (sup A B)"
  unfolding wfR_def sup_fun_def sup_acost_def sup_enat_def
  apply(rule finite_subset[where B="{(s, f). the_acost (A s) f \<noteq> 0}\<union>{(s, f). the_acost (B s) f \<noteq> 0}"])
  by auto

(* I think this is better. It captures "finitely branching" *)
definition wfR' :: "('b \<Rightarrow> ('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR' R = (\<forall>s. finite {f. the_acost (R s) f \<noteq> 0})"

definition wfR'' :: "('b \<Rightarrow> ('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR'' R = (\<forall>f. finite {s. the_acost (R s) f \<noteq> 0})"


lemma wfR''_upd[intro]: "wfR'' F \<Longrightarrow> wfR'' (F(x:=y))"
  unfolding wfR''_def
  apply auto
  subgoal for f
    apply(rule finite_subset[where B="{s. the_acost (F s) f \<noteq> 0} \<union> {x}"])
    by auto
  done



lemma "wfR R \<Longrightarrow> wfR'' R"
  unfolding wfR_def wfR''_def apply safe
  subgoal for f
    apply(rule finite_cartesian_productD1[where B="{f}"])
     apply(rule finite_subset[rotated]) by auto
  done

lemma "wfR R \<Longrightarrow> wfR' R"
  unfolding wfR_def wfR'_def apply safe
  subgoal for s
    apply(rule finite_cartesian_productD2[where A="{s}"])
     apply(rule finite_subset) by auto
  done

(* TODO: refactor the next two lemmas, they essentially do the same *)
lemma timerefineA_propagate:
  assumes "wfR'' E"
  fixes a b :: "('a, enat) acost"
  shows "timerefineA E (a + b) = timerefineA E a + timerefineA E b"
  unfolding timerefineA_def
  apply(auto simp: timerefine_def consume_def timerefineA_def split: nrest.splits option.splits intro!: ext)
  subgoal for  cc    
  apply(cases a, cases b) 
    unfolding plus_acost_alt apply simp
    unfolding  ring_distribs(2)
    apply(subst Sum_any.distrib)
    subgoal apply(rule finite_subset[OF _ assms[unfolded wfR''_def, rule_format]]) by auto
    subgoal apply(rule finite_subset[OF _ assms[unfolded wfR''_def, rule_format]]) by auto
    apply simp
    done
  done

lemma timerefine_consume:
  assumes "wfR'' E"
  shows "\<Down>\<^sub>C E (consume M t) = consume (\<Down>\<^sub>C E (M:: (_, (_, enat) acost) nrest)) (timerefineA E t)"
  apply(auto simp: timerefine_def consume_def timerefineA_def split: nrest.splits option.splits intro!: ext)
  subgoal for x2 r x2a cc    
  apply(cases t, cases x2a) 
    unfolding plus_acost_alt apply simp
    unfolding  ring_distribs(2)
    apply(subst Sum_any.distrib)
    subgoal apply(rule finite_subset[OF _ assms[unfolded wfR''_def, rule_format]]) by auto
    subgoal apply(rule finite_subset[OF _ assms[unfolded wfR''_def, rule_format]]) by auto
    apply simp
    done
  done

lemma assumes "wfn m"
  assumes "m = SPECT M" "M r = Some cm"
  shows "finite {ac. the_acost cm ac * the_acost (R ac) cc \<noteq> 0}"
proof -
  from assms have "finite {x. the_acost cm x \<noteq> 0}" unfolding wfn_def by force
  show ?thesis
    apply(rule finite_subset[where B="{ac. the_acost cm ac \<noteq> 0}"])
    subgoal by auto
    subgoal apply fact done
    done
qed 


lemma "wfR'' (\<lambda>x. acostC (\<lambda>y. if x = y then 1 else 0))"
  unfolding wfR''_def 
  by auto

lemma wfR''_finite_mult_left:
  assumes "wfR'' R"
  shows "finite {ac. the_acost cm ac * the_acost (R ac) cc \<noteq> 0}"
proof - 
  from assms have "finite {s. the_acost (R s) cc \<noteq> 0}" unfolding wfR''_def by auto
  show ?thesis
    apply(rule finite_subset[where B="{ac. the_acost (R ac) cc \<noteq> 0}"])
    subgoal by auto
    subgoal apply fact done
    done
qed 



definition wfR2 :: "(('c, _::mult_zero) acost) \<Rightarrow> bool" where
  "wfR2 R = (finite {f. the_acost R f \<noteq> 0})"


lemma wfR2_If_if_wfR2: "(I \<Longrightarrow> wfR2 f) \<Longrightarrow> wfR2 (if I then f else 0)"
  unfolding wfR2_def apply(cases I) by (auto simp: zero_acost_def)


lemma wfR2_enum:
  fixes R :: "(('c::enum, _) acost)"
  shows "wfR2 R"
  unfolding wfR2_def by simp

lemma wfR_fst: "\<And>y. wfR R \<Longrightarrow> finite {x. the_acost (R x) y \<noteq> 0}"
  unfolding wfR_def apply(rule finite_subset[where B="fst ` {(s, f). the_acost (R s) f \<noteq> 0}"])
  subgoal by auto
  apply(rule finite_imageI) by simp

lemma wfR_snd: "\<And>s. wfR R \<Longrightarrow> finite {y. the_acost (R s) y \<noteq> 0}"
  unfolding wfR_def apply(rule finite_subset[where B="snd ` {(s, f). the_acost (R s) f \<noteq> 0}"])
  subgoal by auto
  apply(rule finite_imageI) by simp

(*
lemma finite_same_support:
  "\<And>f. finite {(x,y). R x y \<noteq> 0} \<Longrightarrow> (\<And>x.  f (R x) = 0 \<longleftrightarrow> R x = 0) \<Longrightarrow> finite {x. f (R x) \<noteq> 0}"
  oops*)

lemma 
  finite_wfR_middle_mult:
  fixes R1 :: "_ \<Rightarrow> ('a, 'b::{semiring_no_zero_divisors}) acost"
  assumes "wfR R1" "wfR R2"
  shows "finite {a. the_acost (R2 x) a * the_acost (R1 a) y \<noteq> 0}"
proof -
  have "{a. the_acost (R2 x) a * the_acost (R1 a) y \<noteq> 0} = {a. the_acost (R2 x) a \<noteq> 0 \<and> the_acost (R1 a) y \<noteq> 0}" by simp
  also have "\<dots> \<subseteq> fst ` {(a,a)| a. the_acost (R2 x) a \<noteq> 0 \<and> the_acost (R1 a) y \<noteq> 0}" by auto
  also have "\<dots> \<subseteq> fst ` ({a. the_acost (R2 x) a \<noteq> 0} \<times> {a. the_acost (R1 a) y \<noteq> 0})"
    apply(rule image_mono) by auto
  finally
  show ?thesis apply(rule finite_subset)
    apply(rule finite_imageI)
    apply(rule finite_cartesian_product)
    apply(rule wfR_snd[where R=R2]) apply fact
    apply(rule wfR_fst) by fact
qed

lemma wfR_finite_mult_left2:
  fixes R2 :: "('b \<Rightarrow> ('c, 'd::mult_zero) acost)"
  assumes "wfR'' R2"
  shows "finite {a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0}"
proof -

  have "{a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0} \<subseteq> {a. the_acost (R2 a) ac \<noteq> 0}"
    apply(cases Mc) by (auto simp: zero_acost_def)
  then
  show ?thesis
    apply(rule finite_subset)
    using assms unfolding wfR''_def by simp
qed


lemma wfR_finite_mult_left:
  fixes R2 :: "('b \<Rightarrow> ('c, 'd::mult_zero) acost)"
  assumes "wfR R2"
  shows "finite {a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0}"
proof -

  have "{a. the_acost Mc a * the_acost (R2 a) ac \<noteq> 0} \<subseteq> {a. the_acost (R2 a) ac \<noteq> 0}"
    apply(cases Mc) by (auto simp: zero_acost_def)
  then
  show ?thesis
    apply(rule finite_subset)
    apply(rule wfR_fst) by fact
qed


lemma 
  wfR_finite_crossprod:
  assumes "wfR R2"
  shows "finite ({a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0})"
proof -
  have i: "{a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<subseteq> fst ` ({(a,b).  the_acost (R2 a) b \<noteq> 0} \<inter> {(a,b). the_acost (R1 b) cc \<noteq> 0})"
    apply safe 
    by (metis (mono_tags, lifting) Int_iff arith_simps(62) arith_simps(63) case_prodI image_eqI mem_Collect_eq prod.sel(1))  
  have ii: "{b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<subseteq> snd ` ({(a,b).  the_acost (R2 a) b \<noteq> 0} \<inter> {(a,b). the_acost (R1 b) cc \<noteq> 0})"
    apply safe  
    by (metis (mono_tags, lifting) Int_iff arith_simps(62) arith_simps(63) case_prodI image_eqI mem_Collect_eq prod.sel(2))  
  

  show ?thesis 
    apply(rule finite_cartesian_product)
    subgoal  apply(rule finite_subset[OF i]) apply(rule finite_imageI)
      apply(rule finite_Int)   using assms wfR_def by auto
    subgoal  apply(rule finite_subset[OF ii]) apply(rule finite_imageI)
      apply(rule finite_Int)   using assms wfR_def by auto
    done    
qed


lemma wfR_finite_Sum_any: 
  assumes *: "wfR R"
  shows "finite {x. ((Sum_any (\<lambda>ac. (the_acost Mc ac * (the_acost (R ac) x)))) \<noteq> 0)}"
proof - 
  {fix x
    have "((Sum_any (\<lambda>ac. ((the_acost Mc ac) * (the_acost (R ac) x)))) \<noteq> 0)
      \<Longrightarrow> \<exists>ac. (the_acost Mc ac) * (the_acost (R ac) x) \<noteq> 0"
      using Sum_any.not_neutral_obtains_not_neutral by blast 
  } then 
  have "{x. ((Sum_any (\<lambda>ac. ((the_acost Mc ac) * (the_acost (R ac) x)))) \<noteq> 0)}
          \<subseteq> {x. \<exists>ac. ((the_acost Mc ac) * (the_acost (R ac) x)) \<noteq> 0}" by blast
  also have "\<dots> \<subseteq> snd ` {(ac,x). ((the_acost Mc ac) * (the_acost (R ac) x)) \<noteq> 0}" by auto 
  also have "\<dots> \<subseteq> snd ` {(ac,x).  (the_acost (R ac) x) \<noteq> 0}" by auto

  finally  show ?thesis 
    apply(rule finite_subset )
    apply(rule finite_imageI) using * unfolding wfR_def by auto
qed 


(*
lemma assumes "R' \<le> R" "wfR R" shows "wfR R'"
proof -                                    
  from assms(1) have *: "\<And> a b. the_acost (R' a) b\<le> the_acost (R a) b"
  unfolding less_eq_acost_def le_fun_def   by auto
  {fix  a b have "the_acost (R a) b  = 0 \<Longrightarrow> the_acost (R' a) b = 0 "   
      using * [of a b] by (auto simp: zero_acost_def less_eq_acost_def)}
  note f=this
  show "wfR R'"
    using \<open>wfR R\<close> unfolding wfR_def apply(rule rev_finite_subset)
    apply safe using f by simp
qed
*)

lemma wfn_timerefine: "wfn m \<Longrightarrow> wfR R \<Longrightarrow> wfn (\<Down>\<^sub>C R m)"
proof -
  assume "wfR R"
  then show "wfn (\<Down>\<^sub>C R m)"
    unfolding wfn_def timerefine_def 
    apply(auto split: nrest.splits option.splits)
    apply(rule wfR_finite_Sum_any) by simp
qed


lemma [simp]: "\<Down>\<^sub>C R FAILT = FAILT" by(auto simp: timerefine_def)

definition pp where
  "pp R2 R1 = (\<lambda>a. acostC (\<lambda>c. Sum_any (%b. the_acost (R1 a) b * the_acost (R2 b) c  ) ))"



lemma pp_fun_upd: "pp A (B(a:=b))
          = (pp A B)(a:=timerefineA A b)"
  unfolding pp_def timerefineA_def
  apply(rule ext) by simp 


term case_nrest 
thm case_nrest_def
term map_nrest   

lemma timerefine_timerefineA:
  "\<Down>\<^sub>C R m =
         case_nrest FAILi 
            (\<lambda>M. REST (\<lambda>r. (case_option None
                                 (\<lambda>cm. Some (timerefineA R cm)) (M r)))) m"
  unfolding timerefine_def timerefineA_def by simp


lemma wfR''_ppI_aux: "(\<And>s. finite {b. f s b \<noteq> 0}) \<Longrightarrow> {s. Sum_any (f s) \<noteq> (0::enat)} = {s. (\<exists>b. f s b \<noteq> 0)}"
  apply auto  
  subgoal using Sum_any.not_neutral_obtains_not_neutral by blast
  subgoal  
    by (simp add: Sum_any.expand_set) 
  done

thm Sum_any.not_neutral_obtains_not_neutral

lemma wfR''_ppI_aux2: "(a::enat) * b \<noteq> 0 \<longleftrightarrow> a \<noteq> 0 \<and> b \<noteq> 0"
  by auto

lemma wfR''D: "wfR'' R \<Longrightarrow> finite {s. the_acost (R s) f \<noteq> 0}"
  by (auto simp: wfR''_def)

lemma 
  wfR_finite_crossprod2:
  fixes Mc :: "('a, enat) acost"
  assumes "wfR'' R1"  "wfR'' R2"
  shows "finite ({a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0})"
proof -

  have **: "{a. \<exists>b. the_acost Mc a \<noteq> 0 \<and> the_acost (R2 a) b \<noteq> 0 \<and> the_acost (R1 b) cc \<noteq> 0}
      \<subseteq> (\<Union>b\<in>{b. the_acost (R1 b) cc \<noteq> 0}. {a. the_acost Mc a \<noteq> 0 \<and> the_acost (R2 a) b \<noteq> 0 })"
    by auto 
  show ?thesis 
    apply(rule finite_cartesian_product)
    subgoal 
      apply(subst wfR''_ppI_aux2)
      apply(subst wfR''_ppI_aux2)
      apply(rule finite_subset[OF **])
      apply(rule finite_Union)
      subgoal apply(rule finite_imageI) using assms(1)[THEN wfR''D] by simp
      subgoal apply auto subgoal for b apply(rule finite_subset[where B="{s. the_acost (R2 s) b \<noteq> 0}"])
        using assms(2)[THEN wfR''D] by auto
      done
    done
    subgoal 
      apply(subst wfR''_ppI_aux2)
      apply(subst wfR''_ppI_aux2)   
      apply(rule finite_subset[where B="{b. the_acost (R1 b) cc \<noteq> 0}"])
      subgoal by auto
      subgoal using  assms(1)[THEN wfR''D] by simp 
      done
    done
  qed 

lemma timerefineA_iter2:
  fixes R1 :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R1" "wfR'' R2"
  shows "timerefineA R1 (timerefineA R2 c) =  timerefineA (pp R1 R2) c"
  unfolding timerefineA_def pp_def
  apply (auto simp: le_fun_def pp_def split: option.splits) apply (rule ext)
  apply(subst Sum_any_right_distrib)
  subgoal apply(rule wfR''_finite_mult_left[of R1]) using assms by simp_all
  subgoal for cc
    apply (subst Sum_any.swap[where C="{a. \<exists>b. the_acost c a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost c a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0}"])
    subgoal      
      apply(rule wfR_finite_crossprod2) using assms by auto
    subgoal by simp 
    apply(subst Sum_any_left_distrib)
    subgoal apply(rule wfR_finite_mult_left2) using assms by simp 
    apply(rule Sum_any.cong)
    by (meson mult.assoc)
  done 


lemma pp_assoc:
  fixes A :: "'d \<Rightarrow> ('b, enat) acost"
  assumes A: "wfR'' A"
  assumes B: "wfR'' B"
  shows "pp A (pp B C) = pp (pp A B) C"
  unfolding pp_def 
  apply(rule ext)
  apply simp
  apply(rule ext) 
  apply(subst Sum_any_left_distrib)
  subgoal for a c aa 
    apply(rule finite_subset[where B="{s. the_acost (B s) aa  \<noteq> 0}"])
    using assms(2)[THEN wfR''D] by auto 
  apply(subst Sum_any_right_distrib)
  subgoal for a c aa 
    apply(rule finite_subset[where B="{s. the_acost (A s) c  \<noteq> 0}"])
    using assms(1)[THEN wfR''D] by auto 
  subgoal for a c
    apply(subst Sum_any.swap)
      prefer 2 apply(rule subset_refl)
     apply(rule finite_cartesian_product)
    subgoal 
      apply(rule finite_subset[where B="{b. the_acost (A b) c \<noteq> 0}"])
      subgoal apply auto done
      using assms(1)[THEN wfR''D] by blast
    subgoal 
      apply(subst wfR''_ppI_aux2)
      apply(subst wfR''_ppI_aux2)
      apply(rule finite_subset[where B="(\<Union>b\<in>{b. the_acost (A b) c \<noteq> 0}. {d. the_acost (C a) d \<noteq> 0 \<and> the_acost (B d) b \<noteq> 0 })"])
      subgoal by auto
      apply(rule finite_Union)
      subgoal apply(rule finite_imageI) using assms(1)[THEN wfR''D] by simp
      subgoal apply auto subgoal for b apply(rule finite_subset[where B="{s. the_acost (B s) b \<noteq> 0}"])
        using assms(2)[THEN wfR''D] by auto 
      done
    done
  apply (simp add: mult.assoc)
  done
  done

subsubsection \<open>monotonicity lemmas\<close>

lemma Sum_any_mono:
  fixes f :: "('c \<Rightarrow> 'b::{nonneg,comm_monoid_add,order,ordered_comm_monoid_add})"
  assumes fg: "\<And>x. f x \<le> g x" (* can one relax that and say the norm is mono, for integer domains ? *)
    and finG: "finite {x. g x \<noteq> 0}"
shows "Sum_any f \<le> Sum_any g"
proof -
  have "{x. f x \<noteq> 0} \<subseteq> {x. g x \<noteq> 0}"
    apply auto
    subgoal for x using fg[of x] needname_nonneg[of " f x"] by auto 
    done
  with finG have "finite {x. f x \<noteq> 0}"  
    using finite_subset by blast   

  thm sum_mono sum_mono2
  thm sum_mono2
  have "sum f {x. f x \<noteq> 0} \<le> sum f {x. g x \<noteq> 0}"
    apply(rule sum_mono2) apply fact apply fact
    by simp
  also have "\<dots> \<le> sum g {x. g x \<noteq> 0}"
    apply(rule sum_mono) using fg by simp
  finally show ?thesis unfolding Sum_any.expand_set .
qed

lemma finite_support_mult:  
  fixes R1 :: "('a, 'b::{semiring_no_zero_divisors}) acost"
  assumes "finite {xa.  the_acost R1 xa \<noteq> 0}"
  and "finite {xa. the_acost R2 xa \<noteq> 0}"
shows "finite {xa. the_acost R2 xa * the_acost R1 xa \<noteq> 0}"
proof -
 
  have "{(xa,xa)|xa. the_acost R2 xa * the_acost R1 xa \<noteq> 0} = {(xa,xa)|xa. the_acost R2 xa \<noteq> 0 \<and> the_acost R1 xa \<noteq> 0}" by auto
  also have "\<dots> \<subseteq> {(xa,xb)|xa xb. the_acost R2 xa \<noteq> 0 \<and> the_acost R1 xb \<noteq> 0}" by auto
  also have "\<dots> = {xa. the_acost R2 xa \<noteq> 0} \<times> {xb. the_acost R1 xb \<noteq> 0}" by auto 
  finally have k: "{xa. the_acost R2 xa * the_acost R1 xa \<noteq> 0} \<subseteq> fst ` ({xa. the_acost R2 xa \<noteq> 0} \<times> {xb. the_acost R1 xb \<noteq> 0})" by blast

  show ?thesis
    apply(rule finite_subset[OF k])
    apply(rule finite_imageI) 
    apply(rule finite_cartesian_product) by fact+
qed

lemma timerefine_mono: 
  fixes R :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR R"
  shows "c\<le>c' \<Longrightarrow> \<Down>\<^sub>C R c \<le> \<Down>\<^sub>C R c'"
  apply(cases c) apply simp
  apply(cases c') apply (auto simp: less_eq_acost_def timerefine_def split: nrest.splits option.splits simp: le_fun_def)
  subgoal  by (metis le_some_optE) 
  proof (goal_cases)
    case (1 x2 x2a x x2b x2c xa)
    then have l: "\<And>ac. the_acost x2b ac \<le>  the_acost x2c ac"
      apply(cases x2b; cases x2c) unfolding less_eq_acost_def  
      apply auto
      by (metis acost.sel less_eq_acost_def less_eq_option_Some)
    show ?case
      apply(rule Sum_any_mono)
      subgoal using l apply(rule ordered_semiring_class.mult_right_mono) by (simp add: needname_nonneg)
      apply(rule wfR_finite_mult_left) by fact
  qed 

lemma timerefine_mono2: 
  fixes R :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR'' R"
  shows "c\<le>c' \<Longrightarrow> \<Down>\<^sub>C R c \<le> \<Down>\<^sub>C R c'"
  apply(cases c) apply simp
  apply(cases c') apply (auto simp: less_eq_acost_def timerefine_def split: nrest.splits option.splits simp: le_fun_def)
  subgoal  by (metis le_some_optE) 
  proof (goal_cases)
    case (1 x2 x2a x x2b x2c xa)
    then have l: "\<And>ac. the_acost x2b ac \<le>  the_acost x2c ac"
      apply(cases x2b; cases x2c) unfolding less_eq_acost_def  
      apply auto
      by (metis acost.sel less_eq_acost_def less_eq_option_Some)
    show ?case
      apply(rule Sum_any_mono)
      subgoal using l apply(rule ordered_semiring_class.mult_right_mono) by (simp add: needname_nonneg)
      apply(rule wfR_finite_mult_left2) by fact
  qed 
  thm wfR''_def



(* TODO: Move *)
lemma timerefine_mono3: 
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R"
  shows "c\<le>c' \<Longrightarrow> R=R' \<Longrightarrow> timerefine R c \<le> timerefine R' c'"
  apply simp
  apply(rule timerefine_mono2)
  using assms by auto

  

lemma timerefine_mono_both: 
  fixes R :: "_ \<Rightarrow> ('c, 'd::{complete_lattice,nonneg,mult_zero,ordered_semiring}) acost"
  assumes "wfR'' R'"
    and "R\<le>R'"
  shows "c\<le>c' \<Longrightarrow> timerefine R c \<le> timerefine R' c'"
  apply(cases c) apply simp
  apply(cases c') apply (auto simp: less_eq_acost_def timerefine_def split: nrest.splits option.splits simp: le_fun_def)
  subgoal  by (metis le_some_optE) 
  proof (goal_cases)
    case (1 x2 x2a x x2b x2c xa)
    then have l: "\<And>ac. the_acost x2b ac \<le>  the_acost x2c ac"
      apply(cases x2b; cases x2c) unfolding less_eq_acost_def  
      apply auto
      by (metis acost.sel less_eq_acost_def less_eq_option_Some)
    show ?case
      apply(rule Sum_any_mono)
      subgoal using l apply(rule ordered_semiring_class.mult_mono)
        subgoal using assms(2) unfolding le_fun_def
          by (simp add: the_acost_mono)
        subgoal by (simp add: needname_nonneg)
        subgoal
          by (simp add: needname_nonneg)
        done
      apply(rule wfR_finite_mult_left2) by fact
  qed 
  
lemma wfR''_ppI:
  fixes R1 :: "'a \<Rightarrow> ('b, enat) acost"
  assumes R1: "wfR'' R1" and R2: "wfR'' R2"
  shows "wfR'' (pp R1 R2)"
  unfolding pp_def wfR''_def
  apply simp apply safe
proof -
  fix f  
  have "\<And>s. finite {b. the_acost (R2 s) b * the_acost (R1 b) f \<noteq> 0}"
    apply(rule wfR_finite_mult_left2) by fact

  have l: "{s. \<exists>b. the_acost (R2 s) b \<noteq> 0 \<and> the_acost (R1 b) f \<noteq> 0}
      = (\<Union>b\<in>{b. the_acost (R1 b) f \<noteq> 0}. {s. the_acost (R2 s) b \<noteq> 0 })"
    by auto

  show "finite {s. (\<Sum>b. the_acost (R2 s) b * the_acost (R1 b) f) \<noteq> 0}"
    apply(subst wfR''_ppI_aux) apply fact
    apply(subst wfR''_ppI_aux2)
    apply(subst l)
    apply(rule finite_Union) 
    subgoal  apply(rule finite_imageI) by (rule R1[THEN wfR''D])
    subgoal       
      using R2
      by (auto simp: wfR''_def)
    done
qed


lemma
  fixes R1 :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R1" "wfR'' R2"
  shows timerefine_iter2: "\<Down>\<^sub>C R1 (\<Down>\<^sub>C R2 c) =  \<Down>\<^sub>C (pp R1 R2) c"
  unfolding timerefine_timerefineA
  apply(subst timerefineA_iter2[OF assms, symmetric])
  by (auto split: nrest.splits option.splits)



lemma
  fixes R1 :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,ordered_semiring,semiring_no_zero_divisors}) acost"
  assumes "wfR R1" "wfR R2"
  shows timerefine_iter: "\<Down>\<^sub>C R1 (\<Down>\<^sub>C R2 c) =  \<Down>\<^sub>C (pp R1 R2) c"
  unfolding timerefine_def 
  apply(cases c)
  subgoal by simp 
  apply (auto simp: le_fun_def pp_def split: option.splits) apply (rule ext)
  apply (auto simp: le_fun_def pp_def split: option.splits)
  apply(subst Sum_any_right_distrib)
  subgoal apply(rule finite_wfR_middle_mult[of R1 R2]) using assms by simp_all
  apply (rule ext)
  subgoal for mc r Mc cc
    apply (subst Sum_any.swap[where C="{a. \<exists>b. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0} \<times> {b. \<exists>a. the_acost Mc a * (the_acost (R2 a) b * the_acost (R1 b) cc) \<noteq> 0}"])
    subgoal apply(rule wfR_finite_crossprod) using assms by simp
    subgoal by simp 
    apply(subst Sum_any_left_distrib)
    subgoal apply(rule wfR_finite_mult_left) using assms by simp 
    apply(rule Sum_any.cong)
    by (meson mult.assoc)
  done 

lemma timerefine_trans: 
  fixes R1 :: "_ \<Rightarrow> ('a, 'b::{complete_lattice,nonneg,ordered_semiring,semiring_no_zero_divisors}) acost"
  assumes "wfR R1" "wfR R2" shows 
  "a \<le> \<Down>\<^sub>C R1 b \<Longrightarrow> b \<le> \<Down>\<^sub>C R2 c \<Longrightarrow> a \<le> \<Down>\<^sub>C (pp R1 R2) c"
  apply(subst timerefine_iter[symmetric, OF assms])
    apply(rule order.trans) apply simp
    apply(rule timerefine_mono) using assms by auto


subsection \<open>Timerefine with monadic operations\<close>

lemma timerefine_RETURNT: "\<Down>\<^sub>C E (RETURNT x') = RETURNT x'"
  by (auto simp: timerefine_def RETURNT_def zero_acost_def)


lemma timerefine_SPECT_map: "\<Down>\<^sub>C E (SPECT [x'\<mapsto>t]) = SPECT [x'\<mapsto>timerefineA E t]"
  by (auto simp: timerefine_def timerefineA_def intro!: ext)


subsection \<open>enum setup\<close>

 

lemma (in enum) sum_to_foldr: "sum f UNIV  
      = foldr (\<lambda>x a. a + f x) enum 0"
  (*= sum_list (map f enum_class.enum)"  *)
  unfolding UNIV_enum using enum_distinct
  apply(simp add: sum.distinct_set_conv_list  )
  apply(simp only: sum_list.eq_foldr foldr_map)  
  by (metis add.commute comp_apply)  

lemma (in enum) Sum_any_to_foldr: "Sum_any f  
      = foldr (\<lambda>x a. a + f x) enum 0"
  apply(subst Sum_any.expand_superset[where A=UNIV])
  by (simp_all add: sum_to_foldr)




subsection \<open>Time Refinement and bind\<close>

lemma nofailT_timerefine[refine_pw_simps]: "nofailT (\<Down>\<^sub>C R m) \<longleftrightarrow> nofailT m" 
  unfolding nofailT_def timerefine_def by (auto split: nrest.splits)



definition inresTf' :: "('a,('b,enat)acost) nrest \<Rightarrow> 'a \<Rightarrow> (('b,enat)acost) \<Rightarrow> bool" where 
  "inresTf' S x t \<equiv> (\<forall>b. (case S of FAILi \<Rightarrow> True | REST X \<Rightarrow> (\<exists>t'. X x = Some t' \<and>  (the_acost t b) \<le> the_acost t' b)) )"

lemma pw_bindT_nofailTf' : "nofailT (bindT M f) \<longleftrightarrow> (nofailT M \<and> (\<forall>x t. inresTf' M x t \<longrightarrow> nofailT (f x)))"
  unfolding bindT_def   
  apply (auto elim: no_FAILTE simp: refine_pw_simps  split: nrest.splits )  
  subgoal  
    by (smt inresTf'_def nofailT_simps(2) nrest.simps(5))  
  subgoal for M x t unfolding inresTf'_def apply auto
  proof (goal_cases)
    case 1
    then have "\<And>t. \<forall>b. \<exists>t'. M x = Some t' \<and>  (the_acost t b) \<le> the_acost t' b \<Longrightarrow> nofailT (f x)" by blast
    with 1(1,3,4) show ?case  
      by auto 
  qed   
  done

         
lemmas limit_bindT = project_acost_bindT


definition "limRef b R m = (case m of FAILi \<Rightarrow> FAILi | REST M \<Rightarrow> SPECT (\<lambda>r. case M r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))))"
 
lemma limRef_limit_timerefine: "(project_acost b (\<Down>\<^sub>C R m)) = limRef b R m"  
  unfolding limRef_def project_acost_def timerefine_def apply(cases m)  by (auto split: option.splits)
 

lemma inresTf'_timerefine: "inresTf' (\<Down>\<^sub>C R m) x t \<Longrightarrow> \<exists>t'. inresTf' m x t'"
  unfolding inresTf'_def timerefine_def by (auto split: nrest.splits option.splits)

lemma ff: "c\<le>a \<Longrightarrow> inresT c  x t \<Longrightarrow> inresT a x t"
  unfolding inresT_def by (auto split: nrest.splits)    



lemma pl2:
  fixes R ::"_ \<Rightarrow> ('a, enat) acost"
  assumes "Ra \<noteq> {}" and "wfR'' R"
  shows  " Sup { Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost  (R ac) b)) |x. x \<in> Ra}
             \<le> Some (Sum_any (\<lambda>ac. (SUP f\<in>Ra. the_acost f ac) * the_acost  (R ac) b))"
proof -
  have *: "{ Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost  (R ac) b)) |x. x \<in> Ra} =
Some ` {  (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra}" by blast
  have *: "Sup { Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra}
          = SUPREMUM { (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra} Some " 
    unfolding * by simp
 
  have a: "\<And>ac. (SUP f\<in>Ra. the_acost f ac) * the_acost (R ac) b = (SUP f\<in>Ra. the_acost f ac * the_acost  (R ac) b)" 
    apply(subst enat_mult_cont') by simp

  have e: "finite {x.  the_acost (R x) b \<noteq> 0}" using assms(2) unfolding wfR''_def by simp

  show ?thesis unfolding *
    apply(subst Some_Sup[symmetric]) using assms apply simp
    apply simp  
    unfolding a apply(rule order.trans[OF _ enat_Sum_any_cont]) 
    subgoal by (simp add: setcompr_eq_image)
    subgoal apply(rule finite_subset[OF _ e]) by auto    
    done
qed
lemma pl:
  fixes R ::"_ \<Rightarrow> ('a, enat) acost"
  assumes "Ra \<noteq> {}" and "wfR R"
  shows  " Sup { Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost  (R ac) b)) |x. x \<in> Ra}
             \<le> Some (Sum_any (\<lambda>ac. (SUP f\<in>Ra. the_acost f ac) * the_acost  (R ac) b))"
proof -
  have *: "{ Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost  (R ac) b)) |x. x \<in> Ra} =
Some ` {  (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra}" by blast
  have *: "Sup { Some (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra}
          = SUPREMUM { (Sum_any (\<lambda>ac. the_acost x ac * the_acost (R ac) b)) |x. x \<in> Ra} Some " 
    unfolding * by simp
 
  have a: "\<And>ac. (SUP f\<in>Ra. the_acost f ac) * the_acost (R ac) b = (SUP f\<in>Ra. the_acost f ac * the_acost  (R ac) b)" 
    apply(subst enat_mult_cont') by simp

  have e: "finite {x.  the_acost (R x) b \<noteq> 0}" apply(rule wfR_fst) by fact

  show ?thesis unfolding *
    apply(subst Some_Sup[symmetric]) using assms apply simp
    apply simp  
    unfolding a apply(rule order.trans[OF _ enat_Sum_any_cont]) 
    subgoal by (simp add: setcompr_eq_image)
    subgoal apply(rule finite_subset[OF _ e]) by auto    
    done
qed

lemma oo: "Option.these (Ra - {None}) = Option.these (Ra)" 
  by (metis insert_Diff_single these_insert_None) 
lemma Sup_wo_None: "Ra \<noteq> {} \<and> Ra \<noteq> {None} \<Longrightarrow> Sup Ra = Sup (Ra-{None})"
  unfolding Sup_option_def apply auto unfolding oo by simp

term continuous

thm continuous_option

lemma kkk2:
  fixes R ::"_ \<Rightarrow> ('a,enat) acost"
  assumes "wfR'' R"
shows 
" (case SUP x\<in>Ra. x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost  (R ac) b)))
   \<ge> Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost  (R ac) b)) |x. x \<in>  Ra}"
  apply(cases "Ra={} \<or> Ra = {None}")
  subgoal by (auto split: option.splits simp: bot_option_def)
  subgoal apply(subst (2) Sup_option_def) apply simp unfolding Sup_acost_def apply simp
    

  proof -
    assume r: "Ra \<noteq> {} \<and> Ra \<noteq> {None}"
    then  obtain x where x: "Some x \<in> Ra"  
      by (metis everywhereNone not_None_eq)  

    have kl: "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}
      = Sup ({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}-{None})"
      apply(subst Sup_wo_None) 
      subgoal apply safe subgoal using x by auto subgoal using x by force
      done by simp
  also have "({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}-{None})
            = ({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra \<and> x\<noteq>None})"
    by (auto split: option.splits)
  also have "\<dots> = ({  Some (\<Sum>ac. the_acost x ac * the_acost (R ac) b) |x. x\<in>Option.these Ra})"
    by (force split: option.splits simp: Option.these_def) 
  finally have rrr: "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}
      = Sup ({  Some (\<Sum>ac. the_acost x ac * the_acost (R ac) b) |x. x\<in>Option.these Ra})" .


  show "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}
         \<le> Some (\<Sum>ac. (SUP f\<in>Option.these Ra. the_acost f ac) * the_acost  (R ac) b)"
      unfolding rrr apply(subst pl2)
      subgoal using x unfolding Option.these_def by auto
      subgoal by fact
      apply simp done
  qed
  done

lemma kkk:
  fixes R ::"_ \<Rightarrow> ('a,enat) acost"
  assumes "wfR R"
shows 
" (case SUP x\<in>Ra. x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost  (R ac) b)))
   \<ge> Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost  (R ac) b)) |x. x \<in>  Ra}"
  apply(cases "Ra={} \<or> Ra = {None}")
  subgoal by (auto split: option.splits simp: bot_option_def)
  subgoal apply(subst (2) Sup_option_def) apply simp unfolding Sup_acost_def apply simp
    

  proof -
    assume r: "Ra \<noteq> {} \<and> Ra \<noteq> {None}"
    then  obtain x where x: "Some x \<in> Ra"  
      by (metis everywhereNone not_None_eq)  

    have kl: "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}
      = Sup ({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}-{None})"
      apply(subst Sup_wo_None) 
      subgoal apply safe subgoal using x by auto subgoal using x by force
      done by simp
  also have "({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}-{None})
            = ({case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra \<and> x\<noteq>None})"
    by (auto split: option.splits)
  also have "\<dots> = ({  Some (\<Sum>ac. the_acost x ac * the_acost (R ac) b) |x. x\<in>Option.these Ra})"
    by (force split: option.splits simp: Option.these_def) 
  finally have rrr: "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}
      = Sup ({  Some (\<Sum>ac. the_acost x ac * the_acost (R ac) b) |x. x\<in>Option.these Ra})" .


  show "Sup {case x of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost  (R ac) b) |x. x \<in> Ra}
         \<le> Some (\<Sum>ac. (SUP f\<in>Option.these Ra. the_acost f ac) * the_acost  (R ac) b)"
      unfolding rrr apply(subst pl)
      subgoal using x unfolding Option.these_def by auto
      subgoal by fact
      apply simp done
  qed
  done

lemma 
  aaa: fixes R ::"_ \<Rightarrow> ('a,enat) acost"
assumes "wfR'' R"
shows 
"(case SUP x\<in>Ra. x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b)))
    \<ge> Sup {case x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b)) |x. x\<in>Ra}"
proof -
  have *: "{case x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}
      = {case x  of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> (\<lambda>f. f r) ` Ra}"
    by auto
  have **: "\<And>f. (case SUP x\<in>Ra. x r of None \<Rightarrow> None | Some cm \<Rightarrow> f cm)
      = (case SUP x\<in>(\<lambda>f. f r) ` Ra. x of None \<Rightarrow> None | Some cm \<Rightarrow> f cm)"    
    by auto       

  show ?thesis unfolding * ** apply(rule kkk2) by fact
qed

lemma 
  ***: fixes R ::"_ \<Rightarrow> ('a,enat) acost"
assumes "wfR R"
shows 
"(case SUP x\<in>Ra. x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b)))
    \<ge> Sup {case x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b)) |x. x\<in>Ra}"
proof -
  have *: "{case x r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> Ra}
      = {case x  of None \<Rightarrow> None | Some cm \<Rightarrow> Some (\<Sum>ac. the_acost cm ac * the_acost (R ac) b) |x. x \<in> (\<lambda>f. f r) ` Ra}"
    by auto
  have **: "\<And>f. (case SUP x\<in>Ra. x r of None \<Rightarrow> None | Some cm \<Rightarrow> f cm)
      = (case SUP x\<in>(\<lambda>f. f r) ` Ra. x of None \<Rightarrow> None | Some cm \<Rightarrow> f cm)"    
    by auto       

  show ?thesis unfolding * ** apply(rule kkk) by fact
qed



lemma nofail'': "x \<noteq> FAILT  \<longleftrightarrow> (\<exists>m. x=SPECT m)"
  unfolding nofailT_def  
  using nrest_noREST_FAILT by blast  

lemma limRef_bindT_le2:
fixes R ::"_ \<Rightarrow> ('a,enat) acost" assumes "wfR'' R"
shows "limRef b R (bindT m f) \<ge> (case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> Sup {case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) t1) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))) |x t1. X x = Some t1})"
    unfolding limRef_def bindT_def apply(cases m) apply auto
  unfolding Sup_nrest_def apply (auto split: nrest.splits)
  apply(rule le_funI)   apply simp unfolding Sup_fun_def     
  subgoal 
    apply(rule order.trans) defer 
    apply(subst aaa[OF assms]) apply simp   
    apply(rule Sup_least)
    apply auto
      apply(subst (asm) nofail'') apply (auto split: option.splits)
    apply(rule Sup_upper)
    apply auto
    subgoal for xa t1 ma x2
    apply(rule exI[where x="map_option ((+) t1) \<circ> ma"])
      apply safe subgoal apply simp done
      subgoal by auto   
      apply(rule exI[where x=xa])
      by simp 
    done
  done

lemma limRef_bindT_le:
fixes R ::"_ \<Rightarrow> ('a,enat) acost" assumes "wfR R"
shows "limRef b R (bindT m f) \<ge> (case m of FAILi \<Rightarrow> FAILT | REST X \<Rightarrow> Sup {case f x of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) t1) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))) |x t1. X x = Some t1})"
    unfolding limRef_def bindT_def apply(cases m) apply auto
  unfolding Sup_nrest_def apply (auto split: nrest.splits)
  apply(rule le_funI)   apply simp unfolding Sup_fun_def     
  subgoal 
    apply(rule order.trans) defer 
    apply(subst ***[OF assms]) apply simp   
    apply(rule Sup_least)
    apply auto
      apply(subst (asm) nofail'') apply (auto split: option.splits)
    apply(rule Sup_upper)
    apply auto
    subgoal for xa t1 ma x2
    apply(rule exI[where x="map_option ((+) t1) \<circ> ma"])
      apply safe subgoal apply simp done
      subgoal by auto   
      apply(rule exI[where x=xa])
      by simp 
    done
  done

lemma nofailT_limRef: "nofailT (limRef b R m) \<longleftrightarrow> nofailT m"
  unfolding limRef_def nofailT_def by (auto split: nrest.splits)

lemma inresT_limRef_D: "inresT (limRef b R (SPECT x2)) r' t' \<Longrightarrow> (\<exists>x2a. x2 r' = Some x2a \<and> enat t' \<le> (Sum_any (\<lambda>ac. the_acost x2a ac * the_acost (R ac) b)))"
  unfolding limRef_def apply simp
   by (auto split: option.splits)

lemma zzz: fixes A B :: "('a, enat) acost"
  shows "the_acost (case A of acostC a \<Rightarrow> case B of acostC b \<Rightarrow> acostC (\<lambda>x. a x + b x)) a *
                    the_acost (R a) b =
        the_acost A a * the_acost (R a) b + the_acost B a * the_acost (R a) b"
  apply(cases A; cases B) apply auto
  by (simp add: comm_semiring_class.distrib)
 
lemma timerefine_bindT_ge:
  fixes R :: "_ \<Rightarrow> ('a,enat) acost"
  assumes wfR: "wfR R"
  shows "bindT (\<Down>\<^sub>C R m) (\<lambda>x. \<Down>\<^sub>C R (f x)) \<le> \<Down>\<^sub>C R (bindT m f)"    
  unfolding  pw_acost_le_iff'
  apply safe
  subgoal apply (simp add: nofailT_timerefine nofailT_project_acost pw_bindT_nofailTf')
          apply auto apply(frule inresTf'_timerefine) by simp 
  subgoal for b x t
    unfolding limit_bindT 
    unfolding pw_inresT_bindT
    unfolding limRef_limit_timerefine
    apply(rule ff[OF limRef_bindT_le]) using assms apply simp
  apply(simp add: nofailT_limRef)
      apply(cases m) subgoal by auto
      apply simp 
      unfolding pw_inresT_Sup apply auto
      apply(drule inresT_limRef_D) apply auto
      subgoal for x2 r' t' t'' x2a
      apply(rule exI[where x="(case f r' of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) x2a) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))))"])
      apply safe
       apply(rule exI[where x=r'])
       apply(rule exI[where x=x2a])
         apply simp
        apply (cases "f r'") subgoal by auto
        apply simp
        apply(drule inresT_limRef_D) apply auto
        apply(rule exI[where x="t' + t''"]) apply (simp add: zzz comm_semiring_class.distrib plus_acost_alt ) 
        apply(subst Sum_any.distrib)
        subgoal apply(rule wfR_finite_mult_left) using wfR by simp
        subgoal apply(rule wfR_finite_mult_left) using wfR by simp
        subgoal  
          using add_mono by fastforce  
        done
    done
  done


lemma timerefine_bindT_ge2:
  fixes R :: "_ \<Rightarrow> ('a,enat) acost"
  assumes wfR'': "wfR'' R"
  shows "bindT (\<Down>\<^sub>C R m) (\<lambda>x. \<Down>\<^sub>C R (f x)) \<le> \<Down>\<^sub>C R (bindT m f)"    
  unfolding  pw_acost_le_iff'
  apply safe
  subgoal apply (simp add: nofailT_timerefine nofailT_project_acost pw_bindT_nofailTf')
          apply auto apply(frule inresTf'_timerefine) by simp 
  subgoal for b x t
    unfolding limit_bindT 
    unfolding pw_inresT_bindT
    unfolding limRef_limit_timerefine
    apply(rule ff[OF limRef_bindT_le2])
    using assms
     apply simp
  apply(simp add: nofailT_limRef)
      apply(cases m) subgoal by auto
      apply simp 
      unfolding pw_inresT_Sup apply auto
      apply(drule inresT_limRef_D) apply auto
      subgoal for x2 r' t' t'' x2a
      apply(rule exI[where x="(case f r' of FAILi \<Rightarrow> FAILT | REST m2 \<Rightarrow> SPECT (\<lambda>r. case (map_option ((+) x2a) \<circ> m2) r of None \<Rightarrow> None | Some cm \<Rightarrow> Some (Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) b))))"])
      apply safe
       apply(rule exI[where x=r'])
       apply(rule exI[where x=x2a])
         apply simp
        apply (cases "f r'") subgoal by auto
        apply simp
        apply(drule inresT_limRef_D) apply auto
        apply(rule exI[where x="t' + t''"]) apply (simp add: zzz comm_semiring_class.distrib plus_acost_alt ) 
        apply(subst Sum_any.distrib)
        subgoal apply(rule wfR''_finite_mult_left) using wfR'' by simp
        subgoal apply(rule wfR''_finite_mult_left) using wfR'' by simp
        subgoal  
          using add_mono by fastforce  
        done
    done
  done


lemma timerefine_R_mono: 
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR R'"
  shows "R\<le>R' \<Longrightarrow> \<Down>\<^sub>C R c \<le> \<Down>\<^sub>C R' c"
  unfolding timerefine_def apply(cases c)
   apply (auto intro!: le_funI simp: less_eq_acost_def split: option.splits)
  apply(rule Sum_any_mono)
   apply(rule mult_left_mono) apply(auto simp: le_fun_def)
  subgoal premises prems for x2 x x2a xa xb 
    using prems(1)[rule_format, of xb] apply(cases "R xb"; cases "R' xb") apply auto 
    unfolding less_eq_acost_def by auto
  subgoal for x2 x x2a xa using assms(1) unfolding wfR_def
    apply -
    apply(rule finite_subset[where B="{x. the_acost (R' x) xa \<noteq> 0}"]) apply auto
    apply(rule wfR_fst) apply (rule assms) done
  done


lemma timerefine_R_mono_wfR'': 
  fixes R :: "_ \<Rightarrow> ('a, enat) acost"
  assumes "wfR'' R'"
  shows "R\<le>R' \<Longrightarrow> \<Down>\<^sub>C R c \<le> \<Down>\<^sub>C R' c"
  unfolding timerefine_def apply(cases c)
   apply (auto intro!: le_funI simp: less_eq_acost_def split: option.splits)
  apply(rule Sum_any_mono)
   apply(rule mult_left_mono) apply(auto simp: le_fun_def)
  subgoal premises prems for x2 x x2a xa xb 
    using prems(1)[rule_format, of xb] apply(cases "R xb"; cases "R' xb") apply auto 
    unfolding less_eq_acost_def by auto
  subgoal for x2 x x2a xa using assms(1) unfolding wfR_def
    apply -
    apply(rule finite_subset[where B="{x. the_acost (R' x) xa \<noteq> 0}"]) apply auto
    using assms[unfolded wfR''_def] apply simp done
  done

subsection \<open>Structure Preserving\<close>

definition "struct_preserving E \<equiv> (\<forall>t. cost ''call'' t \<le> timerefineA E (cost ''call'' t))
                                   \<and> (\<forall>t. cost ''if'' t \<le> timerefineA E (cost ''if'' t))"

lemma struct_preservingI:
  assumes "\<And>t. cost ''call'' t \<le> timerefineA E (cost ''call'' t)"
     "\<And>t. cost ''if'' t \<le> timerefineA E (cost ''if'' t)"
  shows "struct_preserving E"
  using assms unfolding struct_preserving_def by auto

lemma struct_preservingD:
  assumes "struct_preserving E"
  shows "\<And>t. cost ''call'' t \<le> timerefineA E (cost ''call'' t)"
     "\<And>t. cost ''if'' t \<le> timerefineA E (cost ''if'' t)"
  using assms unfolding struct_preserving_def by auto


lemma struct_preserving_upd_I[intro]: 
  fixes F:: "char list \<Rightarrow> (char list, enat) acost"
  shows "struct_preserving F \<Longrightarrow>  x\<noteq>''if''\<Longrightarrow>  x\<noteq>''call'' \<Longrightarrow> struct_preserving (F(x:=y))"
  by (auto simp: struct_preserving_def)


subsection \<open>preserving currency\<close>

definition "preserves_curr R n \<longleftrightarrow> (R n = (cost n 1))"


lemma preserves_curr_other_updI:
  "preserves_curr R m \<Longrightarrow> n\<noteq>m \<Longrightarrow> preserves_curr (R(n:=t)) m"
  by(auto simp: preserves_curr_def)

lemma preserves_curr_D: "preserves_curr R n \<Longrightarrow> R n = (cost n 1)"
  unfolding preserves_curr_def by metis
  


subsection \<open>TId\<close>


definition "TId = (\<lambda>x. acostC (\<lambda>y. (if x=y then 1 else 0)))"


lemma TId_apply: "TId x = cost x 1"
  by (auto simp add: cost_def TId_def zero_acost_def)

lemma preserves_curr_TId[simp]: "preserves_curr TId n"
  by(auto simp: preserves_curr_def TId_def cost_def zero_acost_def)

lemma cost_n_leq_TId_n: "cost n (1::enat) \<le> TId n"
  by(auto simp:  TId_def cost_def zero_acost_def less_eq_acost_def)

lemma timerefine_id:
  fixes M :: "(_,(_,enat)acost) nrest"
  shows "\<Down>\<^sub>C TId M = M"
  apply(cases M; auto simp: timerefine_def TId_def)
  apply(rule ext) apply(auto split: option.splits)
  subgoal for x2 r x2a apply(cases x2a) apply simp
    apply(rule ext) apply(simp add: if_distrib)
    apply(subst mult_zero_right)
    apply(subst Sum_any.delta) by simp
  done

lemma timerefineA_TId:
  fixes T :: "(_,enat) acost"
  shows "T \<le> T' \<Longrightarrow> T \<le> timerefineA TId T'"
  unfolding timerefineA_def TId_def
    apply(simp add: if_distrib)
    apply(subst mult_zero_right)
    apply(subst Sum_any.delta) by(cases T; cases T'; auto)

lemma sp_TId[simp]: "struct_preserving (TId::_\<Rightarrow>(string, enat) acost)" 
  by (auto intro!: struct_preservingI simp: timerefineA_upd timerefineA_TId)

lemma timerefineA_TId_aux: "the_acost x a * (if b then (1::enat) else 0)
    = (if b then the_acost x a  else 0)"
  apply(cases b) by auto

lemma pp_TId_absorbs_right:
  fixes A :: "'b \<Rightarrow> ('c, enat) acost" 
  shows "pp A TId = A"
  unfolding pp_def TId_def apply simp
  apply(rule ext) apply(subst timerefineA_upd_aux)
  by simp

lemma pp_TId_absorbs_left:
  fixes A :: "'b \<Rightarrow> ('c, enat) acost" 
  shows "pp TId A  = A"
  unfolding pp_def TId_def apply simp
  apply(rule ext) apply(subst timerefineA_TId_aux)
  by simp

lemma timerefineA_TId_eq[simp]:
  shows "timerefineA TId x = (x:: ('b, enat) acost)"
  unfolding timerefineA_def TId_def 
  by (simp add: timerefineA_TId_aux)

lemma wfR_TId: "wfR TId"
  unfolding TId_def wfR_def apply simp
  oops

lemma "wfR' TId"
  unfolding TId_def wfR'_def by simp

lemma wfR''_TId[simp]: "wfR'' TId"
  unfolding TId_def wfR''_def by simp





subsection \<open>Stuff about integrating functional Specification (with top time)\<close>


lemma getDiff: assumes "A \<subseteq> C"
  shows "\<exists>B. C = A \<union> B \<and> A \<inter> B = {}"
  using assms 
  by (metis Diff_disjoint Diff_partition)  

lemma sum_extend_zeros: 
  assumes "finite B" "{x. f x\<noteq>0} \<subseteq> B"
  shows "sum f B = sum f {x. f x\<noteq>0}"
proof -
  from assms(2) obtain A where B: "B = A \<union> {x. f x\<noteq>0}" and disj[simp]: "A \<inter> {x. f x\<noteq>0} = {}"    
    by (metis Int_commute getDiff sup_commute)  
  from assms(1) B have [simp]: "finite A" "finite {x. f x\<noteq>0}" by auto

  have *: "sum f A = 0"
    apply(rule sum.neutral)
    using disj by blast    

  show ?thesis
    unfolding B
    by(simp add: * sum.union_disjoint)
qed



lemma inf_acost: "inf (acostC a) (acostC b) = acostC (inf a b)"
  unfolding inf_acost_def by auto
  
lemma inf_absorbs_top_aux1: "\<And>a. a \<noteq> 0 \<Longrightarrow> a * top = (top::enat)" 
    unfolding top_enat_def  
    by (simp add: imult_is_infinity)

lemma inf_absorbs_top_aux2: "\<And>a. a \<noteq> 0 \<Longrightarrow> top * a = (top::enat)" 
    unfolding top_enat_def  
    by (simp add: imult_is_infinity) 

lemma inf_absorbs_top: 
  fixes a b :: enat
  shows "inf (a * b) (a * top) = a * b"
  apply(cases "a=0"; cases "b=0") by (auto simp: inf_absorbs_top_aux1)

lemma inf_absorbs_top2: 
  fixes a b :: enat
  shows "inf (b * a) (top * a) = b * a"
  apply(cases "a=0"; cases "b=0") by (auto simp: inf_absorbs_top_aux2)

lemma timerefine_inf_top_distrib_aux1:
  fixes f :: "_ \<Rightarrow> enat"
  assumes F: "finite {x. f x \<noteq> 0}"
  shows " Sum_any (inf (\<lambda>x. f x * g x) (\<lambda>x. f x * top))
     = inf (Sum_any (\<lambda>x. f x * g x)) (Sum_any (\<lambda>x. f x * top))"
proof (cases "{x. f x \<noteq> 0} = {}")
  case True
  then show ?thesis
    unfolding Sum_any.expand_set by simp
next
  case False 
  with F have cn0: "card {x. f x \<noteq> 0} \<noteq> 0" by simp
  
  have 1: "{a. inf (\<lambda>x.   (f x * g x)) (\<lambda>x.   (f x) * top) a \<noteq> 0}
      \<subseteq> {x. f x \<noteq> 0}" by auto
  have 2: "{a. f a * g a \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by auto
  have 3: "{a. f a * top \<noteq> 0} \<subseteq> {x. f x \<noteq> 0}" by auto
 

  { fix a b :: enat
  have "inf (a * b) (a * top) = a * b"
    apply(cases "a=0"; cases "b=0") by (auto simp: inf_absorbs_top_aux1)
  } note * = this

  have "(\<Sum>a\<in>{x. f x \<noteq> 0}. f a * top) = (\<Sum>a\<in>{x. f x \<noteq> 0}. top)"
    apply(rule sum.cong) apply simp by (auto simp: top_enat_def imult_is_infinity)
  also have "\<dots> = top" 
    using False cn0 by (simp add: top_enat_def imult_is_infinity)
  finally have i: "(\<Sum>a\<in>{x. f x \<noteq> 0}. f a * top) = top" .
    

  show ?thesis
    unfolding Sum_any.expand_set
    apply(subst sum_extend_zeros[symmetric, OF _ 1]) apply fact
    apply(subst sum_extend_zeros[symmetric, OF _ 2]) apply fact
    apply(subst sum_extend_zeros[symmetric, OF _ 3]) apply fact
    by (simp add: * i)
qed

lemma timerefine_inf_top_distrib_aux2:
  fixes f :: "_ \<Rightarrow> enat"
  assumes F: "finite {x. f x \<noteq> 0}"
  shows "inf (Sum_any (\<lambda>x. g x * f x)) (Sum_any (\<lambda>x. top * f x))
    = Sum_any (inf (\<lambda>x. g x * f x) (\<lambda>x. top * f x))"
  apply(subst (1) mult.commute) 
  apply(subst (2) mult.commute)  
  apply(subst timerefine_inf_top_distrib_aux1[symmetric]) apply fact
  by(simp add: mult.commute)

lemma timerefine_inf_top_distrib:
  fixes m :: "('a, ('d, enat) acost) nrest"
  assumes a: "\<And>cc. finite {x. the_acost (R x) cc \<noteq> 0}"
  shows "\<Down>\<^sub>C R (inf m (SPEC P (\<lambda>_. top)))
        = inf (\<Down>\<^sub>C R m) (\<Down>\<^sub>C R (SPEC P (\<lambda>_. top)))"
  unfolding timerefine_def SPEC_def 
  apply(cases m) apply simp apply simp apply(rule ext)
  apply auto
  subgoal for x2 r
    apply(cases "x2 r") apply simp
    apply simp
    unfolding inf_acost apply simp apply(rule ext)
    apply (simp add: top_acost_def) 
    apply(subst timerefine_inf_top_distrib_aux2) apply (rule a)
    apply(subst inf_fun_def)
    using inf_absorbs_top2
    apply(subst inf_absorbs_top2) by simp
  done


lemma 
  SPEC_timerefine:
  "A \<le> A' \<Longrightarrow> (\<And>x. B x \<le> timerefineA R (B' x)) \<Longrightarrow> SPEC A B \<le> \<Down>\<^sub>C R (SPEC A' B')"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT
  apply (simp add: le_fun_def) apply auto
  unfolding timerefineF_def timerefineA_def
  by auto


lemma SPECT_emb'_timerefine:
  "
  (\<And>x. Q x \<Longrightarrow> Q' x)
  \<Longrightarrow>
  (\<And>x. T x \<le> timerefineA E (T' x))
  \<Longrightarrow>
  SPECT (emb' Q T) \<le> \<Down>\<^sub>C E (SPECT (emb' Q' T'))"
  unfolding SPEC_REST_emb'_conv[symmetric]
  apply(rule SPEC_timerefine) by (auto intro: le_funI)


lemma 
  SPEC_timerefine_eq:
  "(\<And>x. B x = timerefineA R (B' x)) \<Longrightarrow> SPEC A B = \<Down>\<^sub>C R (SPEC A B')"
  apply(auto simp: SPEC_def)
  unfolding timerefine_SPECT 
  apply auto
  unfolding timerefineF_def timerefineA_def
  by auto





lemma finite_sum_nonzero_cost:
  "finite {a. the_acost (cost n m) a \<noteq> 0}"
  unfolding cost_def by (auto simp: zero_acost_def)

lemma finite_sum_nonzero_if_summands_finite_nonzero:
  "finite {a. f a \<noteq> 0} \<Longrightarrow> finite {a. g a \<noteq> 0} \<Longrightarrow> finite {a. (f a ::nat) + g a \<noteq> 0}"
  apply(rule finite_subset[where B="{a. f a \<noteq> 0} \<union> {a. g a \<noteq> 0}"])
  by auto


end