theory Currs_Of 
imports Time_Refinement NREST_Main
begin








definition "currs_of f = {x . the_acost f x \<noteq> 0}"

lemma currs_of_0[simp]: "currs_of 0 = {}"
  by(auto simp: currs_of_def zero_acost_def)

lemma blub:
  fixes x2a ::  "('b, enat) acost"
  shows 
 "x\<notin>currs_of x2a
    \<Longrightarrow> the_acost x2a a * the_acost (if a = x then c else TId a) cc
        = (if a=cc then the_acost x2a a else 0)"
  by(auto simp: TId_def currs_of_def)

lemma
    in_currs_of_iff:
  "x\<in>currs_of f \<longleftrightarrow> the_acost f x > (0::enat)"
  unfolding currs_of_def by auto



definition "currs_of_M m = (case m of FAILi \<Rightarrow> UNIV | REST m \<Rightarrow> \<Union>x. (case m x of None \<Rightarrow> {} | Some t \<Rightarrow> currs_of t))"


lemma currs_of_M_Sup:
  fixes M :: "('b, ('a, enat) acost) nrest set"
  shows "FAILT\<notin>M \<Longrightarrow> currs_of_M (Sup M) = (\<Union>m\<in>M. currs_of_M m)"
  unfolding Sup_nrest_def 
  apply(auto split: if_splits)
  oops



lemma currs_of_M_RETURNT[simp]: "currs_of_M (RETURNT x) = {}"
  unfolding currs_of_M_def RETURNT_def by simp

lemma currs_of_M_FAILT[simp]: "currs_of_M FAILT = UNIV"
  unfolding currs_of_M_def by simp

lemma x_in_currs_of_Sup_if_in_currs_of:
  fixes f :: "(_,enat) acost"
  shows "x\<in>currs_of f \<Longrightarrow> f\<in>F \<Longrightarrow> x \<in> currs_of (Sup F)"
  unfolding currs_of_def
  apply (auto simp: Sup_acost_def)
  by (metis SUP_bot_conv(1) bot_enat_def) 


lemma gt0_if_neq0: "(a::enat) \<noteq> 0 \<longleftrightarrow> a>0"
  by auto
lemma neq0_if_gt0: "a>0 \<Longrightarrow> (a::enat) \<noteq> 0"
  by auto

thm Sup_acost_def
 

lemma x_in_currs_of_if_in_currs_of_Sup:
  fixes F :: "((_,enat) acost) set"
  shows "x\<in>currs_of (Sup F) \<Longrightarrow> (\<exists>f\<in>F. x\<in>currs_of f)"
  unfolding currs_of_def
  apply (auto simp: Sup_acost_def)  
  apply(subst (asm) gt0_if_neq0) 
  apply(rule ccontr)
  apply auto  
  by (metis SUP_bot_conv(1) bot_enat_def)  
  

lemma ba: "(SUP f\<in>{f. SPECT f \<in> M}. f xa) = Some y
    \<Longrightarrow> (\<exists>x f. x\<le>y \<and> Some x = f xa \<and> SPECT f \<in> M)"
  apply auto 
  by (smt Sup_bot_conv(1) Sup_empty Sup_option_def Sup_pointwise_eq_fun Sup_upper imageE less_eq_option_Some mem_Collect_eq option.simps(3)) 

lemma one_dir:
  fixes M :: "('b, ('a, enat) acost) nrest set"
  assumes "x \<in> currs_of_M (SPECT (Sup {f. SPECT f \<in> M}))"
  shows "\<exists>xa\<in>M. x \<in> currs_of_M xa"
proof (rule ccontr)
  assume "\<not> (\<exists>m\<in>M. x \<in> currs_of_M m)"
  then have *: "\<And>m. m\<in>M \<Longrightarrow> x \<notin> currs_of_M m" by auto
  then have "\<And>m. m\<in>M \<Longrightarrow> m \<noteq> FAILT" unfolding currs_of_M_def apply auto by force
  from * have **: "\<And>m f. m\<in>M \<Longrightarrow> m \<noteq> FAILT \<and> (m=REST f \<longrightarrow> x\<notin>(\<Union>x. case f x of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x))"
    unfolding currs_of_M_def apply auto 
    subgoal by force 
    subgoal by fastforce
    done
  {
    fix f :: "'b \<Rightarrow> ('a, enat) acost option" and x
    have "x\<notin>(\<Union>y. case f y of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x)
        \<longleftrightarrow> (\<forall>y. f y = None \<or> (\<forall>z. f y = Some z \<longrightarrow> x \<notin> currs_of z))"
      apply auto
      subgoal 
        by (metis option.simps(5)) 
      subgoal 
        by (metis memb_imp_not_empty option.case_eq_if option.exhaust_sel) 
      done
  } note p = this
  from ** have ***: "\<And>m f. m\<in>M \<Longrightarrow> m \<noteq> FAILT \<and> (m=REST f \<longrightarrow> (\<forall>y. f y = None \<or> (\<forall>z. f y = Some z \<longrightarrow> x \<notin> currs_of z)))"
    unfolding p .
  then have ****: "\<And>m f z y. m\<in>M \<Longrightarrow> m \<noteq> FAILT \<and> (m=REST f \<longrightarrow> ( f y = None \<or>  ( f y = Some z \<longrightarrow> x \<notin> currs_of z)))"
    by blast
  


  from assms have "\<exists>xa. x \<in> (case SUP f\<in>{f. SPECT f \<in> M}. f xa of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x)"
    unfolding currs_of_M_def by simp

  then obtain xa where " x \<in> (case SUP f\<in>{f. SPECT f \<in> M}. f xa of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x)" by blast

  with **** show False 
    by (smt Sup_option_def empty_iff imageE in_these_eq mem_Collect_eq option.simps(4)
            option.simps(5) x_in_currs_of_if_in_currs_of_Sup)
qed


lemma currs_of_M_Sup:
  fixes M :: "('b, ('a, enat) acost) nrest set"
  shows "currs_of_M (Sup M) = (\<Union>m\<in>M. currs_of_M m)"
  unfolding Sup_nrest_def 
  apply(auto split: if_splits)
  subgoal for x apply(drule one_dir) by simp
  subgoal for x m
    unfolding currs_of_M_def apply simp
    apply(cases m) apply simp
    apply (auto split: option.splits)
    subgoal for x2 xa y
      apply(rule exI[where x=xa])
      apply safe
      subgoal apply(rule ccontr) apply simp
      proof (goal_cases)
        case 1
        have "(SUP f\<in>{f. SPECT f \<in> M}. f xa) >= Some y"
          apply(rule Sup_upper)
          apply(rule image_eqI) apply(rule 1(5)[symmetric])
          using 1(3) by simp
        then show ?case using 1(6) by auto 
      qed
      unfolding in_currs_of_iff
      proof (goal_cases)
        case (1 x2)
        have "(SUP f\<in>{f. SPECT f \<in> M}. f xa) \<ge> Some y"
          apply(rule Sup_upper)
          apply(rule image_eqI) apply(rule 1(5)[symmetric])
          using 1(3) by simp
        with 1(6) have "Some y \<le> Some x2" by auto 
        then have "y \<le> x2" by auto 
        then have *: "\<And>x. the_acost y x \<le> the_acost x2 x" unfolding less_eq_acost_def by auto 
        from 1(4) show ?case unfolding le_fun_def using *[of x] by auto
      qed
      done
    done

lemma pffa: "currs_of_M (SPECT (map_option ((+) t1) \<circ> x2a)) \<subseteq> currs_of t1 \<union> (\<Union>x. (case x2a x of None \<Rightarrow> {} | Some t \<Rightarrow> currs_of t))"
  unfolding currs_of_M_def apply auto
  unfolding currs_of_def apply auto  
  by (smt add.left_neutral comp_apply disjE_realizer2 mem_Collect_eq option.case_distrib the_acost_plus)  
 


lemma currs_of_M_bindT:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "nofailT(bindT m f)
         \<Longrightarrow> currs_of_M (bindT m f) \<subseteq> currs_of_M m \<union> (\<Union>x\<in>{x. inres m x}. currs_of_M (f x))"
  unfolding bindT_def 
  apply(cases m) apply simp
  apply simp
  apply(subst currs_of_M_Sup)
  apply simp
  apply auto
  subgoal for x2 x xb t1
    apply(cases "f xb") apply simp
    subgoal premises p using p(5) p(1) p(4)
      using inres_def local.p(3) by fastforce
    subgoal apply simp
      apply(drule set_mp[OF pffa]) apply simp apply auto
      subgoal unfolding currs_of_M_def apply auto
        by ( metis option.simps(5))
      subgoal unfolding currs_of_M_def apply auto 
        by (metis (no_types) UNIV_I Union_iff image_eqI inres_def nrest.simps(5)) 
      done
    done
  done

lemma currs_of_M_bindT_loose:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "currs_of_M (bindT m f) \<subseteq> currs_of_M m \<union> (\<Union>x. currs_of_M (f x))"
  unfolding bindT_def 
  apply(cases m) apply simp
  apply simp
  apply(subst currs_of_M_Sup)
  apply simp
  apply auto
  subgoal for x2 x xb t1
    apply(cases "f xb") apply simp
    subgoal premises p using p(2)[rule_format, where x=xb] p(4) apply simp done
    subgoal apply simp
      apply(drule set_mp[OF pffa]) apply simp apply auto
      subgoal unfolding currs_of_M_def apply auto
        by (metis option.simps(5))
      subgoal unfolding currs_of_M_def apply auto 
        by (smt UNIV_I UN_I nrest.simps(5))
      done
    done
  done

lemma timerefine_conv_if_not_in_currs_of:
  fixes m ::  "(_,('b, enat) acost) nrest"
  shows "x\<notin>currs_of_M m \<Longrightarrow> timerefine (f(x:=c)) m = timerefine f m"
  apply(cases m)
  unfolding currs_of_M_def
   apply simp
  apply(auto split: nrest.splits option.splits intro!: ext simp: timerefine_def) 
  apply(rule Sum_any.cong)
  apply auto unfolding currs_of_def by auto 

lemma
  fixes m ::  "(_,('b, enat) acost) nrest"
  shows "x\<notin>currs_of_M m \<Longrightarrow> m = timerefine (TId(x:=c)) m"
  apply(cases m)
  unfolding currs_of_M_def
   apply simp
  apply(auto split: nrest.splits option.splits intro!: ext simp: timerefine_def)
  apply(subst blub)
  subgoal apply auto done
  apply(subst Sum_any.delta) apply simp
  done


abbreviation "overaprox_currs_of_M X m \<equiv> currs_of_M m \<subseteq> X"

lemma 
  fixes m ::  "(_,('b, enat) acost) nrest"
  shows "x \<notin> X \<Longrightarrow> overaprox_currs_of_M X m \<Longrightarrow> timerefine (f(x:=c)) m = timerefine f m"
  apply(rule timerefine_conv_if_not_in_currs_of)
  by auto

lemma overaprox_currs_of_M_RETURNT: "overaprox_currs_of_M {} (RETURNT x)"
  apply simp done
lemma overaprox_currs_of_M_SPEC1: "overaprox_currs_of_M (currs_of t) (SPECT [x\<mapsto>t])"
  unfolding currs_of_M_def by (auto split: if_splits)

lemma overaprox_currs_of_M_bindT_loose:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "overaprox_currs_of_M X m \<Longrightarrow> (\<And>x.  overaprox_currs_of_M (Y x) (f x))
   \<Longrightarrow>  overaprox_currs_of_M (X\<union>(\<Union>x. Y x)) (bindT m f)" 
  apply(rule order.trans[OF currs_of_M_bindT_loose])
  apply(rule Un_mono)
  subgoal apply simp done
  subgoal  
    by auto
  done


lemma overaprox_currs_of_M_bindT:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "(nofailT m \<Longrightarrow> overaprox_currs_of_M X m)
     \<Longrightarrow> (\<And>x. inres m x \<Longrightarrow> nofailT (f x) \<Longrightarrow>  overaprox_currs_of_M (Y x) (f x))
   \<Longrightarrow> nofailT (bindT m f) \<Longrightarrow> overaprox_currs_of_M (X\<union>(\<Union>x. Y x)) (bindT m f)" 
  apply(rule order.trans[OF currs_of_M_bindT])
  apply simp
  apply(rule Un_mono)
  subgoal unfolding nofailT_bindT apply simp done
  subgoal  unfolding nofailT_bindT
    by auto
  done





schematic_goal "overaprox_currs_of_M ?X (bindT (m::('b, ('c, enat) acost) nrest) f)"
  apply(rule overaprox_currs_of_M_bindT) oops


schematic_goal "overaprox_currs_of_M ?X (do { x\<leftarrow>SPECT [1\<mapsto>cost ''a'' (1::enat)]; SPECT [ () \<mapsto> cost ''b'' 2]})"
  apply(rule overaprox_currs_of_M_bindT_loose overaprox_currs_of_M_RETURNT)
  apply(rule overaprox_currs_of_M_RETURNT overaprox_currs_of_M_SPEC1)
  apply(rule overaprox_currs_of_M_RETURNT overaprox_currs_of_M_SPEC1)
  done

lemma currs_of_cost_gt: "i>0 \<Longrightarrow> currs_of (cost x (i::enat)) = {x}"
  unfolding currs_of_def cost_def  by (auto simp: zero_acost_def)
lemmas pff2 = currs_of_cost_gt

lemma "(currs_of (cost ''a'' (1::enat)) \<union> (\<Union>x. currs_of (cost ''b'' (2::enat)))) = {''a'',''b''}"
  by (auto simp add: pff2)

definition "TTId S = (\<lambda>c. (if c\<in>S then cost c 1 else 0))"

lemma meep: "x2 x = Some x2a \<Longrightarrow> the_acost x2a a \<noteq> 0
  \<Longrightarrow> (\<exists>x. a \<in> (case x2 x of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x))"
  unfolding currs_of_def
  apply(rule exI[where x=x]) by simp 

lemma meep2: "x2 x = Some x2a \<Longrightarrow>
  the_acost x2a a * the_acost (if \<exists>x. a \<in> (case x2 x of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x) then cost a 1 else 0) cc
      = (if a=cc then the_acost x2a a else (0::enat))"
  apply(cases "the_acost x2a a = 0")
  subgoal apply auto done
  subgoal apply(subst meep) apply simp apply simp
    unfolding cost_def by (simp add: zero_acost_def) 
  done

lemma meep3: "x2 x = Some x2a \<Longrightarrow> the_acost x2a a \<noteq> 0
  \<Longrightarrow> a \<in> currs_of_M (SPECT x2) "
  unfolding currs_of_M_def currs_of_def apply simp
  apply(rule exI[where x=x]) by simp 

lemma meep21:
  fixes x2a :: "('c, 'd:: {complete_lattice,monoid_add}) acost"
  assumes "x2 x = Some x2a" "the_acost x2a a \<noteq> 0"
  "(\<Union>x. case x2 x of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x) \<subseteq> X"
shows  "a : X"
  apply(rule set_mp)
   defer
   apply(rule meep3[of x2]) apply(rule assms(1)) apply(rule assms(2))
  using assms(3) unfolding currs_of_M_def by auto

lemma meep22: "x2 x = Some x2a \<Longrightarrow>
    (\<Union>x. case x2 x of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x) \<subseteq> X \<Longrightarrow>
    the_acost x2a a * the_acost (if a \<in> X then cost a 1 else 0) cc
  = (if a=cc then the_acost x2a a else (0::enat))"
  apply(cases "the_acost x2a a = 0")
  subgoal by (auto simp: cost_def zero_acost_def) 
  subgoal apply(subst meep21[of x2]) apply simp apply simp apply simp
    unfolding cost_def by (simp add: zero_acost_def) 
  done

lemma selfrefine_TTId_currs_of_M_superset:
  fixes m :: "('a, ('b, enat) acost) nrest"
  shows "currs_of_M m \<subseteq> X \<Longrightarrow> m \<le> timerefine (TTId X) m"
  unfolding timerefine_def TTId_def 
  apply(cases m)
   apply simp
  apply (auto simp add: le_fun_def split: option.splits)
  unfolding currs_of_M_def apply simp
  subgoal for x2 x x2a
    apply(subst meep22[of x2]) apply simp  apply simp
    apply(subst Sum_any.delta) apply simp
    done
  done

lemma selfrefine_TTId_currs_of_M:
  fixes m :: "('a, ('b, enat) acost) nrest"
  shows "m \<le> timerefine (TTId (currs_of_M m)) m"
  unfolding timerefine_def TTId_def 
  apply(cases m)
   apply simp
  apply (auto simp add: le_fun_def split: option.splits)
  unfolding currs_of_M_def apply simp
  apply(subst meep2) apply simp
  apply(subst Sum_any.delta) apply simp
  done


lemma selfrefine_TTId_currs_of_M':
  fixes m :: "('a, ('b, enat) acost) nrest"
  shows "m \<ge> timerefine (TTId (currs_of_M m)) m"
  unfolding timerefine_def TTId_def 
  apply(cases m)
   apply simp
  apply (auto simp add: le_fun_def split: option.splits)
  unfolding currs_of_M_def apply simp
  apply(subst meep2) apply simp
  apply(subst Sum_any.delta) apply simp
  done

lemma selfrefine_TTId_currs_of_M_both:
  fixes m :: "('a, ('b, enat) acost) nrest"
  shows "m = timerefine (TTId (currs_of_M m)) m"
  apply(rule antisym)
  apply(rule selfrefine_TTId_currs_of_M)
  apply(rule selfrefine_TTId_currs_of_M')
  done

lemma selfrefine_TTId_currs_of_M_both_yeah:
  fixes m :: "('a, ('b, enat) acost) nrest"
  assumes "nofailT m \<Longrightarrow> currs_of_M m = A"
  shows "m = timerefine (TTId A) m"
  apply(cases "nofailT m")
  subgoal 
    apply(drule assms[symmetric]) 
    apply simp
    apply(rule antisym)
    apply(rule selfrefine_TTId_currs_of_M)
    apply(rule selfrefine_TTId_currs_of_M')
    done
  subgoal unfolding nofailT_def by simp
  done

lemma assumes "overaprox_currs_of_M X m"
  assumes "\<And>x. overaprox_currs_of_M F (f x)"
  shows "overaprox_currs_of_M (X\<union>F) (bindT m f)"
  oops


  section "Rules for calculating TTId set"

lemma wfR''_TTId_if_finite: "finite X' \<Longrightarrow> wfR'' (TTId X' :: _ \<Rightarrow> (_,enat) acost)"
  unfolding wfR''_def TTId_def by (auto simp: zero_acost_def cost_def)


lemma timerefine_TTId_mono:
  shows "X \<subseteq> X' \<Longrightarrow> finite X' \<Longrightarrow> timerefine (TTId X :: _\<Rightarrow>('v, enat) acost) m \<le> timerefine (TTId X') m "
  apply(rule timerefine_R_mono_wfR'')
  apply(rule wfR''_TTId_if_finite)
  apply simp
  unfolding TTId_def by (auto simp: cost_def zero_acost_def less_eq_acost_def le_fun_def)


lemma R_bind2:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  assumes "m \<le> timerefine (TTId X) m'"
     "finite X"
    "\<And>x. f x \<le> timerefine (TTId Y) (f' x)"
      "finite Y"
  shows "bind m f \<le> timerefine (TTId (X\<union>Y)) (bind m' f')"
  apply(rule bindT_refine_easy[where R=Id and R'=Id, simplified])
  apply(rule wfR''_TTId_if_finite)
  subgoal using assms by auto
   apply(rule order.trans)
  apply(rule assms(1))
   apply(rule timerefine_TTId_mono) apply simp
  subgoal using assms by auto
  apply(rule order.trans)
  apply(rule assms(3))
   apply(rule timerefine_TTId_mono) apply simp
  subgoal using assms by auto
  done

lemma R_bind:
  fixes m :: "('e1,('c1,enat)acost) nrest"
  assumes "m \<le> timerefine (TTId X) m"
     "finite X"
    "\<And>x. f x \<le> timerefine (TTId Y) (f x)"
      "finite Y"
  shows "bind m f \<le> timerefine (TTId (X\<union>Y)) (bind m f)"
  apply(rule R_bind2)
  using assms by auto

lemma R_ASSERT: "ASSERT x \<le> timerefine (TTId {}) (ASSERT x)"
  apply(cases x)
   apply auto by(auto simp: timerefine_def RETURNT_def le_fun_def  zero_acost_def)

lemma R_RETURNT: "RETURNT x \<le> timerefine (TTId {}) (RETURNT x)"
  by(auto simp: timerefine_def RETURNT_def le_fun_def  zero_acost_def)


lemma R_SPECTmap_aux: "the_acost T ac * the_acost (if the_acost T ac = 0 then 0 else cost ac 1) cc
    = (if ac=cc then the_acost T ac else 0::enat)"
  by (auto simp: zero_acost_def cost_def split: if_splits)

lemma R_SPECTmap:
  fixes T :: "(_,enat) acost"
  shows "SPECT [x\<mapsto>T] \<le> timerefine (TTId (currs_of T)) (SPECT [x\<mapsto>T])"
  apply(auto simp: timerefine_def le_fun_def currs_of_def TTId_def)
  unfolding R_SPECTmap_aux apply(subst Sum_any.delta)
  by simp

lemma R_consumea:
  fixes T :: "(_,enat) acost"
  shows  "consumea T \<le> timerefine (TTId (currs_of T)) (consumea T)"
  unfolding consumea_def
  by(rule R_SPECTmap)



lemma R_consume:
  fixes t :: "(_,enat) acost"
  shows "m \<le> timerefine (TTId X) m' \<Longrightarrow> finite X \<Longrightarrow>
    finite (currs_of t) \<Longrightarrow> consume m t \<le> timerefine (TTId (X\<union>currs_of t)) (consume m' t)"
  unfolding consume_alt
  apply(rule R_bind2) apply simp
  apply simp
  apply(rule order.trans)
   apply(rule R_bind)
       apply(rule R_consumea)
  apply simp
     apply(rule R_RETURNT)
  by simp_all


lemma R_prod: "m (fst x) (snd x) \<le> timerefine (TTId X) (m (fst x) (snd x))
   \<Longrightarrow> (case x of (a,b) \<Rightarrow> m a b) \<le> timerefine (TTId X) (case x of (a,b) \<Rightarrow> m a b)"
  apply(cases x)
  by auto


thm RECT_refine_t


lemma R_RECT:
  assumes M: "mono2 body"
  assumes RS: "\<And>f f' x. \<lbrakk> \<And>x. f x \<le> (timerefine (TTId Y) (f' x)) \<rbrakk> 
    \<Longrightarrow> body f x \<le> (timerefine (TTId Y) (body f' x))"
  shows "RECT (\<lambda>f x. body f x) x \<le> (timerefine (TTId Y) (RECT (\<lambda>f x. body f x) x))"
  apply(rule RECT_refine_t[where S=Id and R=Id, simplified])                                              
    apply(rule M)
   apply simp
  apply simp
  apply(rule RS)
  by simp

lemma R_RECT_annotate:
  assumes M: "mono2 body"
  assumes RS: "\<And>f f' x. \<lbrakk> \<And>x. f x \<le> (timerefine (TTId X) (f' x)) \<rbrakk> 
    \<Longrightarrow> body f x \<le> (timerefine (TTId Y) (body f' x))"
  assumes XY: "X=Y"
  shows "RECT (\<lambda>f x. body f x) x \<le> (timerefine (TTId Y) (RECT (\<lambda>f x. body f x) x))"
  apply(rule RECT_refine_t[where S=Id and R=Id, simplified])                                              
    apply(rule M)
   apply simp
  apply simp
  apply(rule RS)
  using XY by simp


lemma R_SPECc2: "((SPECc2 c op a b):: ('b, ('c, enat) acost) nrest) \<le> timerefine (TTId {c}) (SPECc2 c op a b)"
  unfolding SPECc2_def
  apply(rule order.trans)
   apply(rule R_SPECTmap)
  by(simp add: pff2)



lemma R_MIf:
  fixes c1 :: "(_,(string, enat) acost) nrest"
  shows "c1 \<le> timerefine (TTId X1) c1' \<Longrightarrow> finite X1 \<Longrightarrow> 
    c2 \<le> timerefine (TTId X2) c2' \<Longrightarrow> finite X2 \<Longrightarrow>  MIf b c1 c2 \<le> (timerefine (TTId ({''if''} \<union> X1 \<union> X2)) (MIf b c1' c2'))"
  unfolding MIf_def
  apply auto
  subgoal apply(rule order.trans)
     apply(rule R_consume)
       apply assumption
      apply(simp_all add: pff2)
    apply(rule timerefine_TTId_mono)
    by auto
  subgoal apply(rule order.trans)
     apply(rule R_consume)
       apply assumption
      apply(simp_all add: pff2) 
    apply(rule timerefine_TTId_mono)
    by auto
  done


subsection "ocoM setup"


lemma currs_of_M_data:
  fixes m :: "('e, ('b, enat) acost) nrest"
  shows "currs_of_M (\<Down>R m) \<subseteq> currs_of_M m"
  unfolding conc_fun_def  nofailT_def
  apply(cases m) apply simp
  apply simp
  apply (auto split: option.splits)
  apply(rule ccontr)
  unfolding currs_of_M_def
  apply (auto split: option.splits)
  proof (goal_cases)
    case (1 x2 x xa y)
    from 1(1) have "\<And>xa x2a. x2 xa = Some x2a \<Longrightarrow> the_acost x2a x = 0"
      unfolding currs_of_M_def currs_of_def 
      by (auto split: option.splits)  

    with 1(4) have "the_acost y x = 0"       
      by (smt "1"(1) "1"(3) Sup_option_these in_these_eq mem_Collect_eq x_in_currs_of_if_in_currs_of_Sup)

    with 1(3) show ?case unfolding in_currs_of_iff by auto
  qed 


lemma ocoM_blub_aux:
  fixes f :: "('b, enat) acost option"
  shows " (case case f of None \<Rightarrow> None | Some cm \<Rightarrow> Some (acostC (\<lambda>cc. Sum_any (\<lambda>ac. the_acost cm ac * the_acost (R ac) cc))) of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x)
  \<subseteq> (\<Union>x\<in>case f of None \<Rightarrow> {} | Some x \<Rightarrow> currs_of x. currs_of (R x))"
  apply(cases "f")
  apply simp
  apply simp
  unfolding currs_of_def
  apply auto
  subgoal for a xa apply(rule ccontr)
    apply auto
  proof (goal_cases)
    case 1
    from 1(3) have pp: "\<And>ac. the_acost a ac * the_acost (R ac) xa = 0" by auto
    have "(\<Sum>ac. the_acost a ac * the_acost (R ac) xa) = 0"
      unfolding pp by simp
    with 1(2) show ?case by simp
  qed
  done

lemma ocoM_lole2: "(\<And>x. f x \<subseteq> g x) \<Longrightarrow> (\<Union>x\<in>A. f x) \<subseteq>  (\<Union>x\<in>A. g x)"
  by auto

  


lemma ocoM_blub: fixes m :: "('b, ('c, enat) acost) nrest"
  shows "nofailT m \<Longrightarrow> currs_of_M (timerefine R m) \<subseteq> (\<Union>x\<in>currs_of_M m. currs_of (R x))"
  unfolding timerefine_def   
  apply(cases m) apply simp
  apply simp
  unfolding currs_of_M_def apply simp 
  apply(rule ocoM_lole2)
  apply(rule ocoM_blub_aux) 
  done

lemma currs_of_M_SPEC: "currs_of_M (SPEC P T) = (\<Union>x\<in>{x. P x}. currs_of (T x))"
  unfolding currs_of_M_def SPEC_def apply simp
  by (auto split: if_splits)

lemma currs_of_M_SPEC2: "currs_of_M (SPEC P T) \<subseteq> (\<Union>x. currs_of (T x))"
  unfolding currs_of_M_def SPEC_def apply simp
  by (auto split: if_splits)

lemma currs_cost_left: "currs_of x \<subseteq> X \<Longrightarrow> currs_of (cost c (i::enat) + x) \<subseteq> {c} \<union> X"
  unfolding currs_of_def apply(cases x) by (auto simp: plus_acost_alt cost_def zero_acost_def)

lemma currs_cost: "currs_of (cost c (i::enat)) \<subseteq> {c}"
  unfolding currs_of_def by (auto simp: plus_acost_alt cost_def zero_acost_def)

lemma
    currs_of_M_mono:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "m \<le> m' \<Longrightarrow> currs_of_M m \<le> currs_of_M m'"
  unfolding currs_of_M_def
  apply(cases m) apply simp
  apply(cases m') apply simp
  apply simp
  apply (auto split: option.splits)
  subgoal for a b c d e
    apply(rule exI[where x=d])
    apply (auto simp: le_fun_def)
    subgoal premises p using p(1)[rule_format, of d] p(4) 
      using not_Some_eq by fastforce 
    subgoal premises p using p(1)[rule_format, of d] p(4) p(5) p(6)
      unfolding in_currs_of_iff
      by (metis i0_less leD less_eq_acost_def less_eq_option_Some) 
    done
  done
  
definition "ocoM X m \<equiv> nofailT m \<longrightarrow> currs_of_M m \<subseteq> X"

lemma ocoMI:
  assumes "nofailT m \<Longrightarrow> currs_of_M m \<subseteq> X"
  shows "ocoM X m"
  using assms unfolding ocoM_def by auto

lemma ocoMD:
  assumes "ocoM X m"
  shows "nofailT m \<Longrightarrow> currs_of_M m \<subseteq> X"
  using assms unfolding ocoM_def by auto



lemma overaprox_currs_of_M_ASSERT: "nofailT (ASSERT x) \<Longrightarrow> overaprox_currs_of_M {} (ASSERT x)"
  apply(simp add: pw_ASSERT)  done



lemma overaprox_currs_of_M_consume: "overaprox_currs_of_M X M
    \<Longrightarrow> overaprox_currs_of_M (X \<union> currs_of x) (consume M x)"
  unfolding consume_def apply(cases M)
  subgoal by auto
  apply simp
  apply(rule subset_trans)
   apply(rule pffa)
  unfolding currs_of_M_def apply simp
  apply auto  done
 


lemma ocoM_consume: "ocoM X M \<Longrightarrow> ocoM (X \<union> currs_of x) (consume M x)"
  apply(rule ocoMI)
  apply(rule overaprox_currs_of_M_consume)
  apply(drule ocoMD)
  by(auto simp: nofailT_consume )


lemma ocoM_ASSERT: "ocoM {} (ASSERT x)"
  by(auto intro!: ocoMI overaprox_currs_of_M_ASSERT)

lemma ocoM_bindT:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "(ocoM X m)
     \<Longrightarrow> (\<And>x. inres m x \<Longrightarrow> ocoM (Y x) (f x))
   \<Longrightarrow> ocoM (X\<union>(\<Union>x. Y x)) (bindT m f)" 
  apply(rule ocoMI)
  apply(rule overaprox_currs_of_M_bindT)
  by (auto dest: ocoMD)


lemma ocoM_SPECT: "ocoM (currs_of t) (SPECT[x\<mapsto>t])"
  apply(rule ocoMI)
  unfolding currs_of_M_def currs_of_def by (auto split: if_splits)

lemma ocoM_RETURNT: "ocoM {} (RETURNT x)"
  apply(rule ocoMI)
  apply(rule overaprox_currs_of_M_RETURNT)
  done

lemma ocoM_prod: "ocoM X (m (fst xb) (snd xb)) \<Longrightarrow> ocoM X (case xb of (x, xs) \<Rightarrow> m x xs)"
  unfolding ocoM_def by (auto split: prod.splits)
 (*
lemma assumes "(\<And>D s. (\<And>s'. ocoM X (D s')) \<Longrightarrow> ocoM X (F D s))"
    "mono2 F"
  shows "ocoM X (RECT (\<lambda>D s. F D s) x)"
  unfolding RECT_def using assms(2) apply simp 
  apply(subst gfp_transfer[where \<alpha>="\<lambda>F. ocoM X (F x)" and g="id"])
  subgoal unfolding ocoM_def currs_of_M_def  sorry
  subgoal  sorry
  subgoal by (metis eq_id_iff inf_continuous_id)
  subgoal unfolding ocoM_def nofailT_def by simp 
  subgoal   sorry
  oops
*)

lemma assumes "(\<And>D s. (\<And>s'. ocoM X (D s')) \<Longrightarrow> ocoM X (F D s))"
    "mono2 F"
  shows "ocoM X (RECT (\<lambda>D s. F D s) x)"
  apply(subst RECT_unfold)
  apply fact
  apply(rule assms(1))
  unfolding RECT_def gfp_def 
  oops

lemma ocoM_lole: "A\<subseteq>B \<Longrightarrow> (\<Union>x\<in>A. f x) \<subseteq>  (\<Union>x\<in>B. f x)"
  by auto

lemma ocoM_zz: "A\<noteq>{} \<Longrightarrow> (\<Union>x\<in>A. f) = f"
  by simp

lemma currs_of_TId: "currs_of (TId x) \<subseteq> {x}"
  by (auto simp add: currs_of_def cost_def TId_def zero_acost_def)
lemma currs_of_TId2: "currs_of (((TId x):: ('b, enat) acost)) = {x}"
  by (auto simp add: currs_of_def cost_def TId_def zero_acost_def)

lemma ocoM_rr: "(\<Union>x\<in>R. f x) \<subseteq> X \<Longrightarrow> (\<Union>x\<in>({u}\<union>R). f x) \<subseteq> f u \<union> X"
  by auto
lemma ocoM_rrend: "(\<Union>x\<in>({u}). f x) \<subseteq> f u"
  by auto

lemma ocuM_refine:
  fixes m :: "('b, ('c, enat) acost) nrest"
  shows "overaprox_currs_of_M A m' \<Longrightarrow> m \<le> m' \<Longrightarrow> overaprox_currs_of_M A m"
  apply(rule order.trans)
   apply(rule currs_of_M_mono) apply simp
  apply simp done



end