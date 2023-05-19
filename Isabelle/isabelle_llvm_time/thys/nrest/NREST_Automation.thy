\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
\<^marker>\<open>contributor "Peter Lammich"\<close>
section \<open>Automation for NREST\<close>
theory NREST_Automation
imports NREST_Backwards_Reasoning "../cost/Enat_Cost"
begin


paragraph \<open>Summary\<close>
text \<open>This theory contains automation for NREST:
\<^item> A refinement condition generator for lockstep refinement
\<^item> Solver for Time Side conditions
\<^item> Setup for normalizing time functions and exchange rates
\<close>



subsection "Monadic Refinement Automation"


ML \<open>
structure Refine = struct

  structure vcg = Named_Thms
    ( val name = @{binding refine_vcg}
      val description = "Refinement Framework: " ^ 
        "Verification condition generation rules (intro)" )

  structure vcg_cons = Named_Thms
    ( val name = @{binding refine_vcg_cons}
      val description = "Refinement Framework: " ^
        "Consequence rules tried by VCG" )

  structure refine0 = Named_Thms
    ( val name = @{binding refine0}
      val description = "Refinement Framework: " ^
        "Refinement rules applied first (intro)" )

  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )

  structure refine2 = Named_Thms
    ( val name = @{binding refine2}
      val description = "Refinement Framework: " ^
        "Refinement rules 2nd stage (intro)" )

  (* If set to true, the product splitter of refine_rcg is disabled. *)
  val no_prod_split = 
    Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

  fun rcg_tac add_thms ctxt = 
    let 
      val cons_thms = vcg_cons.get ctxt
      val ref_thms = (refine0.get ctxt 
        @ add_thms @ refine.get ctxt @ refine2.get ctxt);
      val prod_ss = (Splitter.add_split @{thm prod.split} 
        (put_simpset HOL_basic_ss ctxt));
      val prod_simp_tac = 
        if Config.get ctxt no_prod_split then 
          K no_tac
        else
          (simp_tac prod_ss THEN' 
            REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}));
    in
      REPEAT_ALL_NEW_FWD (DETERM o FIRST' [
        resolve_tac ctxt ref_thms,
        resolve_tac ctxt cons_thms THEN' resolve_tac ctxt ref_thms,
        prod_simp_tac
      ])
    end;

  fun post_tac ctxt = REPEAT_ALL_NEW_FWD (FIRST' [
    eq_assume_tac,
    (*match_tac ctxt thms,*)
    SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
         

end;
\<close>
setup \<open>Refine.vcg.setup\<close>
setup \<open>Refine.vcg_cons.setup\<close>
setup \<open>Refine.refine0.setup\<close>
setup \<open>Refine.refine.setup\<close>
setup \<open>Refine.refine2.setup\<close>
(*setup {* Refine.refine_post.setup *}*)

method_setup refine_rcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac add_thms ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement conditions"     

(*method_setup refine_vcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac (add_thms @ Refine.vcg.get ctxt) ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement and verification conditions"
*)

subsection \<open>Solver for Time Side conditions\<close>

lemma lift_acost_propagate: "lift_acost (t+t') = lift_acost t + lift_acost t' "
  unfolding lift_acost_def by (cases t; cases t'; auto)

definition "leq_sidecon (a::(string,enat) acost) as1 as2 b bs1 bs2 T \<equiv> a + as1 + as2 \<le> b + bs1 + bs2 \<and> T"

lemma leq_sc_init: 
    "leq_sidecon a 0 (as + 0) 0 0 (bs + 0) True \<Longrightarrow> a + as \<le> bs"
    "leq_sidecon a 0 0 0 0 (bs + 0) True \<Longrightarrow> a \<le> bs"
  unfolding leq_sidecon_def by simp_all

lemma leq_sc_l_SUCC:
  "leq_sidecon (cost n (x+y)) ar as 0 0 bs P \<Longrightarrow> leq_sidecon (cost n x) ar (cost n y + as) 0 0 bs P"
  unfolding leq_sidecon_def apply (subst add.commute) apply (subst add.assoc) apply (subst cost_same_curr_left_add)
  apply (subst add.assoc[symmetric]) apply (subst add.commute) by simp

lemma leq_sc_l_FAIL:
 (* "leq_sidecon (cost n x) c as 0 0 bs2 P \<Longrightarrow> leq_sidecon (cost n x) 0 (c + as) 0 0 bs2 P" *)
  "leq_sidecon (cost n x) (c + ar) as 0 0 bs2 P \<Longrightarrow> leq_sidecon (cost n x) ar (c + as) 0 0 bs2 P"
  unfolding leq_sidecon_def by(simp_all add: add.commute add.left_commute)

lemma leq_sc_l_DONE:
  "leq_sidecon (cost n x) l 0 (cost n 0) 0 bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 0 0 bs2 P"
  unfolding leq_sidecon_def by (simp add: cost_zero)

lemma leq_sc_r_SUCC:
  "leq_sidecon (cost n x) l 0 (cost n (y+z)) bs1 bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 (cost n y) bs1 (cost n z + bs2) P"
  unfolding leq_sidecon_def apply (subst (3) add.commute) apply (subst (2) add.assoc) apply (subst cost_same_curr_left_add)
  apply (subst add.assoc[symmetric]) apply (subst (3) add.commute) by simp

lemma leq_sc_r_FAIL:
(*  "leq_sidecon (cost n x) l 0 (cost n y) c bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 (cost n y) 0 (c + bs2) P" *)
  "leq_sidecon (cost n x) l 0 (cost n y) (c + bs1) bs2 P \<Longrightarrow> leq_sidecon (cost n x) l 0 (cost n y) bs1 (c + bs2) P"
  unfolding leq_sidecon_def by(simp_all add: add.commute add.left_commute)

lemma cost_mono: "(x::enat)\<le>y \<Longrightarrow> cost n x \<le> cost n y"
  by(auto simp: cost_def less_eq_acost_def)
lemma ecost_nneg: "0 \<le> (r::(string,enat) acost)"
  by (rule needname_nonneg)
  
lemma leq_sc_r_DONE_ALL:
  "(P \<and> x\<le>y) \<Longrightarrow> leq_sidecon (cost n x) 0 0 (cost n y) r 0 P"
  unfolding leq_sidecon_def by (auto intro: add_increasing2 cost_mono ecost_nneg )

lemma leq_sc_r_DONE1:
  "leq_sidecon l 0 ls 0 0 r (P \<and> x\<le>y) \<Longrightarrow> leq_sidecon (cost n x) (l + ls) 0 (cost n y) r 0 P"
  unfolding leq_sidecon_def by (auto intro: add_mono cost_mono ecost_nneg)


definition "sc_solve_debug n x = x"

lemma leq_sc_r_DONE_ALL_debug:
  "(P \<and> sc_solve_debug n (x\<le>y)) \<Longrightarrow> leq_sidecon (cost n x) 0 0 (cost n y) r 0 P"
  unfolding leq_sidecon_def by (auto simp: sc_solve_debug_def intro: add_increasing2 cost_mono ecost_nneg )

lemma leq_sc_r_DONE1_debug:
  "leq_sidecon l 0 ls 0 0 r (P \<and> sc_solve_debug n (x\<le>y)) \<Longrightarrow> leq_sidecon (cost n x) (l + ls) 0 (cost n y) r 0 P"
  unfolding leq_sidecon_def by (auto simp: sc_solve_debug_def intro: add_mono cost_mono ecost_nneg)


lemma "cost ''a'' 1 + cost ''b'' (1::enat) + cost ''b'' 1 + cost ''b'' 1 + cost ''a'' 2 \<le> cost ''a'' 3 + cost ''b'' 3"
  apply(simp only: add.assoc)
  apply(rule leq_sc_init)
  apply(simp only: add.assoc)
  apply(rule leq_sc_l_SUCC leq_sc_l_FAIL)+
  apply(rule  leq_sc_l_DONE)
  apply(rule leq_sc_r_SUCC leq_sc_r_FAIL )+
  apply(rule leq_sc_r_DONE_ALL leq_sc_r_DONE1) 
  oops

method sc_solve' =  ( (simp only: add.assoc)?; rule leq_sc_init, (simp only: add.assoc)?,
         ( (rule leq_sc_l_SUCC leq_sc_l_FAIL leq_sc_l_DONE)+,
           (rule leq_sc_r_SUCC leq_sc_r_FAIL leq_sc_r_DONE_ALL leq_sc_r_DONE1)+ )+ )
method sc_solve =  ( (simp add: lift_acost_propagate lift_acost_cost)?; sc_solve' )

method sc_solve'_debug =  ( (simp only: add.assoc)?; rule leq_sc_init, (simp only: add.assoc)?,
         ( (rule leq_sc_l_SUCC leq_sc_l_FAIL leq_sc_l_DONE)+,
           (rule leq_sc_r_SUCC leq_sc_r_FAIL leq_sc_r_DONE_ALL_debug leq_sc_r_DONE1_debug)+ )+ )
method sc_solve_debug =  ( (simp add: lift_acost_propagate lift_acost_cost)?; sc_solve'_debug )

lemma
  lift_acost_diff_to_the_front:
   "a + (lift_acost (b - c) + d) = (lift_acost (b - c) + (a + d))"
    "(a + lift_acost (b - c)) = (lift_acost (b - c) + a)"
  by(simp_all add: add_ac)


lemma lift_acost_diff_to_the_right:
  assumes "b\<le>a"
  shows "(lift_acost (a-b) + c) \<le> d \<longleftrightarrow> (lift_acost a + c) \<le>  d + (lift_acost b)"
  using assms
  apply(auto simp: lift_acost_def less_eq_acost_def minus_acost_alt plus_acost_alt split: acost.splits)
  subgoal by (smt add.assoc add.commute add_left_mono le_add_diff_inverse plus_enat_simps(1)) 
  subgoal by (smt add.assoc add.commute add_diff_cancel_enat enat.simps(3) le_add_diff_inverse2 needname_adjoint of_nat_add of_nat_eq_enat)
 done

lemma lift_acost_diff_to_the_right_Some:
  assumes "b\<le>a"
  shows "Some (lift_acost (a-b) + c) \<le> d \<longleftrightarrow> Some (lift_acost a + c) \<le> Someplus d (Some (lift_acost b))"
  using assms
  by (cases d; auto simp: lift_acost_diff_to_the_right) 

lemma "b \<le> a \<Longrightarrow> Some
         (cost ''list_set'' 1 +
          (lift_acost (a - b) +
           (cost ''list_cmp_v'' 1 + (cost ''if'' 1 + cost ''i_gt'' 1 + cost ''i_sub'' 1) + cost ''if'' 1 +
            (cost ''list_get'' 1 + cost ''call'' 1))))
        \<le> (if I then Some (lift_acost (E_u (length xs)) + cost ''list_get'' 1) else None)"
  apply(simp add: lift_acost_diff_to_the_front lift_acost_diff_to_the_right) oops


lemma "cost ''a'' 1 + cost ''b'' (1::enat) + cost ''b'' 1 + cost ''b'' 1 + cost ''a'' 2 \<le> cost ''a'' 3 + cost ''b'' 3"
  apply sc_solve
  by simp

lemma "cost ''a'' 1 + cost ''b'' (1::enat) + cost ''b'' 1 + cost ''a'' 2  + cost ''aa'' (enat (Suc i)) + cost ''c'' 1
           \<le> cost ''aa'' 1 + cost ''a'' 3 + cost ''b'' 3 + cost ''aa'' (enat i)  + cost ''c'' 3"
  apply sc_solve
  apply simp
  oops

subsection \<open>Setup for simplifying a cost expression by finding an upper bound\<close>

lemma leq_sc_l_TERMINATE_special:
  "P \<Longrightarrow> leq_sidecon (cost n x) 0 0 0 0 (cost n x + 0) P"   
  unfolding leq_sidecon_def by (simp add: cost_zero)

lemma leq_sc_l_DONE_special:
  "leq_sidecon 0 l 0 0 0 (bs3+0) P \<Longrightarrow> leq_sidecon (cost n x) l 0 0 0 ((cost n x + bs3) + 0) P"   
  unfolding leq_sidecon_def apply (simp add: cost_zero)
  apply(rule add_mono) by auto

lemma leq_sc_l_NEXT_ROW_special:
  "leq_sidecon (cost n x) 0 ls 0 0 bs P \<Longrightarrow> leq_sidecon 0 ((cost n x)+ls) 0 0 0 bs P"
  unfolding leq_sidecon_def by (simp add: cost_zero) 

method sc_solve_upperbound = ( ( (simp only: add.assoc)?; rule leq_sc_init, (simp only: add.assoc)?),
        ( ((rule leq_sc_l_SUCC leq_sc_l_FAIL )+)?,
            ((rule leq_sc_l_DONE_special, rule leq_sc_l_NEXT_ROW_special)
              | (rule  leq_sc_l_TERMINATE_special))  )+ 
    )

subsubsection \<open>example\<close>

schematic_goal "cost ''a'' (1::enat) + cost ''b'' 2  + cost ''b'' 2  + cost ''b'' 5 \<le> ?x" 
  apply sc_solve_upperbound
  by simp


subsection \<open>Lemma Collections for Normalizing Resource Functions and Exchange Rates\<close>

lemmas norm_cost = costmult_add_distrib costmult_cost lift_acost_propagate lift_acost_cost
              the_acost_propagate timerefineA_cost lift_acost_zero timerefineA_propagate TId_apply
              timerefineA_cost_apply_costmult

lemmas norm_pp = pp_TId_absorbs_right pp_TId_absorbs_left pp_fun_upd




end