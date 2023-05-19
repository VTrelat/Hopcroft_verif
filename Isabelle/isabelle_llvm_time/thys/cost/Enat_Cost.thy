theory Enat_Cost
imports "HOL-Library.Extended_Nat" Abstract_Cost
begin

type_synonym ecost = "(string,enat) acost"

declare [[coercion_enabled = false]]


definition "lift_acost c \<equiv> acostC (enat o the_acost c)"

lemma lift_acost_zero: "lift_acost 0 = 0" by (auto simp add: lift_acost_def zero_acost_def zero_enat_def )


lemma lift_acost_cost: "lift_acost (cost name x) = (cost name (enat x))"
  by (auto simp: one_enat_def zero_enat_def lift_acost_def cost_def zero_acost_def)

lemma ecost_le_zero: "(Ca::ecost) \<le> 0 \<longleftrightarrow> Ca=0"
  apply(cases Ca) by(auto simp: zero_acost_def less_eq_acost_def)

lemma get_delta: "Ca \<le> (T::(_,enat)acost) \<Longrightarrow> \<exists>delta. T = delta + Ca"
  apply(cases Ca; cases T)
  apply(rule exI[where x="T - Ca"])
  apply (auto simp: minus_acost_alt less_eq_acost_def) 
  apply(rule ext)  
  subgoal premises p for f g x
    using p(1)[rule_format, of x]  
    by (metis add.commute add_diff_cancel_enat less_eqE plus_eq_infty_iff_enat) 
  done


end