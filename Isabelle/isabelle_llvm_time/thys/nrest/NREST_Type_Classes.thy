\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
\<^marker>\<open>contributor "Peter Lammich"\<close>
section \<open>Type Class needed for currency refine and backwards reasoning gwp\<close>
theory NREST_Type_Classes
imports NREST
begin

paragraph \<open>Summary\<close>
text \<open>This theory collects the properties a resource type needs to allow for currency refinement
  and backwards reasoning.\<close>

subsection \<open>Type class for currency refinement\<close>

text \<open>this is needed for monotonicity of Sum_any\<close>

class nonneg = ord + zero +
  assumes needname_nonneg: "0 \<le> x"

subsection \<open>Algebraic structure needed for backwards reasoning\<close>



lemma le_None: "t \<le> None \<longleftrightarrow> t = None" apply(cases t) apply auto done


lemma enat_1: "top - a = (top::enat)"
  apply(cases a) by (auto simp: top_enat_def)
lemma enat_2: "a - (b + c) = a - c - (b::enat)" 
  apply(cases a;cases b;cases c) by (auto)  
lemma enat_3: "  \<lbrakk>a + b \<le> c;   b \<le> (c::enat) \<rbrakk> \<Longrightarrow>  a \<le> c - b"
  apply(cases a; cases b; cases c) by auto
lemma enat_4: "a + b \<le> c\<Longrightarrow>  b \<le> (c::enat)"
  apply(cases a; cases b; cases c) by auto
lemma enat_5: "\<lbrakk>t1 \<le> b - a; aa \<le> b - a - t1; a \<le> b\<rbrakk> \<Longrightarrow> t1 + a \<le> (b::enat)"
  apply(cases t1; cases b; cases aa; cases a) by auto

lemma nat_2: "a - (b + c) = a - c - (b::nat)" 
  apply(cases a;cases b;cases c) by (auto)  
lemma nat_3: "  \<lbrakk>a + b \<le> c;   b \<le> (c::nat) \<rbrakk> \<Longrightarrow>  a \<le> c - b"
  apply(rule linordered_semidom_class.add_le_imp_le_diff) .
lemma nat_4: "a + b \<le> c\<Longrightarrow>  b \<le> (c::nat)"
  by(rule Nat.add_leD2)

(* TODO: good name *)
class needname = complete_lattice + minus + plus +
  assumes top_absorb: "\<And>a. top - a = top" 
      and minus_plus_assoc2: "\<And>a b c. a - (b + c) = a - c - b"
      and le_diff_if_add_le: "\<And>a b c. \<lbrakk>a + b \<le> c;   b \<le> c \<rbrakk> \<Longrightarrow>  a \<le> c - b"
      and add_leD2: "\<And>a b c. a + b \<le> c\<Longrightarrow>  b \<le> c"
      and add_le_if_le_diff: "\<And>t1 a aa b. \<lbrakk>t1 \<le> b - a; aa \<le> b - a - t1; a \<le> b\<rbrakk> \<Longrightarrow> t1 + a \<le> b"
begin 
lemma needname_cancle: "t1 + t2 \<le> t \<Longrightarrow> t2 \<le> t" 
  apply(rule add_leD2) .

lemma needname_adjoint: "a + b \<le> c \<Longrightarrow> a \<le> c - b"
  using add_leD2 le_diff_if_add_le by blast

end

(*
class resource = complete_lattice + monoid_add
begin

definition minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "minus a b = Sup {c. c + b \<le> a  }"

lemma "minus top a = top"
  unfolding minus_def 
  apply(rule antisym)
   apply simp
  apply(rule Sup_upper)
  by simp

lemma "minus a (b + c) = minus (minus a b) c"
  unfolding minus_def
  apply(rule antisym)
  subgoal
   apply (rule Sup_upper)
   apply auto
    apply (rule Sup_upper)
    apply auto
    sorry
  subgoal 
    apply(rule Sup_upper)
    apply auto
    sorry

    oops

lemma "\<lbrakk>a + b \<le> c;   b \<le> c \<rbrakk> \<Longrightarrow>  a \<le> minus c b"
  unfolding minus_def apply(rule Sup_upper)
  apply simp
  done

lemma " a + b \<le> c\<Longrightarrow>  b \<le> c"
  sorry

lemma " \<lbrakk>t1 \<le> minus b a; aa \<le> minus (minus b a) t1; a \<le> b\<rbrakk> \<Longrightarrow> t1 + a \<le> b"
  unfolding minus_def
  sorry
    


end
*)


instance enat :: needname
  apply standard
      apply(fact enat_1)
     apply(fact enat_2)
    apply(fact enat_3)
   apply(fact enat_4)
  apply(fact enat_5)
  done

instantiation acost :: (type, needname) needname
begin
instance
  apply standard
  subgoal for a apply(cases a) by (auto simp: top_acost_def top_absorb fun_eq_iff)
  subgoal for a b c apply(cases a;cases b;cases c) by (auto simp:  minus_plus_assoc2 less_eq_acost_def)
  subgoal for a b c apply(cases a;cases b;cases c) by (auto simp:  le_diff_if_add_le less_eq_acost_def)
  subgoal for a b c apply(cases a;cases b;cases c) by (auto intro: add_leD2 simp: less_eq_acost_def)
  subgoal for a b c d apply(cases a;cases b;cases c;cases d) by (auto intro: add_le_if_le_diff simp: less_eq_acost_def)
  done
end


lemma diff_left_mono_enat:
   "b \<le> (c::enat)   \<Longrightarrow> a - c \<le> a - b"  
  apply(cases a; cases b; cases c) by(auto simp: minus_acost_alt less_eq_acost_def diff_left_mono )


class drm = minus + plus + ord + Inf + Sup +
  assumes diff_right_mono: "a \<le> b \<Longrightarrow> a - c \<le> b - c"
  and diff_left_mono: "\<And>a b c. b \<le> c   \<Longrightarrow> a - c \<le> a - b"  
    (* TODO: investigate what those mean *)
  and minus_continuousInf: "R\<noteq>{} \<Longrightarrow> (INF r\<in>R. r - mt) \<le> Inf R - mt"
  and minus_continuousSup: "\<And>X t q. X\<noteq>{} \<Longrightarrow> \<forall>x\<in>X. t \<le> q - (x::'a) \<Longrightarrow> t \<le> q - (Sup X)" 
  and plus_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"







lemma ASSN_enat:
  shows "X\<noteq>{} \<Longrightarrow> \<forall>x\<in>X. t \<le> q - (x::enat) \<Longrightarrow> t \<le> q - (Sup X)"  
  unfolding Sup_enat_def apply auto
  apply(cases q) apply auto
  by (metis antisym cancel_comm_monoid_add_class.diff_cancel diff_left_mono_enat
          finite_enat_bounded idiff_enat_enat linear zero_enat_def zero_le)

instance enat :: drm
  apply standard
  subgoal for a b c apply(cases a; cases b; cases c) by auto
  subgoal for a b c apply(cases a; cases b; cases c) by auto
  subgoal for R mt
    unfolding Inf_enat_def apply auto  
    by (metis (full_types) INF_lower Inf_enat_def LeastI_ex equals0D imageI) 
  subgoal apply(rule ASSN_enat) by auto
  subgoal for a b c apply(cases a; cases b; cases c) by auto
  done



class needname_zero = needname + nonneg + drm + ordered_comm_monoid_add + mult_zero +
  assumes needname_minus_absorb: "x - 0 = x"                                 
   and needname_plus_absorb: "0 + x = x"

instance enat :: needname_zero 
  apply standard
  by auto
lemma ll: "(case acostC x of acostC b \<Rightarrow> f b) = f x" by auto

instantiation acost :: (type, needname_zero) needname_zero
begin
  definition "a*b = acostC (\<lambda>x. the_acost a x * the_acost b x)"

instance
  apply standard
  subgoal for a b c apply(cases a; cases b; cases c) by(auto simp: minus_acost_alt less_eq_acost_def plus_left_mono )  subgoal for a b c apply(cases a; cases b; cases c) by(auto simp: minus_acost_alt less_eq_acost_def diff_right_mono )
  subgoal for a b c apply(cases a; cases b; cases c) by(auto simp: minus_acost_alt less_eq_acost_def diff_left_mono )
  subgoal premises prems for R mt apply(cases mt) unfolding Inf_acost_def less_eq_acost_def minus_acost_alt  apply simp
    apply (subst image_image) apply (auto ) apply(subst ll) 
    apply(rule order.trans)
     defer apply(rule minus_continuousInf) subgoal using prems by auto 
    apply (rule Inf_mono) apply auto
    by (metis acost.case_eq_if acost.sel order_mono_setup.refl)
  subgoal for X t q
    unfolding less_eq_acost_def minus_acost_alt Sup_acost_def
    apply(cases t) apply(cases q)
    apply simp
    apply clarsimp
    apply(rule minus_continuousSup)
    subgoal by blast
    subgoal by (simp add: acost.case_eq_if)
    done
  subgoal for x apply(cases x) by (auto simp: less_eq_acost_def zero_acost_def needname_nonneg)
  subgoal for x apply(cases x) by (auto simp: less_eq_acost_def times_acost_def zero_acost_def)
  subgoal for x apply(cases x) by (auto simp: less_eq_acost_def times_acost_def zero_acost_def)
  subgoal for x apply(cases x) by (auto simp: zero_acost_def needname_minus_absorb)
  subgoal for x apply(cases x) by (auto simp: zero_acost_def needname_plus_absorb)
  done
end



end