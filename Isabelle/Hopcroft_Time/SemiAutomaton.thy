(*  Title:       A theory of Semi-Automata
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

section \<open> Semi Automata \<close>

theory SemiAutomaton
imports Main LTS Accessible
        "HOL-Library.Nat_Bijection"
begin

text \<open> Semi Automata are finite automata without an acceptance condition. By adding an
acceptance condition one can get the classical nondeterministic, universal and deterministic
automata on finite words as well as omega automata like Buechi automata. \<close> 

subsection \<open> Basic Definitions \<close>

text \<open> The type of states of an automaton is unimportant most of the time. However,
it is important that one can always get a fresh state. This means that the type has to be infinite
and one can easily get access to new elements. This demand is expressed by the following 
class. \<close>

class automaton_states =
  fixes states_enumerate :: "nat \<Rightarrow> 'a"
  assumes states_enumerate_inj: "inj states_enumerate"
begin
  lemma states_enumerate_eq: "states_enumerate n = states_enumerate m \<longleftrightarrow> n = m"
    using states_enumerate_inj
    unfolding inj_on_def by auto

  lemma not_finite_automaton_states_UNIV : "~(finite (UNIV::'a set))"
  proof 
    assume fin_UNIV: "finite (UNIV::'a set)"
    hence "finite (states_enumerate ` UNIV)"
      by (rule_tac finite_subset[of _ UNIV], simp_all)
    hence "finite (UNIV::nat set)"
      using states_enumerate_inj
      by (rule finite_imageD)
    thus "False" using infinite_UNIV_nat by simp
  qed
end


instantiation nat :: automaton_states
begin
  definition "states_enumerate q = q"

  instance proof  
    show "inj (states_enumerate::nat \<Rightarrow> nat)"
      unfolding states_enumerate_nat_def[abs_def]
      by (simp add: inj_on_def)
  qed
end

text \<open> This theory defines finite semi-automata.
  These automata are represented as records containing a transtion relation, 
  a set of initial states.\<close>

record ('q,'a) SemiAutomaton_rec =
  \<Q> :: "'q set"          \<comment>\<open>The set of states\<close>
  \<Sigma> :: "'a set"          \<comment>\<open>The set of labels\<close>
  \<Delta> :: "('q,'a) LTS"     \<comment>\<open>The transition relation\<close>
  \<I> :: "'q set"           \<comment>\<open>The set of initial states\<close>

text \<open> Semi-Automata define sets of runs \<close>
definition SemiAutomaton_is_fin_run where
  "SemiAutomaton_is_fin_run \<A> w r \<longleftrightarrow>
   (hd r \<in> \<I> \<A>) \<and> LTS_is_fin_run (\<Delta> \<A>) w r"

lemma SemiAutomaton_is_fin_run_simps[simp] :
  "SemiAutomaton_is_fin_run \<A> w [] = False" 
  "SemiAutomaton_is_fin_run \<A> w [q] = (w = [] \<and> q \<in> (\<I> \<A>))" 
  "SemiAutomaton_is_fin_run \<A> [] r = (\<exists>q. r = [q] \<and> q \<in> (\<I> \<A>))"
unfolding SemiAutomaton_is_fin_run_def by (auto simp add: length_Suc_conv)

definition SemiAutomaton_is_inf_run where
  "SemiAutomaton_is_inf_run \<A> w r \<longleftrightarrow>
   (r 0 \<in> \<I> \<A>) \<and> LTS_is_inf_run (\<Delta> \<A>) w r"

subsubsection \<open> Wellformedness \<close>

text \<open> The following locales capture, whether a Semi-Automaton are well-formed. \<close>
locale SemiAutomaton =  
  fixes \<A>::"('q,'a, 'SemiAutomaton_more) SemiAutomaton_rec_scheme" 
  assumes \<Delta>_consistent: "\<And>q \<sigma> q'. (q,\<sigma>,q') \<in> \<Delta> \<A> \<Longrightarrow> (q \<in> \<Q> \<A>) \<and> (\<sigma> \<in> \<Sigma> \<A>) \<and> (q' \<in> \<Q> \<A>)"
      and \<I>_consistent: "\<I> \<A> \<subseteq> \<Q> \<A>"

locale FinSemiAutomaton = SemiAutomaton \<A>
  for \<A>::"('q,'a, 'SemiAutomaton_more) SemiAutomaton_rec_scheme" +
  assumes finite_\<Q>: "finite (\<Q> \<A>)"
      and finite_\<Delta>: "finite (\<Delta> \<A>)"

lemma FinSemiAutomaton_alt_def :
  "FinSemiAutomaton \<A> \<longleftrightarrow> SemiAutomaton \<A> \<and>  finite (\<Q> \<A>) \<and> finite (\<Delta> \<A>)"
unfolding FinSemiAutomaton_def FinSemiAutomaton_axioms_def by simp

lemma FinSemiAutomaton_full_def :
  "FinSemiAutomaton \<A> \<longleftrightarrow> 
   ((\<forall>q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<longrightarrow> q \<in> \<Q> \<A> \<and> \<sigma> \<in> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>) \<and>
     \<I> \<A> \<subseteq> \<Q> \<A> \<and> finite (\<Q> \<A>) \<and> finite (\<Delta> \<A>))"
unfolding FinSemiAutomaton_def FinSemiAutomaton_axioms_def SemiAutomaton_def
by simp

lemma SemiAutomaton_truncate[simp]:
 "SemiAutomaton (SemiAutomaton.truncate \<A>) \<longleftrightarrow> SemiAutomaton \<A>"
unfolding SemiAutomaton_def by (simp add: SemiAutomaton_rec.defs)

lemma FinSemiAutomaton_truncate[simp]:
 "FinSemiAutomaton (SemiAutomaton.truncate \<A>) \<longleftrightarrow> FinSemiAutomaton \<A>"
unfolding FinSemiAutomaton_full_def by (simp add: SemiAutomaton_rec.defs)

lemma FinSemiAutomaton_is_Semiautomaton :
  "FinSemiAutomaton \<A> \<Longrightarrow> SemiAutomaton \<A>"
unfolding FinSemiAutomaton_def by simp

lemma SemiAutomaton_intro [intro!] :
  " \<lbrakk>\<And>q \<sigma> q'. (q,\<sigma>,q') \<in> \<Delta> \<A> \<Longrightarrow> (q \<in> \<Q> \<A>) \<and> (\<sigma> \<in> \<Sigma> \<A>) \<and> (q' \<in> \<Q> \<A>);
     \<I> \<A> \<subseteq> \<Q> \<A>; finite (\<Q> \<A>); finite (\<Delta> \<A>)\<rbrakk> \<Longrightarrow> SemiAutomaton \<A>"
by (simp add: SemiAutomaton_def)

lemma (in FinSemiAutomaton) finite_\<I> :
  "finite (\<I> \<A>)"
using \<I>_consistent finite_\<Q>
by (metis finite_subset)

lemma (in SemiAutomaton) \<Delta>_subset :
"\<Delta> \<A> \<subseteq> \<Q> \<A> \<times> \<Sigma> \<A> \<times> \<Q> \<A>" 
using \<Delta>_consistent
by (simp add: subset_iff)

lemma (in SemiAutomaton) SemiAutomaton_\<Q>_not_empty:
  assumes "SemiAutomaton_is_inf_run \<A> w r"
    shows "\<Q>(\<A>) \<noteq> {}"
using assms SemiAutomaton_is_inf_run_def[of \<A> w r] \<I>_consistent by auto

lemma (in SemiAutomaton) SemiAutomaton_\<Delta>_cons___is_fin_run_LTS :
assumes run: "LTS_is_fin_run (\<Delta> \<A>) w r"
    and wr_OK: "w \<noteq> [] \<or> hd r \<in> \<Q> \<A>"
shows "w \<in> lists (\<Sigma> \<A>)" "r \<in> lists (\<Q> \<A>)"
proof -
  from run \<Delta>_consistent have
    wr_in: "\<And>i. i < length w \<Longrightarrow> w ! i \<in> \<Sigma> \<A> \<and> r ! i \<in> \<Q> \<A> \<and> r ! (Suc i) \<in> \<Q> \<A>" and
    len_eq: "length r = Suc (length w)"
    unfolding LTS_is_fin_run_def by auto

  from wr_in show "w \<in> lists (\<Sigma> \<A>)" 
    unfolding in_lists_conv_set Ball_def in_set_conv_nth by metis

  have "\<And>i. i < length r \<Longrightarrow> r ! i \<in> \<Q> \<A>"
  proof -
    fix i 
    assume i_less: "i < length r"
    show "r ! i \<in> \<Q> \<A>"
    proof (cases "i < length w")
      case True with wr_in show ?thesis by simp
    next
      case False with i_less len_eq
      have i_eq: "i = length w" by auto

      show ?thesis
      proof (cases w)
        case Nil with i_eq wr_OK len_eq show ?thesis by (cases r, simp_all)
      next
        case (Cons q w')
        with wr_in[of "length w'"] i_eq show ?thesis by simp
      qed
    qed
  qed
  thus "r \<in> lists (\<Q> \<A>)" 
    unfolding in_lists_conv_set Ball_def in_set_conv_nth by metis
qed

lemma (in SemiAutomaton) SemiAutomaton_\<Delta>_cons___is_fin_run :
assumes run: "SemiAutomaton_is_fin_run \<A> w r"
shows "w \<in> lists (\<Sigma> \<A>)" "r \<in> lists (\<Q> \<A>)"
using SemiAutomaton_\<Delta>_cons___is_fin_run_LTS[of w r] run
      \<I>_consistent
unfolding SemiAutomaton_is_fin_run_def by auto

lemma (in SemiAutomaton) SemiAutomaton_\<Delta>_cons___LTS_is_reachable :
  "\<lbrakk>LTS_is_reachable (\<Delta> \<A>) q w q'\<rbrakk> \<Longrightarrow> (q \<in> \<Q> \<A> \<longrightarrow> q' \<in> \<Q> \<A>) \<and> w \<in> lists (\<Sigma> \<A>)"
using \<Delta>_consistent
apply (induct w arbitrary: q)
apply auto
done

lemma (in SemiAutomaton) LTS_is_reachable___labels :
  "LTS_is_reachable (\<Delta> \<A>) q w q' \<Longrightarrow> w \<in> lists (\<Sigma> \<A>)"
by (simp add: SemiAutomaton_\<Delta>_cons___LTS_is_reachable)

lemma (in SemiAutomaton) SemiAutomaton_\<Delta>_cons___is_inf_run_LTS :
assumes run: "LTS_is_inf_run (\<Delta> \<A>) w r"
shows "w i \<in> (\<Sigma> \<A>)" "r i \<in> (\<Q> \<A>)"
using run \<Delta>_consistent 
unfolding LTS_is_inf_run_def by auto

lemma (in SemiAutomaton) SemiAutomaton_\<Delta>_cons___is_inf_run :
assumes run: "SemiAutomaton_is_inf_run \<A> w r"
shows "w i \<in> (\<Sigma> \<A>)" "r i \<in> (\<Q> \<A>)"
using SemiAutomaton_\<Delta>_cons___is_inf_run_LTS[of w r i] run
unfolding SemiAutomaton_is_inf_run_def by simp_all

lemma (in SemiAutomaton) LTS_is_reachable_from_initial_alt_def :
  "accessible (LTS_forget_labels (\<Delta> \<A>)) (\<I> \<A>) =
   {q'. (\<exists> q\<in> (\<I> \<A>). \<exists>w. LTS_is_reachable (\<Delta> \<A>) q w q')}"
by (simp add: accessible_def rtrancl_LTS_forget_labels)

lemma (in SemiAutomaton) LTS_is_reachable_from_initial_subset :
  "accessible (LTS_forget_labels (\<Delta> \<A>)) (\<I> \<A>) \<subseteq> \<Q> \<A>"
using SemiAutomaton_\<Delta>_cons___LTS_is_reachable \<I>_consistent
unfolding LTS_is_reachable_from_initial_alt_def
by auto

lemma (in FinSemiAutomaton) LTS_is_reachable_from_initial_finite :
  "finite (accessible (LTS_forget_labels (\<Delta> \<A>)) (\<I> \<A>))"
using LTS_is_reachable_from_initial_subset finite_\<Q>
by (rule finite_subset)


subsection \<open> Determistic, complete Semiautomata \<close>

definition SemiAutomaton_is_deterministic where
  "SemiAutomaton_is_deterministic \<A> \<equiv> (LTS_is_deterministic (\<Delta> \<A>) \<and> (\<exists>q0. \<I> \<A> = {q0}))"

definition SemiAutomaton_is_complete_deterministic where
  "SemiAutomaton_is_complete_deterministic \<A> \<equiv>
   (LTS_is_complete_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>) \<and> (\<exists>q0. \<I> \<A> = {q0}))"

lemma SemiAutomaton_is_complete_deterministic_alt_def :
  "SemiAutomaton_is_complete_deterministic \<A> = (LTS_is_complete (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>) \<and> SemiAutomaton_is_deterministic \<A>)"
  unfolding SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def SemiAutomaton_is_deterministic_def
  by blast

locale DetSemiAutomaton = SemiAutomaton \<A>
  for \<A>::"('q,'a, 'SemiAutomaton_more) SemiAutomaton_rec_scheme" +
  assumes complete_deterministic_SemiAutomaton: "SemiAutomaton_is_complete_deterministic \<A>"

lemma DetSemiAutomaton_alt_def :
  "DetSemiAutomaton \<A> = (SemiAutomaton \<A> \<and> SemiAutomaton_is_complete_deterministic \<A>)"
unfolding DetSemiAutomaton_def DetSemiAutomaton_axioms_def by simp

lemma SemiAutomaton_is_complete_deterministic_truncate [simp] :
  "SemiAutomaton_is_complete_deterministic (SemiAutomaton.truncate \<A>) = 
   SemiAutomaton_is_complete_deterministic \<A>"
unfolding SemiAutomaton_is_complete_deterministic_def 
by (simp add: SemiAutomaton_rec.defs)

lemma DetSemiAutomaton_truncate [simp] :
  "DetSemiAutomaton (SemiAutomaton.truncate \<A>) = DetSemiAutomaton \<A>"
unfolding DetSemiAutomaton_alt_def by simp

locale DetFinSemiAutomaton = FinSemiAutomaton \<A> +
                             DetSemiAutomaton \<A>
  for \<A>::"('q,'a, 'SemiAutomaton_more) SemiAutomaton_rec_scheme"

lemma DetFinSemiAutomaton_alt_def :
  "DetFinSemiAutomaton \<A> = (FinSemiAutomaton \<A> \<and> DetSemiAutomaton \<A>)"
unfolding DetFinSemiAutomaton_def by simp

lemma DetFinSemiAutomaton_truncate [simp] :
  "DetFinSemiAutomaton (SemiAutomaton.truncate \<A>) = DetFinSemiAutomaton \<A>"
unfolding DetFinSemiAutomaton_alt_def
by simp

lemma (in DetSemiAutomaton) complete_LTS: "LTS_is_complete (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>)"
  using complete_deterministic_SemiAutomaton
  unfolding SemiAutomaton_is_complete_deterministic_alt_def 
  by simp

lemma (in DetSemiAutomaton) deterministic_SemiAutomaton: "SemiAutomaton_is_deterministic \<A>"
  using complete_deterministic_SemiAutomaton
  unfolding SemiAutomaton_is_complete_deterministic_alt_def 
  by simp

lemma (in DetSemiAutomaton) complete_deterministic_LTS: "LTS_is_complete_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>)"
  using complete_deterministic_SemiAutomaton
  unfolding SemiAutomaton_is_complete_deterministic_alt_def
            LTS_is_complete_deterministic_def SemiAutomaton_is_deterministic_def 
  by simp

lemma (in DetSemiAutomaton) deterministic_LTS: "LTS_is_deterministic (\<Delta> \<A>)"
  using complete_deterministic_LTS
  unfolding LTS_is_complete_deterministic_def
  by simp
 
lemma (in DetSemiAutomaton) unique_initial : "\<exists>! x. x \<in> \<I> \<A>"
using deterministic_SemiAutomaton unfolding SemiAutomaton_is_deterministic_def by (auto) 

lemma (in DetFinSemiAutomaton) finite_\<Sigma>I: 
  assumes "\<Q> \<A> \<noteq> {}"
  shows "finite (\<Sigma> \<A>)"
proof -
  note complete_deterministic_LTS
  hence "LTS_is_complete (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>)"
    by (simp add: LTS_is_complete_deterministic_def)
  with assms have "\<Sigma> \<A> \<subseteq> (\<lambda>(q,a,q'). a) ` \<Delta> \<A>"
    unfolding LTS_is_complete_def
    by (fastforce split: prod.split)
  with finite_subset finite_\<Delta> show ?thesis by blast
qed

definition \<i> where "\<i> \<A> \<equiv> SOME q. q \<in> \<I> \<A>"

lemma (in DetSemiAutomaton) \<I>_is_set_\<i> [simp] : "\<I> \<A> = {\<i> \<A>}"
proof -
  obtain x where x: "\<I> \<A> = {x}" using unique_initial by blast
  then show "\<I> \<A> = {\<i> \<A>}" unfolding \<i>_def by simp
qed

lemma (in DetSemiAutomaton) \<i>_is_state : "\<i> \<A> \<in> \<Q> \<A>" using \<I>_consistent by simp
lemma (in DetSemiAutomaton) \<Q>_not_Emp: "\<Q> \<A> \<noteq> {}" using \<i>_is_state by auto

subsubsection \<open> The unique transition function \<close>

definition \<delta> where "\<delta> \<A> \<equiv> LTS_to_DLTS (\<Delta> \<A>)"

lemma (in DetSemiAutomaton) \<delta>_to_\<Delta> [simp] : "DLTS_to_LTS (\<delta> \<A>) = \<Delta> \<A>"
  by (simp add: \<delta>_def LTS_to_DLTS_inv deterministic_LTS)

lemma (in DetSemiAutomaton) \<delta>_in_\<Delta>_iff :
  "(q, \<sigma>, q') \<in> \<Delta> \<A> \<longleftrightarrow> (\<delta> \<A>) (q, \<sigma>) = Some q'"
unfolding \<delta>_def 
by (simp add: LTS_to_DLTS_is_some_det deterministic_LTS)

lemma (in DetSemiAutomaton) \<delta>_wf :
  assumes "\<delta> \<A> (q,\<sigma>) = Some q'" 
  shows "q \<in> \<Q> \<A> \<and> (\<sigma> \<in> \<Sigma> \<A>) \<and> (q' \<in> \<Q> \<A>)"
using assms
by (simp add: \<delta>_in_\<Delta>_iff [symmetric] \<Delta>_consistent)

subsubsection \<open> Lemmas about deterministic semiautomata \<close>

lemma (in DetSemiAutomaton) DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp :
  "LTS_is_reachable (\<Delta> \<A>) q w q' \<longleftrightarrow> (DLTS_reach (\<delta> \<A>) q w = Some q')"
by (simp add: LTS_is_reachable_determistic deterministic_LTS \<delta>_def)

lemma (in DetSemiAutomaton) DetSemiAutomaton_LTS_is_reachable_unique :
  "\<lbrakk>LTS_is_reachable (\<Delta> \<A>) q w q'; LTS_is_reachable (\<Delta> \<A>) q w q''\<rbrakk> \<Longrightarrow> q'' = q'"
by (simp add: DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp)

lemma (in DetSemiAutomaton) DetSemiAutomaton_\<delta>_is_none_iff :
  "(\<delta> \<A> (q, \<sigma>) = None) \<longleftrightarrow> \<not> (q \<in> \<Q> \<A> \<and> \<sigma> \<in> \<Sigma> \<A>)"
apply (insert complete_LTS)
apply (simp add: \<delta>_def LTS_to_DLTS_def LTS_is_complete_def)
apply (auto simp add: \<Delta>_consistent)
done

lemma (in DetSemiAutomaton) DetSemiAutomaton_\<delta>_is_some :
  "\<lbrakk>q \<in> \<Q> \<A>; \<sigma> \<in> \<Sigma> \<A>\<rbrakk> \<Longrightarrow> \<not> (\<delta> \<A> (q, \<sigma>) = None)"
by (simp add: DetSemiAutomaton_\<delta>_is_none_iff)

lemma (in DetSemiAutomaton) DetSemiAutomaton_reach_is_none_iff :
  "DLTS_reach (\<delta> \<A>) q w = None \<longleftrightarrow> \<not>((w \<noteq> [] --> q \<in> \<Q> \<A>) \<and> w \<in> lists (\<Sigma> \<A>))"
proof (induct w arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> w)
  note ind_hyp = this

  show ?case 
  proof (cases "\<delta> \<A> (q, \<sigma>)")
    case None thus ?thesis by (simp, auto simp add: DetSemiAutomaton_\<delta>_is_none_iff)
  next
    case (Some q') note \<delta>_eq = this
    hence "q \<in> \<Q> \<A> \<and> \<sigma> \<in> \<Sigma> \<A> \<and> q' \<in> \<Q> \<A>" by (simp add: \<delta>_wf)
    with \<delta>_eq show ?thesis by (simp add: ind_hyp)
  qed
qed

primrec DetSemiAutomaton_fin_run where
  "DetSemiAutomaton_fin_run \<A> q [] = [q]"
| "DetSemiAutomaton_fin_run \<A> q (a # w) =
   q # DetSemiAutomaton_fin_run \<A> (the (\<delta> \<A> (q, a))) w"

lemma (in DetSemiAutomaton) DetSemiAutomaton_fin_run_alt_def :
assumes w_OK: "w \<in> lists (\<Sigma> \<A>)"
    and q_OK: "q \<in> \<Q> \<A>"
shows "DetSemiAutomaton_fin_run \<A> q w = CLTS_fin_run (\<Q> \<A>) (\<Delta> \<A>) q w"
using w_OK q_OK
proof (induct w arbitrary: q)
  case Nil thus ?case unfolding DetSemiAutomaton_fin_run_def by simp
next
  case (Cons a w) 
  note aw_OK = Cons(1,2)
  note indhyp = Cons(3)
  note q_OK = Cons(4)
  
  from complete_LTS aw_OK(1) q_OK \<delta>_in_\<Delta>_iff [of q a] obtain q' where
    \<delta>_eq: "\<delta> \<A> (q, a) = Some q'" and
    q'_in: "q' \<in> \<Q> \<A>"
    unfolding LTS_is_complete_def by metis

  have \<delta>_eq': "(SOME q'. (q, a, q') \<in> \<Delta> \<A> \<and> q' \<in> \<Q> \<A>) = q'" 
    apply (simp add: \<delta>_in_\<Delta>_iff \<delta>_eq)
    apply (rule some_equality)
    apply (simp_all add: q'_in)
  done

  from indhyp [OF q'_in]
  show ?case by (simp add: \<delta>_eq \<delta>_eq')
qed

primrec DetSemiAutomaton_inf_run where
  "DetSemiAutomaton_inf_run \<A> q w 0 = q"
| "DetSemiAutomaton_inf_run \<A> q w (Suc i) =
   the (\<delta> \<A> (DetSemiAutomaton_inf_run \<A> q w i, w i))"

lemma (in DetSemiAutomaton) DetSemiAutomaton_inf_run_alt_def :
assumes w_OK: "\<And>i. w i \<in> (\<Sigma> \<A>)"
    and q_OK: "q \<in> \<Q> \<A>"
shows "DetSemiAutomaton_inf_run \<A> q w = CLTS_inf_run (\<Q> \<A>) (\<Delta> \<A>) q w"
proof -
  { fix i 
    have "DetSemiAutomaton_inf_run \<A> q w i = CLTS_inf_run (\<Q> \<A>) (\<Delta> \<A>) q w i"
    proof (induct i)
      case 0 thus ?case by simp
    next
      case (Suc i) note indhyp = this

      define qq where "qq \<equiv> CLTS_inf_run (\<Q> \<A>) (\<Delta> \<A>) q w i"

      from CLTS_inf_run_correct(2)[OF complete_LTS, of w q i, OF w_OK q_OK]
      have qq_in: "qq \<in> \<Q> \<A>" unfolding qq_def .

      from complete_LTS w_OK[of i] qq_in \<delta>_in_\<Delta>_iff [of qq "w i"] obtain qq' where
          \<delta>_eq: "\<delta> \<A> (qq, w i) = Some qq'" and
          qq'_in: "qq' \<in> \<Q> \<A>"
        unfolding LTS_is_complete_def by metis

      have \<delta>_eq': "(SOME q'. (qq, w i, q') \<in> \<Delta> \<A> \<and> q' \<in> \<Q> \<A>) = qq'" 
        apply (simp add: \<delta>_in_\<Delta>_iff \<delta>_eq)
        apply (rule some_equality)
        apply (simp_all add: qq'_in)
      done

      show ?case by (simp add: qq_def[symmetric] indhyp \<delta>_eq \<delta>_eq')
    qed
  } 
  thus ?thesis by auto
qed

lemma (in DetSemiAutomaton) DetSemiAutomaton_fin_run_correct :
  "SemiAutomaton_is_fin_run \<A> w r \<longleftrightarrow>
   w \<in> lists (\<Sigma> \<A>) \<and> r = DetSemiAutomaton_fin_run \<A> (\<i> \<A>) w"
proof (cases "w \<in> lists (\<Sigma> \<A>)")
  case False thus ?thesis
    by (metis SemiAutomaton_\<Delta>_cons___is_fin_run(1))
next
  case True note w_in = this

  note detSemi_run_eq = DetSemiAutomaton_fin_run_alt_def[OF w_in \<i>_is_state]
  note fin_run_rule = CDLTS_fin_run_correct [OF complete_deterministic_LTS w_in, of r]

  show ?thesis
    unfolding DetSemiAutomaton_fin_run_alt_def detSemi_run_eq
    apply (simp add: w_in SemiAutomaton_is_fin_run_def)
    apply (metis \<i>_is_state fin_run_rule hd_CLTS_fin_run)
  done
qed

lemma (in DetSemiAutomaton) DetSemiAutomaton_inf_run_correct :
  "SemiAutomaton_is_inf_run \<A> w r \<longleftrightarrow>
   (\<forall>i. w i \<in> (\<Sigma> \<A>)) \<and> r = DetSemiAutomaton_inf_run \<A> (\<i> \<A>) w"
proof (cases "\<forall>i. w i \<in> (\<Sigma> \<A>)")
  case False thus ?thesis
    by (metis SemiAutomaton_\<Delta>_cons___is_inf_run(1))
next
  case True note w_in = this

  note detSemi_run_eq = DetSemiAutomaton_inf_run_alt_def[of w, OF _ \<i>_is_state]
  note inf_run_rule = CDLTS_inf_run_correct [OF complete_deterministic_LTS, of w r]

  show ?thesis
    apply (simp add: w_in SemiAutomaton_is_inf_run_def detSemi_run_eq)
    apply (metis CDLTS_inf_run_correct CLTS_inf_run.simps(1) True \<i>_is_state complete_deterministic_LTS)
  done
qed
 
lemma (in DetSemiAutomaton) DetSemiAutomaton_DLTS_reach_is_some :
  "\<lbrakk>q \<in> \<Q> \<A>; w \<in> lists (\<Sigma> \<A>)\<rbrakk> \<Longrightarrow> \<not> (DLTS_reach (\<delta> \<A>) q w = None)"
by (simp add: DetSemiAutomaton_reach_is_none_iff)

lemma (in DetSemiAutomaton) DetSemiAutomaton_DLTS_reach_wf : "\<lbrakk> q \<in> \<Q> \<A>; DLTS_reach (\<delta> \<A>) q w = Some q'\<rbrakk> \<Longrightarrow>  q' \<in> \<Q> \<A> \<and>
w \<in> lists (\<Sigma> \<A>)"
by (simp add: DetSemiAutomaton_LTS_is_reachable_DLTS_reach_simp [symmetric] SemiAutomaton_\<Delta>_cons___LTS_is_reachable)


subsection \<open> Constructing from a list representation \<close>

fun construct_SemiAutomaton_aux where 
   "construct_SemiAutomaton_aux \<A> (q1, l, q2) =
    \<lparr> \<Q>=insert q1 (insert q2 (\<Q> \<A>)),
      \<Sigma>=\<Sigma> \<A> \<union> set l,
      \<Delta>=\<Delta> \<A> \<union> { (q1,a,q2) | a. a \<in> set l}, 
      \<I> = \<I> \<A>\<rparr>"

fun SemiAutomaton_construct where
   "SemiAutomaton_construct (Q, A, D, I) =
    foldl construct_SemiAutomaton_aux 
    \<lparr> \<Q>=set (Q @ I), \<Sigma>=set A, \<Delta>={}, \<I> =set I \<rparr> D"
declare SemiAutomaton_construct.simps [simp del]

(* TODO: Move to Misc.thy *)
lemma foldl_fun_comm:
  assumes "\<And>x y s. f (f s x) y = f (f s y) x"
  shows "f (foldl f s xs) x = foldl f (f s x) xs"
  by (induct xs arbitrary: s)
    (simp_all add: assms)

lemma SemiAutomaton_construct_alt_def :
  "SemiAutomaton_construct (Q, A, D, I) =
   \<lparr> \<Q>=set Q \<union> set I \<union>
       set (map fst D) \<union>
       set (map (snd \<circ> snd) D), \<Sigma>=set A \<union> \<Union> (set (map (set \<circ> fst \<circ> snd) D)),
       \<Delta> = { (q1,a,q2) . (\<exists>l. (q1, l, q2) \<in> set D \<and> a \<in> set l)}, \<I> = set I\<rparr>"
proof (induct D)
  case Nil thus ?case by (auto simp add: SemiAutomaton_construct.simps)
next
  case (Cons qlq D)

  have fold_lemma: "\<And>\<A>. foldl construct_SemiAutomaton_aux (construct_SemiAutomaton_aux \<A> qlq) D =
            construct_SemiAutomaton_aux (foldl construct_SemiAutomaton_aux \<A> D) qlq"
    by (rule_tac foldl_fun_comm [symmetric], auto)

  obtain q1 l q2 where qlq_eq : "qlq = (q1, l, q2)" by (cases qlq, auto)

  from Cons fold_lemma show ?case 
    by (simp add: SemiAutomaton_construct.simps, auto simp add: qlq_eq)
qed

fun SemiAutomaton_construct_simple where
  "SemiAutomaton_construct_simple (Q, A, D, I) =
   SemiAutomaton_construct (Q, A, map (\<lambda>(q1, a, q2). (q1, [a], q2)) D, I)" 

lemma SemiAutomaton_construct___is_well_formed :
  "FinSemiAutomaton (SemiAutomaton_construct l)"
proof -
  obtain Q A D I where l_eq[simp]: "l = (Q, A, D, I)"
    using prod_cases4 by blast

  { fix q \<sigma> q'
    assume "(q, \<sigma>, q') \<in> \<Delta> (SemiAutomaton_construct (Q, A, D, I))"
    then obtain l where in_D: "(q, l, q') \<in> set D" and
                       in_l: "\<sigma> \<in> set l" by (auto simp add: SemiAutomaton_construct_alt_def)

    from in_D have p1: "q \<in> fst ` set D" by (metis fst_conv imageI) 
    from in_l have p2: "\<sigma> \<in> set (fst (snd (q, l, q')))" by simp
    from in_D have p3: "q' \<in> (snd \<circ> snd) ` set D"
      by (metis imageI image_comp snd_conv)

    note p1 p3
  } 
  moreover define f where "f \<equiv> \<lambda>(q::'a,l::'b list,q'::'a). {(q,a,q') | a. a \<in> set l}"
  hence  "\<Delta> (SemiAutomaton_construct (Q, A, D, I)) = \<Union>(f ` set D)"
    unfolding SemiAutomaton_construct_alt_def
    by auto
  hence "finite (\<Delta> (SemiAutomaton_construct (Q, A, D, I)))"
    by (auto simp add: f_def)

  ultimately show ?thesis
    apply (auto simp add: SemiAutomaton_construct_alt_def FinSemiAutomaton_full_def Ball_def) 
    apply metis
  done
qed 

lemma SemiAutomaton_construct_exists :
fixes \<A> :: "('q, 'a) SemiAutomaton_rec"
assumes wf_A: "FinSemiAutomaton \<A>"
  and fin\<Sigma>: "finite (\<Sigma> \<A>)"
shows "\<exists>Q A D I. \<A> = SemiAutomaton_construct (Q, A, D, I)"
proof -
  interpret SemiAutomaton_A: FinSemiAutomaton \<A> by (fact wf_A)
  from finite_list[OF SemiAutomaton_A.finite_\<Q>] obtain Q where "set Q = \<Q> \<A>" .. note set_Q = this
  from finite_list[OF SemiAutomaton_A.finite_\<I>] obtain I where "set I = \<I> \<A>" .. note set_I = this 
  from finite_list[OF fin\<Sigma>] obtain A where "set A = \<Sigma> \<A>" .. note set_A = this 
  from finite_list[OF SemiAutomaton_A.finite_\<Delta>] obtain DD where "set DD = \<Delta> \<A>" .. note set_DD = this 

  let ?D = "map (\<lambda>qaq. (fst qaq, [fst (snd qaq)], snd (snd qaq))) DD"

  have "\<A> = SemiAutomaton_construct (Q, A, ?D, I)"
    apply (rule SemiAutomaton_rec.equality)
    apply (simp_all add: SemiAutomaton_construct_alt_def set_Q set_I set_A set_DD o_def)
        apply (insert SemiAutomaton_A.\<Delta>_consistent SemiAutomaton_A.\<I>_consistent) []
        apply auto[]
      apply (insert SemiAutomaton_A.\<Delta>_consistent) []
      apply auto []
    apply (simp del: ex_simps add: image_iff Bex_def ex_simps[symmetric])
  done
  thus ?thesis by blast
qed

subsection \<open> Removing states \<close>
  
definition SemiAutomaton_remove_states :: "('q, 'a, 'x) SemiAutomaton_rec_scheme \<Rightarrow> 'q set \<Rightarrow> ('q, 'a) SemiAutomaton_rec" where
"SemiAutomaton_remove_states \<A> S == \<lparr> \<Q>=\<Q> \<A> - S, \<Sigma>=\<Sigma> \<A>, \<Delta> = { (s1,a,s2) . (s1,a,s2) \<in> \<Delta> \<A> \<and> s1 \<notin> S \<and> s2 \<notin> S}, \<I> = \<I> \<A> - S \<rparr>"

lemma [simp] : "\<I> (SemiAutomaton_remove_states \<A> S) = \<I> \<A> - S" by (simp add: SemiAutomaton_remove_states_def)
lemma [simp] : "\<Q> (SemiAutomaton_remove_states \<A> S) = \<Q> \<A> - S" by (simp add: SemiAutomaton_remove_states_def)
lemma [simp] : "\<Sigma> (SemiAutomaton_remove_states \<A> S) = \<Sigma> \<A>" by (simp add: SemiAutomaton_remove_states_def)
lemma [simp] : "x \<in> \<Delta> (SemiAutomaton_remove_states \<A> S) \<longleftrightarrow> 
                x \<in> \<Delta> \<A> \<and> fst x \<notin> S \<and> snd (snd x) \<notin> S" by (cases x, simp add: SemiAutomaton_remove_states_def)

lemma SemiAutomaton_remove_states_\<Delta>_subset : "\<Delta> (SemiAutomaton_remove_states \<A> S) \<subseteq> \<Delta> \<A>" by (simp add: subset_iff)
lemma SemiAutomaton_remove_states___is_well_formed : "SemiAutomaton \<A> \<Longrightarrow> SemiAutomaton (SemiAutomaton_remove_states \<A> S)" by (auto simp add: SemiAutomaton_def)

lemma SemiAutomaton_remove_states_empty [simp] : "SemiAutomaton_remove_states \<A> {} = \<A>"
  by (rule SemiAutomaton_rec.equality, simp_all add: SemiAutomaton_remove_states_def)

lemma SemiAutomaton_remove_states_SemiAutomaton_remove_states [simp] : "SemiAutomaton_remove_states (SemiAutomaton_remove_states \<A> S1) S2 = 
  SemiAutomaton_remove_states \<A> (S1 \<union> S2)"
  by (rule SemiAutomaton_rec.equality, auto simp add: SemiAutomaton_remove_states_def)


lemma SemiAutomaton_remove_states_fin_run_LTS_impl : 
  "LTS_is_fin_run (\<Delta> (SemiAutomaton_remove_states \<A> S)) w r \<Longrightarrow>
   LTS_is_fin_run (\<Delta> \<A>) w r"
  by (simp add: LTS_is_fin_run_def)

lemma SemiAutomaton_remove_states_reachable_impl : 
  "LTS_is_reachable (\<Delta> (SemiAutomaton_remove_states \<A> S)) q1 w q2 \<Longrightarrow>
   LTS_is_reachable (\<Delta> \<A>) q1 w q2"
  unfolding LTS_is_reachable_alt_def
  by (metis SemiAutomaton_remove_states_fin_run_LTS_impl)

lemma SemiAutomaton_remove_states_inf_run_LTS_impl : 
  "LTS_is_inf_run (\<Delta> (SemiAutomaton_remove_states \<A> S)) w r \<Longrightarrow>
   LTS_is_inf_run (\<Delta> \<A>) w r"
  by (simp add: LTS_is_inf_run_def)

lemma SemiAutomaton_remove_states_fin_run_LTS_eq : 
assumes Q_unreach: "\<And>q'. q'\<in>Q \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) (hd r) q'"
shows "LTS_is_fin_run (\<Delta> (SemiAutomaton_remove_states \<A> Q)) w r = 
       LTS_is_fin_run (\<Delta> \<A>) w r"
      (is "?ls = ?rs")
proof (rule iffI)
  assume ?ls thus ?rs by (rule SemiAutomaton_remove_states_fin_run_LTS_impl)
next
  assume rs: ?rs
  with Q_unreach show ?ls
  proof (induct w arbitrary: r)
    case Nil thus ?case by simp
  next
    case (Cons a w')
    note indhyp = Cons(1)
    note Q_unreach = Cons(2)
    note inf_run = Cons(3)

    from inf_run obtain r1 r2 r' where r_eq[simp]: "r = r1 # r2 # r'" 
      by (cases r, simp, rename_tac qq r'', case_tac r'', auto)
    have hd_r_eq: "hd r = r1" by simp

    from inf_run have step: "(r1, a, r2) \<in> \<Delta> \<A>" and
         inf_run': "LTS_is_fin_run (\<Delta> \<A>) w' (r2 # r')" by simp_all

    have Q_unreach': "\<And>q'. q' \<in> Q \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) (hd (r2 # r')) q'"
    proof -
      fix q'
      assume "q' \<in> Q"

      from step have "LTS_is_reachable (\<Delta> \<A>) r1 [a] r2" by simp
      with Q_unreach[OF `q' \<in> Q`, unfolded hd_r_eq] show "LTS_is_unreachable (\<Delta> \<A>) (hd (r2 # r')) q'"
        by (simp, rule LTS_is_unreachable_reachable_start)
    qed

    from Q_unreach[of r1] have q_nin_Q: "r1 \<notin> Q" by auto
    from Q_unreach'[of r2] have r1_nin_Q: "r2 \<notin> Q" by auto

    from indhyp[OF Q_unreach' inf_run']
    show ?case by (simp add: q_nin_Q r1_nin_Q step)
  qed
qed

lemma SemiAutomaton_remove_states_inf_run_LTS_eq : 
assumes Q_unreach: "\<And>q'. q'\<in>Q \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) (r 0) q'"
shows "LTS_is_inf_run (\<Delta> (SemiAutomaton_remove_states \<A> Q)) w r = 
       LTS_is_inf_run (\<Delta> \<A>) w r"
      (is "?ls = ?rs")
proof (rule iffI)
  assume ?ls thus ?rs by (rule SemiAutomaton_remove_states_inf_run_LTS_impl)
next
  assume rs: ?rs

  have "\<And>i. r i \<notin> Q"
  proof -
    fix i
    from LTS_is_inf_run___is_unreachable[OF rs, of 0 i] 
    have "\<not> LTS_is_unreachable (\<Delta> \<A>) (r 0) (r i)" by simp
    with Q_unreach show "r i \<notin> Q" by auto
  qed
  with rs show ?ls
    unfolding LTS_is_inf_run_def by simp
qed

lemma SemiAutomaton_remove_states_reachable_eq : 
assumes Q_unreach: "\<And>q'. q'\<in>Q \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) q1 q'"
shows "LTS_is_reachable (\<Delta> (SemiAutomaton_remove_states \<A> Q)) q1 w q2 \<longleftrightarrow>
   LTS_is_reachable (\<Delta> \<A>) q1 w q2"
    unfolding LTS_is_reachable_alt_def
by (metis Q_unreach SemiAutomaton_remove_states_fin_run_LTS_eq)

definition SemiAutomaton_unreachable_states where
  "SemiAutomaton_unreachable_states \<A> = {q'. \<forall>q\<in>\<I> \<A>. LTS_is_unreachable (\<Delta> \<A>) q q'}"

lemma SemiAutomaton_unreachable_states_extend :
  "\<lbrakk>x \<notin> SemiAutomaton_unreachable_states \<A>; (x, \<sigma>, q') \<in> \<Delta> \<A>\<rbrakk> \<Longrightarrow> q' \<notin> SemiAutomaton_unreachable_states \<A>"
proof
  assume "x \<notin> SemiAutomaton_unreachable_states \<A>"
  then obtain w q where 
     reach_x: "LTS_is_reachable (\<Delta> \<A>) q w x" and
     q_in_I: "q \<in> \<I> \<A>" 
  by (auto simp add: SemiAutomaton_unreachable_states_def LTS_is_unreachable_def)
   
  assume "(x, \<sigma>, q') \<in> \<Delta> \<A>" 
  with reach_x have reach_q' : "LTS_is_reachable (\<Delta> \<A>) q (w @ [\<sigma>]) q'" by auto
   
  assume "q' \<in> SemiAutomaton_unreachable_states \<A>" 
  thus "False"
    by (simp add: SemiAutomaton_unreachable_states_def LTS_is_unreachable_def,
        metis q_in_I reach_q')
qed

definition SemiAutomaton_is_initially_connected where
  "SemiAutomaton_is_initially_connected \<A> \<longleftrightarrow> \<Q> \<A> \<inter> SemiAutomaton_unreachable_states \<A> = {}"

lemma SemiAutomaton_is_initially_connected_truncate [simp]:
  "SemiAutomaton_is_initially_connected (SemiAutomaton.truncate \<A>) \<longleftrightarrow>
   SemiAutomaton_is_initially_connected \<A>"
unfolding SemiAutomaton_is_initially_connected_def
          SemiAutomaton_unreachable_states_def
by (simp add: SemiAutomaton_rec.defs)

lemma SemiAutomaton_is_initially_connected_alt_def :
  "SemiAutomaton_is_initially_connected \<A> \<longleftrightarrow> (\<forall>q \<in> \<Q> \<A>. 
   \<exists>i\<in>\<I> \<A>. \<exists>w. LTS_is_reachable (\<Delta> \<A>) i w q)"
unfolding SemiAutomaton_is_initially_connected_def
by (auto simp add: set_eq_iff SemiAutomaton_unreachable_states_def LTS_is_unreachable_def)

lemma SemiAutomaton_not_in_unreachable_states_run :
  "q \<notin> SemiAutomaton_unreachable_states \<A> \<longleftrightarrow>
   (\<exists>w r. SemiAutomaton_is_fin_run \<A> w r \<and> last r = q)"
unfolding SemiAutomaton_unreachable_states_def LTS_is_unreachable_def LTS_is_reachable_alt_def
          SemiAutomaton_is_fin_run_def
by auto

definition SemiAutomaton_remove_unreachable_states where
  "SemiAutomaton_remove_unreachable_states \<A> = SemiAutomaton_remove_states \<A> (SemiAutomaton_unreachable_states \<A>)"

lemma SemiAutomaton_remove_unreachable_states___is_well_formed [simp] : 
"SemiAutomaton \<A> \<Longrightarrow> SemiAutomaton (SemiAutomaton_remove_unreachable_states \<A>)"
by (simp add: SemiAutomaton_remove_unreachable_states_def SemiAutomaton_remove_states___is_well_formed)

lemma SemiAutomaton_unreachable_states_\<I> :
  "q \<in> \<I> \<A> \<Longrightarrow> q \<notin> SemiAutomaton_unreachable_states \<A>"
proof -
   have f1: "LTS_is_reachable (\<Delta> \<A>) q [] q \<and> [] \<in> lists (\<Sigma> \<A>)" by simp
   show "q \<in> \<I> \<A> \<Longrightarrow> q \<notin> SemiAutomaton_unreachable_states \<A>"  
     by (simp add: SemiAutomaton_unreachable_states_def LTS_is_unreachable_def, metis f1)
qed

lemma SemiAutomaton_remove_unreachable_states_\<I> [simp] :
  "\<I> (SemiAutomaton_remove_unreachable_states \<A>) = \<I> \<A>"
by (auto simp add: SemiAutomaton_remove_unreachable_states_def SemiAutomaton_unreachable_states_\<I>)

lemma SemiAutomaton_remove_unreachable_states_\<Sigma> [simp] : "\<Sigma> (SemiAutomaton_remove_unreachable_states \<A>) = \<Sigma> \<A>"
by (simp add: SemiAutomaton_remove_unreachable_states_def)

lemma SemiAutomaton_remove_unreachable_states_fin_run_eq [simp] : 
  "SemiAutomaton_is_fin_run (SemiAutomaton_remove_unreachable_states \<A>) w r \<longleftrightarrow>
   SemiAutomaton_is_fin_run \<A> w r"
proof -
  have I_prop: "\<I> (SemiAutomaton_remove_unreachable_states \<A>) = \<I> \<A>" by simp

  { fix q'
    assume "q' \<in> SemiAutomaton_unreachable_states \<A>" "hd r \<in> \<I> \<A>"
    hence "LTS_is_unreachable (\<Delta> \<A>) (hd r) q'"
      unfolding SemiAutomaton_unreachable_states_def by simp
  } note hd_r_unreach = this

  from SemiAutomaton_remove_states_fin_run_LTS_eq [of 
     "SemiAutomaton_unreachable_states \<A>" \<A> r w, OF hd_r_unreach]
  show ?thesis
    unfolding SemiAutomaton_is_fin_run_def
    by (metis I_prop SemiAutomaton_remove_unreachable_states_def)
qed

lemma SemiAutomaton_remove_unreachable_states_inf_run_eq [simp] : 
  "SemiAutomaton_is_inf_run (SemiAutomaton_remove_unreachable_states \<A>) w r \<longleftrightarrow>
   SemiAutomaton_is_inf_run \<A> w r"
proof -
  have I_prop: "\<I> (SemiAutomaton_remove_unreachable_states \<A>) = \<I> \<A>" by simp

  { fix q'
    assume "q' \<in> SemiAutomaton_unreachable_states \<A>" "r 0 \<in> \<I> \<A>"
    hence "LTS_is_unreachable (\<Delta> \<A>) (r 0) q'"
      unfolding SemiAutomaton_unreachable_states_def by simp
  } note r0_unreach = this
  from SemiAutomaton_remove_states_inf_run_LTS_eq [of 
     "SemiAutomaton_unreachable_states \<A>" \<A> r w, OF r0_unreach]
  show ?thesis
    unfolding SemiAutomaton_is_inf_run_def
    by (metis I_prop SemiAutomaton_remove_unreachable_states_def)
qed

lemma SemiAutomaton_unreachable_states_SemiAutomaton_remove_unreachable_states :
  "SemiAutomaton_unreachable_states (SemiAutomaton_remove_unreachable_states \<A>) =
   SemiAutomaton_unreachable_states \<A>"
proof -
  have "\<And>q q' w. q \<in> \<I> \<A> \<Longrightarrow> 
        LTS_is_reachable (\<Delta> (SemiAutomaton_remove_unreachable_states \<A>)) q w q' \<longleftrightarrow>
        LTS_is_reachable (\<Delta> \<A>) q w q'"
  proof -
    fix q q' w
    assume q_in_I: "q \<in> \<I> \<A>"
  
    with q_in_I have 
      Q_OK: "\<And>q'. q' \<in> SemiAutomaton_unreachable_states \<A> \<Longrightarrow> LTS_is_unreachable (\<Delta> \<A>) q q'"
      by (simp add: SemiAutomaton_unreachable_states_def)

    note SemiAutomaton_remove_states_reachable_eq [of "SemiAutomaton_unreachable_states \<A>" \<A> q w q']
    with Q_OK show "LTS_is_reachable (\<Delta> (SemiAutomaton_remove_unreachable_states \<A>)) q w q' \<longleftrightarrow>
          LTS_is_reachable (\<Delta> \<A>) q w q'"
      by (simp add: SemiAutomaton_remove_unreachable_states_def)
  qed
  thus ?thesis by (simp add: SemiAutomaton_unreachable_states_def LTS_is_unreachable_def)
qed


lemma SemiAutomaton_remove_unreachable_states_SemiAutomaton_remove_unreachable_states [simp] :
fixes \<A> :: "('q, 'a, _) SemiAutomaton_rec_scheme"
shows  "SemiAutomaton_remove_unreachable_states (SemiAutomaton_remove_unreachable_states \<A>) = 
        SemiAutomaton_remove_unreachable_states \<A>"
apply (simp add: SemiAutomaton_remove_unreachable_states_def)
apply (simp add: SemiAutomaton_remove_unreachable_states_def [symmetric]
                 SemiAutomaton_unreachable_states_SemiAutomaton_remove_unreachable_states)
done

lemma SemiAutomaton_remove_unreachable_states___SemiAutomaton_is_initially_connected :
  "SemiAutomaton_is_initially_connected (SemiAutomaton_remove_unreachable_states \<A>)"
apply (simp add: SemiAutomaton_is_initially_connected_def SemiAutomaton_unreachable_states_SemiAutomaton_remove_unreachable_states)
apply (simp add: SemiAutomaton_remove_unreachable_states_def)
apply fastforce
done

definition SemiAutomaton_reachable_states where
  "SemiAutomaton_reachable_states \<A> = \<Q> \<A> - SemiAutomaton_unreachable_states \<A>"

lemma (in SemiAutomaton) SemiAutomaton_reachable_states_run :
  "SemiAutomaton_reachable_states \<A> = {q | q w r. SemiAutomaton_is_fin_run \<A> w r \<and> last r = q}"
unfolding SemiAutomaton_reachable_states_def 
apply (auto simp add: SemiAutomaton_not_in_unreachable_states_run set_eq_iff)
apply (metis LTS_is_reachable_alt_def SemiAutomaton_\<Delta>_cons___LTS_is_reachable SemiAutomaton_is_fin_run_def \<I>_consistent subsetD)
done

lemma (in SemiAutomaton) SemiAutomaton_reachable_states_reachable :
  "SemiAutomaton_reachable_states \<A> = {q . \<exists>i w. i \<in> \<I> \<A> \<and> LTS_is_reachable (\<Delta> \<A>) i w q}"
unfolding SemiAutomaton_reachable_states_run SemiAutomaton_is_fin_run_def LTS_is_reachable_alt_def
by auto

lemma (in SemiAutomaton) SemiAutomaton_in_reachable_states_eq :
  "q \<in> SemiAutomaton_reachable_states \<A> \<longleftrightarrow> 
   q \<notin> SemiAutomaton_unreachable_states \<A>"
unfolding SemiAutomaton_reachable_states_run SemiAutomaton_not_in_unreachable_states_run
by simp 

lemmas (in SemiAutomaton) SemiAutomaton_not_in_unreachable_states_eq = SemiAutomaton_in_reachable_states_eq[symmetric]

lemma (in SemiAutomaton) SemiAutomaton_remove_unreachable_states_alt_def :
  "SemiAutomaton_remove_unreachable_states \<A> = 
   \<lparr>\<Q> = SemiAutomaton_reachable_states \<A>, \<Sigma> = \<Sigma> \<A>,
    \<Delta> = {(s1, a, s2).
            (s1, a, s2) \<in> \<Delta> \<A> \<and>
            s1 \<in> SemiAutomaton_reachable_states \<A> \<and>
            s2 \<in> SemiAutomaton_reachable_states \<A>},
    \<I> = \<I> \<A> \<inter> SemiAutomaton_reachable_states \<A>\<rparr>"
unfolding SemiAutomaton_remove_unreachable_states_def SemiAutomaton_remove_states_def
          SemiAutomaton_not_in_unreachable_states_eq
          SemiAutomaton_reachable_states_def[symmetric]
using \<I>_consistent
by (simp add: set_eq_iff SemiAutomaton_not_in_unreachable_states_eq)

subsection \<open> Rename States / Combining \<close>

definition SemiAutomaton_rename_states_ext :: 
"(('q1 \<Rightarrow> 'q2) \<Rightarrow> ('q1, 'a, 'more1) SemiAutomaton_rec_scheme \<Rightarrow> 'more2) \<Rightarrow>
 ('q1, 'a, 'more1) SemiAutomaton_rec_scheme \<Rightarrow> 
 ('q1 \<Rightarrow> 'q2) \<Rightarrow> ('q2, 'a, 'more2) SemiAutomaton_rec_scheme" where
"SemiAutomaton_rename_states_ext more_f \<A> f \<equiv> 
\<lparr> \<Q>=f ` (\<Q> \<A>), \<Sigma>=\<Sigma> \<A>, \<Delta> = { (f s1, a, f s2) | s1 a s2. (s1,a,s2) \<in> \<Delta> \<A>}, 
  \<I>=f ` (\<I> \<A>), \<dots> = more_f f \<A> \<rparr>"

abbreviation "SemiAutomaton_rename_states \<equiv> SemiAutomaton_rename_states_ext (\<lambda>_ _. ())"

lemma SemiAutomaton_rename_states_ext_\<I> [simp] : "\<I> (SemiAutomaton_rename_states_ext more_f \<A> f) = f ` \<I> \<A>" by (simp add: SemiAutomaton_rename_states_ext_def)
lemma SemiAutomaton_rename_states_ext_\<Q> [simp] : "\<Q> (SemiAutomaton_rename_states_ext more_f \<A> f) = f ` \<Q> \<A>" by (simp add: SemiAutomaton_rename_states_ext_def)
lemma SemiAutomaton_rename_states_ext_\<Sigma> [simp] : "\<Sigma> (SemiAutomaton_rename_states_ext more_f \<A> f) = \<Sigma> \<A>" by (simp add: SemiAutomaton_rename_states_ext_def)
lemma SemiAutomaton_rename_states_ext_\<Delta> [simp] : "(fq, \<sigma>, fq') \<in> \<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f) \<longleftrightarrow> 
                (\<exists>q q'. (q, \<sigma>, q') \<in> \<Delta> \<A> \<and> (fq = f q) \<and> (fq' = f q'))" 
  by (auto simp add: SemiAutomaton_rename_states_ext_def)
lemma SemiAutomaton_rename_states_ext_more [simp] : "more (SemiAutomaton_rename_states_ext more_f \<A> f) = more_f f \<A>" by (simp add: SemiAutomaton_rename_states_ext_def)

lemma SemiAutomaton_rename_states_ext__finite_\<Delta>:
  assumes inj: "inj_on f (\<Q> \<A>)"
  and wf: "SemiAutomaton \<A>"
  shows "finite (\<Delta> \<A>) \<longleftrightarrow> finite (\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f))"
proof -
  define \<Delta>_f where "\<Delta>_f \<equiv> \<lambda>(q,a::'c,q'). (f q, a, f q')"
  with inj SemiAutomaton.\<Delta>_consistent[OF wf] have inj\<Delta>: "inj_on \<Delta>_f (\<Delta> \<A>)" by (auto simp: inj_on_def)

  have \<Delta>_eq: "\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f) = \<Delta>_f ` \<Delta> \<A>"
    unfolding SemiAutomaton_rename_states_ext_def image_def
    by (fastforce split: prod.splits simp: \<Delta>_f_def)
  
  from inj\<Delta> show ?thesis
    unfolding \<Delta>_eq
    by (auto intro: finite_imageD)
qed

lemma SemiAutomaton_rename_states___is_well_formed :
 "SemiAutomaton \<A> \<Longrightarrow> SemiAutomaton (SemiAutomaton_rename_states_ext more_f \<A> f)"
by (auto simp add: SemiAutomaton_def image_iff Bex_def)

lemma SemiAutomaton_rename_states_ext_id[simp] : 
  "SemiAutomaton_rename_states_ext more_f \<A> id = \<A> \<longleftrightarrow> more_f id \<A> = (more \<A>)" 
  by (cases \<A>, auto simp add: SemiAutomaton_rename_states_ext_def)

lemma SemiAutomaton_rename_states_ext_truncate :
  "SemiAutomaton_rename_states_ext more_f \<A>1 f = \<A>2 \<Longrightarrow>
   SemiAutomaton_rename_states (SemiAutomaton.truncate \<A>1) f = SemiAutomaton.truncate \<A>2"
unfolding SemiAutomaton_rename_states_ext_def
by (auto simp add: SemiAutomaton.truncate_def)  metis

lemma SemiAutomaton_rename_states_ext_truncate_sym :
  "\<A>2 = SemiAutomaton_rename_states_ext more_f \<A>1 f \<Longrightarrow>
   SemiAutomaton.truncate \<A>2 = SemiAutomaton_rename_states (SemiAutomaton.truncate \<A>1) f"
by (metis SemiAutomaton_rename_states_ext_truncate)

lemma SemiAutomaton_rename_states_SemiAutomaton_rename_states [simp] : 
   "SemiAutomaton_rename_states (SemiAutomaton_rename_states \<A> f1) f2 = 
    SemiAutomaton_rename_states \<A> (f2 \<circ> f1)" 
by (auto simp add: SemiAutomaton_rename_states_ext_def image_comp, metis)

lemma SemiAutomaton_rename_states_ext_SemiAutomaton_rename_states_ext : 
assumes more21_OK: "\<And>\<A>'. more \<A>' = more_f1 f1 \<A> \<Longrightarrow> more_f2 f2 \<A>' = more_f21 (f2 \<circ> f1) \<A>" 
shows "SemiAutomaton_rename_states_ext more_f2 (SemiAutomaton_rename_states_ext more_f1 \<A> f1) f2 = 
       SemiAutomaton_rename_states_ext more_f21 \<A> (f2 \<circ> f1)" 
apply (auto simp add: SemiAutomaton_rename_states_ext_def image_comp)
apply metis
apply (rule more21_OK) 
apply simp
done

lemma (in SemiAutomaton) SemiAutomaton_rename_states_ext_agree_on_Q :
assumes f12_agree: "\<And>q. q \<in> \<Q> \<A> \<Longrightarrow> f1 q = f2 q"
    and more_f_eq: "more_f1 f1 \<A> = more_f2 f2 \<A>" 
shows "SemiAutomaton_rename_states_ext more_f1 \<A> f1 = SemiAutomaton_rename_states_ext more_f2 \<A> f2"
unfolding SemiAutomaton_rename_states_ext_def
proof (rule SemiAutomaton_rec.equality, simp_all)
  have image_Q: "\<And>Q. Q \<subseteq> \<Q> \<A> \<Longrightarrow> f1 ` Q = f2 ` Q"
    using f12_agree 
    by (simp add: subset_iff set_eq_iff image_iff)

  from image_Q show "f1 ` (\<Q> \<A>) = f2 ` (\<Q> \<A>)" by simp
  from \<I>_consistent image_Q show "f1 ` (\<I> \<A>) = f2 ` (\<I> \<A>)" by simp
next
  from \<Delta>_consistent f12_agree
  show "{(f1 s1, a, f1 s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>} =
        {(f2 s1, a, f2 s2) |s1 a s2. (s1, a, s2) \<in> \<Delta> \<A>}" 
    by (simp add: set_eq_iff) metis
next
  show "more_f1 f1 \<A> = more_f2 f2 \<A>" by fact
qed

lemma LTS_is_reachable___SemiAutomaton_rename_statesE :
 "LTS_is_reachable (\<Delta> \<A>) q w q' \<Longrightarrow>
  LTS_is_reachable (\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f)) (f q) w (f q')"
proof (induct w arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> w) 
  note ind_hyp = Cons(1)
  note reach_\<sigma>w = Cons(2)

  from reach_\<sigma>w obtain q'' where 
     q''_\<Delta>: "(q, \<sigma>, q'') \<in> \<Delta> \<A>" and
     reach_w: "LTS_is_reachable (\<Delta> \<A>) q'' w q'" by auto

  from ind_hyp reach_w 
    have reach_w': "LTS_is_reachable (\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f)) (f q'') w (f q')" 
    by blast

  from q''_\<Delta> have q''_\<Delta>' : "(f q, \<sigma>, f q'') \<in> (\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f))" by auto

  from q''_\<Delta>' reach_w' show ?case by auto
qed

lemma SemiAutomaton_rename_states_ext_fin_run_LTS : 
  "LTS_is_fin_run (\<Delta> \<A>) w r \<Longrightarrow>
   LTS_is_fin_run (\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f)) w (map f r)"
  by (simp add: LTS_is_fin_run_def) metis

lemma SemiAutomaton_rename_states_ext_fin_run : 
  "SemiAutomaton_is_fin_run \<A> w r \<Longrightarrow>
   SemiAutomaton_is_fin_run (SemiAutomaton_rename_states_ext more_f \<A> f) w (map f r)"
  apply (simp add: SemiAutomaton_is_fin_run_def SemiAutomaton_rename_states_ext_fin_run_LTS)
  apply (cases r) 
  apply (auto)
done

lemma SemiAutomaton_rename_states_ext_inf_run_LTS : 
  "LTS_is_inf_run (\<Delta> \<A>) w r \<Longrightarrow>
   LTS_is_inf_run (\<Delta> (SemiAutomaton_rename_states_ext more_f \<A> f)) w (f \<circ> r)"
  by (simp add: LTS_is_inf_run_def) metis

lemma SemiAutomaton_rename_states_ext_inf_run : 
  "SemiAutomaton_is_inf_run \<A> w r \<Longrightarrow>
   SemiAutomaton_is_inf_run (SemiAutomaton_rename_states_ext more_f \<A> f) w (f \<circ> r)"
  by (simp add: SemiAutomaton_is_inf_run_def SemiAutomaton_rename_states_ext_inf_run_LTS)

lemma (in DetSemiAutomaton) SemiAutomaton_is_complete_deterministic___inj_rename :
assumes inj_f: "inj_on f (\<Q> \<A>)"
shows "SemiAutomaton_is_complete_deterministic (SemiAutomaton_rename_states_ext more_f \<A> f)"
proof -
  have step1: 
    "\<And>\<sigma> s1 s1' s2 s2'.
       \<lbrakk>f s1 = f s1'; (s1, \<sigma>, s2) \<in> \<Delta> \<A>; (s1', \<sigma>, s2') \<in> \<Delta> \<A>\<rbrakk> \<Longrightarrow> f s2 = f s2'"
  proof -
    fix \<sigma> s1 s1' s2 s2'
    assume in_D: "(s1, \<sigma>, s2) \<in> \<Delta> \<A>" and in_D': "(s1', \<sigma>, s2') \<in> \<Delta> \<A>"
    
    from \<Delta>_consistent in_D have s1_in: "s1 \<in> \<Q> \<A>" by fast
    from \<Delta>_consistent in_D' have s1'_in: "s1' \<in> \<Q> \<A>" by fast

    assume "f s1 = f s1'"
    with s1_in s1'_in inj_f have s1_eq: "s1 = s1'"
      unfolding inj_on_def by simp

    from s1_eq in_D in_D' deterministic_LTS
    have "s2 = s2'"
      by (auto simp add: LTS_is_deterministic_def)
    thus "f s2 = f s2'" by simp
  qed

  show "SemiAutomaton_is_complete_deterministic (SemiAutomaton_rename_states_ext more_f \<A> f)"
    apply (simp add: SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def
       SemiAutomaton_rename_states_ext_def LTS_is_deterministic_def LTS_is_complete_def)
    apply (rule conjI)
      apply (metis step1)
    apply (metis complete_LTS[unfolded LTS_is_complete_def])
  done
qed


subsection \<open> Isomorphy \<close>

definition SemiAutomaton_isomorphic_ext where
  "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<equiv>
   (\<exists>f. inj_on f (\<Q> \<A>1) \<and> \<A>2 = SemiAutomaton_rename_states_ext more_f \<A>1 f)"

abbreviation SemiAutomaton_isomorphic where
  "SemiAutomaton_isomorphic \<equiv> SemiAutomaton_isomorphic_ext (\<lambda>_ _. ())"

lemma SemiAutomaton_isomorphic_ext_truncate :
  "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic (SemiAutomaton_rec.truncate \<A>1) (SemiAutomaton_rec.truncate \<A>2)"
unfolding SemiAutomaton_isomorphic_ext_def SemiAutomaton_rename_states_ext_def
by (cases \<A>2) (auto simp add: SemiAutomaton_rec.defs)

lemma SemiAutomaton_isomorphic_ext_truncate1 :
  "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic (SemiAutomaton_rec.truncate \<A>1) \<A>2"
unfolding SemiAutomaton_isomorphic_ext_def SemiAutomaton_rename_states_ext_def
by (cases \<A>2) (auto simp add: SemiAutomaton_rec.defs)

lemma SemiAutomaton_isomorphic_ext_truncate2 :
  "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic \<A>1 (SemiAutomaton_rec.truncate \<A>2)"
unfolding SemiAutomaton_isomorphic_ext_def SemiAutomaton_rename_states_ext_def
by (cases \<A>2) (auto simp add: SemiAutomaton_rec.defs)

lemma SemiAutomaton_isomorphic_ext_refl :
assumes more_f_id: "more_f id \<A> = more \<A>"
shows "SemiAutomaton_isomorphic_ext more_f \<A> \<A>"
proof -
  have "inj_on id (\<Q> \<A>)" by simp
  moreover
  have "SemiAutomaton_rename_states_ext more_f \<A> id = \<A>" 
    by (simp add: more_f_id)
  ultimately
  show ?thesis unfolding SemiAutomaton_isomorphic_ext_def by metis
qed

lemma SemiAutomaton_isomorphic_refl [simp] :
  "SemiAutomaton_isomorphic \<A> \<A>"
apply (rule SemiAutomaton_isomorphic_ext_refl)
apply (simp add: fun_eq_iff)
done

lemma SemiAutomaton_isomorphic_ext_bijections :
assumes wf_SemiAutomaton1 : "SemiAutomaton \<A>1"
    and equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic_ext more_f1 \<A>1 \<A>2"
    and more_eq: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                             \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                             more \<A> = more_f1 f1 \<A>1\<rbrakk> \<Longrightarrow>
           more \<A>1 = more_f2 f2 \<A>" 
shows "(\<exists>f1 f2. \<A>2 = SemiAutomaton_rename_states_ext more_f1 \<A>1 f1 \<and>
                \<A>1 = SemiAutomaton_rename_states_ext more_f2 \<A>2 f2 \<and>
                (\<forall>q \<in> \<Q> \<A>1. f2 (f1 q) = q) \<and>
                (\<forall>q \<in> \<Q> \<A>2. f1 (f2 q) = q) \<and>
                (inj_on f1 (\<Q> \<A>1)) \<and> (inj_on f2 (\<Q> \<A>2)))"
proof -
  from equiv_\<A>1_\<A>2 
  obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f1 \<A>1 f" 
    unfolding SemiAutomaton_isomorphic_ext_def by auto

  obtain f' where f'_def : "f' = inv_into (\<Q> \<A>1) f" by auto
  with inj_f have f'_f: "\<And>q. q \<in> (\<Q> \<A>1) \<Longrightarrow> f' (f q) = q" by simp

  from \<A>2_eq have Q_A2_eq: "\<Q> \<A>2 = f ` (\<Q> \<A>1)"
    by (simp add: SemiAutomaton_rename_states_ext_def) 
  with f'_f have inj_f' : "inj_on f' (\<Q> \<A>2)"
    by (simp add: inj_on_def)

  have f_f': "\<And>q. q \<in> (\<Q> \<A>2) \<Longrightarrow> f (f' q) = q" 
    by (auto simp add: Q_A2_eq image_iff f'_f)

  have \<A>1_eq : "\<A>1 = SemiAutomaton_rename_states_ext more_f2 \<A>2 f'"
  proof (rule SemiAutomaton_rec.equality)
    show "\<Sigma> \<A>1 = \<Sigma> (SemiAutomaton_rename_states_ext more_f2 \<A>2 f')" 
      by (simp add: \<A>2_eq SemiAutomaton_remove_states_def)
  next
    from f'_f 
    show "\<Q> \<A>1 = \<Q> (SemiAutomaton_rename_states_ext more_f2 \<A>2 f')"
      by (auto simp add: \<A>2_eq image_iff)
  next
    from wf_SemiAutomaton1 have "\<I> \<A>1 \<subseteq> \<Q> \<A>1" by (simp add: SemiAutomaton_def)
    with f'_f have "\<And>q. q \<in> (\<I> \<A>1) \<Longrightarrow> f' (f q) = q" by auto
    thus "\<I> \<A>1 = \<I> (SemiAutomaton_rename_states_ext more_f2 \<A>2 f')"
      by (auto simp add: \<A>2_eq image_iff)
  next
    from wf_SemiAutomaton1 f'_f 
    have "\<And>q1 a q2. (q1, a, q2) \<in> (\<Delta> \<A>1) \<Longrightarrow> f' (f q1) = q1 \<and>  f' (f q2) = q2" 
       unfolding SemiAutomaton_def by auto
    thus "\<Delta> \<A>1 = \<Delta> (SemiAutomaton_rename_states_ext more_f2 \<A>2 f')"
      by (auto simp add: \<A>2_eq, metis)
  next     
    from \<A>2_eq 
    show "more \<A>1 = more (SemiAutomaton_rename_states_ext more_f2 \<A>2 f')"
      apply (simp add: SemiAutomaton_rename_states_ext_def)
      apply (rule_tac more_eq[of f' f])
      apply (auto simp add: f'_f)
    done
  qed

  show ?thesis
    apply (rule exI[where x = f])
    apply (rule exI[where x = f'])
    apply (intro conjI)
    apply fact
    apply fact
    apply (simp add: f'_f)
    apply (simp add: f_f')
    apply fact
    apply fact
  done
qed

lemma SemiAutomaton_isomorphic_bijections :
assumes wf_SemiAutomaton1 : "SemiAutomaton \<A>1"
    and iso_\<A>1_\<A>2: "SemiAutomaton_isomorphic \<A>1 \<A>2"
shows "(\<exists>f1 f2. \<A>2 = SemiAutomaton_rename_states \<A>1 f1 \<and>
                \<A>1 = SemiAutomaton_rename_states \<A>2 f2 \<and>
                (\<forall>q \<in> \<Q> \<A>1. f2 (f1 q) = q) \<and>
                (\<forall>q \<in> \<Q> \<A>2. f1 (f2 q) = q) \<and>
                (inj_on f1 (\<Q> \<A>1)) \<and> (inj_on f2 (\<Q> \<A>2)))"
apply (rule SemiAutomaton_isomorphic_ext_bijections)
apply (simp_all add: fun_eq_iff wf_SemiAutomaton1 iso_\<A>1_\<A>2)
done

lemma SemiAutomaton_isomorphic_ext_sym_impl :
assumes wf_SemiAutomaton1 : "SemiAutomaton \<A>1"
    and equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic_ext more_f1 \<A>1 \<A>2"
    and more_eq: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                             \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                             more \<A> = more_f1 f1 \<A>1\<rbrakk> \<Longrightarrow>
           more \<A>1 = more_f2 f2 \<A>" 
shows "SemiAutomaton_isomorphic_ext more_f2 \<A>2 \<A>1"
using SemiAutomaton_isomorphic_ext_bijections [OF wf_SemiAutomaton1 equiv_\<A>1_\<A>2, of more_f2] more_eq
unfolding SemiAutomaton_isomorphic_ext_def by blast

lemma SemiAutomaton_isomorphic_sym_impl :
assumes wf_SemiAutomaton1 : "SemiAutomaton \<A>1"
    and equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic \<A>1 \<A>2"
shows "SemiAutomaton_isomorphic \<A>2 \<A>1"
apply (rule SemiAutomaton_isomorphic_ext_sym_impl [OF wf_SemiAutomaton1 equiv_\<A>1_\<A>2])
apply simp
done

lemma SemiAutomaton_isomorphic_ext_sym :
assumes wf_SemiAutomaton1: "SemiAutomaton \<A>1"
    and wf_SemiAutomaton2: "SemiAutomaton \<A>2"
    and more_eq1: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                             \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                             more \<A> = more_f1 f1 \<A>1\<rbrakk> \<Longrightarrow>
           more \<A>1 = more_f2 f2 \<A>" 
    and more_eq2: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                               \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                               more \<A> = more_f2 f2 \<A>2\<rbrakk> \<Longrightarrow>
           more \<A>2 = more_f1 f1 \<A>" 
shows "SemiAutomaton_isomorphic_ext more_f1 \<A>1 \<A>2 \<longleftrightarrow> SemiAutomaton_isomorphic_ext more_f2 \<A>2 \<A>1"
using SemiAutomaton_isomorphic_ext_sym_impl[of \<A>1 more_f1 \<A>2 more_f2]
      SemiAutomaton_isomorphic_ext_sym_impl[of \<A>2 more_f2 \<A>1 more_f1]
      assms
by blast

lemma SemiAutomaton_isomorphic_sym :
assumes wf_SemiAutomaton1: "SemiAutomaton \<A>1"
    and wf_SemiAutomaton2: "SemiAutomaton \<A>2"
shows "SemiAutomaton_isomorphic \<A>1 \<A>2 \<longleftrightarrow> SemiAutomaton_isomorphic \<A>2 \<A>1"
using assms
by (metis SemiAutomaton_isomorphic_sym_impl)

lemma SemiAutomaton_isomorphic___implies_well_formed :
assumes wf_SemiAutomaton1: "SemiAutomaton \<A>1"
    and equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2"
shows "SemiAutomaton \<A>2"
using assms 
by (metis SemiAutomaton_rename_states___is_well_formed SemiAutomaton_isomorphic_ext_def)

lemma SemiAutomaton_isomorphic_ext_trans :
assumes equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic_ext more_f1 \<A>1 \<A>2"
    and equiv_\<A>2_\<A>3: "SemiAutomaton_isomorphic_ext more_f2 \<A>2 \<A>3"
assumes more21_OK: "\<And>\<A>' f1 f2. more \<A>' = more_f1 f1 \<A>1 \<Longrightarrow> more_f2 f2 \<A>' = more_f21 (f2 \<circ> f1) \<A>1" 
shows "SemiAutomaton_isomorphic_ext more_f21 \<A>1 \<A>3"
proof -
  from equiv_\<A>1_\<A>2 
  obtain f1 where inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
                  \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f1 \<A>1 f1" 
    unfolding SemiAutomaton_isomorphic_ext_def by auto

  from equiv_\<A>2_\<A>3 
  obtain f2 where inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
                  \<A>3_eq: "\<A>3 = SemiAutomaton_rename_states_ext more_f2 \<A>2 f2" 
    unfolding SemiAutomaton_isomorphic_ext_def by auto

  from \<A>2_eq \<A>3_eq have \<A>3_eq' : "\<A>3 = SemiAutomaton_rename_states_ext more_f21 \<A>1 (f2 \<circ> f1)" 
    apply (simp)
    apply (rule SemiAutomaton_rename_states_ext_SemiAutomaton_rename_states_ext)
    apply (rule_tac more21_OK)
    apply simp
  done

  from \<A>2_eq have "\<Q> \<A>2 = f1 ` (\<Q> \<A>1)" by (simp add: SemiAutomaton_remove_states_def)
  with inj_f1 inj_f2 have f2_f1_inj: "inj_on (f2 \<circ> f1) (\<Q> \<A>1)"
    by (simp add: inj_on_def)

  from \<A>3_eq' f2_f1_inj show "SemiAutomaton_isomorphic_ext more_f21 \<A>1 \<A>3" unfolding SemiAutomaton_isomorphic_ext_def by auto
qed

lemma SemiAutomaton_isomorphic_trans :
assumes equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic \<A>1 \<A>2"
    and equiv_\<A>2_\<A>3: "SemiAutomaton_isomorphic \<A>2 \<A>3"
shows "SemiAutomaton_isomorphic \<A>1 \<A>3"
apply (rule SemiAutomaton_isomorphic_ext_trans[OF equiv_\<A>1_\<A>2 equiv_\<A>2_\<A>3])
apply simp
done

text \<open> Normaly, one is interested in only well-formed automata. This simplifies
        reasoning about isomorphy. \<close>
definition SemiAutomaton_isomorphic_wf_ext where
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<equiv> SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<and> SemiAutomaton \<A>1"
abbreviation "SemiAutomaton_isomorphic_wf \<equiv> SemiAutomaton_isomorphic_wf_ext (\<lambda>_ _. ())"

definition SemiAutomaton_isomorphic_wf_fin_ext where
  "SemiAutomaton_isomorphic_wf_fin_ext more_f \<A>1 \<A>2 \<equiv> SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<and> FinSemiAutomaton \<A>1"
abbreviation "SemiAutomaton_isomorphic_wf_fin \<equiv> SemiAutomaton_isomorphic_wf_fin_ext (\<lambda>_ _. ())"

lemma SemiAutomaton_isomorphic_wf_\<Sigma> :
assumes equiv: "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2"
shows "\<Sigma> \<A>1 = \<Sigma> \<A>2"
proof -
  from equiv
  obtain f where \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f \<A>1 f" 
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by auto

  with \<A>2_eq show ?thesis by simp
qed

lemma SemiAutomaton_isomorphic_wf_ext_alt_def :
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<longleftrightarrow>
   SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2 \<and> SemiAutomaton \<A>1 \<and> SemiAutomaton \<A>2"
unfolding SemiAutomaton_isomorphic_wf_ext_def
by (metis SemiAutomaton_isomorphic___implies_well_formed)

lemma SemiAutomaton_isomorphic_wf_alt_def :
  "SemiAutomaton_isomorphic_wf \<A>1 \<A>2 \<longleftrightarrow>
   SemiAutomaton_isomorphic \<A>1 \<A>2 \<and> SemiAutomaton \<A>1 \<and> SemiAutomaton \<A>2"
by (simp add: SemiAutomaton_isomorphic_wf_ext_alt_def)

lemma SemiAutomaton_isomorphic_wf_ext_truncate :
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic_wf (SemiAutomaton_rec.truncate \<A>1) (SemiAutomaton_rec.truncate \<A>2)"
unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def SemiAutomaton_rename_states_ext_def
apply (cases \<A>2)
apply simp
apply (simp add: SemiAutomaton_rec.defs)
apply auto
done

lemma SemiAutomaton_isomorphic_wf_ext___fin_iff :
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<Longrightarrow>
   FinSemiAutomaton \<A>1 \<longleftrightarrow> FinSemiAutomaton \<A>2"
unfolding SemiAutomaton_isomorphic_wf_ext_alt_def FinSemiAutomaton_def FinSemiAutomaton_axioms_def
          SemiAutomaton_isomorphic_ext_def
using SemiAutomaton_rename_states_ext__finite_\<Delta>[where more_f = more_f]
by (auto dest: finite_imageD)

lemma SemiAutomaton_isomorphic_wf_fin_ext_alt_def :
  "SemiAutomaton_isomorphic_wf_fin_ext more_f \<A>1 \<A>2 =
   (SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<and> FinSemiAutomaton \<A>1 \<and> FinSemiAutomaton \<A>2)"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_def FinSemiAutomaton_axioms_def 
by (metis FinSemiAutomaton_is_Semiautomaton SemiAutomaton_isomorphic_wf_ext___fin_iff 
          SemiAutomaton_isomorphic_wf_ext_def)

lemma SemiAutomaton_isomorphic_wf_fin_alt_def :
  "SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>2 \<longleftrightarrow>
   SemiAutomaton_isomorphic_wf \<A>1 \<A>2 \<and> FinSemiAutomaton \<A>1 \<and> FinSemiAutomaton \<A>2"
by (simp add: SemiAutomaton_isomorphic_wf_fin_ext_alt_def)

lemma SemiAutomaton_isomorphic_wf_fin_ext_truncate :
  "SemiAutomaton_isomorphic_wf_fin_ext more_f \<A>1 \<A>2 \<Longrightarrow>
   SemiAutomaton_isomorphic_wf_fin (SemiAutomaton_rec.truncate \<A>1) (SemiAutomaton_rec.truncate \<A>2)"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_alt_def 
using SemiAutomaton_isomorphic_wf_ext_truncate[of more_f \<A>1 \<A>2]
by simp

lemma SemiAutomaton_isomorphic_wf_ext_sym :
assumes more_eq1: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                             \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                             more \<A> = more_f1 f1 \<A>1\<rbrakk> \<Longrightarrow>
           more \<A>1 = more_f2 f2 \<A>" 
    and more_eq2: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                               \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                               more \<A> = more_f2 f2 \<A>2\<rbrakk> \<Longrightarrow>
           more \<A>2 = more_f1 f1 \<A>" 
shows "SemiAutomaton_isomorphic_wf_ext more_f1 \<A>1 \<A>2 = SemiAutomaton_isomorphic_wf_ext more_f2 \<A>2 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_ext_alt_def
using SemiAutomaton_isomorphic_ext_sym[of \<A>1 \<A>2 more_f1 more_f2] more_eq1 more_eq2
by auto blast+

lemma SemiAutomaton_isomorphic_wf_sym :
  "SemiAutomaton_isomorphic_wf \<A>1 \<A>2 = SemiAutomaton_isomorphic_wf \<A>2 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_ext_alt_def
by (metis SemiAutomaton_isomorphic_sym)

lemma SemiAutomaton_isomorphic_wf_ext_fin_sym :
assumes more_eq1: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                             \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                             more \<A> = more_f1 f1 \<A>1\<rbrakk> \<Longrightarrow>
           more \<A>1 = more_f2 f2 \<A>" 
    and more_eq2: "\<And>f1 f2 \<A>. \<lbrakk>\<And>q. q \<in> \<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q;
                               \<And>q. q \<in> \<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q;
                               more \<A> = more_f2 f2 \<A>2\<rbrakk> \<Longrightarrow>
           more \<A>2 = more_f1 f1 \<A>" 
shows "SemiAutomaton_isomorphic_wf_fin_ext more_f1 \<A>1 \<A>2 = SemiAutomaton_isomorphic_wf_fin_ext more_f2 \<A>2 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_alt_def
using SemiAutomaton_isomorphic_wf_ext_sym[of \<A>1 \<A>2 more_f1 more_f2] more_eq1 more_eq2
by auto blast+

lemma SemiAutomaton_isomorphic_wf_fin_sym :
  "SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>2 = SemiAutomaton_isomorphic_wf_fin \<A>2 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_alt_def
by (metis SemiAutomaton_isomorphic_wf_sym)

lemma SemiAutomaton_isomorphic_wf_ext_trans :
assumes equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic_wf_ext more_f1 \<A>1 \<A>2"
    and equiv_\<A>2_\<A>3: "SemiAutomaton_isomorphic_wf_ext more_f2 \<A>2 \<A>3"
assumes more21_OK: "\<And>\<A>' f1 f2. more \<A>' = more_f1 f1 \<A>1 \<Longrightarrow> more_f2 f2 \<A>' = more_f21 (f2 \<circ> f1) \<A>1" 
shows "SemiAutomaton_isomorphic_wf_ext more_f21 \<A>1 \<A>3"
using SemiAutomaton_isomorphic_ext_trans[of more_f1 \<A>1 \<A>2 more_f2 \<A>3 more_f21, OF _ _ more21_OK]
      equiv_\<A>1_\<A>2 equiv_\<A>2_\<A>3
unfolding SemiAutomaton_isomorphic_wf_ext_def
by simp

lemma SemiAutomaton_isomorphic_wf_trans :
  "\<lbrakk>SemiAutomaton_isomorphic_wf \<A>1 \<A>2; SemiAutomaton_isomorphic_wf \<A>2 \<A>3\<rbrakk> \<Longrightarrow>
   SemiAutomaton_isomorphic_wf \<A>1 \<A>3"
unfolding SemiAutomaton_isomorphic_wf_ext_alt_def
by (metis SemiAutomaton_isomorphic_trans)

lemma SemiAutomaton_isomorphic_wf_fin_ext_trans :
assumes equiv_\<A>1_\<A>2: "SemiAutomaton_isomorphic_wf_fin_ext more_f1 \<A>1 \<A>2"
    and equiv_\<A>2_\<A>3: "SemiAutomaton_isomorphic_wf_fin_ext more_f2 \<A>2 \<A>3"
assumes more21_OK: "\<And>\<A>' f1 f2. more \<A>' = more_f1 f1 \<A>1 \<Longrightarrow> more_f2 f2 \<A>' = more_f21 (f2 \<circ> f1) \<A>1" 
shows "SemiAutomaton_isomorphic_wf_fin_ext more_f21 \<A>1 \<A>3"
using SemiAutomaton_isomorphic_ext_trans[of more_f1 \<A>1 \<A>2 more_f2 \<A>3 more_f21, OF _ _ more21_OK]
      equiv_\<A>1_\<A>2 equiv_\<A>2_\<A>3
unfolding SemiAutomaton_isomorphic_wf_fin_ext_def
by simp

lemma SemiAutomaton_isomorphic_wf_fin_trans :
  "\<lbrakk>SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>2; SemiAutomaton_isomorphic_wf_fin \<A>2 \<A>3\<rbrakk> \<Longrightarrow>
   SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>3"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_alt_def
by (metis SemiAutomaton_isomorphic_wf_trans)

lemma SemiAutomaton_isomorphic_wf_ext_refl :
assumes more_f_id: "more_f id \<A> = more \<A>"
shows "SemiAutomaton \<A> \<Longrightarrow> SemiAutomaton_isomorphic_wf_ext more_f \<A> \<A>"
unfolding SemiAutomaton_isomorphic_wf_ext_def
using SemiAutomaton_isomorphic_ext_refl[of more_f \<A>, OF more_f_id] by simp

lemma SemiAutomaton_isomorphic_wf_refl :
  "SemiAutomaton \<A>1 \<Longrightarrow> SemiAutomaton_isomorphic_wf \<A>1 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_ext_def
by simp

lemma SemiAutomaton_isomorphic_wf_fin_ext_refl :
assumes more_f_id: "more_f id \<A> = more \<A>"
shows "FinSemiAutomaton \<A> \<Longrightarrow> SemiAutomaton_isomorphic_wf_fin_ext more_f \<A> \<A>"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_def
using SemiAutomaton_isomorphic_ext_refl[of more_f \<A>, OF more_f_id] by simp

lemma SemiAutomaton_isomorphic_wf_fin_refl :
  "FinSemiAutomaton \<A>1 \<Longrightarrow> SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_fin_ext_def
by simp

lemma SemiAutomaton_isomorphic_wf_ext_intro :
  "\<lbrakk>SemiAutomaton \<A>1; SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2\<rbrakk> \<Longrightarrow> 
    SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2"
unfolding SemiAutomaton_isomorphic_wf_ext_def by simp

lemma SemiAutomaton_isomorphic_wf_ext_D :
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton \<A>1"
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton \<A>2"
  "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2"
unfolding SemiAutomaton_isomorphic_wf_ext_alt_def
by simp_all

lemma SemiAutomaton_isomorphic_wf_D :
  "SemiAutomaton_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton \<A>1"
  "SemiAutomaton_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton \<A>2"
  "SemiAutomaton_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton_isomorphic \<A>1 \<A>2"
  "SemiAutomaton_isomorphic_wf \<A>1 \<A>2 \<Longrightarrow> SemiAutomaton_isomorphic \<A>2 \<A>1"
unfolding SemiAutomaton_isomorphic_wf_ext_alt_def
by (simp_all, metis SemiAutomaton_isomorphic_sym)

lemma SemiAutomaton_isomorphic___SemiAutomaton_rename_states_ext :
"inj_on f (\<Q> \<A>) \<Longrightarrow> SemiAutomaton_isomorphic_ext more_f \<A> (SemiAutomaton_rename_states_ext more_f \<A> f)"
unfolding SemiAutomaton_isomorphic_ext_def
by blast

lemma SemiAutomaton_isomorphic___SemiAutomaton_rename_states :
"inj_on f (\<Q> \<A>) \<Longrightarrow> SemiAutomaton_isomorphic \<A> (SemiAutomaton_rename_states \<A> f)"
by (simp add: SemiAutomaton_isomorphic___SemiAutomaton_rename_states_ext)

lemma SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_states_ext :
"\<lbrakk>inj_on f (\<Q> \<A>); SemiAutomaton \<A>\<rbrakk> \<Longrightarrow> 
 SemiAutomaton_isomorphic_wf_ext more_f \<A> (SemiAutomaton_rename_states_ext more_f \<A> f)"
unfolding SemiAutomaton_isomorphic_ext_def SemiAutomaton_isomorphic_wf_ext_def
by blast

lemma SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_states :
"\<lbrakk>inj_on f (\<Q> \<A>); SemiAutomaton \<A>\<rbrakk> \<Longrightarrow> SemiAutomaton_isomorphic_wf \<A> (SemiAutomaton_rename_states \<A> f)"
by (simp add: SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_states_ext)

lemma SemiAutomaton_isomorphic_wf___rename_states_cong :
fixes \<A>1 :: "('q1, 'a) SemiAutomaton_rec"
fixes \<A>2 :: "('q2, 'a) SemiAutomaton_rec"
assumes inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
        inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
        equiv: "SemiAutomaton_isomorphic_wf \<A>1 \<A>2"
shows "SemiAutomaton_isomorphic_wf (SemiAutomaton_rename_states \<A>1 f1) (SemiAutomaton_rename_states \<A>2 f2)"
proof -
  note wf_\<A>1 = SemiAutomaton_isomorphic_wf_D(1)[OF equiv]
  note wf_\<A>2 = SemiAutomaton_isomorphic_wf_D(2)[OF equiv]

  note eq_1 = SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_states [OF inj_f1 wf_\<A>1]
  note eq_2 = SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_states [OF inj_f2 wf_\<A>2]
  from eq_1 eq_2 equiv show ?thesis
    by (metis SemiAutomaton_isomorphic_wf_trans SemiAutomaton_isomorphic_wf_sym)
qed

lemma SemiAutomaton_rename_states___unreachable_states :
assumes A2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f \<A>1 f"
    and f_q_in: "f q \<in> SemiAutomaton_unreachable_states \<A>2"
shows "q \<in> SemiAutomaton_unreachable_states \<A>1"
proof (rule ccontr)
  assume "q \<notin> SemiAutomaton_unreachable_states \<A>1"
  then obtain w r where
    "SemiAutomaton_is_fin_run \<A>1 w r" "last r = q"
    by (auto simp add: SemiAutomaton_not_in_unreachable_states_run)       
  with SemiAutomaton_rename_states_ext_fin_run [of \<A>1 w r more_f f, folded A2_eq]
  have "SemiAutomaton_is_fin_run \<A>2 w (map f r)" and "last (map f r) = f q"
    apply (simp_all, cases r, simp)
    apply hypsubst
    apply (subst last_map)
    apply simp_all
  done
  with SemiAutomaton_not_in_unreachable_states_run[of "f q" "\<A>2"]
  have "f q \<notin> SemiAutomaton_unreachable_states \<A>2" by auto
  with f_q_in show False by simp
qed

lemma SemiAutomaton_rename_states___unreachable_states_iff :
fixes \<A>1 :: "('q1, 'a) SemiAutomaton_rec"
fixes \<A>2 :: "('q2, 'a) SemiAutomaton_rec"
assumes \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f1 \<A>1 f1" and
        \<A>1_eq: "\<A>1 = SemiAutomaton_rename_states_ext more_f2 \<A>2 f2" and
        wf_\<A>1: "SemiAutomaton \<A>1" and
        f2_f1: "\<And>q. q\<in>\<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q" and
        q_in: "q \<in> \<Q> \<A>1"
shows "f1 q \<in> SemiAutomaton_unreachable_states \<A>2 \<longleftrightarrow>
       q \<in> (SemiAutomaton_unreachable_states \<A>1 \<inter> \<Q> \<A>1)"
       (is "?ls \<longleftrightarrow> ?rs")
proof (rule iffI)
  assume "?ls"
  with SemiAutomaton_rename_states___unreachable_states[OF \<A>2_eq, of q] q_in
  show "?rs" by simp
next
  assume "?rs"
  with SemiAutomaton_rename_states___unreachable_states[OF \<A>1_eq, of "f1 q"] f2_f1[of q]
  show "?ls" by simp
qed

lemma SemiAutomaton_rename_states___SemiAutomaton_remove_unreachable_states :
fixes \<A>1 :: "('q1, 'a) SemiAutomaton_rec"
fixes \<A>2 :: "('q2, 'a) SemiAutomaton_rec"
assumes \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f1 \<A>1 f1" and
        \<A>1_eq: "\<A>1 = SemiAutomaton_rename_states_ext more_f2 \<A>2 f2" and
        wf_\<A>1: "SemiAutomaton \<A>1" and
        f2_f1: "\<And>q. q\<in>\<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q" 
shows "SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1 = (SemiAutomaton_remove_unreachable_states \<A>2)"
proof -
  note unreach_lem = SemiAutomaton_rename_states___unreachable_states_iff[OF \<A>2_eq \<A>1_eq wf_\<A>1, OF f2_f1]

  have diff_lem : 
   "\<And>Q. Q \<subseteq> \<Q> \<A>1 \<Longrightarrow>
    f1 ` Q - SemiAutomaton_unreachable_states \<A>2 =
    f1 ` (Q - SemiAutomaton_unreachable_states \<A>1)"
  apply (rule set_eqI)
  apply (insert unreach_lem)
  apply (auto)
  done

  show "SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1 =
        SemiAutomaton_remove_unreachable_states \<A>2"
    proof (rule  SemiAutomaton_rec.equality)
      show "\<Sigma> (SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1) =
            \<Sigma> (SemiAutomaton_remove_unreachable_states \<A>2)"
           "SemiAutomaton.more (SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1) =
            SemiAutomaton.more (SemiAutomaton_remove_unreachable_states \<A>2)"

        unfolding SemiAutomaton_remove_unreachable_states_def \<A>2_eq
        by simp_all
    next
      from diff_lem [of "\<Q> \<A>1"]
      show "\<Q> (SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1) =
            \<Q> (SemiAutomaton_remove_unreachable_states \<A>2)"
        unfolding SemiAutomaton_remove_unreachable_states_def \<A>2_eq
        by simp
    next
      from diff_lem [OF SemiAutomaton.\<I>_consistent [OF wf_\<A>1]]
      show "\<I> (SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1) =
            \<I> (SemiAutomaton_remove_unreachable_states \<A>2)"
        unfolding SemiAutomaton_remove_unreachable_states_def \<A>2_eq
        by simp
    next
      from unreach_lem[unfolded \<A>2_eq] SemiAutomaton.\<Delta>_consistent [OF wf_\<A>1]
      have "\<And>q a q'. (q, a, q') \<in> \<Delta> \<A>1 \<and>
                     f1 q \<notin> SemiAutomaton_unreachable_states (SemiAutomaton_rename_states_ext more_f1 \<A>1 f1) \<and>
                     f1 q' \<notin> SemiAutomaton_unreachable_states (SemiAutomaton_rename_states_ext more_f1 \<A>1 f1) \<longleftrightarrow>
                     (q, a, q') \<in> \<Delta> \<A>1 \<and>
                     q \<notin> SemiAutomaton_unreachable_states \<A>1 \<and>
                     q' \<notin> SemiAutomaton_unreachable_states \<A>1"
        by auto
      hence "\<And>q a q'. (q, a, q') \<in> \<Delta> (SemiAutomaton_remove_unreachable_states \<A>2) \<longleftrightarrow>
                     (q, a, q') \<in> \<Delta> (SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1)"
        unfolding SemiAutomaton_remove_unreachable_states_def \<A>2_eq
        by (simp, blast)
      thus "\<Delta> (SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1) =
            \<Delta> (SemiAutomaton_remove_unreachable_states \<A>2)"
        by auto
    qed
qed

lemma SemiAutomaton_isomorphic_wf___SemiAutomaton_remove_unreachable_states :
fixes \<A>1 :: "('q1, 'a) SemiAutomaton_rec"
fixes \<A>2 :: "('q2, 'a) SemiAutomaton_rec"
assumes equiv: "SemiAutomaton_isomorphic_wf \<A>1 \<A>2"
shows "SemiAutomaton_isomorphic_wf (SemiAutomaton_remove_unreachable_states \<A>1) (SemiAutomaton_remove_unreachable_states \<A>2)"
proof -
  from equiv
  obtain f1 f2 where 
     inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
     \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states \<A>1 f1" and
     inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
     \<A>1_eq: "\<A>1 = SemiAutomaton_rename_states \<A>2 f2" and
     wf_\<A>1: "SemiAutomaton \<A>1" and
     wf_\<A>2: "SemiAutomaton \<A>2" and
     f2_f1: "\<And>q. q\<in>\<Q> \<A>1 \<Longrightarrow> f2 (f1 q) = q" and
     f1_f2: "\<And>q. q\<in>\<Q> \<A>2 \<Longrightarrow> f1 (f2 q) = q"
    unfolding SemiAutomaton_isomorphic_wf_alt_def 
    using SemiAutomaton_isomorphic_bijections[of \<A>1 \<A>2]
    by blast

  have "\<Q> (SemiAutomaton_remove_unreachable_states \<A>1) \<subseteq> \<Q> \<A>1"
    unfolding SemiAutomaton_remove_unreachable_states_def by auto
  with inj_f1 have inj_f1' : "inj_on f1 (\<Q> (SemiAutomaton_remove_unreachable_states \<A>1))"
    by (rule subset_inj_on)

  have \<A>2_eq' :
    "SemiAutomaton_remove_unreachable_states \<A>2 = SemiAutomaton_rename_states (SemiAutomaton_remove_unreachable_states \<A>1) f1"
    using SemiAutomaton_rename_states___SemiAutomaton_remove_unreachable_states[OF \<A>2_eq \<A>1_eq wf_\<A>1] 
          f2_f1
    by simp

  from inj_f1' \<A>2_eq' SemiAutomaton_remove_unreachable_states___is_well_formed[OF wf_\<A>1]
  show ?thesis
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def
    by blast
qed


lemma SemiAutomaton_is_initially_connected___SemiAutomaton_rename_states :
assumes connected: "SemiAutomaton_is_initially_connected \<A>"
shows "SemiAutomaton_is_initially_connected (SemiAutomaton_rename_states_ext more_f \<A> f)"
unfolding SemiAutomaton_is_initially_connected_alt_def
proof (intro ballI)
  fix q2
  let ?A2 = "SemiAutomaton_rename_states_ext more_f \<A> f"
  assume q2_in: "q2 \<in> \<Q> ?A2"
  from q2_in obtain q1 where q1_in: "q1 \<in> \<Q> \<A>" and q2_eq: "q2 = f q1" by auto

  from connected q1_in obtain i1 w where
     i1_in: "i1 \<in> \<I> \<A>" and 
     reach1: "LTS_is_reachable (\<Delta> \<A>) i1 w q1"
    unfolding SemiAutomaton_is_initially_connected_alt_def
    by blast

  have i2_in: "f i1 \<in> \<I> ?A2"
    using i1_in by auto

  have reach2 : "LTS_is_reachable (\<Delta> ?A2) (f i1) w (f q1)"
    using LTS_is_reachable___SemiAutomaton_rename_statesE [OF reach1, of more_f f] .  

  from i2_in reach2
  show "\<exists>i\<in>\<I> ?A2. \<exists>w. LTS_is_reachable (\<Delta> ?A2) i w q2"
    by (simp add: Bex_def q2_eq) fastforce
qed

lemma SemiAutomaton_is_initially_connected___SemiAutomaton_isomorphic :
assumes equiv: "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2"
    and connected_A1: "SemiAutomaton_is_initially_connected \<A>1"
shows "SemiAutomaton_is_initially_connected \<A>2"
proof -
  from equiv obtain f where \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f \<A>1 f"
    unfolding SemiAutomaton_isomorphic_ext_def by auto

  from SemiAutomaton_is_initially_connected___SemiAutomaton_rename_states [OF connected_A1, of more_f f, folded \<A>2_eq]
  show ?thesis .
qed

lemma SemiAutomaton_is_initially_connected___SemiAutomaton_isomorphic_wf :
fixes \<A>1 :: "('q1, 'a) SemiAutomaton_rec"
fixes \<A>2 :: "('q2, 'a) SemiAutomaton_rec"
assumes iso: "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2"
shows "SemiAutomaton_is_initially_connected \<A>1 = SemiAutomaton_is_initially_connected \<A>2"
proof -
  from SemiAutomaton_isomorphic_wf_ext_truncate[OF iso]
  have "SemiAutomaton_isomorphic_wf (truncate \<A>1) (truncate \<A>2)" by simp
  hence "SemiAutomaton_is_initially_connected (truncate \<A>1) = 
         SemiAutomaton_is_initially_connected (truncate \<A>2)"
    by (metis SemiAutomaton_is_initially_connected___SemiAutomaton_isomorphic
              SemiAutomaton_isomorphic_wf_sym SemiAutomaton_isomorphic_wf_ext_def)
  thus ?thesis by simp
qed

lemma DetSemiAutomaton___SemiAutomaton_isomorphic :
assumes equiv: "SemiAutomaton_isomorphic_ext more_f \<A>1 \<A>2"
    and det_A1: "DetSemiAutomaton \<A>1"
shows "DetSemiAutomaton \<A>2"
proof -
  from equiv obtain f where \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states_ext more_f \<A>1 f"
                        and inj_f: "inj_on f (\<Q> \<A>1)"
    unfolding SemiAutomaton_isomorphic_ext_def by auto

  from DetSemiAutomaton.SemiAutomaton_is_complete_deterministic___inj_rename [OF det_A1
          inj_f, of more_f] \<A>2_eq
  have det_A2: "SemiAutomaton_is_complete_deterministic \<A>2" by simp

  from SemiAutomaton_isomorphic___implies_well_formed[OF _ equiv] det_A1
  have wf_A2: "SemiAutomaton \<A>2" unfolding DetSemiAutomaton_alt_def by simp

  from det_A2 wf_A2
  show ?thesis unfolding DetSemiAutomaton_alt_def by simp
qed

lemma DetSemiAutomaton___SemiAutomaton_isomorphic_wf :
assumes iso: "SemiAutomaton_isomorphic_wf_ext more_f \<A>1 \<A>2"
shows "DetSemiAutomaton \<A>1 \<longleftrightarrow> DetSemiAutomaton \<A>2"
proof -
  from SemiAutomaton_isomorphic_wf_ext_truncate[OF iso]
  have "SemiAutomaton_isomorphic_wf (truncate \<A>1) (truncate \<A>2)" by simp
  with DetSemiAutomaton___SemiAutomaton_isomorphic[of "\<lambda>_ _. ()" "truncate \<A>1" "truncate \<A>2"]
       DetSemiAutomaton___SemiAutomaton_isomorphic[of "\<lambda>_ _. ()" "truncate \<A>2" "truncate \<A>1"]
  have "DetSemiAutomaton (truncate \<A>1) = DetSemiAutomaton (truncate \<A>2)" 
    by (metis SemiAutomaton_isomorphic_wf_sym SemiAutomaton_isomorphic_wf_ext_def)
  thus ?thesis by simp
qed


subsection \<open> Renaming letters (i.e. elements of the alphabet) \<close>

definition SemiAutomaton_rename_labels :: "('q, 'a, 'more) SemiAutomaton_rec_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
                              ('q, 'b, 'more) SemiAutomaton_rec_scheme" where
"SemiAutomaton_rename_labels \<A> f \<equiv> 
  \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = f ` (\<Sigma> \<A>), \<Delta> = { (p, f \<sigma>, q) | p \<sigma> q. (p,\<sigma>,q) \<in> \<Delta> \<A>}, \<I> = \<I> \<A>, \<dots> = more \<A> \<rparr>"

lemma [simp] : "\<Q> (SemiAutomaton_rename_labels \<A> f) = \<Q> \<A>" by (simp add: SemiAutomaton_rename_labels_def)
lemma [simp] : "\<Sigma> (SemiAutomaton_rename_labels \<A> f) = f ` (\<Sigma> \<A>)" by (simp add: SemiAutomaton_rename_labels_def)
lemma [simp] : "(p, f\<sigma>, q) \<in> \<Delta> (SemiAutomaton_rename_labels \<A> f) \<longleftrightarrow> 
                (\<exists> \<sigma>. (p, \<sigma>, q) \<in> \<Delta> \<A> \<and> (f\<sigma> = f \<sigma>))" 
  by (auto simp add: SemiAutomaton_rename_labels_def)
lemma [simp] : "\<I> (SemiAutomaton_rename_labels \<A> f) = \<I> \<A>" by (simp add: SemiAutomaton_rename_labels_def)

lemma (in SemiAutomaton) SemiAutomaton_rename_labels___is_well_formed :
"SemiAutomaton (SemiAutomaton_rename_labels \<A> f)"
using SemiAutomaton_axioms
by (auto simp add: SemiAutomaton_def image_iff Bex_def)

lemma SemiAutomaton_rename_labels_id [simp] : "SemiAutomaton_rename_labels \<A> id = \<A>" 
  by (rule SemiAutomaton_rec.equality, auto simp add: SemiAutomaton_rename_labels_def)

lemma SemiAutomaton_rename_labels_fin_run_LTS :
 "LTS_is_fin_run (\<Delta> \<A>) w r \<Longrightarrow>
  LTS_is_fin_run (\<Delta> (SemiAutomaton_rename_labels \<A> f)) (map f w) r"
unfolding LTS_is_fin_run_def by auto

lemma SemiAutomaton_rename_labels_fin_run_LTS2 :
 "LTS_is_fin_run (\<Delta> (SemiAutomaton_rename_labels \<A> f)) w r \<Longrightarrow>
 \<exists>w'. w = map f w' \<and> LTS_is_fin_run (\<Delta> \<A>) w' r"
proof (induct w arbitrary: r)
  case Nil thus ?case by simp
next
  case (Cons a w)
  note indhyp = Cons(1)

  note run = Cons(2)
  from run obtain r1 r2 r' where
     r_eq: "r = r1 # r2 # r'" by (cases r, simp, rename_tac r1 r'', case_tac r'', auto)

  from run r_eq obtain a' where 
     step: "(r1, a', r2) \<in> \<Delta> \<A>" and 
     a_eq: "f a' = a" and
     run': "LTS_is_fin_run (\<Delta> (SemiAutomaton_rename_labels \<A> f)) w (r2 # r')"
  by auto

  from indhyp[OF run']
  obtain w' where w'_props: "w = map f w' \<and> LTS_is_fin_run (\<Delta> \<A>) w' (r2 # r')" by auto

  show ?case
    apply (rule exI[where x = "a' # w'"])
    apply (simp add: r_eq a_eq w'_props step)
  done
qed

lemma LTS_is_reachable___SemiAutomaton_rename_labels :
 "LTS_is_reachable (\<Delta> \<A>) q w q' \<Longrightarrow>
  LTS_is_reachable (\<Delta> (SemiAutomaton_rename_labels \<A> f)) q (map f w) q'"
unfolding LTS_is_reachable_alt_def
by (metis SemiAutomaton_rename_labels_fin_run_LTS)

lemma LTS_is_reachable___SemiAutomaton_rename_labelsE :
  "LTS_is_reachable (\<Delta> (SemiAutomaton_rename_labels \<A> f)) q w q' \<Longrightarrow>
   \<exists> w'. w = (map f w') \<and> LTS_is_reachable (\<Delta> \<A>) q w' q'"
unfolding LTS_is_reachable_alt_def
by (metis SemiAutomaton_rename_labels_fin_run_LTS2)

lemma SemiAutomaton_rename_labels_inf_run_LTS :
 "LTS_is_inf_run (\<Delta> \<A>) w r \<Longrightarrow>
  LTS_is_inf_run (\<Delta> (SemiAutomaton_rename_labels \<A> f)) (f \<circ> w) r"
unfolding LTS_is_inf_run_def by auto

lemma SemiAutomaton_rename_labels_inf_run_LTS2 :
 "LTS_is_inf_run (\<Delta> (SemiAutomaton_rename_labels \<A> f)) w r \<Longrightarrow>
 \<exists>w'. w = f \<circ> w' \<and> LTS_is_inf_run (\<Delta> \<A>) w' r"
unfolding LTS_is_inf_run_def o_def fun_eq_iff by simp metis

lemma SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_labels_cong :
assumes equiv: "SemiAutomaton_isomorphic_wf \<A>1 \<A>2"
shows "SemiAutomaton_isomorphic_wf (SemiAutomaton_rename_labels \<A>1 fl) (SemiAutomaton_rename_labels \<A>2 fl)"
proof -
  from equiv
  obtain f where inj_f : "inj_on f (\<Q> \<A>1)" and
                 \<A>2_eq: "\<A>2 = SemiAutomaton_rename_states \<A>1 f" and
                 wf_\<A>1: "SemiAutomaton \<A>1" 
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by auto

  note wf_rename = SemiAutomaton.SemiAutomaton_rename_labels___is_well_formed [OF wf_\<A>1, of fl]

  have "SemiAutomaton_rename_labels \<A>2 fl = SemiAutomaton_rename_states (SemiAutomaton_rename_labels \<A>1 fl) f"
    unfolding \<A>2_eq SemiAutomaton_rename_labels_def SemiAutomaton_rename_states_ext_def
    by auto metis
  with wf_rename inj_f show ?thesis
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def 
    by auto
qed

lemma SemiAutomaton_is_initially_connected___SemiAutomaton_rename_labels :
assumes connected: "SemiAutomaton_is_initially_connected \<A>"
shows "SemiAutomaton_is_initially_connected (SemiAutomaton_rename_labels \<A> f)"
unfolding SemiAutomaton_is_initially_connected_alt_def
proof (intro ballI)
  fix q
  let ?A2 = "SemiAutomaton_rename_labels \<A> f"
  assume q2_in_A2: "q \<in> \<Q> ?A2"
  hence q2_in_A1: "q \<in> \<Q> \<A>" by simp

  from connected q2_in_A1 obtain i w1 where
     i_in: "i \<in> \<I> \<A>" and 
     reach1: "LTS_is_reachable (\<Delta> \<A>) i w1 q"
    unfolding SemiAutomaton_is_initially_connected_alt_def
    by blast

  from LTS_is_reachable___SemiAutomaton_rename_labels[OF reach1, of f]
  have reach2: "LTS_is_reachable (\<Delta> ?A2) i (map f w1) q" .
 
  from i_in reach2
  show "\<exists>i\<in>\<I> ?A2. \<exists>w. LTS_is_reachable (\<Delta> ?A2) i w q"
     by (simp add: Bex_def) blast
qed


subsection \<open> Normalise states \<close>

text \<open> Operations like building the product of two automata, naturally lead to a different type
of automaton states. When combining several operations, one often needs to stay in the same
type, however. The following definitions allows to transfer an automaton to an isomorphic
one with a different type of states. \<close>

definition SemiAutomaton_normalise_states :: "('q, 'a, _) SemiAutomaton_rec_scheme \<Rightarrow> 
                                              ('q2::{automaton_states}, 'a) SemiAutomaton_rec" where
  "SemiAutomaton_normalise_states \<A> = (SemiAutomaton_rename_states \<A> (SOME (f::'q \<Rightarrow> 'q2). inj_on f (\<Q> \<A>)))"

lemma ex_inj_on_finite :
assumes inf_univ: "~(finite (UNIV::'b set))"
    and fin_A: "finite (A::'a set)"
shows "\<exists>f::('a \<Rightarrow> 'b). inj_on f A"
using fin_A
proof (induct rule: finite_induct)
  case empty show ?case by simp
next
  case (insert a A)
  note fin_A = insert(1)
  note a_nin = insert(2)
  from insert(3) obtain f where inj_f: "inj_on (f::'a\<Rightarrow>'b) A" by blast

  from fin_A have "finite (f ` A)" by (rule finite_imageI)
  then obtain b where b_nin: "b \<notin> (f ` A)" by (metis ex_new_if_finite inf_univ)

  let ?f' = "\<lambda>x. if (x = a) then b else f x"
  from inj_f a_nin b_nin have "inj_on ?f' (insert a A)"
    unfolding inj_on_def by auto
  thus ?case by blast
qed

lemma SemiAutomaton_isomorphic_wf_normalise_states :
fixes \<A>:: "('q, 'a, _) SemiAutomaton_rec_scheme"
assumes wf_A: "FinSemiAutomaton \<A>"
shows "SemiAutomaton_isomorphic_wf \<A> ((SemiAutomaton_normalise_states \<A>)::('q2::{automaton_states},'a) SemiAutomaton_rec)"
unfolding SemiAutomaton_normalise_states_def
  apply (rule SemiAutomaton_isomorphic_wf___SemiAutomaton_rename_states [OF _ FinSemiAutomaton_is_Semiautomaton[OF wf_A]])
  apply (rule someI_ex [where P = "\<lambda>f. inj_on f (\<Q> \<A>)"])
  apply (rule ex_inj_on_finite)
  apply (simp_all add: FinSemiAutomaton.finite_\<Q>[OF wf_A] not_finite_automaton_states_UNIV)
done

lemma SemiAutomaton_normalise_states_truncate[simp]:
  "SemiAutomaton_normalise_states (SemiAutomaton.truncate \<A>) =
   SemiAutomaton_normalise_states \<A>"
by (simp add: SemiAutomaton_normalise_states_def SemiAutomaton_rename_states_ext_def
              SemiAutomaton_rec.defs)

lemma SemiAutomaton_isomorphic_wf___SemiAutomaton_normalise_states :
assumes iso: "SemiAutomaton_isomorphic_wf_fin_ext more_f1 \<A>1 \<A>2" 
shows "SemiAutomaton_isomorphic_wf_fin \<A>1 (SemiAutomaton_normalise_states \<A>2)"
proof -
  from SemiAutomaton_isomorphic_wf_fin_ext_truncate[OF iso]
  have "SemiAutomaton_isomorphic_wf_fin (truncate \<A>1) (truncate \<A>2)" by simp
  hence "SemiAutomaton_isomorphic_wf_fin (truncate \<A>1) (SemiAutomaton_normalise_states (truncate \<A>2))"
    by (metis SemiAutomaton_isomorphic_wf_ext___fin_iff 
              SemiAutomaton_isomorphic_wf_fin_ext_alt_def SemiAutomaton_isomorphic_wf_fin_trans 
              SemiAutomaton_isomorphic_wf_normalise_states)
  thus ?thesis 
    unfolding SemiAutomaton_isomorphic_wf_fin_alt_def
    apply simp
    apply (simp add: SemiAutomaton_isomorphic_wf_ext_def
                     SemiAutomaton_isomorphic_ext_def
                     SemiAutomaton_rename_states_ext_def)
    apply (simp add: SemiAutomaton_rec.defs)
  done
qed

lemma SemiAutomaton_isomorphic_wf___SemiAutomaton_normalise_states_cong :
fixes \<A>1::"('q1, 'a) SemiAutomaton_rec"
  and \<A>2::"('q2, 'a) SemiAutomaton_rec"
shows "SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>2 \<Longrightarrow> 
 SemiAutomaton_isomorphic_wf (SemiAutomaton_normalise_states \<A>1) (SemiAutomaton_normalise_states \<A>2)"
unfolding SemiAutomaton_normalise_states_def
  apply (rule SemiAutomaton.SemiAutomaton_isomorphic_wf___rename_states_cong [of _ \<A>1])
  apply (rule someI_ex [where P = "\<lambda>f. inj_on f (\<Q> \<A>1)"])
  apply (rule ex_inj_on_finite)
  defer defer
  apply (rule someI_ex [where P = "\<lambda>f. inj_on f (\<Q> \<A>2)"])
  apply (rule ex_inj_on_finite)
  apply (simp_all add: FinSemiAutomaton.finite_\<Q> 
                       not_finite_automaton_states_UNIV SemiAutomaton_isomorphic_wf_fin_alt_def)
done

lemma SemiAutomaton_normalise_states_\<Sigma> [simp] :
"\<Sigma> (SemiAutomaton_normalise_states \<A>) = \<Sigma> \<A>"
unfolding SemiAutomaton_normalise_states_def by simp

lemma SemiAutomaton_is_initially_connected___normalise_states :
assumes connected: "SemiAutomaton_is_initially_connected \<A>"
shows "SemiAutomaton_is_initially_connected (SemiAutomaton_normalise_states \<A>)"
unfolding SemiAutomaton_normalise_states_def
by (intro connected SemiAutomaton_is_initially_connected___SemiAutomaton_rename_states)


subsection \<open> Product automata \<close>

definition product_SemiAutomaton :: 
  "('q1, 'a, 'x1) SemiAutomaton_rec_scheme \<Rightarrow> 
   ('q2, 'a, 'x2) SemiAutomaton_rec_scheme \<Rightarrow> ('q1 \<times> 'q2, 'a) SemiAutomaton_rec" where
"product_SemiAutomaton \<A>1 \<A>2 == \<lparr>
   \<Q>=\<Q> \<A>1 \<times> \<Q> \<A>2,
   \<Sigma>=\<Sigma> \<A>1 \<inter> \<Sigma> \<A>2,
   \<Delta> = LTS_product (\<Delta> \<A>1) (\<Delta> \<A>2),
   \<I> = \<I> \<A>1 \<times> \<I> \<A>2\<rparr>"

lemma [simp] : "\<I> (product_SemiAutomaton \<A>1 \<A>2) = \<I> \<A>1 \<times> \<I> \<A>2" by (simp add: product_SemiAutomaton_def)
lemma [simp] : "\<Q> (product_SemiAutomaton \<A>1 \<A>2) = \<Q> \<A>1 \<times> \<Q> \<A>2" by (simp add: product_SemiAutomaton_def)
lemma [simp] : "\<Sigma> (product_SemiAutomaton \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2" by (simp add: product_SemiAutomaton_def)
lemma [simp] : "\<Delta> (product_SemiAutomaton \<A>1 \<A>2) = LTS_product (\<Delta> \<A>1) (\<Delta> \<A>2)" by (simp add: product_SemiAutomaton_def)

lemma product_SemiAutomaton___is_well_formed :
  "\<lbrakk>SemiAutomaton \<A>1;  SemiAutomaton \<A>2\<rbrakk> \<Longrightarrow> SemiAutomaton (product_SemiAutomaton \<A>1 \<A>2)"
unfolding SemiAutomaton_def by (auto simp add: product_SemiAutomaton_def)

lemma product_SemiAutomaton___is_well_formed_fin :
  "\<lbrakk> FinSemiAutomaton \<A>1; FinSemiAutomaton \<A>2\<rbrakk> \<Longrightarrow> FinSemiAutomaton (product_SemiAutomaton \<A>1 \<A>2)"
unfolding FinSemiAutomaton_alt_def 
by (simp add: product_SemiAutomaton___is_well_formed LTS_product_finite)

lemma product_SemiAutomaton___is_well_formed_det :
  "\<lbrakk> DetSemiAutomaton \<A>1; DetSemiAutomaton \<A>2\<rbrakk> \<Longrightarrow> DetSemiAutomaton (product_SemiAutomaton \<A>1 \<A>2)"
unfolding DetSemiAutomaton_alt_def 
   apply (auto simp add: 
             product_SemiAutomaton___is_well_formed 
             SemiAutomaton_is_complete_deterministic_def LTS_is_complete_deterministic_def
             LTS_is_complete_def LTS_is_deterministic_def)
done

lemma product_SemiAutomaton___is_well_formed_det_fin :
  assumes "DetFinSemiAutomaton \<A>1" 
  and "DetFinSemiAutomaton \<A>2"
  shows "DetFinSemiAutomaton (product_SemiAutomaton \<A>1 \<A>2)"
proof -
  from assms interpret DetSemiAutomaton "product_SemiAutomaton \<A>1 \<A>2"
    using product_SemiAutomaton___is_well_formed_det
    unfolding DetFinSemiAutomaton_def
    by blast
  from assms interpret FinSemiAutomaton "product_SemiAutomaton \<A>1 \<A>2"
    using product_SemiAutomaton___is_well_formed_fin
    unfolding DetFinSemiAutomaton_def
    by blast
  show ?thesis by intro_locales
qed

lemma product_SemiAutomaton_is_fin_run :
  "SemiAutomaton_is_fin_run (product_SemiAutomaton \<A>1 \<A>2) w r \<longleftrightarrow>
   SemiAutomaton_is_fin_run \<A>1 w (map fst r) \<and>
   SemiAutomaton_is_fin_run \<A>2 w (map snd r)"
apply (simp add: product_SemiAutomaton_def SemiAutomaton_is_fin_run_def
                 LTS_is_fin_run_product_iff)
apply (cases r) 
apply auto
done

lemma product_SemiAutomaton_is_inf_run :
  "SemiAutomaton_is_inf_run (product_SemiAutomaton \<A>1 \<A>2) w r \<longleftrightarrow>
   SemiAutomaton_is_inf_run \<A>1 w (fst \<circ> r) \<and>
   SemiAutomaton_is_inf_run \<A>2 w (snd \<circ> r)"
apply (simp add: product_SemiAutomaton_def SemiAutomaton_is_inf_run_def
                 LTS_is_inf_run_product_iff)
apply (cases "r 0") 
apply auto
done

lemma SemiAutomaton_isomorphic_product_SemiAutomaton :
assumes equiv_1: "SemiAutomaton_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "SemiAutomaton_isomorphic_wf \<A>2 \<A>2'"
shows "SemiAutomaton_isomorphic_wf (product_SemiAutomaton \<A>1 \<A>2) (product_SemiAutomaton \<A>1' \<A>2')"
proof -
  from equiv_1 obtain f1 where inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
                 \<A>1'_eq: "\<A>1' = SemiAutomaton_rename_states \<A>1 f1" and
                 wf_\<A>1 : "SemiAutomaton \<A>1" 
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by auto

  from equiv_2 obtain f2 where inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
                 \<A>2'_eq: "\<A>2' = SemiAutomaton_rename_states \<A>2 f2" and
                 wf_\<A>2: "SemiAutomaton \<A>2" 
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by auto

  define f where "f \<equiv> \<lambda>(q1, q2). (f1 q1, f2 q2)"
  with inj_f1 inj_f2 have inj_f : "inj_on f (\<Q> (product_SemiAutomaton \<A>1 \<A>2))"
    by (simp add: inj_on_def)

  have f_image: "\<And>S1 S2. f ` (S1 \<times> S2) = (f1 ` S1) \<times> (f2 ` S2)"
    unfolding f_def by auto

  hence prod_eq': "product_SemiAutomaton \<A>1' \<A>2' = SemiAutomaton_rename_states (product_SemiAutomaton \<A>1 \<A>2) f"
    unfolding \<A>1'_eq \<A>2'_eq product_SemiAutomaton_def 
    apply (rule_tac SemiAutomaton_rec.equality)
    apply (simp_all add: f_image)
    apply (simp del: ex_simps add: SemiAutomaton_rename_states_ext_def set_eq_iff ex_simps[symmetric] f_def)
    apply (blast)
  done

  from inj_f prod_eq' product_SemiAutomaton___is_well_formed [OF wf_\<A>1 wf_\<A>2]
  show ?thesis
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by blast
qed

lemma SemiAutomaton_isomorphic_product_SemiAutomaton_fin :
assumes equiv_1: "SemiAutomaton_isomorphic_wf_fin \<A>1 \<A>1'"
    and equiv_2: "SemiAutomaton_isomorphic_wf_fin \<A>2 \<A>2'"
shows "SemiAutomaton_isomorphic_wf_fin (product_SemiAutomaton \<A>1 \<A>2) (product_SemiAutomaton \<A>1' \<A>2')"
using assms
by (metis SemiAutomaton_isomorphic_product_SemiAutomaton SemiAutomaton_isomorphic_wf_fin_alt_def 
          product_SemiAutomaton___is_well_formed_fin)

(* TODO: Is this the right level of abstraction here or should it go to
  LTS with finiteness conditions on LTS *)
lemma LTS_product_bound:
  assumes invar: "SemiAutomaton sa" "SemiAutomaton fa"
  shows "LTS_product (\<Delta> sa) (\<Delta> fa) \<subseteq> (\<Q> sa\<times>\<Q> fa) \<times> (\<Sigma> sa \<inter> \<Sigma> fa) \<times> (\<Q> sa\<times>\<Q> fa)"
proof -  
  interpret sa: SemiAutomaton sa + fa: SemiAutomaton fa by fact+

  show ?thesis
    unfolding LTS_product_def
    by (auto dest: sa.\<Delta>_consistent fa.\<Delta>_consistent)
qed

subsection \<open> Composition of automata \<close>

definition comb_SemiAutomaton :: 
  "('q1, 'a, 'x1) SemiAutomaton_rec_scheme \<Rightarrow> 
   ('q2, 'a, 'x2) SemiAutomaton_rec_scheme \<Rightarrow> ('q1 + 'q2, 'a) SemiAutomaton_rec" where
"comb_SemiAutomaton \<A>1 \<A>2 == \<lparr>
   \<Q>=\<Q> \<A>1 <+>  \<Q> \<A>2,
   \<Sigma>=\<Sigma> \<A>1 \<inter> \<Sigma> \<A>2,
   \<Delta> = LTS_comb (\<Delta> \<A>1) (\<Delta> \<A>2),
   \<I> = \<I> \<A>1 <+> \<I> \<A>2 \<rparr>"

lemma [simp] : "\<I> (comb_SemiAutomaton \<A>1 \<A>2) = \<I> \<A>1 <+> \<I> \<A>2" by (simp add: comb_SemiAutomaton_def)
lemma [simp] : "\<Q> (comb_SemiAutomaton \<A>1 \<A>2) = \<Q> \<A>1 <+> \<Q> \<A>2" by (simp add: comb_SemiAutomaton_def)
lemma [simp] : "\<Sigma> (comb_SemiAutomaton \<A>1 \<A>2) = \<Sigma> \<A>1 \<inter> \<Sigma> \<A>2" by (simp add: comb_SemiAutomaton_def)
lemma [simp] : "\<Delta> (comb_SemiAutomaton \<A>1 \<A>2) = LTS_comb (\<Delta> \<A>1) (\<Delta> \<A>2)" by (simp add: comb_SemiAutomaton_def)

lemma comb_SemiAutomaton___is_well_formed :
  "\<lbrakk> SemiAutomaton \<A>1;  SemiAutomaton \<A>2; \<Sigma> \<A>1 = \<Sigma> \<A>2\<rbrakk> \<Longrightarrow> SemiAutomaton (comb_SemiAutomaton \<A>1 \<A>2)"
unfolding SemiAutomaton_def by (auto simp add: comb_SemiAutomaton_def LTS_comb_alt2_def)

lemma comb_SemiAutomaton_is_fin_run :
  "SemiAutomaton_is_fin_run (comb_SemiAutomaton \<A>1 \<A>2) w r \<longleftrightarrow>
   ((\<exists>r1. map Inl r1 = r \<and> SemiAutomaton_is_fin_run \<A>1 w r1) \<or>
    (\<exists>r2. map Inr r2 = r \<and> SemiAutomaton_is_fin_run \<A>2 w r2))"
apply (simp add: comb_SemiAutomaton_def SemiAutomaton_is_fin_run_def
                 LTS_is_fin_run_LTS_comb)
apply (cases r) 
apply auto
done

lemma SemiAutomaton_isomorphic_comb_SemiAutomaton :
assumes equiv_1: "SemiAutomaton_isomorphic_wf \<A>1 \<A>1'"
    and equiv_2: "SemiAutomaton_isomorphic_wf \<A>2 \<A>2'"
    and \<Sigma>_eq: "\<Sigma> \<A>1 = \<Sigma> \<A>2"
shows "SemiAutomaton_isomorphic_wf (comb_SemiAutomaton \<A>1 \<A>2) (comb_SemiAutomaton \<A>1' \<A>2')"
proof -
  from equiv_1 obtain f1 where inj_f1 : "inj_on f1 (\<Q> \<A>1)" and
                 \<A>1'_eq: "\<A>1' = SemiAutomaton_rename_states \<A>1 f1" and
                 wf_\<A>1 : "SemiAutomaton \<A>1" 
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by auto

  from equiv_2 obtain f2 where inj_f2 : "inj_on f2 (\<Q> \<A>2)" and
                 \<A>2'_eq: "\<A>2' = SemiAutomaton_rename_states \<A>2 f2" and
                 wf_\<A>2: "SemiAutomaton \<A>2" 
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by auto

  define f where "f \<equiv> \<lambda>q. case q of (Inl q1) \<Rightarrow> Inl (f1 q1) | Inr q2 \<Rightarrow> Inr (f2 q2)"
  with inj_f1 inj_f2 have inj_f : "inj_on f (\<Q> (comb_SemiAutomaton \<A>1 \<A>2))"
    by (auto simp add: inj_on_def Ball_def)

  have f_image: "\<And>S1 S2. f ` (S1 <+> S2) = (f1 ` S1) <+> (f2 ` S2)"
    unfolding f_def 
      apply (auto simp add: image_iff Bex_def)
      apply auto
    done

  with inj_f1 inj_f2
  have prod_eq': "comb_SemiAutomaton \<A>1' \<A>2' = SemiAutomaton_rename_states (comb_SemiAutomaton \<A>1 \<A>2) f"
    unfolding \<A>1'_eq \<A>2'_eq  
    apply (rule_tac SemiAutomaton_rec.equality)
    apply (simp_all add: f_image)
    apply (simp del: ex_simps add: SemiAutomaton_rename_states_ext_def set_eq_iff ex_simps[symmetric] f_def
                LTS_comb_alt2_def)
    apply (intro allI iffI)
    apply auto[]
    apply (rule_tac x="Inl s1" in exI)
    apply simp
    apply (rule_tac x="Inl s2" in exI)
    apply simp
    apply (rule_tac x="Inr s1" in exI)
    apply simp
    apply (rule_tac x="Inr s2" in exI)
    apply simp
    apply auto[]
  done

  from inj_f prod_eq' comb_SemiAutomaton___is_well_formed [OF wf_\<A>1 wf_\<A>2 \<Sigma>_eq]
  show ?thesis
    unfolding SemiAutomaton_isomorphic_wf_ext_def SemiAutomaton_isomorphic_ext_def by blast
qed

subsection \<open> Powerset Construction \<close>

definition powerset_SemiAutomaton where
  "powerset_SemiAutomaton \<A> = 
   \<lparr> \<Q> = {q. q \<subseteq> (\<Q> \<A>)},
     \<Sigma> = (\<Sigma> \<A>),
     \<Delta> = {(Q, \<sigma>, Q')| Q Q' \<sigma>. Q \<subseteq> \<Q> \<A> \<and> \<sigma> \<in> \<Sigma> \<A> \<and> Q' = {q'. (\<exists>q\<in>Q. (q, \<sigma>, q') \<in> \<Delta> \<A>)}},
     \<I> = {\<I> \<A>} \<rparr>"

lemma powerset_SemiAutomaton_\<I> [simp] : "\<I> (powerset_SemiAutomaton \<A>) = {\<I> \<A>}" by (simp add: powerset_SemiAutomaton_def)
lemma powerset_SemiAutomaton_\<Q> [simp] : "(q \<in> \<Q> (powerset_SemiAutomaton \<A>)) \<longleftrightarrow> q \<subseteq> \<Q> \<A>" by (simp add: powerset_SemiAutomaton_def)
lemma powerset_SemiAutomaton_\<Sigma> [simp] : "\<Sigma> (powerset_SemiAutomaton \<A>) = \<Sigma> \<A>" by (simp add: powerset_SemiAutomaton_def)

lemma powerset_SemiAutomaton_\<Delta> [simp] : "Q\<sigma>Q' \<in> \<Delta> (powerset_SemiAutomaton \<A>) \<longleftrightarrow> 
  ((snd (snd Q\<sigma>Q') = {q'. \<exists>q\<in>(fst Q\<sigma>Q'). (q, fst (snd Q\<sigma>Q'), q') \<in> \<Delta> \<A>}) \<and>
   (fst Q\<sigma>Q' \<subseteq> \<Q> \<A>) \<and> ((fst (snd Q\<sigma>Q')) \<in> \<Sigma> \<A>))" 
by (cases Q\<sigma>Q') (auto simp add: powerset_SemiAutomaton_def)

lemma (in FinSemiAutomaton) powerset_SemiAutomaton__finite_\<Delta>:
  "finite (\<Sigma> \<A>) \<Longrightarrow> finite (\<Delta> (powerset_SemiAutomaton \<A>))"
proof -
  assume A: "finite (\<Sigma> \<A>)"
  let ?power = " (Pow (\<Q> \<A>)) \<times> \<Sigma> \<A> \<times> (Pow (\<Q> \<A>))"
  from finite_\<Q> finite_\<Delta> A have "finite ?power" by auto
  moreover have "\<Delta> (powerset_SemiAutomaton \<A>) \<subseteq> ?power"
    by (fastforce simp add: \<Delta>_consistent)
  ultimately show ?thesis using finite_subset by blast
qed

lemma powerset_SemiAutomaton_is_deterministic :
  "SemiAutomaton_is_deterministic (powerset_SemiAutomaton \<A>)"
proof -
  let ?\<A> = "powerset_SemiAutomaton \<A>"
  have "\<exists>q0. \<I> ?\<A> = {q0}" by simp
  moreover
  have "LTS_is_deterministic (\<Delta> ?\<A>)"
    unfolding LTS_is_deterministic_def powerset_SemiAutomaton_def 
    by auto
  ultimately show "SemiAutomaton_is_deterministic ?\<A>" 
    unfolding SemiAutomaton_is_deterministic_def by simp
qed

lemma (in SemiAutomaton) powerset_SemiAutomaton_is_complete_determistic :
  "SemiAutomaton_is_complete_deterministic (powerset_SemiAutomaton \<A>)"
proof -
  let ?\<A> = "powerset_SemiAutomaton \<A>"
  have "LTS_is_complete (\<Q> ?\<A>) (\<Sigma> ?\<A>) (\<Delta> ?\<A>)"
    unfolding LTS_is_complete_def powerset_SemiAutomaton_def 
    using \<Delta>_consistent by auto
  thus "SemiAutomaton_is_complete_deterministic ?\<A>" 
    unfolding SemiAutomaton_is_complete_deterministic_alt_def 
    by (simp add: powerset_SemiAutomaton_is_deterministic)
qed

lemma powerset_SemiAutomaton_\<i> [simp] : "\<i> (powerset_SemiAutomaton \<A>) = \<I> \<A>" unfolding \<i>_def by simp

lemma powerset_SemiAutomaton_\<delta> :
  "\<delta> (powerset_SemiAutomaton \<A>) = (\<lambda>(Q,\<sigma>). 
     if (Q \<subseteq> (\<Q> \<A>) \<and> \<sigma> \<in> \<Sigma> \<A>) then Some {q' |q q'. q \<in> Q \<and> (q, \<sigma>, q') \<in> \<Delta> \<A>} else None)"
apply (subst fun_eq_iff, clarify)
apply (simp add: powerset_SemiAutomaton_def \<delta>_def LTS_to_DLTS_def Bex_def)
done

lemma powerset_SemiAutomaton___is_well_formed :
  "SemiAutomaton \<A> \<Longrightarrow> SemiAutomaton (powerset_SemiAutomaton \<A>)"
by (auto simp add: SemiAutomaton_def powerset_SemiAutomaton_def)

lemma powerset_SemiAutomaton___is_well_formed_fin :
  assumes "FinSemiAutomaton \<A>"
  and "finite (\<Sigma> \<A>)"
  shows "FinSemiAutomaton (powerset_SemiAutomaton \<A>)"
using assms
using powerset_SemiAutomaton___is_well_formed[of \<A>]
using FinSemiAutomaton.powerset_SemiAutomaton__finite_\<Delta>[OF assms]
by (auto simp add: powerset_SemiAutomaton_def FinSemiAutomaton_alt_def)

lemma powerset_SemiAutomaton___is_well_formed_det :
  "SemiAutomaton \<A> \<Longrightarrow> DetSemiAutomaton (powerset_SemiAutomaton \<A>)"
by (simp add: powerset_SemiAutomaton___is_well_formed DetSemiAutomaton_alt_def
              SemiAutomaton.powerset_SemiAutomaton_is_complete_determistic)

lemma powerset_SemiAutomaton___is_well_formed_det_fin :
  assumes "FinSemiAutomaton \<A>" "finite (\<Sigma> \<A>)"
  shows "DetFinSemiAutomaton (powerset_SemiAutomaton \<A>)"
proof -
  from assms interpret F: FinSemiAutomaton "powerset_SemiAutomaton \<A>"
    by (rule powerset_SemiAutomaton___is_well_formed_fin)
  from assms interpret D: DetSemiAutomaton "powerset_SemiAutomaton \<A>"
    using powerset_SemiAutomaton___is_well_formed_det
    unfolding FinSemiAutomaton_def
    by blast
  show ?thesis by intro_locales
qed

lemma (in SemiAutomaton) powerset_SemiAutomaton___DLTS_reach :
shows "Q \<subseteq> \<Q> \<A> \<Longrightarrow>
  DLTS_reach (\<delta> (powerset_SemiAutomaton \<A>)) Q w = 
  (if (w \<in> lists (\<Sigma> \<A>)) then Some {q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'} else None)"
proof (induct w arbitrary: Q)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> w)
  note ind_hyp = Cons(1)
  note Q_subset = Cons(2)

  interpret detSemi_detA:  DetSemiAutomaton "(powerset_SemiAutomaton \<A>)" 
    using powerset_SemiAutomaton___is_well_formed_det[OF SemiAutomaton_axioms] 
    by assumption

  let ?Q' = "{q' |q q'. q \<in> Q \<and> (q, \<sigma>, q') \<in> \<Delta> \<A>}"
  from \<Delta>_consistent have Q'_subset : "?Q' \<subseteq> \<Q> \<A>" by auto

  note ind_hyp' = ind_hyp [OF Q'_subset]
  thus ?case
    by (auto simp add: powerset_SemiAutomaton_\<delta> Q_subset)
qed

lemma (in SemiAutomaton) powerset_SemiAutomaton___LTS_is_reachable :
shows "Q \<subseteq> \<Q> \<A> \<Longrightarrow>
  LTS_is_reachable (\<Delta> (powerset_SemiAutomaton \<A>)) Q w Q' \<longleftrightarrow> 
  (w \<in> lists (\<Sigma> \<A>)) \<and> Q' = {q'. \<exists>q\<in>Q. LTS_is_reachable (\<Delta> \<A>) q w q'}"
using LTS_is_reachable_determistic [of "\<Delta> (powerset_SemiAutomaton \<A>)" Q w Q']
      powerset_SemiAutomaton_is_deterministic[of \<A>]
      powerset_SemiAutomaton___DLTS_reach[of Q w]
by (simp add: SemiAutomaton_is_deterministic_def \<delta>_def) blast

lemma SemiAutomaton_is_complete_deterministic___SemiAutomaton_remove_unreachable_states :
  "SemiAutomaton_is_complete_deterministic \<A> \<Longrightarrow>
   SemiAutomaton_is_complete_deterministic (SemiAutomaton_remove_unreachable_states \<A>)"
proof -
  have det_impl: 
    "LTS_is_complete_deterministic (\<Q> \<A>) (\<Sigma> \<A>) (\<Delta> \<A>) \<Longrightarrow>
     LTS_is_complete_deterministic (\<Q> (SemiAutomaton_remove_unreachable_states \<A>)) (\<Sigma> \<A>)
           (\<Delta> (SemiAutomaton_remove_unreachable_states \<A>))" 
    apply (simp add: LTS_is_deterministic_def LTS_is_complete_deterministic_def 
                     LTS_is_complete_def SemiAutomaton_remove_unreachable_states_def Ball_def Bex_def)
    apply (metis SemiAutomaton_unreachable_states_extend)
  done
 
  assume "SemiAutomaton_is_complete_deterministic \<A>"
  with det_impl show ?thesis by (simp add: SemiAutomaton_is_complete_deterministic_def)
qed

end
