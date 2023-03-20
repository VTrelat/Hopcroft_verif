(*  Title:       An adaptation of the work on Presburger automata to the automata
                 defined here
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

section \<open> Presburger Adaptation \<close>

theory Presburger_Adapt
imports Main NFA DFA
  "implementation/NFASpec"
  "../Presburger-Automata/DFS"
  "../Presburger-Automata/Presburger_Automata"
begin             


text \<open> The translation of Presburger arithmetic to finite automata
defined in the AFP Library \emph{Presburger-Automata} consists of
building finite automata for Diophantine equations and inequations as well as
standard automata constructions. These automata constructions are
however defined on a datastructure which is well suited for the
specific automata used. Here, let's try to replace these specialised
finite automata with general ones. \<close>

subsection \<open> DFAs for Diophantine Equations and Inequations \<close>

subsubsection \<open> Definition \<close>

datatype pres_NFA_state =
   pres_NFA_state_error 
 | pres_NFA_state_int int 


fun pres_DFA_eq_ineq_trans_fun where
   "pres_DFA_eq_ineq_trans_fun ineq ks pres_NFA_state_error _ = pres_NFA_state_error"
 | "pres_DFA_eq_ineq_trans_fun ineq ks (pres_NFA_state_int j) bs =
      (if (ineq \<or> (eval_dioph ks (map nat_of_bool bs)) mod 2 = j mod 2)
           then pres_NFA_state_int ((j - (eval_dioph ks (map nat_of_bool bs))) div 2)
           else pres_NFA_state_error)"

fun pres_DFA_is_node where
  "pres_DFA_is_node ks l (pres_NFA_state_error) = True"
| "pres_DFA_is_node ks l (pres_NFA_state_int m) =
   dioph_is_node ks l m"

lemma finite_pres_DFA_is_node_set [simp] :
  "finite {q. pres_DFA_is_node ks l q}"
proof -
  have set_eq: "{q. pres_DFA_is_node ks l q} =
   insert pres_NFA_state_error 
     (pres_NFA_state_int ` {m. dioph_is_node ks l m})"
   (is "?s1 = ?s2")
  proof (intro set_eqI)
    fix q
    show "(q \<in> ?s1) = (q \<in> ?s2)"
    proof (cases q)
      case pres_NFA_state_error thus ?thesis by simp
    next
      case (pres_NFA_state_int m)
      thus ?thesis by auto
    qed
  qed

  show ?thesis
  apply (simp add: set_eq)
  apply (rule finite_imageI)
  apply (insert Presburger_Automata.dioph_dfs.graph_finite)
  apply simp
  done
qed


definition pres_DFA_eq_ineq ::
  "bool \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> (pres_NFA_state, bool list) NFA_rec" where
  "pres_DFA_eq_ineq ineq n ks l = 
     \<lparr> \<Q> = {q. pres_DFA_is_node ks l q}, 
       \<Sigma> = {bs . length bs = n}, 
       \<Delta> = {(q, bs, pres_DFA_eq_ineq_trans_fun ineq ks q bs) | q bs. 
             pres_DFA_is_node ks l q \<and> length bs = n}, 
       \<I> = {pres_NFA_state_int l}, 
       \<F> = {pres_NFA_state_int m |m.
             dioph_is_node ks l m \<and> 0 \<le> m \<and> (ineq \<or> m = 0)} \<rparr>"

subsubsection \<open> Properties \<close>
lemma pres_DFA_is_node___pres_DFA_eq_ineq_trans_fun :
assumes q_OK: "pres_DFA_is_node ks l q"
    and bs_OK: "length bs = n"
shows "pres_DFA_is_node ks l (pres_DFA_eq_ineq_trans_fun i ks q bs)"
proof (cases "pres_DFA_eq_ineq_trans_fun i ks q bs")
    case pres_NFA_state_error
    thus ?thesis 
       unfolding pres_DFA_eq_ineq_def by simp
next
    case (pres_NFA_state_int m')
    note q'_eq = this

    then obtain m where
          q_eq : "q = pres_NFA_state_int m"
      and m'_eq : "m' = (m - eval_dioph ks (map nat_of_bool bs)) div 2"
      and cond: "i \<or> eval_dioph ks (map nat_of_bool bs) mod 2 = m mod 2"
      apply (cases q, simp_all)
      apply (case_tac "i \<or> eval_dioph ks (map nat_of_bool bs) mod 2 = int mod 2")
      apply (simp_all)
    done

    from q_OK q_eq have is_node_m: "dioph_is_node ks l m"
      unfolding pres_DFA_eq_ineq_def
      by simp
    
    have "m' \<in> set (dioph_ineq_succs n ks m)" 
      using bs_OK
      unfolding dioph_ineq_succs_def List.map_filter_def pres_DFA_eq_ineq_def
      apply (simp add: o_def image_iff m'_eq Bex_def)
      apply (rule_tac exI [where x = "map nat_of_bool bs"])
      apply (simp add: nat_of_bool_mk_nat_vecs)
    done
    with dioph_ineq_dfs.succs_is_node [OF is_node_m]
    show ?thesis
      unfolding pres_DFA_eq_ineq_def q'_eq 
      by (simp add: list_all_iff)
qed

lemma pres_DFA_eq_ineq___is_well_formed :
  "DFA (pres_DFA_eq_ineq i n ks l)"
unfolding DFA_alt_def NFA_full_def SemiAutomaton_is_complete_deterministic_def
proof (intro conjI allI impI)
  show "\<I> (pres_DFA_eq_ineq i n ks l) \<subseteq> \<Q> (pres_DFA_eq_ineq i n ks l)"
    unfolding pres_DFA_eq_ineq_def
    by (simp add: dioph_is_node_def)
next
  show "\<F> (pres_DFA_eq_ineq i n ks l) \<subseteq> \<Q> (pres_DFA_eq_ineq i n ks l)"
    unfolding pres_DFA_eq_ineq_def
    by (auto simp add: subset_iff)
next
  let ?p = "pres_DFA_eq_ineq i n ks l"
  show "finite (\<Sigma> ?p)"
    unfolding pres_DFA_eq_ineq_def
    by (simp, rule Presburger_Automata.finite_list)
  
  moreover
  show fin\<Q>: "finite (\<Q> ?p)"
    unfolding pres_DFA_eq_ineq_def
    by simp

  moreover
  { 
    fix q bs q'
    assume in_D: "(q, bs, q') \<in> \<Delta> ?p"
    then show "q \<in> \<Q> ?p"
      and  "bs \<in> \<Sigma> ?p"
      and  "q' \<in> \<Q> ?p"
      using pres_DFA_is_node___pres_DFA_eq_ineq_trans_fun
      unfolding pres_DFA_eq_ineq_def
      by simp_all
  }
  hence "\<Delta> ?p \<subseteq> \<Q> ?p \<times> \<Sigma> ?p \<times> \<Q> ?p" by auto
  ultimately show "finite (\<Delta> ?p)" using finite_subset by blast
next
  show "\<exists>q0. \<I> (pres_DFA_eq_ineq i n ks l) = {q0}"
    unfolding pres_DFA_eq_ineq_def
    by simp
next
  show "LTS_is_complete_deterministic (\<Q> (pres_DFA_eq_ineq i n ks l)) (\<Sigma> (pres_DFA_eq_ineq i n ks l))
     (\<Delta> (pres_DFA_eq_ineq i n ks l))"
  unfolding pres_DFA_eq_ineq_def LTS_is_complete_deterministic_def 
    LTS_is_deterministic_def LTS_is_complete_def 
  by (simp add: pres_DFA_is_node___pres_DFA_eq_ineq_trans_fun)
qed

interpretation pres_DFA_eq_ineq : 
  DFA "pres_DFA_eq_ineq i n ks l"
using  pres_DFA_eq_ineq___is_well_formed[of i n ks l] .

lemma \<delta>_pres_DFA_eq_ineq :
 "\<delta> (pres_DFA_eq_ineq i n ks l) (q, bs) = 
  (if (pres_DFA_is_node ks l q \<and> length bs = n) then
      Some (pres_DFA_eq_ineq_trans_fun i ks q bs)
   else None)"
using pres_DFA_eq_ineq.\<delta>_in_\<Delta>_iff [symmetric]
      pres_DFA_eq_ineq.DetSemiAutomaton_\<delta>_is_none_iff 
  by (simp add: pres_DFA_eq_ineq_def)


lemma pres_DFA_eq_ineq_reach_error :
"list_all (is_alph n) bss \<Longrightarrow>
 DLTS_reach (\<delta> (pres_DFA_eq_ineq i n ks l)) pres_NFA_state_error bss = Some (pres_NFA_state_error)"
proof (induct bss)
  case Nil thus ?case by simp
next
  case (Cons bs bss)
  from Cons(2) have len_bs: "length bs = n" by (simp add: is_alph_def)
  from Cons(2) have bss_OK: "list_all (is_alph n) bss" by simp
  note ind_hyp = Cons(1) [OF bss_OK]
 
  from len_bs
  have step: "\<delta> (pres_DFA_eq_ineq i n ks l) (pres_NFA_state_error, bs) =
    Some pres_NFA_state_error" 
    unfolding \<delta>_pres_DFA_eq_ineq
    by simp

  from step ind_hyp
  show ?case by simp
qed


lemma eval_dioph_nats_of_boolss_eq:
"\<lbrakk>length bs = n; list_all (is_alph n) bss\<rbrakk> \<Longrightarrow>
eval_dioph ks (nats_of_boolss n (bs # bss)) = j \<longleftrightarrow>
eval_dioph ks (map nat_of_bool bs) mod 2 = j mod 2 \<and>
eval_dioph ks (nats_of_boolss n bss) = (j - eval_dioph ks (map nat_of_bool bs)) div 2"
apply (subst eval_dioph_div_mod)
apply (simp add: nats_of_boolss_mod2 nats_of_boolss_div2)
done



lemma pres_DFA_eq_ineq_reach_eq :
assumes "pres_NFA_state_int j \<in> \<Q> (pres_DFA_eq_ineq False n ks l)"
    and "list_all (is_alph n) bss"
shows "DLTS_reach (\<delta> (pres_DFA_eq_ineq False n ks l)) (pres_NFA_state_int j) bss = Some (pres_NFA_state_int 0) \<longleftrightarrow>
       eval_dioph ks (nats_of_boolss n bss) = j"
using assms
proof (induct bss arbitrary: j)
  case Nil
  thus ?case 
  by (simp add: eval_dioph_replicate_0)
next
  case (Cons bs bss' j)
  from Cons(3) have 
    bs_in: "length bs = n" and
    bss'_in : "list_all (is_alph n) bss'"
    by (simp_all add: is_alph_def)
  note ind_hyp = Cons(1) [OF _ bss'_in]
  note j_in_Q = Cons(2)

  have \<delta>_j_bs_eq:
   "\<delta> (pres_DFA_eq_ineq False n ks l) (pres_NFA_state_int j, bs) = Some (pres_DFA_eq_ineq_trans_fun False ks (pres_NFA_state_int j) bs)"
    using j_in_Q bs_in
    unfolding \<delta>_pres_DFA_eq_ineq 
    unfolding pres_DFA_eq_ineq_def
    by simp
  
  show ?case
  proof (cases "eval_dioph ks (map nat_of_bool bs) mod 2 = j mod 2")
    case False
    thus ?thesis
      by (simp add: pres_DFA_eq_ineq_reach_error 
        \<delta>_j_bs_eq eval_dioph_nats_of_boolss_eq bs_in bss'_in)
  next
    case True note cond_true = True

    have j'_in_Q: "pres_DFA_eq_ineq_trans_fun False ks (pres_NFA_state_int j) bs \<in> \<Q> (pres_DFA_eq_ineq False n ks l)"
    using bs_in j_in_Q pres_DFA_is_node___pres_DFA_eq_ineq_trans_fun [where i = False]
    unfolding pres_DFA_eq_ineq_def
    by (simp add: cond_true del: pres_DFA_eq_ineq_trans_fun.simps)

    have j'_eq: "pres_DFA_eq_ineq_trans_fun False ks (pres_NFA_state_int j) bs = 
      pres_NFA_state_int ((j - eval_dioph ks (map nat_of_bool bs)) div 2)"
      by (simp add: cond_true)


    from ind_hyp [OF j'_in_Q [unfolded j'_eq]]
    show ?thesis
      by (simp add: pres_DFA_eq_ineq_reach_error 
        \<delta>_j_bs_eq eval_dioph_nats_of_boolss_eq bs_in bss'_in)
  qed
qed


lemma pres_DFA_eq_correct :
assumes bss_OK: "list_all (is_alph n) bss"
shows "NFA_accept (pres_DFA_eq_ineq False n ks l) bss = 
       (eval_dioph ks (nats_of_boolss n bss) = l)"
proof -
  have \<i>_eval: "\<i> (pres_DFA_eq_ineq False n ks l) = pres_NFA_state_int l"
    unfolding pres_DFA_eq_ineq_def
    by (simp add: \<i>_def)

  have \<F>_eval: "\<F> (pres_DFA_eq_ineq False n ks l) = {pres_NFA_state_int 0}"
    unfolding pres_DFA_eq_ineq_def
    by (auto simp add: dioph_is_node_def)

  from pres_DFA_eq_ineq.\<i>_is_state [of False n ks l]
  have l_in_Q: "pres_NFA_state_int l \<in> \<Q> (pres_DFA_eq_ineq False n ks l)" 
    by (simp add: \<i>_eval)
  note dioph_OK = pres_DFA_eq_ineq_reach_eq [OF l_in_Q bss_OK, symmetric]

  have "DLTS_reach (\<delta> (pres_DFA_eq_ineq False n ks l)) (pres_NFA_state_int l) bss \<noteq> None"
    using bss_OK
    apply (simp add: pres_DFA_eq_ineq.DetSemiAutomaton_reach_is_none_iff)
    apply (simp add: pres_DFA_eq_ineq_def is_alph_def in_lists_conv_set
      dioph_is_node_def Ball_set_list_all)
  done
  thus ?thesis
    by (auto simp add: pres_DFA_eq_ineq.DFA_accept_alt_def dioph_OK \<F>_eval \<i>_eval) 
qed

lemma pres_DFA_eq_ineq_reach_ineq :
assumes "pres_NFA_state_int j \<in> \<Q> (pres_DFA_eq_ineq True n ks l)"
    and "list_all (is_alph n) bss"
    and "DLTS_reach (\<delta> (pres_DFA_eq_ineq True n ks l)) (pres_NFA_state_int j) bss = Some (pres_NFA_state_int j')"
shows "0 \<le> j' \<longleftrightarrow> eval_dioph ks (nats_of_boolss n bss) \<le> j"
using assms
proof (induct bss arbitrary: j j')
  case Nil
  thus ?case 
  by (simp add: eval_dioph_replicate_0)
next
  case (Cons bs bss' j)
  from Cons(3) have 
    bs_in: "length bs = n" and
    bss'_in : "list_all (is_alph n) bss'"
    by (simp_all add: is_alph_def)
  note ind_hyp = Cons(1) [OF _ bss'_in]
  note j_in_Q = Cons(2)
  note reach_j_j' = Cons(4)

  let ?j' = "(j - eval_dioph ks (map nat_of_bool bs)) div 2"
  have \<delta>_j_bs_eq:
   "\<delta> (pres_DFA_eq_ineq True n ks l) (pres_NFA_state_int j, bs) = 
    Some (pres_NFA_state_int ?j')"
    using j_in_Q bs_in
    unfolding \<delta>_pres_DFA_eq_ineq 
    unfolding pres_DFA_eq_ineq_def
    by simp
  
  have j'_in_Q: "pres_DFA_eq_ineq_trans_fun True ks (pres_NFA_state_int j) bs \<in> \<Q> (pres_DFA_eq_ineq True n ks l)"
    using bs_in j_in_Q pres_DFA_is_node___pres_DFA_eq_ineq_trans_fun [where i = True]
    unfolding pres_DFA_eq_ineq_def
    by (simp del: pres_DFA_eq_ineq_trans_fun.simps)

  have j'_eq: "pres_DFA_eq_ineq_trans_fun True ks (pres_NFA_state_int j) bs = 
    pres_NFA_state_int ?j'"
      by simp

  with ind_hyp [OF j'_in_Q [unfolded j'_eq]] reach_j_j'
  show ?case
    by (simp add: \<delta>_j_bs_eq
        eval_dioph_ineq_div_mod [where xs = "nats_of_boolss n (bs#bss')"]
        nats_of_boolss_div2 bs_in bss'_in nats_of_boolss_mod2)
qed

lemma pres_DFA_ineq_reach_exists :
"\<lbrakk>list_all (is_alph n) bss; dioph_is_node ks l j\<rbrakk> \<Longrightarrow>
 \<exists>j'. DLTS_reach (\<delta> (pres_DFA_eq_ineq True n ks l)) (pres_NFA_state_int j) bss = 
 Some (pres_NFA_state_int j') \<and> dioph_is_node ks l j'"
proof (induct bss arbitrary: j)
  case Nil thus ?case by simp
next
  case (Cons bs bss')

  let ?j' = "(j - eval_dioph ks (map nat_of_bool bs)) div 2"
  have "pres_DFA_eq_ineq_trans_fun True ks (pres_NFA_state_int j) bs \<in> \<Q> (pres_DFA_eq_ineq False n ks l)"
    using Cons pres_DFA_is_node___pres_DFA_eq_ineq_trans_fun [where i = True]
    unfolding pres_DFA_eq_ineq_def
    by (simp del: pres_DFA_eq_ineq_trans_fun.simps)
  hence j'_is_node: "dioph_is_node ks l ?j'"
    unfolding pres_DFA_eq_ineq_def
    by simp

  from Cons j'_is_node
  show ?case
    by (simp add: is_alph_def \<delta>_pres_DFA_eq_ineq)
qed

lemma pres_DFA_ineq_correct :
assumes bss_OK: "list_all (is_alph n) bss"
shows "NFA_accept (pres_DFA_eq_ineq True n ks l) bss = 
       (eval_dioph ks (nats_of_boolss n bss) \<le> l)"
proof -
  have \<i>_eval: "\<i> (pres_DFA_eq_ineq True n ks l) = pres_NFA_state_int l"
    unfolding pres_DFA_eq_ineq_def
    by (simp add: \<i>_def)

  have \<F>_eval: "\<F> (pres_DFA_eq_ineq True n ks l) = {pres_NFA_state_int m |m. dioph_is_node ks l m \<and> 0 \<le> m}"
    unfolding pres_DFA_eq_ineq_def
    by simp

  obtain j' where reach_eq:
    "DLTS_reach (\<delta> (pres_DFA_eq_ineq True n ks l)) (pres_NFA_state_int l) bss =
     Some (pres_NFA_state_int j')"
    and is_node_j': "dioph_is_node ks l j'"
     using pres_DFA_ineq_reach_exists [OF bss_OK, of ks l l]
     by (simp add: dioph_is_node_def, blast)

  have l_in_Q: "pres_NFA_state_int l \<in> \<Q> (pres_DFA_eq_ineq True n ks l)"
    unfolding pres_DFA_eq_ineq_def 
    by (simp add: dioph_is_node_def)

  from pres_DFA_eq_ineq_reach_ineq [OF l_in_Q bss_OK reach_eq, symmetric]
  show ?thesis
    by (simp add: pres_DFA_eq_ineq.DFA_accept_alt_def \<i>_eval \<F>_eval 
                  reach_eq is_node_j') 
qed


subsubsection \<open> Efficiency \<close>

subsubsection \<open> Implementation \<close>
text \<open> For using these automata constructions let's replace
the new datatype for states with natural numbers and consider only
reachable states. \<close>

fun pres_NFA_state_to_nat where
  "pres_NFA_state_to_nat pres_NFA_state_error = 0"
| "pres_NFA_state_to_nat (pres_NFA_state_int m) =
   int_encode m + 1"

lemma pres_NFA_state_nat_eq_0 [simp] :
  "(pres_NFA_state_to_nat q = 0) \<longleftrightarrow> q = pres_NFA_state_error"
by (cases q, auto)

lemma pres_NFA_state_nat_neq_0 [simp] :
  "(pres_NFA_state_to_nat q = Suc m) \<longleftrightarrow> q = pres_NFA_state_int (int_decode m)"
by (cases q, auto)


lemma inj_pres_NFA_state_to_nat:
  "inj_on pres_NFA_state_to_nat S"
unfolding inj_on_def Ball_def
proof (intro allI impI)
  fix q1 q2
  assume f_q1: "pres_NFA_state_to_nat q1 = pres_NFA_state_to_nat q2"
  thus "q1 = q2"
    by (cases "pres_NFA_state_to_nat q2", simp_all)
qed

definition efficient_pres_DFA_eq_ineq where
  "efficient_pres_DFA_eq_ineq i n ks l =
   NFA_rename_states (NFA_remove_unreachable_states (pres_DFA_eq_ineq i n ks l)) pres_NFA_state_to_nat"

lemma efficient_pres_DFA_eq_ineq___is_well_formed :
  "DFA (efficient_pres_DFA_eq_ineq i n ks l)"
unfolding efficient_pres_DFA_eq_ineq_def
apply (intro DFA___inj_rename DFA___NFA_remove_unreachable_states)
apply (simp_all add: pres_DFA_eq_ineq___is_well_formed inj_pres_NFA_state_to_nat)
done

lemma pres_DFA_eq_ineq___isomorphic_wf :
  "NFA_isomorphic_wf (NFA_remove_unreachable_states (pres_DFA_eq_ineq i n ks l)) 
                     (efficient_pres_DFA_eq_ineq i n ks l)"
unfolding efficient_pres_DFA_eq_ineq_def
by (intro NFA_isomorphic_wf___NFA_rename_states inj_pres_NFA_state_to_nat
          NFA_remove_unreachable_states___is_well_formed pres_DFA_eq_ineq.NFA_axioms)

lemma efficient_pres_DFA_eq_ineq___NFA_accept [simp] :
  "NFA_accept (efficient_pres_DFA_eq_ineq i n ks l) bss =
   NFA_accept (pres_DFA_eq_ineq i n ks l) bss"
proof -
  have equiv_f: "\<And>\<A>. NFA_is_equivalence_rename_fun \<A> pres_NFA_state_to_nat"
    by (rule NFA_is_equivalence_rename_funI___inj_used, fact inj_pres_NFA_state_to_nat)

  have wf_1 : "DFA (NFA_remove_unreachable_states (pres_DFA_eq_ineq i n ks l))"
    by (intro DFA___NFA_remove_unreachable_states, fact pres_DFA_eq_ineq___is_well_formed)
  hence wf_2: "NFA (NFA_remove_unreachable_states (pres_DFA_eq_ineq i n ks l))"
    by (simp add: DFA_alt_def)

  note NFA.NFA_rename_states___accept [OF wf_2 equiv_f]
  thus ?thesis
    unfolding efficient_pres_DFA_eq_ineq_def
    by simp
qed

subsection \<open> Existential Quantification \<close>

type_synonym pres_NFA = "(nat, bool list) NFA_rec"

definition pres_DFA_labels_tl ::
  "pres_NFA \<Rightarrow> pres_NFA" where
  "pres_DFA_labels_tl \<A> = SemiAutomaton_rename_labels \<A> tl"

lemma pres_DFA_labels_tl___well_formed:
"NFA \<A> \<Longrightarrow> NFA (pres_DFA_labels_tl \<A>)" 
  by (simp add: pres_DFA_labels_tl_def
                NFA.NFA_rename_labels___is_well_formed)

lemma pres_DFA_labels_tl___NFA_accept :
assumes wf_A: "NFA \<A>"
    and \<Sigma>_A: "\<And>bs. bs \<in> \<Sigma> \<A> \<Longrightarrow> bs \<noteq> []"
shows "NFA_accept (pres_DFA_labels_tl \<A>) bss \<longleftrightarrow>
       (\<exists>bs. length bs = length bss \<and> NFA_accept \<A> (insertll 0 bs bss))"
apply (simp add: pres_DFA_labels_tl_def NFA_accept___NFA_rename_labels_iff)
proof 
  assume "\<exists>bss'. bss = map tl bss' \<and> NFA_accept \<A> bss'"
  then obtain bss' where
       bss_eq: "bss = map tl bss'"
   and bss'_acc: "NFA_accept \<A> bss'" by blast  

  have len_bs : "length (map hd bss') = length bss"
    unfolding bss_eq by simp

  from bss'_acc have "bss' \<in> lists (\<Sigma> \<A>)"
    by (simp add: NFA.NFA_accept_wf_def[OF wf_A])
  hence "insertll 0 (map hd bss') (map tl bss') = bss'"
  proof (induct bss')
    case Nil thus ?case by simp
  next
    case (Cons bs bss)
    from Cons(1) have "bs \<noteq> []" using \<Sigma>_A by simp
    then obtain bs_hd bs_tl where bs_eq: "bs = bs_hd # bs_tl"
      by (cases bs, simp)
    
    with Cons(3) show ?case
      by (simp add: insertl_0_eq)
  qed
  hence "NFA_accept \<A> (insertll 0 (map hd bss') bss)"
    unfolding bss_eq
    using bss'_acc
    by simp
  with len_bs show "\<exists>bs. length bs = length bss \<and> NFA_accept \<A> (insertll 0 bs bss)" by blast
next
  assume "\<exists>bs. length bs = length bss \<and> NFA_accept \<A> (insertll 0 bs bss)"
  then obtain bs where
       bss_acc: "NFA_accept \<A> (insertll 0 bs bss)" 
   and len_bs: "length bs = length bss" by blast  

  from len_bs 
  have "map tl (insertll 0 bs bss) = bss"
  proof (induct bss arbitrary: bs)
    case Nil thus ?case by simp
  next
    case (Cons bss_hd bss_tl bs)
    thus ?case
      by (cases bs, simp_all add: insertl_0_eq)    
  qed
  with bss_acc show "\<exists>bss'. bss = map tl bss' \<and> NFA_accept \<A> bss'" 
    apply (rule_tac exI [where x = "insertll 0 bs bss"])
    apply simp
  done
qed

definition pres_DFA_exists ::
  "nat \<Rightarrow> pres_NFA \<Rightarrow> pres_NFA" where
  "pres_DFA_exists n \<A> = NFA_right_quotient_lists (pres_DFA_labels_tl \<A>) 
    {replicate n False}"

lemma pres_DFA_exists___well_formed:
"NFA \<A> \<Longrightarrow> NFA (pres_DFA_exists n \<A>)" 
 unfolding pres_DFA_exists_def
 by (intro NFA_right_quotient___is_well_formed pres_DFA_labels_tl___well_formed, assumption)
 
lemma pres_DFA_exists___NFA_accept :
assumes wf_A: "NFA \<A>"
    and \<Sigma>_A: "\<And>bs. bs \<in> \<Sigma> \<A> \<Longrightarrow> bs \<noteq> []"
shows "NFA_accept (pres_DFA_exists n \<A>) bss \<longleftrightarrow>
       (\<exists>bs m. length bs = length bss + m \<and> NFA_accept \<A> (insertll 0 bs (bss @ zeros m n)))"
proof -
  have lists_repl: "lists {replicate n False} = {zeros m n | m. True}" (is "?s1 = ?s2")
  proof (intro set_eqI iffI)
    fix bss
    assume "bss \<in> ?s2" 
    thus "bss \<in> ?s1" by (auto simp add: zeros_def list_all_iff)
  next
    fix bss
    assume "bss \<in> ?s1"
    hence "\<And>bs. bs \<in> set bss \<Longrightarrow> bs = replicate n False" by (auto simp add: list_all_iff)
    hence "bss = replicate (length bss) (replicate n False)"
      by (induct bss, auto)
    thus "bss \<in> ?s2" by (simp add: zeros_def, blast)
  qed

  note wf_ex = pres_DFA_labels_tl___well_formed [OF wf_A]
  note NFA_accept = NFA.NFA_right_quotient___accepts [OF wf_ex, where L = "lists {replicate n False}"]
  with lists_repl show ?thesis
    by (simp del: ex_simps 
             add: pres_DFA_exists_def pres_DFA_labels_tl___NFA_accept [OF wf_A \<Sigma>_A]
                  ex_simps[symmetric] zeros_len)
qed

lemma nats_of_boolss_append_zeros :
assumes bss_in: "list_all (is_alph n) bss"
shows "nats_of_boolss n (bss @ zeros m n) = nats_of_boolss n bss"
proof -
  have map_eq: "\<And>nl::nat list. map (\<lambda>(x, y). x + (2::nat) ^ length bss * y) (zip nl (replicate (length nl) 0)) = nl"
  proof -
    fix nl
    show "map (\<lambda>(x::nat, y). x + 2 ^ length bss * y) (zip nl (replicate (length nl) 0)) = nl"
    proof (induct nl)
      case Nil thus ?case by simp
    next
      case (Cons x nl)
      thus ?case by (simp)
    qed
  qed

  from map_eq [of "nats_of_boolss n bss"]
       nats_of_boolss_append [of n bss "zeros m n"]
  show "nats_of_boolss n (bss @ zeros m n) = nats_of_boolss n bss"
    by (simp add: bss_in zeros_is_alpha nats_of_boolss_zeros nats_of_boolss_length)
qed


lemma pres_DFA_exists___NFA_accept___nats :
assumes wf_A: "NFA \<A>"
    and \<Sigma>_A: "\<Sigma> \<A> = {bs. length bs = Suc n}"
    and acc_A: "\<And>bss. list_all (is_alph (Suc n)) bss \<Longrightarrow> NFA_accept \<A> bss \<longleftrightarrow> P (nats_of_boolss (Suc n) bss)"
    and bss_in: "list_all (is_alph n) bss"
shows "NFA_accept (pres_DFA_exists n \<A>) bss =
       (\<exists>x. P (x # nats_of_boolss n bss))"
proof -
  have \<Sigma>_A': "\<And>bs. bs \<in> \<Sigma> \<A> \<Longrightarrow> bs \<noteq> []" 
  proof -
    fix bs
    assume "bs \<in> \<Sigma> \<A>"
    with \<Sigma>_A have "length bs = Suc n" by simp
    thus "bs \<noteq> []" by auto
  qed

  have "\<And>bs m. length bs = length bss + m \<Longrightarrow>
                NFA_accept \<A> (insertll 0 bs (bss @ zeros m n)) =
                P (nats_of_boolss (Suc n) (insertll 0 bs (bss @ zeros m n)))"
  proof -
    fix bs :: "bool list"
    fix m
    assume len_bs: "length bs = length bss + m"
    with insertll_len2 [of n "bss @ (zeros m n)" bs 0]
         acc_A
    show "NFA_accept \<A> (insertll 0 bs (bss @ zeros m n)) =
          P (nats_of_boolss (Suc n) (insertll 0 bs (bss @ zeros m n)))"
      by (simp add: bss_in zeros_is_alpha zeros_len)
  qed
  hence step0: 
     "(\<exists>bs m. length bs = length bss + m \<and> NFA_accept \<A> (insertll 0 bs (bss @ zeros m n))) = 
      (\<exists>bs m. length bs = length bss + m \<and> P (nats_of_boolss (Suc n) (insertll 0 bs (bss @ zeros m n))))"
    by auto


  have "\<And>bs m. length bs = length bss + m \<Longrightarrow> 
        nats_of_boolss (Suc n) (insertll 0 bs (bss @ zeros m n)) =
        nat_of_bools bs # nats_of_boolss n bss"
  proof -
   fix bs :: "bool list" 
   fix m
   assume "length bs = length bss + m"
   hence len_bs: "length bs = length (bss @ zeros m n)"
     by (simp add: zeros_len)   

   have bss'_in: "list_all (is_alph n) (bss @ zeros m n)"
     by (simp add: bss_in zeros_is_alpha)

   from nats_of_boolss_insertll [of n "bss @ (zeros m n)" bs 0, OF bss'_in len_bs]
        nats_of_boolss_append_zeros [of n bss m, OF bss_in]
   show "nats_of_boolss (Suc n) (insertll 0 bs (bss @ zeros m n)) =
         nat_of_bools bs # nats_of_boolss n bss"
     by (simp add: insertl_0_eq)
  qed
  hence step1: 
     "(\<exists>bs m. length bs = length bss + m \<and> P (nats_of_boolss (Suc n) (insertll 0 bs (bss @ zeros m n)))) = 
      (\<exists>bs m. length bs = length bss + m \<and> P (nat_of_bools bs # nats_of_boolss n bss))"
    by (metis (no_types))

  have step2: "(\<exists>bs m. length bs = length bss + m \<and> P (nat_of_bools bs # nats_of_boolss n bss)) =
               (\<exists>x. P (x # nats_of_boolss n bss))"
    apply (rule iffI)
    apply (erule exE conjE)+
    apply (erule exI)
    apply (erule exE)
    apply (rule_tac x="bools_of_nat (length bss) x" in exI)
    apply (rule_tac x="length (bools_of_nat (length bss) x) - length bss" in exI)
    apply (simp add: bools_of_nat_inverse bools_of_nat_length)
  done

  from step0 step1 step2 show ?thesis
    by (simp add: pres_DFA_exists___NFA_accept [OF wf_A \<Sigma>_A'] 
                  nats_of_boolss_insertll)
qed

definition pres_DFA_exists_min where
  "pres_DFA_exists_min n \<A> = NFA_right_quotient_lists (
     NFA_minimise (pres_DFA_labels_tl \<A>)) {replicate n False}"

find_theorems name: "NFA_right_quotient" name: "well_formed"
lemma pres_DFA_exists_min___well_formed :
assumes wf_A: "NFA \<A>"
shows "DFA (pres_DFA_exists_min n \<A>)"
unfolding pres_DFA_exists_min_def pres_DFA_labels_tl_def
by (metis NFA_right_quotient___is_well_formed_DFA NFA.NFA_rename_labels___is_well_formed 
          NFA_minimise_spec(3) assms DFA_is_minimal_gen_def)

lemma pres_DFA_exists_min___well_formed_DFA :
"DFA \<A> \<Longrightarrow> DFA (pres_DFA_exists_min n \<A>)"
using pres_DFA_exists_min___well_formed
by (metis DFA_alt_def)

lemma pres_DFA_exists_min___NFA_accept :
assumes wf_A: "DFA \<A>"
shows "NFA_accept (pres_DFA_exists_min n \<A>) bss \<longleftrightarrow>
       NFA_accept (pres_DFA_exists n \<A>) bss"
proof -
  let ?A1 = "pres_DFA_labels_tl \<A>"
  let ?A2 = "NFA_minimise ?A1"

  from wf_A have NFA_A: "NFA \<A>" by (simp add: DFA_alt_def)
  have NFA_A1: "NFA ?A1"
    unfolding pres_DFA_labels_tl_def
    by (simp add: NFA.NFA_rename_labels___is_well_formed [OF NFA_A])

  from NFA_minimise_spec(3)[OF NFA_A1]
  have NFA_A2: "NFA ?A2" unfolding DFA_is_minimal_def DFA_alt_def by simp

  from NFA_minimise_spec(1)[OF NFA_A1]
  have NFA_accept_A2: "\<And>bss. NFA_accept ?A2 bss = NFA_accept ?A1 bss"
    by (auto simp add: \<L>_def)
    
  show ?thesis
    unfolding pres_DFA_exists_min_def pres_DFA_exists_def
    by (simp add: NFA.NFA_right_quotient___accepts NFA_A1 NFA_A2 NFA_accept_A2)
qed

lemma pres_DFA_exists_min___NFA_accept___nats :
assumes wf_A: "DFA \<A>"
    and \<Sigma>_A: "\<Sigma> \<A> = {bs. length bs = Suc n}"
    and acc_A: "\<And>bss. list_all (is_alph (Suc n)) bss \<Longrightarrow> NFA_accept \<A> bss \<longleftrightarrow> P (nats_of_boolss (Suc n) bss)"
    and bss_in: "list_all (is_alph n) bss"
shows "NFA_accept (pres_DFA_exists_min n \<A>) bss =
       (\<exists>x. P (x # nats_of_boolss n bss))"
proof -
  have wf_A' : "NFA \<A>" 
    using wf_A unfolding DFA_alt_def by simp
  show ?thesis by (metis pres_DFA_exists___NFA_accept___nats [OF wf_A' \<Sigma>_A acc_A bss_in]
       pres_DFA_exists_min___NFA_accept [OF wf_A])
qed

lemma \<Sigma>_pres_DFA_exists_min :
  "NFA \<A> \<Longrightarrow> \<Sigma> (pres_DFA_exists_min n \<A>) = tl ` \<Sigma> \<A>"
by (simp add: pres_DFA_exists_min_def pres_DFA_labels_tl_def NFA_minimise_spec(2)
              NFA.NFA_rename_labels___is_well_formed)


subsection \<open> Universal Quantification \<close>

definition pres_DFA_forall_min where
  "pres_DFA_forall_min n \<A> = DFA_complement (pres_DFA_exists_min n (DFA_complement \<A>))"

lemma pres_DFA_forall_min___well_formed_DFA :
"DFA \<A> \<Longrightarrow> DFA (pres_DFA_forall_min n \<A>)"
unfolding pres_DFA_forall_min_def
by (intro DFA_complement_of_DFA_is_DFA pres_DFA_exists_min___well_formed_DFA,
    assumption)

lemma \<Sigma>_image_tl : "tl ` {bs::'a list. length bs = Suc n} = {bs. length bs = n}"
proof (intro set_eqI iffI)
   fix bs :: "'a list"
   assume "bs \<in> tl ` {bs. length bs = Suc n}"
   thus "bs \<in> {bs. length bs = n}" by auto
next
   fix bs :: "'a list"
   assume "bs \<in> {bs. length bs = n}" 
   thus "bs \<in> tl ` {bs. length bs = Suc n}"
     apply (simp add: image_iff)
     apply (rule exI [where x = "e # bs"])
     apply simp
   done
qed


lemma pres_DFA_forall_min___NFA_accept___nats :
fixes \<A> :: pres_NFA
assumes wf_A: "DFA \<A>"
    and \<Sigma>_A: "\<Sigma> \<A> = {bs. length bs = Suc n}"
    and acc_A: "\<And>bss. list_all (is_alph (Suc n)) bss \<Longrightarrow> NFA_accept \<A> bss \<longleftrightarrow> P (nats_of_boolss (Suc n) bss)"
    and bss_in: "list_all (is_alph n) bss"
shows "NFA_accept (pres_DFA_forall_min n \<A>) bss =
       (\<forall>x. P (x # nats_of_boolss n bss))"
proof -
  let ?cA = "DFA_complement \<A>"
  note wf_ca = DFA_complement_of_DFA_is_DFA [OF wf_A]
  hence wf'_ca: "NFA ?cA" unfolding DFA_alt_def by simp

  have acc_cA: "\<And>bss. list_all (is_alph (Suc n)) bss \<Longrightarrow> NFA_accept ?cA bss \<longleftrightarrow> \<not>(P (nats_of_boolss (Suc n) bss))"
    using DFA_complement_word [OF wf_A] \<Sigma>_A
    by (simp add: list_all_iff in_lists_conv_set acc_A is_alph_def)

  have acc : "NFA_accept (pres_DFA_forall_min n \<A>) bss \<longleftrightarrow>
              \<not> (NFA_accept (pres_DFA_exists_min n ?cA) bss)"
    unfolding pres_DFA_forall_min_def 
    apply (rule DFA_complement_word [OF pres_DFA_exists_min___well_formed_DFA [OF wf_ca]])
    apply (insert bss_in)
    apply (simp add: \<Sigma>_pres_DFA_exists_min[OF wf'_ca] \<Sigma>_A \<Sigma>_image_tl)
    apply (simp add: list_all_iff is_alph_def in_lists_conv_set)
  done

  with pres_DFA_exists_min___NFA_accept___nats [OF wf_ca _ acc_cA bss_in] \<Sigma>_A
  show ?thesis by simp
qed

lemma \<Sigma>_pres_DFA_forall_min :
  "NFA \<A> \<Longrightarrow> \<Sigma> (pres_DFA_forall_min n \<A>) = tl ` \<Sigma> \<A>"
by (simp add: pres_DFA_forall_min_def \<Sigma>_pres_DFA_exists_min DFA_complement___is_well_formed)

    
subsection \<open> Translation \<close>
 
fun DFA_of_pf :: "nat \<Rightarrow> pf \<Rightarrow> pres_NFA" where
  Eq:     "DFA_of_pf n (Eq ks l) = efficient_pres_DFA_eq_ineq False n ks l"
| Le:     "DFA_of_pf n (Le ks l) = efficient_pres_DFA_eq_ineq True n ks l"
| And:    "DFA_of_pf n (And p q) = NFA_bool_comb op\<and> (DFA_of_pf n p) (DFA_of_pf n q)"
| Or:     "DFA_of_pf n (Or p q) = NFA_bool_comb op\<or> (DFA_of_pf n p) (DFA_of_pf n q)"
| Imp:    "DFA_of_pf n (Imp p q) = NFA_bool_comb op\<longrightarrow> (DFA_of_pf n p) (DFA_of_pf n q)"
| Exists: "DFA_of_pf n (Exist p) = pres_DFA_exists_min n (DFA_of_pf (Suc n) p)"
| Forall: "DFA_of_pf n (Forall p) = pres_DFA_forall_min n (DFA_of_pf (Suc n) p)"
| Neg:    "DFA_of_pf n (Neg p) = DFA_complement (DFA_of_pf n p)"

lemmas DFA_of_pf_induct =
  DFA_of_pf.induct [case_names Eq Le And Or Imp Exist Forall Neg]

lemma DFA_of_pf___correct: 
  "DFA (DFA_of_pf n p) \<and>
   \<Sigma> (DFA_of_pf n p) = {bs. length bs = n} \<and>
   (\<forall>bss. list_all (is_alph n) bss \<longrightarrow>
     NFA.NFA_accept (DFA_of_pf n p) bss = eval_pf p (nats_of_boolss n bss))"
   (is "?P1 n p \<and> ?P2 n p \<and> ?P3 n p")
proof (induct n p rule: DFA_of_pf_induct)
  case (Eq n ks l)
  show ?case
    apply (simp add: efficient_pres_DFA_eq_ineq___is_well_formed pres_DFA_eq_correct)
    apply (simp add: efficient_pres_DFA_eq_ineq_def pres_DFA_eq_ineq_def)
  done
next
  case (Le n ks l)
  show ?case
    apply (simp add: efficient_pres_DFA_eq_ineq___is_well_formed pres_DFA_ineq_correct)
    apply (simp add: efficient_pres_DFA_eq_ineq_def pres_DFA_eq_ineq_def)
  done
next
  case (And n p q)
  thus ?case
    by (simp add: NFA_bool_comb_DFA___NFA_accept NFA_bool_comb_DFA___is_well_formed
                  in_lists_conv_set list_all_iff is_alph_def)
next
  case (Or n p q)
  thus ?case
    by (simp add: NFA_bool_comb_DFA___NFA_accept NFA_bool_comb_DFA___is_well_formed
                  in_lists_conv_set list_all_iff is_alph_def)
next
  case (Imp n p q)
  thus ?case
    by (simp add: NFA_bool_comb_DFA___NFA_accept NFA_bool_comb_DFA___is_well_formed
                  in_lists_conv_set list_all_iff is_alph_def)
next
  case (Neg n p)
  thus ?case
    by (simp add: DFA_complement_of_DFA_is_DFA DFA_complement_word
                  in_lists_conv_set list_all_iff is_alph_def)
next
  case (Exist n p)
  with pres_DFA_exists_min___NFA_accept___nats [where \<A> = "DFA_of_pf (Suc n) p" and n = n and P = "eval_pf p"]
  show ?case
    by (simp add: \<Sigma>_pres_DFA_exists_min \<Sigma>_image_tl pres_DFA_exists_min___well_formed_DFA)
next
  case (Forall n p)
  with pres_DFA_forall_min___NFA_accept___nats [where \<A> = "DFA_of_pf (Suc n) p" and n = n and P = "eval_pf p"]
  show ?case
    by (simp add: \<Sigma>_pres_DFA_forall_min \<Sigma>_image_tl pres_DFA_forall_min___well_formed_DFA)
qed


subsection \<open> Code Generation \<close>

text \<open> The automata used for presburger arithmetic have label sets that consist of all
bitvectors of a certain length. The following locale is used to cache these sets. \<close>

locale presburger_label_set_cache = set a_\<alpha> a_invar
    for a_\<alpha> :: "'al_set \<Rightarrow> ('a list) set" and a_invar +
    fixes c_\<alpha> :: "'cache \<Rightarrow> nat \<Rightarrow> 'cache \<times> 'al_set"
    fixes c_invar :: "'cache \<Rightarrow> bool"
    fixes init_cache :: "unit \<Rightarrow> 'cache"
    assumes init_cache_OK :
      "c_invar (init_cache ())"
    assumes cache_correct :
      "c_invar c \<Longrightarrow> c_invar (fst (c_\<alpha> c n))"
      "c_invar c \<Longrightarrow> a_invar (snd (c_\<alpha> c n))"
      "c_invar c \<Longrightarrow> a_\<alpha> (snd (c_\<alpha> c n)) = {bs. length bs = n}"

locale presburger_locale = 
   nfa: StdNFA nfa_ops +
   presburger_label_set_cache a_\<alpha> a_invar c_\<alpha> c_invar c_init +
   dfa_construct_no_enc_fun "nfa_op_\<alpha> nfa_ops" "nfa_op_invar nfa_ops" a_\<alpha> a_invar dfa_construct +
   labels_gen: nfa_rename_labels_gen "nfa_op_\<alpha> nfa_ops" "nfa_op_invar nfa_ops"
                         "nfa_op_\<alpha> nfa_ops" "nfa_op_invar nfa_ops" a_\<alpha> a_invar rename_labels_gen 
   for a_\<alpha> :: "'bl_set \<Rightarrow> (bool list) set" and a_invar c_init and
       c_\<alpha> :: "'cache \<Rightarrow> nat \<Rightarrow> ('cache \<times> 'bl_set)" and c_invar and
       nfa_ops :: "('q::{automaton_states}, bool list, 'nfa) nfa_ops" and
       dfa_construct :: "(pres_NFA_state,nat,bool list,'bl_set,'nfa) nfa_construct_fun" and
       rename_labels_gen 
begin
  definition pres_DFA_eq_ineq_impl where
    "pres_DFA_eq_ineq_impl A ineq n ks l = 
     dfa_construct pres_NFA_state_to_nat (pres_NFA_state_int l) A
           (if ineq then
             (\<lambda>q. case q of pres_NFA_state_error \<Rightarrow> False
                          | pres_NFA_state_int m \<Rightarrow> (0 \<le> m))
           else
             (\<lambda>q. case q of pres_NFA_state_error \<Rightarrow> False
                          | pres_NFA_state_int m \<Rightarrow> (m = 0)))
           (pres_DFA_eq_ineq_trans_fun ineq ks)"

  lemma pres_DFA_eq_ineq_impl_correct :
  assumes A_OK: "a_invar A" "a_\<alpha> A = {bs. length bs = n}"
  shows "invar (pres_DFA_eq_ineq_impl A ineq n ks l)"
        "NFA_isomorphic_wf (\<alpha> (pres_DFA_eq_ineq_impl A ineq n ks l)) 
                           (efficient_pres_DFA_eq_ineq ineq n ks l)" 
  proof -
    have "invar (pres_DFA_eq_ineq_impl A ineq n ks l) \<and>
           NFA_isomorphic_wf (\<alpha> (pres_DFA_eq_ineq_impl A ineq n ks l)) 
                           (NFA_remove_unreachable_states (pres_DFA_eq_ineq ineq n ks l))" 
    unfolding pres_DFA_eq_ineq_impl_def
      apply (rule dfa_construct_no_enc_fun_correct) 
      apply (rule pres_DFA_eq_ineq___is_well_formed)
      apply (auto simp add: pres_DFA_eq_ineq_def A_OK inj_pres_NFA_state_to_nat
                       split: pres_NFA_state.split)
    done
    thus "invar (pres_DFA_eq_ineq_impl A ineq n ks l)"
         "NFA_isomorphic_wf (\<alpha> (pres_DFA_eq_ineq_impl A ineq n ks l)) 
                           (efficient_pres_DFA_eq_ineq ineq n ks l)"
    by (simp_all add: NFA_isomorphic_wf_trans[OF _ pres_DFA_eq_ineq___isomorphic_wf])
  qed

  definition pres_DFA_exists_min_impl where
    "pres_DFA_exists_min_impl A AA = 
      right_quotient_lists (list_all (\<lambda>b. \<not> b)) (minimise_Hopcroft_NFA (rename_labels_gen AA A tl))"

  lemma im_tl_eq: "tl ` {bl. length bl = Suc n} = {bl. length bl = n}"
     apply (auto simp add: image_iff length_Suc_conv)[]
     apply (simp add: ex_simps[symmetric] del: ex_simps)
  done

  lemma pres_DFA_exists_min_impl_correct_invar :
    assumes "nfa.invar AA" 
          "a_invar A" "\<Sigma> (nfa.\<alpha> AA) = {bl. length bl = Suc n}"
          "a_\<alpha> A = {bl. length bl = n}"
    shows "nfa.invar (pres_DFA_exists_min_impl A AA)"
    unfolding pres_DFA_exists_min_impl_def pres_DFA_exists_min_def pres_DFA_labels_tl_def
    apply (insert assms)
    apply (intro nfa.correct_isomorphic conjI rename_labels_gen_correct___isomorphic)+
    apply (simp_all add: im_tl_eq)
  done

  lemma pres_DFA_exists_min_impl_correct_\<alpha> :
    assumes "nfa.invar AA" 
          "NFA_isomorphic_wf (nfa.\<alpha> AA) \<A>" 
          "a_invar A" "\<Sigma> (nfa.\<alpha> AA) = {bl. length bl = Suc n}"
          "a_\<alpha> A = {bl. length bl = n}"
    shows "NFA_isomorphic_wf (nfa.\<alpha> (pres_DFA_exists_min_impl A AA)) (pres_DFA_exists_min n \<A>)"
    unfolding pres_DFA_exists_min_impl_def pres_DFA_exists_min_def pres_DFA_labels_tl_def
    apply (insert assms)
    apply (intro nfa.correct_isomorphic conjI rename_labels_gen_correct___isomorphic)+
    apply (simp_all add: im_tl_eq)
  proof -
     assume iso: "NFA_isomorphic_wf (nfa_op_\<alpha> nfa_ops AA) \<A>"
        and \<Sigma>_eq: "\<Sigma> (nfa_op_\<alpha> nfa_ops AA) = {bl. length bl = Suc n}"
     hence \<Sigma>_eq': "\<Sigma> \<A> = {bl. length bl = Suc n}"
       by (simp add: NFA_isomorphic_wf_\<Sigma>)

     from iso have "NFA \<A>" unfolding NFA_isomorphic_wf_alt_def by simp
     hence \<Sigma>_min: "\<Sigma> (NFA_minimise (SemiAutomaton_rename_labels \<A> tl)) = {bl. length bl = n}"
       by (simp add: NFA_minimise_spec(2) NFA.NFA_rename_labels___is_well_formed \<Sigma>_eq' im_tl_eq)

     have "{replicate n False} \<inter> {bl. length bl = n} =
           {a. list_all Not a} \<inter> {bl. length bl = n}"
       apply (intro set_eqI iffI)
       apply (induct n, simp_all)
       apply (induct n, auto simp add: length_Suc_conv)
     done
     with \<Sigma>_min
     show "{replicate n False} \<inter> \<Sigma> (NFA_minimise (SemiAutomaton_rename_labels \<A> tl)) = 
           {a. list_all Not a} \<inter> \<Sigma> (NFA_minimise (SemiAutomaton_rename_labels \<A> tl))" 
       by metis
  qed

  lemmas pres_DFA_exists_min_impl_correct = 
    pres_DFA_exists_min_impl_correct_invar pres_DFA_exists_min_impl_correct_\<alpha>

  definition pres_DFA_forall_min_impl where
    "pres_DFA_forall_min_impl A AA = 
     complement (pres_DFA_exists_min_impl A (complement AA))"

  lemma pres_DFA_forall_min_impl_correct_invar :
    assumes "nfa.invar AA" 
          "a_invar A" "\<Sigma> (nfa.\<alpha> AA) = {bl. length bl = Suc n}"
          "a_\<alpha> A = {bl. length bl = n}"
    shows "nfa.invar (pres_DFA_forall_min_impl A AA)"
  unfolding pres_DFA_forall_min_impl_def pres_DFA_forall_min_def pres_DFA_labels_tl_def
    apply (insert assms)
    apply (intro nfa.correct_isomorphic conjI 
                 pres_DFA_exists_min_impl_correct | assumption)+
    apply (simp_all add: nfa.correct)
  done

  lemma pres_DFA_forall_min_impl_correct_\<alpha> :
    assumes "nfa.invar AA" 
          "NFA_isomorphic_wf (nfa.\<alpha> AA) \<A>" 
          "a_invar A" "\<Sigma> (nfa.\<alpha> AA) = {bl. length bl = Suc n}"
          "a_\<alpha> A = {bl. length bl = n}"
    shows "NFA_isomorphic_wf (nfa.\<alpha> (pres_DFA_forall_min_impl A AA)) (pres_DFA_forall_min n \<A>)"
    unfolding pres_DFA_forall_min_impl_def pres_DFA_forall_min_def pres_DFA_labels_tl_def
    apply (insert assms)
    apply (intro nfa.correct_isomorphic conjI 
                pres_DFA_exists_min_impl_correct | assumption)+
    apply (simp_all add: nfa.correct)
  done

  lemmas pres_DFA_forall_min_impl_correct = 
    pres_DFA_forall_min_impl_correct_invar pres_DFA_forall_min_impl_correct_\<alpha>

  fun nfa_of_pf :: "nat \<Rightarrow> pf \<Rightarrow> 'cache \<Rightarrow> 'nfa \<times> 'cache" where
      Eq:     "nfa_of_pf n (Eq ks l) c = 
                 (let (c', A) = c_\<alpha> c n in
                  (pres_DFA_eq_ineq_impl A False n ks l, c'))"
    | Le:     "nfa_of_pf n (Le ks l) c = 
                 (let (c', A) = c_\<alpha> c n in
                  (pres_DFA_eq_ineq_impl A True n ks l, c'))"
    | And:    "nfa_of_pf n (And p q) c = 
                 (let (P, c') = nfa_of_pf n p c in
                  let (Q, c'') = nfa_of_pf n q c' in
                  (bool_comb op\<and> P Q, c''))"
    | Or:     "nfa_of_pf n (Or p q) c = 
                 (let (P, c') = nfa_of_pf n p c in
                  let (Q, c'') = nfa_of_pf n q c' in
                  (bool_comb op\<or> P Q, c''))"
    | Imp:    "nfa_of_pf n (Imp p q) c = 
                 (let (P, c') = nfa_of_pf n p c in
                  let (Q, c'') = nfa_of_pf n q c' in
                  (bool_comb op\<longrightarrow> P Q, c''))"
    | Exists: "nfa_of_pf n (Exist p) c = 
                 (let (c', A) = c_\<alpha> c n in
                  let (P, c'') = nfa_of_pf (Suc n) p c' in
                  (pres_DFA_exists_min_impl A P, c''))"
    | Forall: "nfa_of_pf n (Forall p) c = 
                 (let (c', A) = c_\<alpha> c n in
                  let (P, c'') = nfa_of_pf (Suc n) p c' in
                  (pres_DFA_forall_min_impl A P, c''))"
    | Neg:    "nfa_of_pf n (Neg p) c = 
                 (let (P, c') = nfa_of_pf n p c in
                  (complement P, c'))"

lemmas nfa_of_pf_induct =
  nfa_of_pf.induct [case_names Eq Le And Or Imp Exist Forall Neg]

lemma nfa_of_pf___correct: 
assumes "c_invar c"
shows "c_invar (snd (nfa_of_pf n p c)) \<and>
       nfa.invar (fst (nfa_of_pf n p c)) \<and>
       NFA_isomorphic_wf (nfa.\<alpha> (fst (nfa_of_pf n p c)))
                         (DFA_of_pf n p)"
using assms
proof (induct n p arbitrary: c rule: DFA_of_pf_induct )
  case (Eq n ks l c) note invar_c = this
  from cache_correct [OF invar_c, of n]
  show ?case
    by (auto simp add: pres_DFA_eq_ineq_impl_correct split: prod.split)
next
  case (Le n ks l c) note invar_c = this
  from cache_correct [OF invar_c, of n]
  show ?case
    by (auto simp add: pres_DFA_eq_ineq_impl_correct split: prod.split)
next
  case (And n p q c) 
  obtain P c' where [simp]: "nfa_of_pf n p c = (P, c')" by (rule PairE)
  obtain Q c'' where [simp]: "nfa_of_pf n q c' = (Q, c'')" by (rule PairE)

  from And(1)[of c] And(2)[of c'] And(3)
  show ?case 
    apply simp
    apply (intro conjI nfa.correct_isomorphic)
    apply simp_all
    apply (metis NFA_isomorphic_wf_\<Sigma> DFA_of_pf___correct)+
  done   
next
  case (Or n p q c) 
  obtain P c' where [simp]: "nfa_of_pf n p c = (P, c')" by (rule PairE)
  obtain Q c'' where [simp]: "nfa_of_pf n q c' = (Q, c'')" by (rule PairE)

  from Or(1)[of c] Or(2)[of c'] Or(3)
  show ?case 
    apply simp
    apply (intro conjI nfa.correct_isomorphic)
    apply simp_all
    apply (metis NFA_isomorphic_wf_\<Sigma> DFA_of_pf___correct)+
  done   
next
  case (Imp n p q c) 
  obtain P c' where [simp]: "nfa_of_pf n p c = (P, c')" by (rule PairE)
  obtain Q c'' where [simp]: "nfa_of_pf n q c' = (Q, c'')" by (rule PairE)

  from Imp(1)[of c] Imp(2)[of c'] Imp(3)
  show ?case 
    apply simp
    apply (intro conjI nfa.correct_isomorphic)
    apply simp_all
    apply (metis NFA_isomorphic_wf_\<Sigma> DFA_of_pf___correct)+
  done   
next
  case (Exist n p c)
  obtain c' A where [simp]: "c_\<alpha> c n = (c', A)" by (rule PairE)
  obtain P c'' where [simp]: "nfa_of_pf (Suc n) p c' = (P, c'')" by (rule PairE)

  from Exist(1)[of c'] Exist(2) cache_correct [of c n]
  show ?case 
    apply simp
    apply (intro conjI pres_DFA_exists_min_impl_correct)
    apply simp_all
    apply (metis NFA_isomorphic_wf_\<Sigma> DFA_of_pf___correct)+
  done   
next
  case (Forall n p c)
  obtain c' A where [simp]: "c_\<alpha> c n = (c', A)" by (rule PairE)
  obtain P c'' where [simp]: "nfa_of_pf (Suc n) p c' = (P, c'')" by (rule PairE)

  from Forall(1)[of c'] Forall(2) cache_correct [of c n]
  show ?case 
    apply simp
    apply (intro conjI pres_DFA_forall_min_impl_correct)
    apply simp_all
    apply (metis NFA_isomorphic_wf_\<Sigma> DFA_of_pf___correct)+
  done   
next
  case (Neg n p c)
  obtain P c' where [simp]: "nfa_of_pf n p c = (P, c')" by (rule PairE)

  from Neg(1)[of c] Neg(2)
  show ?case 
    apply simp
    apply (intro conjI nfa.correct_isomorphic)
    apply simp_all
  done   
qed


definition pf_to_nfa where
  "pf_to_nfa n pf = fst (nfa_of_pf n pf (c_init ()))" 

lemma pf_to_nfa___correct: 
shows "nfa.invar (pf_to_nfa n p)"
      "NFA_isomorphic_wf (nfa.\<alpha> (pf_to_nfa n p)) (DFA_of_pf n p)"
using nfa_of_pf___correct [of "c_init ()" n p]
unfolding pf_to_nfa_def
by (simp_all add: init_cache_OK)

lemma eval_pf_impl :
  "eval_pf pf [] = accept (pf_to_nfa 0 pf) []"
proof -
  note equiv_wf = pf_to_nfa___correct [of 0 pf]
  note NFA_accept_OK = accept_correct___isomorphic [OF equiv_wf, of "[]"]
  with DFA_of_pf___correct [of 0 pf] NFA_accept_OK 
  show ?thesis by simp
qed


end


locale presburger_label_set_cache_by_map_set = 
    s: StdSet s_ops + m: StdMap m_ops +
    set_image "set_op_\<alpha> s_ops" "set_op_invar s_ops" "set_op_\<alpha> s_ops" "set_op_invar s_ops" s_image
    for s_ops :: "(bool list, 'bl, _) set_ops_scheme"
    and m_ops :: "(nat, 'bl, 'm, _) map_ops_scheme" 
    and s_image
begin
  definition c_invar where
    "c_invar m \<equiv> m.invar m \<and>
      (\<forall>n bl. m.\<alpha> m n = Some bl \<longrightarrow> s.invar bl \<and> s.\<alpha> bl = {bv . length bv = n})"

  primrec c_\<alpha> where
     "c_\<alpha> m 0 = (m, s.sng [])"
   | "c_\<alpha> m (Suc n) =
      (case (m.lookup (Suc n) m) of Some bl \<Rightarrow> (m, bl) | None =>
       (let (m', bl) = c_\<alpha> m n in
        let bl' = s.union (s_image (\<lambda>l. True # l) bl) (s_image (\<lambda>l. False # l) bl) in
        let m'' = m.update (Suc n) bl' m' in
        (m'', bl')))" 

  lemma c_\<alpha>_correct :
    assumes "c_invar m"
    shows "c_invar (fst (c_\<alpha> m n)) \<and>
           s.invar (snd (c_\<alpha> m n)) \<and>
           s.\<alpha> (snd (c_\<alpha> m n)) = {bs. length bs = n}"
  using assms
  proof (induct n arbitrary: m)  
    case 0 thus ?case by (simp add: s.correct)
  next
    case (Suc n m)
    note ind_hyp = Suc(1)
    note invar_m = Suc(2)

    show ?case
    proof (cases "m.lookup (Suc n) m")
      case (Some bl)
      thus ?thesis
        apply (simp add: invar_m)
        apply (insert invar_m)
        apply (simp add: c_invar_def m.correct)
      done
    next
      case None note lookup_eq_none[simp] = this
      obtain m' bl where [simp]: "c_\<alpha> m n = (m', bl)" by (rule PairE)

      def bl' \<equiv> "set_op_union s_ops (s_image (op # True) bl) (s_image (op # False) bl)"

      from ind_hyp [OF invar_m] 
      have bl'_props: "s.invar bl'" "s.\<alpha> bl' = {bs. length bs = Suc n}" and invar_m': "c_invar m'"
          apply (simp_all add: s.correct bl'_def image_correct)
          apply (auto simp add: image_iff length_Suc_conv)
      done

      from invar_m'
      show ?thesis 
        by (simp add: bl'_def[symmetric] bl'_props c_invar_def m.correct)
    qed
  qed

  lemma  presburger_label_set_cache_OK :
    "presburger_label_set_cache s.\<alpha> s.invar c_\<alpha> c_invar m.empty"
    unfolding presburger_label_set_cache_def
    apply (simp add: c_\<alpha>_correct)
    apply (simp add: c_invar_def m.correct)
  done
end

end
