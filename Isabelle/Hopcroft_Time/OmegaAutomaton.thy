(*  Title:       Omega Automata
*)

header {* Omega Automata *}

theory OmegaAutomaton
imports Main LTS SemiAutomaton 
        "../Libs/Automata_Merz/Buchi"
begin

text {* This theory defines omega automata. *}


datatype ('q, 'a, 'more) OmegaAutomaton =
   ExOmegaAutomaton "('q, 'a, 'more) SemiAutomaton_rec_scheme" 
                    "(('q, 'a, 'more) SemiAutomaton_rec_scheme \<Rightarrow> ('q word) \<Rightarrow> bool)"
 | UnOmegaAutomaton "('q, 'a, 'more) SemiAutomaton_rec_scheme" 
                    "(('q, 'a, 'more) SemiAutomaton_rec_scheme \<Rightarrow> ('q word) \<Rightarrow> bool)"

fun OmegaAutomaton_accept where
  "OmegaAutomaton_accept (ExOmegaAutomaton \<A> a_fun) w =
     (\<exists>r. SemiAutomaton_is_inf_run \<A> w r \<and> a_fun \<A> r)"
 | "OmegaAutomaton_accept (UnOmegaAutomaton \<A> a_fun) w =
     (\<forall>r. SemiAutomaton_is_inf_run \<A> w r \<longrightarrow> a_fun \<A> r)"

definition OmegaAutomaton_\<L> where
  "OmegaAutomaton_\<L> A = {w. OmegaAutomaton_accept A w}"

record ('q,'a) Buchi_rec =
  "('q, 'a) SemiAutomaton_rec" +
  \<F> :: "'q set"           -- "The set of accepting states"

definition SemiAutomaton_to_Buchi ::
  "('q, 'a, _) SemiAutomaton_rec_scheme \<Rightarrow> 'q set \<Rightarrow> ('q, 'a) Buchi_rec" where
  "SemiAutomaton_to_Buchi \<A> F =  \<lparr> \<Q> = \<Q> \<A>, \<Sigma> = \<Sigma> \<A>, \<Delta> = \<Delta> \<A>, \<I> = \<I> \<A>, \<F> = F \<rparr>"

lemma SemiAutomaton_to_Buchi_\<Q>[simp]:
  "\<Q> (SemiAutomaton_to_Buchi \<A> F) = \<Q> \<A>" unfolding SemiAutomaton_to_Buchi_def by simp

lemma SemiAutomaton_to_Buchi_\<Sigma>[simp]:
  "\<Sigma> (SemiAutomaton_to_Buchi \<A> F) = \<Sigma> \<A>" unfolding SemiAutomaton_to_Buchi_def by simp

lemma SemiAutomaton_to_Buchi_\<I>[simp]:
  "\<I> (SemiAutomaton_to_Buchi \<A> F) = \<I> \<A>" unfolding SemiAutomaton_to_Buchi_def by simp

lemma SemiAutomaton_to_Buchi_\<Delta>[simp]:
  "\<Delta> (SemiAutomaton_to_Buchi \<A> F) = \<Delta> \<A>" unfolding SemiAutomaton_to_Buchi_def by simp

lemma SemiAutomaton_to_Buchi_\<delta>[simp]:
  "\<delta> (SemiAutomaton_to_Buchi \<A> F) = \<delta> \<A>" unfolding \<delta>_def by simp

lemma SemiAutomaton_to_Buchi_\<F>[simp]:
  "\<F> (SemiAutomaton_to_Buchi \<A> F) = F" unfolding SemiAutomaton_to_Buchi_def by simp

definition BuchiAutomaton :: "('q, 'a, _) Buchi_rec_scheme \<Rightarrow> ('q, 'a, _) OmegaAutomaton" where
  "BuchiAutomaton \<A> = ExOmegaAutomaton \<A> (\<lambda>\<A> r. buchi_accepting (\<F> \<A>) r)"

definition BuchiAutomaton' :: "('q, 'a, _) Buchi_rec_scheme \<Rightarrow> ('q, 'a, _) OmegaAutomaton" where
  "BuchiAutomaton' \<A> = ExOmegaAutomaton \<A> (\<lambda>\<A> r. buchi_accepting' (\<F> \<A>) r)"


subsection {* To Merz *}

definition SemiAutomaton_to_ndtable_ext :: "_ \<Rightarrow> ('q, 'a, _) SemiAutomaton_rec_scheme \<Rightarrow> ('q, 'a, _) ndtable_scheme" where
  "SemiAutomaton_to_ndtable_ext m \<A> = 
   \<lparr> initial = \<I> \<A>, trans = (\<lambda>q a. {q'. (q, a, q') \<in> \<Delta> \<A>}), \<dots> = m\<rparr>"

abbreviation "SemiAutomaton_to_ndtable \<equiv> (SemiAutomaton_to_ndtable_ext ())"

lemma SemiAutomaton_to_ndtable_ext___SemiAutomaton_to_Buchi[simp] :
  "SemiAutomaton_to_ndtable_ext m (SemiAutomaton_to_Buchi \<A> F) =
   SemiAutomaton_to_ndtable_ext m \<A>"
unfolding SemiAutomaton_to_ndtable_ext_def by simp

lemma SemiAutomaton_to_ndtable_ext_\<I> [simp]:
  "initial (SemiAutomaton_to_ndtable_ext m \<A>) = \<I> \<A>"
unfolding SemiAutomaton_to_ndtable_ext_def by simp

lemma SemiAutomaton_to_ndtable_ext_\<Delta> [simp]:
  "(q' \<in> (trans (SemiAutomaton_to_ndtable_ext m \<A>) q a)) = ((q, a, q') \<in> \<Delta> \<A>)"
unfolding SemiAutomaton_to_ndtable_ext_def by simp

lemma SemiAutomaton_to_ndtable_ext___nd_exec_fragment [simp] :
  "nd_exec_fragment (SemiAutomaton_to_ndtable_ext m \<A>) inp run \<longleftrightarrow>
   LTS_is_fin_run (\<Delta> \<A>) inp run"
unfolding nd_exec_fragment_def LTS_is_fin_run_def 
by simp

lemma SemiAutomaton_to_ndtable_ext___nd_execution [simp] :
  "nd_execution (SemiAutomaton_to_ndtable_ext m \<A>) inp run \<longleftrightarrow>
   LTS_is_inf_run (\<Delta> \<A>) inp run"
unfolding nd_execution_def LTS_is_inf_run_def  by simp

lemma SemiAutomaton_to_ndtable_ext___nd_run [simp] :
  "nd_run (SemiAutomaton_to_ndtable_ext m \<A>) inp run \<longleftrightarrow>
   SemiAutomaton_is_inf_run \<A> inp run"
unfolding nd_run_def SemiAutomaton_is_inf_run_def by auto

lemma SemiAutomaton_to_ndtable_ext___det_table [simp] :
assumes "\<I> \<A> \<noteq> {}"
shows "det_table (SemiAutomaton_to_ndtable_ext m \<A>) \<longleftrightarrow>
       SemiAutomaton_is_deterministic \<A>"
using assms
unfolding det_table_def atmost_one_def SemiAutomaton_is_deterministic_def LTS_is_deterministic_def
by auto

lemma SemiAutomaton_to_ndtable_ext___det_table_impl :
  "SemiAutomaton_is_deterministic \<A> \<Longrightarrow> det_table (SemiAutomaton_to_ndtable_ext m \<A>)"
unfolding det_table_def atmost_one_def 
          SemiAutomaton_is_deterministic_def LTS_is_deterministic_def
by auto

lemma (in SemiAutomaton) SemiAutomaton_to_ndtable___states_of :
  "states_of (SemiAutomaton_to_ndtable_ext m \<A>) \<subseteq> \<Q> \<A>"
unfolding states_of_def SemiAutomaton_to_ndtable_ext_def
using \<Delta>_consistent \<I>_consistent
by auto

lemma SemiAutomaton_to_ndtable_ext___one_step [simp] :
  "one_step (SemiAutomaton_to_ndtable_ext m \<A>) =
   LTS_forget_labels (\<Delta> \<A>)"
unfolding one_step_def LTS_forget_labels_def 
by simp

definition BuchiAutomaton_to_ndbuchi :: "('q, 'a, _) Buchi_rec_scheme \<Rightarrow> ('q, 'a) ndbuchi" where
  "BuchiAutomaton_to_ndbuchi \<A> = 
   SemiAutomaton_to_ndtable_ext \<lparr>accept = \<F> \<A>\<rparr> \<A>"

lemma BuchiAutomaton_to_ndbuchi_alt_def :
  "BuchiAutomaton_to_ndbuchi \<A> = 
   \<lparr> initial = \<I> \<A>, trans = (\<lambda>q a. {q'. (q, a, q') \<in> \<Delta> \<A>}), accept = \<F> \<A>\<rparr>"
unfolding BuchiAutomaton_to_ndbuchi_def SemiAutomaton_to_ndtable_ext_def by simp

lemma BuchiAutomaton_to_ndbuchi___accept[simp]:
  "accept (BuchiAutomaton_to_ndbuchi \<A>) = \<F> \<A>" 
  unfolding BuchiAutomaton_to_ndbuchi_alt_def by simp

lemmas BuchiAutomaton_to_ndbuchi___accept'[simp] =
  BuchiAutomaton_to_ndbuchi___accept[unfolded BuchiAutomaton_to_ndbuchi_def]

lemma BuchiAutomaton_to_ndbuchi___initial[simp]:
  "initial (BuchiAutomaton_to_ndbuchi \<A>) = \<I> \<A>" 
  unfolding BuchiAutomaton_to_ndbuchi_alt_def by simp

lemma BuchiAutomaton_to_ndbuchi_correct :
  "OmegaAutomaton_\<L> (BuchiAutomaton \<A>) =
   buchi_language (BuchiAutomaton_to_ndbuchi \<A>)"
unfolding buchi_language_def OmegaAutomaton_\<L>_def BuchiAutomaton_def
by (simp add: set_eq_iff BuchiAutomaton_to_ndbuchi_def)

lemma BuchiAutomaton_to_ndbuchi_correct' :
  "OmegaAutomaton_\<L> (BuchiAutomaton' \<A>) =
   buchi_language' (BuchiAutomaton_to_ndbuchi \<A>)"
unfolding buchi_language'_def OmegaAutomaton_\<L>_def BuchiAutomaton'_def
by (simp add: set_eq_iff BuchiAutomaton_to_ndbuchi_def)


definition comb_BuchiAutomaton :: 
  "('q1, 'a, _) Buchi_rec_scheme \<Rightarrow> 
   ('q2, 'a, _) Buchi_rec_scheme \<Rightarrow> ('q1 + 'q2, 'a) Buchi_rec" where
"comb_BuchiAutomaton \<A>1 \<A>2 == SemiAutomaton_to_Buchi (comb_SemiAutomaton \<A>1 \<A>2)
   ((\<F> \<A>1) <+> (\<F> \<A>2))"

lemma BuchiAutomaton_to_ndbuchi_comb [simp] :
   "BuchiAutomaton_to_ndbuchi (comb_BuchiAutomaton \<A>1 \<A>2) =
    buchi_union (BuchiAutomaton_to_ndbuchi \<A>1) (BuchiAutomaton_to_ndbuchi \<A>2)"
apply (simp add: BuchiAutomaton_to_ndbuchi_def comb_BuchiAutomaton_def
         buchi_union_def SemiAutomaton_to_ndtable_ext_def LTS_comb_def)
apply (rule ext)
apply (rule ext)
apply (auto simp add: set_eq_iff split: sum.splits)
done

lemma BuchiAutomaton_comb_correct :
  "OmegaAutomaton_\<L> (BuchiAutomaton (comb_BuchiAutomaton \<A>1 \<A>2)) =
   OmegaAutomaton_\<L> (BuchiAutomaton \<A>1) \<union> OmegaAutomaton_\<L> (BuchiAutomaton \<A>2)"
by (simp add: BuchiAutomaton_to_ndbuchi_correct buchi_union)

lemma BuchiAutomaton_comb_correct' :
  "OmegaAutomaton_\<L> (BuchiAutomaton' (comb_BuchiAutomaton \<A>1 \<A>2)) =
   OmegaAutomaton_\<L> (BuchiAutomaton' \<A>1) \<union> OmegaAutomaton_\<L> (BuchiAutomaton' \<A>2)"
by (simp add: BuchiAutomaton_to_ndbuchi_correct' buchi_union')

end
