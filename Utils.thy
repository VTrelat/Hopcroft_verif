(*
    Author:     Vincent Trélat <vincent.trelat@depinfonancy.net>
*)

theory Utils
  imports Main "HOL-Library.Multiset"
begin

definition subset_mset_rel :: "('a multiset * 'a multiset) set" where
  "subset_mset_rel \<equiv> {(A,B). A <# B}"

primrec multiset_of :: "'a list \<Rightarrow> 'a multiset" where
  "multiset_of [] = {#}" |
  "multiset_of (a # x) = multiset_of x + {# a #}"


lemma multiset_of_append [simp]:
  "multiset_of (xs @ ys) = multiset_of xs + multiset_of ys"
  by (induct xs arbitrary: ys) (auto simp: add_ac)

lemma triple_conjI:
  "\<lbrakk>P \<and> Q; R\<rbrakk> \<Longrightarrow> P \<and> Q \<and> R"
  by simp
end