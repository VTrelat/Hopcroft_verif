\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
section \<open>Final Hoare Triples for heapsort and introsort\<close>
theory Sorting_Results
imports Sorting_Export_Code
begin

paragraph \<open>Summary\<close>
text \<open>This theory collects the final Hoare Triples for heapsort and introsort.
  They do not involve the NREST monad any more. For inspecting their validity, only the
  LLVM semantics and the definitions of Hoare triples must be checked.
  By summing over all currencies, we project the fine-grained cost functions used in the
  Hoare Triples down to functions in @{typ "nat \<Rightarrow> nat"} and examine their asymptotic complexity.\<close>


subsection \<open>Heapsort\<close>


context sort_impl_context begin

lemma "slice_sort_aux xs\<^sub>0 xs l h \<equiv> (length xs = length xs\<^sub>0 \<and> take l xs = take l xs\<^sub>0
                    \<and> drop h xs = drop h xs\<^sub>0 \<and> sort_spec (\<^bold><) (slice l h xs\<^sub>0) (slice l h xs))"
  by simp

text \<open>Final correctness lemma:\<close>
lemma 
  assumes "l \<le> h \<and> h \<le> length xs\<^sub>0"
  shows "llvm_htriple ($heapsort_impl_cost l h \<and>* arr_assn xs\<^sub>0 p
           \<and>* snat_assn l l' \<and>* snat_assn h h')
        (heapsort_impl p l' h')
      (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>(slice_sort_aux xs\<^sub>0 xs l h) \<and>* arr_assn xs r) s)
            \<and>* snat_assn l l' \<and>* snat_assn h h')"
  using assms
  apply(rule heapsort_final_hoare_triple[unfolded hn_ctxt_def])
  done

(*text \<open>@{term heapsort_impl_cost} projected to a function @{typ "nat \<Rightarrow> nat"} \<close>
lemma "heapsort3_allcost (h-l) = project_all (heapsort_impl_cost l h)"
  by (simp add: heapsort3_allcost_is_heapsort3_allcost' heapsort3_allcost'_Sum_any)
  *)

end

lemma "heapsort3_allcost n = 12 + 187 * n  + 82 * (n * Discrete.log n)"
  unfolding heapsort3_allcost_def by simp
  
lemma "(\<lambda>x. real (heapsort3_allcost x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  by (fact heapsort3_allcost_nlogn)


subsection \<open>Introsort\<close>

subsubsection \<open>For Nats\<close>

(*
lemma "introsort3_allcost n = 4693 + 5 *  Discrete.log n + 231 * n + 455 * (n * Discrete.log n)"
  by(fact introsort3_allcost_simplified)

  
lemma "(\<lambda>x. real (introsort3_allcost x)) \<in> \<Theta>(\<lambda>n. (real n)*(ln (real n)))"
  by (fact introsort3_allcost_nlogn)
*)
(* Final results for unat_sort: *)  
thm unat_sort.introsort_final_hoare_triple[no_vars] (* Hoare triple *)

lemma "l \<le> h \<and> h \<le> length xs\<^sub>0 \<Longrightarrow>
  llvm_htriple 
    ($unat_sort.introsort_impl_cost (h - l) \<and>* unat_sort.arr_assn xs\<^sub>0 p 
        \<and>* snat_assn l l' \<and>* snat_assn h h') 
      (unat_sort_introsort_impl p l' h')
    (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>unat_sort.slice_sort_aux xs\<^sub>0 xs l h \<and>* unat_sort.arr_assn xs r) s)
        \<and>* snat_assn l l' \<and>* snat_assn h h')"
  apply(rule unat_sort.introsort_final_hoare_triple) .

(* Cost estimation *)
  
theorem "(\<lambda>n. real (project_all (unat_sort.introsort_impl_cost n)))
            \<in> \<Theta>(\<lambda>n. (real n) * (ln (real n)))"
  unfolding unat_sort_allcost_simp
  by auto2


subsubsection \<open>For Strings\<close>


thm string_sort.introsort_final_hoare_triple[no_vars]  (* Hoare triple *)
 string_sort_introsort_cost

lemma "l \<le> h \<and> h \<le> length xs\<^sub>0 \<Longrightarrow>
  llvm_htriple 
    ($string_sort.introsort_impl_cost m (h - l) \<and>* string_sort.arr_assn m xs\<^sub>0 p
         \<and>* snat_assn l l' \<and>* snat_assn h h') 
      (string_sort_introsort_impl p l' h')
    (\<lambda>r. (\<lambda>s. \<exists>xs. (\<up>string_sort.slice_sort_aux xs\<^sub>0 xs l h \<and>* string_sort.arr_assn m xs r) s)
         \<and>* snat_assn l l' \<and>* snat_assn h h')"
  apply(rule string_sort.introsort_final_hoare_triple) .


lemma "(\<lambda>(m, n). real (project_all (string_sort.introsort_impl_cost m n)))
             \<in> \<Theta>\<^sub>2 (\<lambda>(m, n). real m * real n * ln (real n))"
  apply(rule string_sort_introsort_cost) .


subsection \<open>Dynamic arrays\<close>

lemma
  assumes "Sepref_Basic.is_pure A"
  and "2 * length a < max_snat LENGTH('c::len2)"
  and "8 \<le> LENGTH('c)"
shows dyn_array_push_impl_ht:
    "llvm_htriple
      ($da_append_spec_cost \<and>* al_assn' TYPE('c) A a ai \<and>* A b bi)
         (dyn_array_push_impl ai bi)
     (\<lambda>r. (\<lambda>s. \<exists>x. (\<up>(x = a @ [b]) \<and>* dynamic_array_assn A x r) s) \<and>* A b bi)"
  apply(rule introsort_final_hoare_triple[OF assms]) .

lemma "(\<lambda>_::nat. real (project_all da_append_spec_cost)) \<in> \<Theta>(\<lambda>_::nat. 1::real)"
  unfolding all_da_append_spec_cost
  by auto2


end
