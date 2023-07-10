# Bimonthly report for tracking progress

---

## Table of Contents

-   [01.03.2023 - 12.03.2023](#01032023---12032023)
-   [13.03.2023 - 26.03.2023](#13032023---26032023)
-   [27.03.2023 - 09.04.2023](#27032023---09042023)
-   [10.04.2023 - 23.04.2023](#10042023---23042023)
-   [24.04.2023 - 07.05.2023](#24042023---07052023)
-   [08.05.2023 - 21.05.2023](#08052023---21052023)
-   [22.05.2023 - 04.06.2023](#22052023---04062023)
-   [05.06.2023 - 18.06.2023](#05062023---18062023)
-   [19.06.2023 - 02.07.2023](#19062023---02072023)
-   [03.07.2023 - 16.07.2023](#03072023---16072023)
-   [Remarks](#remarks)

---

<div style="text-align: justify">

## 03.07.2023 - 16.07.2023

-   #### Notes

    - Cleaned up the proof of lemma `estimate2_decrease`
    - I am now at the interesting part of the project : the inequality in `estimate2_decrease` is large, we want a strict one.

---

## 19.06.2023 - 02.07.2023

-   #### Notes

    -   Work on the estimate for the time spent in the loop, see lemma `estimate2_decrease`

        -   Now working on a simplified estimate `estimate2` which is easier to work with but still captures the essential idea (being the linearithmic time):

            > Instead of proving that the following quantity decreases:
            > $$\sum_{(a, C)\in L} |\overset{\hookleftarrow{a}}{C}| \log|C| + \sum_{(a, C)\in ((\Sigma \times P)\setminus L)} |\overset{\hookleftarrow{a}}{C}| \log\frac{|C|}{2}$$
            > We remove the halving factor in the second sum, which allows us to gather the two sums into one over $\Sigma \times P$:
            > $$\sum_{(a, C)\in \Sigma \times P} |\overset{\hookleftarrow{a}}{C}| \log|C|$$

            The reason of this change is that with the halving factor, we would have to show that for a state transition $(P, L) \rightarrow (P', L')$, we would have to examine all cases for all blocks whether they are splitters (or not) or whether they are split by some other splitter (or not) or whether there are new splitters created from this splitter (or not). This would be very tedious to formalize. Here are some things I tried:

            -   Splitters of the workset can be uniquely characterized thanks to '$a$-$q$-splitters'. It is defined as follows. For any $a \in \Sigma$ and any $q \in \mathcal{Q}$, there is a unique block $B$ of the partition containing $q$. Now, either $(a, B)$ is a splitter i.e. is in the workset and is the $a$-$q$-splitter or not. I used the option type in Isabelle. This is a good characterization of the splitters but it is not easy to work with it. For example, if we want to show that the number of splitters decreases, we would have to show that the number of $a$-$q$-splitters decreases for any $a \in \Sigma$ and any $q \in \mathcal{Q}$. This is not easy to formalize.

        -   The estimate `estimate1` was defined in Isabelle as the sum of a (finite) set as `∑{?f s | s. s ∈ L}` (skipping over the details). This is incorrect because the aforementioned function `?f` is probably not injective! Thus, this sum was less than or equal to the actual sum that we want to prove to decrease. Here are the fixes that I tried:
            -   The only way that I found to 'fix the injectivity issue' is to sum over multisets instead. The problem was that in the proof, I still need to distinguish between blocks that are split or not. What is convenient with blocks is that they are split iff they do not appear in the next partition. In other words, given the state transition $(P, L) \rightarrow (P', L')$, none of the blocks in $P \cap P'$ are split and all of the blocks in $P \setminus (P \cap P')$ are.
            -   Given this observation, I thought it would be convenient to have a structure that allows for induction (just in case at first) so I modified the sum again to lists. In order to keep the properties of multisets, those are not just any lists but permutations of those multisets. Thus, we can work on lists and write inductive properties on the sums while keeping the flexibility of multisets. Yet, this adds some overhead because of the permutations, but it allows for the following:
                > For all $(a, C) \in \Sigma \times P$, we are interested in whether $C$ is split or not, i.e. whether $C \in P \cap P'$ or not. We can easily prove that there exists a (list) permutation `xs` of $\Sigma \times P$ such that `xs` can be written as `xs1 @ xs2` where all elements in `xs1` are split and all elements in `xs2` are not split.
                > Likewise, we can obtain `xs'`, `xs1'` and `xs2'` for the next state $(P', L')$.
                >
                > Then, it is easy to see that `xs2` and `xs2'` are permutations of each other, so summing over them is the same, i.e.:
                > $$\forall f \sum_{x\in xs2} f(x) = \sum_{x\in xs2'} f(x)$$
                >
                > Thus, the state of the proof can be reduced to showing that the sum over `xs1'` is less than or equal to the sum over `xs1`:
                > $$\sum_{(a, C)\in xs1'} |\overset{\hookleftarrow{a}}{C}| \log|C| \leq \sum_{(a, C)\in xs1} |\overset{\hookleftarrow{a}}{C}| \log|C|$$
                >
                > To show this, we show that every element in `xs1` is split into two elements in `xs1'` and we show that we can construct a bijection between both sets (of lists) using the following property:
                > For any splitter $(a,B)$ in `xs1`, we can find two unique blocks $B'$ and $B''$ in `xs1'` such that $(a, B')$ and $(a, B'')$ are in `xs1'` and $B'$ and $B''$ are the result of splitting $B$ in the new partition $P'$. We define a function $f$ using this property and show that the image of `xs1` by $f$ is (a permutation of) `xs1'` and that $f$ is injective on `set xs1`.
                >
                > If $f_1$ and $f_2$ are the two components of $f$, and if for any $(a, C)$, $(a, C)_{[1]} := a$ and $(a, C)_{[2]} := C$, then we can show that:
                > $$\forall x \in \text{set }\texttt{xs1}, f_1(x)_{[1]} = f_2(x)_{[1]} = x_{[1]}$$
                > This reduces the proof to showing the following:
                > $$\sum_{x\in xs1}\left( |\overset{\hookleftarrow{x_{[1]}}}{f_1(x)_{[2]}}| \log|f_1(x)_{[2]}| + |\overset{\hookleftarrow{x_{[1]}}}{f_2(x)_{[2]}}| \log|f_2(x)_{[2]}| \right) \leq \sum_{x\in xs1} |\overset{\hookleftarrow{x_{[1]}}}{x_{[2]}}| \log|x_{[2]}|$$
                >
                > A way to show this is to show the following:
                > $$\forall x \in \text{set }\texttt{xs1}, |\overset{\hookleftarrow{x_{[1]}}}{f_1(x)_{[2]}}| \log|f_1(x)_{[2]}| + |\overset{\hookleftarrow{x_{[1]}}}{f_2(x)_{[2]}}| \log|f_2(x)_{[2]}| \leq |\overset{\hookleftarrow{x_{[1]}}}{x_{[2]}}| \log|x_{[2]}| \qquad (1)$$
                > This is easy because by definition of $f$:
                > $$\forall x \in \text{set }\texttt{xs1}, f_1(x)_{[2]} \cup f_2(x)_{[2]} = x_{[2]} \land f_1(x)_{[2]} \cap f_2(x)_{[2]} = \varnothing \qquad (2)$$
                >
                > Using algebraic properties of the logarithm, we can show that
                > $$a \log x + b \log y \le (a+b) \log (x+y) \qquad (3)$$
                > Using properties of the cardinal for finite sets in $(2)$ together with $(3)$, we show $(1)$ and conclude the proof.

</div>

## 05.06.2023 - 18.06.2023

-   #### Notes
    -   Work on the estimate for the time spent in the loop
        -   Work on paper and in Isabelle: I tried to define some predicates from which I could be able to derive the time spent in the loop
        -   Struggling to formalize my ideas from the paper proof to Isabelle
    -   Added some details in `proof.tex`

## 22.05.2023 - 04.06.2023

-   #### Notes
    -   Work on the estimate for the time spent in the loop
        -   Work on paper and in Isabelle: I tried to define some predicates from which I could be able to derive the time spent in the loop
        -   Struggling to formalize my ideas from the paper proof to Isabelle
    -   Started to prove some lemmas
    -   Split document `main.tex` into `report.tex` and `proof.tex`
        -   `proof.tex` will contain the detailed paper proof for the time complexity
        -   `report.tex` will contain the report for the internship with fewer details

---

## 08.05.2023 - 21.05.2023

-   #### Notes

    -   Started to write formal assertions on the runtime analysis with the NREST framework on paper, respectively to the paper proof

        -   top-down strategy (abstract to implementation)
        -   started with the abstract level, see `Hopcroft_abstract` in `Hopcroft_Minimisation.thy`

    -   Started to build Isabelle theories for time analysis (see [Hopcroft_Time](./Isabelle/Hopcroft_Time/))
        -   Peter helped me to get started with the abstract level

---

## 24.04.2023 - 07.05.2023

-   #### Notes
    -   Read papers about the NREST framework and Isabelle / LLVM with time
    -   Added template theory `Hopcroft_Time`
    -   Experimented with the NREST framework

---

## 10.04.2023 - 23.04.2023

-   #### Notes
    -   ✅ finished paper proof for time complexity (see [here](./LaTeX/main.pdf))
    -   :x: Peter Lammich helped me to solve some subgoals in the broken parts of `NFAByLTS` but it is still broken

---

<!--
[c28]		Maximilian P. L. Haslbeck, Peter Lammich:
Refinement with Time - Refining the Run-Time of Algorithms in Isabelle/HOL. ITP 2019: 20:1-20:18

[j9]		Maximilian P. L. Haslbeck, Peter Lammich:
For a Few Dollars More: Verified Fine-Grained Algorithm Analysis Down to LLVM. ACM Trans. Program. Lang. Syst. 44(3): 14:1-14:36 (2022)
-->

## 27.03.2023 - 09.04.2023

-   #### Notes
    -   :x: theory `NFAByLTS` is still broken
    -   :x: advances in the proof of lemma `NFA_construct_reachable_impl_correct` but two subgoals are still unproved.  
        I think the problem is that we would have to prove that `nfa_α (Qs, As, D0, Is, Fs, ⦇nfa_prop_is_complete_deterministic = det, nfa_prop_is_initially_connected = True⦈)` is an NFA for things to work correctly. In particular, we would get `s.α Fs ⊆ s.α Qs`.
    -   :x: theory `RBT_NFAImpl` is still broken:
        -   Isabelle seems to struggle with abbreviations, e.g. `lsnd` and `lss`, which causes some proofs to fail (nitpick even finds counterexamples)
    -   :x: theory `RBTSetImpl` is still broken:
        -   :x: definitions for `rs_image_filter` and `rs_image` are still undefined
    -   **leave out Isabelle implementation issues for the moment**
    -   started paper proof for time complexity based on Hopcroft's original 1971 paper
        -   quite unclear, difficult to read
        -   some arguments are claimed without really proving them
        -   the final result is that the complexity is $O(n \log n)$, which strictly speaking is wrong. It should be $O(mn \log n)$

---

## 13.03.2023 - 26.03.2023

-   #### Notes

    -   ✅ repaired proof of lemma `Hopcroft_map2_step_compute_iM_cache_swap_check_loop_correct`
        -   definition `Hopcroft_map2_step_compute_iM_cache_swap_check_loop` was broken: two arguments of `FOREACHoi` were swapped
    -   ✅ repaired proof of lemma `Hopcroft_map2_f_correct`
        -   added lemma `Hopcroft_map2_state_rel_full_rewrite` to be able to apply rule `Hopcroft_map2_step_no_spec_correct_full`
    -   ✅ repaired proof of lemma `Hopcroft_map2_correct`
        -   Modified some applications of rules because subgoals were slightly different
    -   ✅ repaired proof of lemma `Hopcroft_impl_step_correct` ~~is broken~~

        -   the proof in apply-style is quite long and can probably be shortened
        -   the previous proof was way shorter but some rules could not be applied

    -   ✅ repaired proof of lemma `class_map_init_pred_code_correct`
        -   unprovable subgoal due to application of the method `refine_transfer` which was mistakenly applying wrong rules. Surprisingly, the proof was still converging for some subgoals but made others unprovable.
        -   Peter Lammich found a way to fix this issue with the following trick:
            ```
            declare cm_it.iteratei_rule[refine_transfer]
            declare s.iteratei_correct[refine_transfer del]
            ```
    -   added code generation with the help of Peter Lammich and the following trick:

        ```
        setup Locale_Code.open_block
        interpretation hop_impl ...
        setup Locale_Code.close_block
        ```

    -   :white_check_mark: **old theory `Hopcroft_Minimisation` is fully repaired**
    -   added $\LaTeX$ template report for the final report
    -   :x: to make it a suitable AFP entry, need to add a final explicit theorem stating that the algorithm is correct and actually minimises a DFA on the lowest level (i.e. implementation)
    -   :x: to achieve this, we need theory `RBT_Presburger_Impl` and its imports to be repaired:
        -   :white_check_mark: repaired theory `LTSByLTS_DLTS`
        -   :white_check_mark: repaired theory `LTSGA`
        -   :white_check_mark: repaired theory `LTSImpl`
        -   :white_check_mark: repaired theory `TripleSetSpec`
        -   :white_check_mark: repaired theory `DLTSByMap`
        -   :white_check_mark: repaired theory `NFAConstruct`
        -   :white_check_mark: repaired theory `NFASpec` ~~is broken~~
        -   :white_check_mark: repaired theory `NFAGA` ~~is broken~~
        -   :white_check_mark: repaired theory `AccessibleImpl` ~~is broken~~
        -   :white_check_mark: repaired theory `Presburger_Adapt` ~~is broken~~
        -   :white_check_mark: repaired theory `Presburger_Automata` ~~is broken~~
        -   :x: theory `RBT_NFAImpl` is broken
            -   Isabelle seems to struggle with abbreviations, e.g. `lsnd` and `lss`, which causes some proofs to fail (nitpick even finds counterexamples)
        -   :x: theory `NFAByLTS` is broken
            -   :white_check_mark: repaired proof of lemma `hopcroft_lts_copy_correct` ~~is broken~~
            -   :white_check_mark: repaired proof of lemma `right_quotient_lists_impl_code` ~~is broken~~
            -   :x: proof of lemma `NFA_construct_reachable_impl_correct` is broken and I cannot fix it
    -   ✅ **theory `Hopcroft_Minimisation` is fully repaired**

---

## 01.03.2023 - 12.03.2023

-   #### Notes

    -   start of the project: creation of the repository and the structure of the project. This was a lot to process since I had to go through $\approx$ 139k lines of code.
    -   ⚠️ I could find quite a number of typos — fixed — in the comments and the documentation.
    -   I have started to understand the refinement framework.
    -   reading and understanding the theory `Hopcroft_Minimisation.thy`
    -   those old theories needed to be updated to the current Isabelle version. I fixed all import related issues and syntax issues and got them to work again.
    -   ✅ repaired proof of lemma `Hopcroft_precompute_step_correct` ~~is broken~~:
        -   use of rule `inj_on_id` that I do not understand
        -   I found another way to fix the first subgoals ~~but one is remaining that I cannot fix~~
        -   for the last subgoal, I found an explicit way to prove it but ~~am not sure if it is the shortest way to do it~~ Peter Lammich helped me to find a shorter proof
    -   ✅ repaired proof of lemma `Hopcroft_map_step_correct`:
        -   slightly modified the structure of the proof because rule `FOREACHi_refine` could not be applied anymore
        -   structural modifications created a new subgoal but it was easily proved
    -   Added missing lemma `RES_refine_sv` to `Refine_Basic.thy`
    -   ✅ repaired proof of lemma `Hopcroft_map2_step_correct`:
        -   some subgoals needed to be reordered
    -   ✅ repaired proof of lemma `Hopcroft_map2_step_compute_iM_correct`:
        -   only syntax issues and fixing old names of rules

## Remarks

-   I think lemma `in_br_conv` should be added as a simp rule
-   `def` --> `define`
-   `guess` --> `obtain`
-   `PairE` --> `prod.exhaust`
-   `prod_case_beta` --> `case_prod_beta`
-   `empty` --> `Map.empty`
-   `the.simps` --> `option.sel`
-   `op f` --> `(f)` for any function `f`
-   `map_pair_inj_on` --> `map_prod_inj_on`
-   `Option.map` --> `map_option`
-   `br_single_valued` --> `br_sv`
-   `rprod` --> `prod_rel`, adjusted with `prod_rel_syn`
-   `pair_collapse` --> `prod.collapse`
-   `strong_UN_cong` --> `SUP_cong_simp`
