# Bimonthly report for tracking progress

---

## Table of Contents

-   [01.03.2023 - 12.03.2023](#01032023---12032023)
-   [13.03.2023 - 26.03.2023](#13032023---26032023)
-   [27.03.2023 - 09.04.2023](#27032023---09042023)
-   [10.04.2023 - 23.04.2023](#10042023---23042023)
-   [24.04.2023 - 07.05.2023](#24042023---07052023)
-   [08.05.2023 - 21.05.2023](#08052023---21052023)
-   [Remarks](#remarks)

---

## 08.05.2023 - 21.05.2023

-   #### Notes
    -   Started to write formal assertions on the runtime analysis with the NREST framework on paper, respectively to the paper proof
        -   top-down strategy (abstract to implementation)
        -   started with the abstract level, see `Hopcroft_abstract` in `Hopcroft_Minimisation.thy`

## 24.04.2023 - 07.05.2023

-   #### Notes
    -   Read papers about the NREST framework and Isabelle / LLVM with time
    -   Added template theory `Hopcroft_Time`
    -   Experimented with the NREST framework

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
-   syntax of the form `xs[i := x]` for list updates --> `list_update xs i x`
-   `strong_UN_cong` --> `SUP_cong_simp`
