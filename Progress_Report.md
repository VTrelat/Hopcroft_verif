# Biweekly report for tracking progress

---

## Table of Contents

-   [01.03.2023 - 12.03.2023](#01032023---12032023)
-   [13.03.2023 - 26.03.2023](#13032023---26032023)

---

## 13.03.2023 - 26.03.2023

-   #### Notes
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map2_step_compute_iM_cache_swap_check_loop_correct`
        -   definition `Hopcroft_map2_step_compute_iM_cache_swap_check_loop` was broken: two arguments of `FOREACHoi` were swapped
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map2_f_correct`
        -   added lemma `Hopcroft_map2_state_rel_full_rewrite` to be able to apply rule `Hopcroft_map2_step_no_spec_correct_full`
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map2_correct`
        -   Modified some applications of rules because subgoals were slightly different
    -   :x: proof of lemma `Hopcroft_impl_step_correct` is broken

## 01.03.2023 - 12.03.2023

-   #### Notes

    -   start of the project: creation of the repository and the structure of the project. This was a lot to process since I had to go through $\approx$ 139k lines of code.
    -   :warning: I could find quite a number of typos — fixed — in the comments and the documentation.
    -   I have started to understand the refinement framework.
    -   reading and understanding the theory `Hopcroft_Minimisation.thy`
    -   those old theories needed to be updated to the current Isabelle version. I fixed all import related issues and syntax issues and got them to work again.
    -   :white_check_mark: repaired proof of lemma `Hopcroft_precompute_step_correct` ~~is broken~~:
        -   use of rule `inj_on_id` that I do not understand
        -   I found another way to fix the first subgoals ~~but one is remaining that I cannot fix~~
        -   for the last subgoal, I found an explicit way to prove it but ~~am not sure if it is the shortest way to do it~~ Peter Lammich helped me to find a shorter proof
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map_step_correct`:
        -   slightly modified the structure of the proof because rule `FOREACHi_refine` could not be applied anymore
        -   structural modifications created a new subgoal but it was easily proved
    -   Added missing lemma `RES_refine_sv` to `Refine_Basic.thy`
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map2_step_correct`:
        -   some subgoals needed to be reordered
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map2_step_compute_iM_correct`:
        -   only syntax issues and fixing old names of rules

-   #### Remarks
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
