# Biweekly report for tracking progress

---

## Table of Contents

-   [01.03.2023 - 12.03.2023](#01032023---12032023)

---

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
        -   lemma `in_br_conv` needed to be added to a lot of subgoals
    -   :white_check_mark: repaired proof of lemma `Hopcroft_map2_step_compute_iM_correct`:
        -   only syntax issues and fixing old names of rules

-   #### Remarks

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