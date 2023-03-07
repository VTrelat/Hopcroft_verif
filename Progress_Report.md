# Biweekly report for tracking progress

-   #### 01.03.2023 - 14.03.2023
    ##### Notes
    -   start of the project: creation of the repository and the structure of the project. This was a lot to process since I had to go through $\approx$ 139k lines of code.
    -   :warning: I could find quite a number of typos — fixed — in the comments and the documentation.
    -   I have started to understand the refinement framework.
    -   reading and understanding the theory `Hopcroft_Minimisation.thy`
    -   those old theories needed to be updated to the current Isabelle version. I fixed all import related issues and syntax issues and got them to work again.
    -   :x: proof of lemma `Hopcroft_precompute_step_correct` is broken:
        -   use of rule `inj_on_id` that I do not understand
        -   I found another way to fix the first subgoals but one is remaining that I cannot fix
    ##### Remarks
    -   `def` --> `define`
    -   `guess` --> `obtain`
    -   `PairE` --> `prod.exhaust`
    -   `prod_case_beta` --> `case_prod_beta`
    -   `empty` --> `Map.empty`
