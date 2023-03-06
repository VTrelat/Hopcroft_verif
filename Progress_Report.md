# Biweekly report for tracking progress

-   ### 01.03.2023 - 14.03.2023
    -   start of the project: creation of the repository and the structure of the project. This was a lot to process since I had to go through $\approx$ 139k lines of code.
    -   :warning: I could find quite a number of typos — fixed — in the comments and the documentation.
    -   I have started to understand the refinement framework.
    -   those old theories needed to be updated to the current Isabelle version. I fixed all import related issues and syntax issues and got them to work again.
    -   **Remarks**:
        -   rule `PairE` is now `prod.exhaust`
        -   `def` command in Isar is now `define`
        -   `guess` command is has been replaced by an explicit `obtain`
        -   rule `prod_case_beta` is now `case_prod_beta`
        -   fixed `empty` which refers to the empty set to `Map.empty`
