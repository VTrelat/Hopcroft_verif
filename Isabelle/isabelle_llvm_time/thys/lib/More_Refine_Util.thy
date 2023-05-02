theory More_Refine_Util
imports "Automatic_Refinement.Refine_Util"
begin

  ML \<open>
  
    signature MORE_REFINE_UTIL = sig
      include REFINE_UTIL
      
      
      (* Prove premises of theorem by given tactics. Warning: Simultaneous semantics, 
        will fail/misbehave if tactic instantiates schematic that occurs in later premise to be proved *)
      val prove_prems: bool -> Proof.context -> thm -> (Proof.context -> int -> tactic) option list -> thm
      
    end
  
    
    structure More_Refine_Util : MORE_REFINE_UTIL = struct
      open Refine_Util
  
      fun prove_prems tryflag ctxt thm tacs = let
        
        fun mk_cnv [] = Conv.all_conv
          | mk_cnv (NONE::xs) = Conv.implies_concl_conv (mk_cnv xs)
          | mk_cnv (SOME _::xs) = Conv.implies_conv (Object_Logic.atomize ctxt) (mk_cnv xs)
      
        (* Atomize relevant premises *)  
        val thm = Conv.fconv_rule (mk_cnv tacs) thm
          

        fun prove t tac = Goal.prove ctxt [] [] t (fn {context=ctxt, ...} => 
          ALLGOALS (
            REPEAT_DETERM' (match_tac ctxt @{thms allI impI}) (* TODO: Maybe apply atomize-rules in reverse *)
            THEN' tac ctxt
          ) 
        )

        fun try_prove t tac =
          case (try (prove t) tac ) of SOME thm => thm
              | NONE => asm_rl
        
        val prove_t = (if tryflag then try_prove else prove)

        fun proves [] _ = []
          | proves _ [] = []
          | proves (_::ps) (NONE::tacs) = asm_rl :: proves ps tacs
          | proves (p::ps) (SOME tac :: tacs) = prove_t p tac :: proves ps tacs
          
        (* Prove premises *)  
        val pthms = proves (Thm.prems_of thm) tacs
        
        val thm = thm OF pthms
      in
        thm
      end  
  
    end
  
  
  \<close>




end
