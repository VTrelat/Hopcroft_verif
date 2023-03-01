(*
  no_document use_thys ["This_Theory1", "This_Theory2"];
  use_thys ["That_Theory1", "That_Theory2", "That_Theory3"];
*)

no_document use_thys [
  "../Libs/Refine/Refine", 
  "../General/Accessible", 
  "~~/src/HOL/Library/afp/Presburger-Automata/DFS",
  "~~/src/HOL/Library/afp/Presburger-Automata/Presburger_Automata"];

use_thys ["NFA", "DFA", "LTS"];


no_document use_thys [
  "implementation/NFASpec"
];

use_thys ["Hopcroft_Minimisation", "Presburger_Adapt"];
