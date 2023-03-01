#!/bin/sh
export OCAMLRUNPARAM=l=64M
#ocamlbuild -clean
#ocamlbuild -libs nums,unix Automata_Minimise_Test.native Automata_Minimise_Test.p.native Presburger_Test.native Presburger_Test.byte Automata_Test.native

ocamlbuild -libs unix Automata_Minimise_Test.native Automata_Minimise_Test.p.native Presburger_Test.native Presburger_Test.p.native Presburger_Test.byte Automata_Test.native