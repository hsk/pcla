all:
	ocamlyacc Parser.mly
	rm Parser.mli
	ocamllex Lexer.mll
	ocamlc -o oclaire -I lib \
		FOL.ml LK.ml Claire.ml Parser.ml Lexer.ml \
		Env.ml Typecheck.ml CheckerCommand.ml Checker.ml \
		lib/Commands.ml lib/EqCommands.ml \
		Main.ml
	rm -rf *.cm* lib/*.cm* Parser.ml Lexer.ml a.out
	./oclaire lib/hol.cl
clean:
	rm -rf *.cm* lib/*.cm* Parser.ml Lexer.ml a.out oclaire
