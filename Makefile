All:
	ocamlyacc prologParser.mly
	ocamlc -c prologParser.mli
	ocamllex prologLexer.mll
	ocamlyacc interactionParser.mly
	ocamlc -c interactionParser.mli
	ocamllex interactionLexer.mll
