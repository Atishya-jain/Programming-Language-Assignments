rm *.cmo
rm *.cmi
rm *.mli
rm toyProlog
rm MyParser.ml
rm MyLex.ml

ocamlc -c MyOcaml.ml
	ocamllex MyLex.mll
	ocamlyacc MyParser.mly
	ocamlc -c MyParser.mli
	ocamlc -c MyLex.ml
	ocamlc -c MyParser.ml
	ocamlc -c toyProlog.ml
ocamlc -o toyProlog MyOcaml.cmo MyLex.cmo MyParser.cmo toyProlog.cmo 