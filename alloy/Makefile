default: json_to_alloy_execution

json_to_alloy_execution: json_to_alloy_execution.ml
	ocamlfind ocamlopt -g -o $@ -linkpkg -package unix,yojson,str $<

clean :
	rm -f *.cmi
	rm -f *.cmx
	rm -f *.o
	rm -f json_to_alloy_execution
