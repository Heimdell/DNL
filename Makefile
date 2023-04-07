
Lisp/Grammar/LexLisp.hs: Lisp/Grammar/AbsLisp.hs
	@echo "LEXER"
	alex Lisp/Grammar/LexLisp.x

Lisp/Grammar/ParLisp.hs: Lisp/Grammar/AbsLisp.hs
	@echo "PARSER"
	happy Lisp/Grammar/ParLisp.y -a -g -c

Lisp/Grammar/AbsLisp.hs:
	@echo "GRAMMAR"
	bnfc Lisp.cf --agda -p Lisp.Grammar --text-token --functor

grammar: Lisp/Grammar/AbsLisp.hs Lisp/Grammar/ParLisp.hs Lisp/Grammar/LexLisp.hs
	@echo "EXE"
	agda --compile Lisp/Grammar/Main.agda

clean:
	rm MAlonzo -fr
	rm Lisp/Grammar -rf