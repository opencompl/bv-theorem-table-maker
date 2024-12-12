.PHONY: all plot
all:
	lake build
	lake env .lake/build/bin/lean4checker Init.Data.BitVec.Lemmas
plot:
	python3 mk-latex-table.py
