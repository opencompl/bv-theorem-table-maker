.PHONY: theorem-table.csv

bitvec_functions.tex: theorem-table.csv mk-latex-table.py
	python3 mk-latex-table.py

theorem-table.csv: lean-toolchain Main.lean
	lake build
	lake env .lake/build/bin/lean4checker Init.Data.BitVec.Lemmas
