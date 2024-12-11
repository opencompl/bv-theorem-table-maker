.PHONY: all
all:
	lake build
	lake env .lake/build/bin/lean4checker Init.Data.BitVec.Lemmas
