.PHONY=pdf code all clean exec

MAIN=main

all: pdf code binary exec

pdf:
	lhs2tex -o ${MAIN}.tex ${MAIN}.lidr
	latexmk -pdf ${MAIN}.tex

code:
	lhs2TeX --newcode -o ${MAIN}.idr ${MAIN}.lidr

binary:
	idris ${MAIN}.idr -o ${MAIN}

exec:
	./${MAIN}

clean:
	rm -f ${MAIN}.ibc ${MAIN}.idr ${MAIN}.tex ${MAIN}.ptb ${MAIN}.log ${MAIN}.aux ${MAIN}.fdb_latexmk ${MAIN}.fls ${MAIN} ${MAIN}.pdf
