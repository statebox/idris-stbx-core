.PHONY=pdf code all clean exec

MAIN=main
AUX=auxiliary
SOURCES=sources
BINARIES=build

all: pdf code binary exec

pdf:
	lhs2TeX -o ${SOURCES}/${MAIN}.tex ${MAIN}.lidr
	latexmk -pdf ${SOURCES}/${MAIN}.tex -outdir=${AUX}
	mv ${AUX}/${MAIN}.pdf ${BINARIES}/

code:
	lhs2TeX --newcode -o ${SOURCES}/${MAIN}.idr ${MAIN}.lidr

binary:
	idris ${SOURCES}/${MAIN}.idr -o ${BINARIES}/${MAIN}

exec:
	.${BINARIES}/${MAIN}

cleanAuxiliary:
	rm -f ${AUX}/*

cleanAll:
	rm -f ${AUX}/* ${SOURCES}/* ${BINARIES}/*

cleanSources:
	rm -f ${SOURCES}/*

cleanBinaries:
	rm  -f ${BINARIES}/*
