.PHONY=all pdf clean cleanAuxiliary cleanBinaries cleanSources

MAIN=main
AUX=auxiliary
SOURCES=sources
BINARIES=build

all: pdf

pdf:
	mkdir -p ${SOURCES}
	mkdir -p ${AUX}
	mkdir -p ${BINARIES}
	lhs2TeX -o ${SOURCES}/${MAIN}.tex ${MAIN}.lidr
	latexmk -pdf ${SOURCES}/${MAIN}.tex -outdir=${AUX}
	mv ${AUX}/${MAIN}.pdf ${BINARIES}/

clean:
	rm -f ${AUX}/* ${SOURCES}/* ${BINARIES}/*

cleanAuxiliary:
	rm -f ${AUX}/*

cleanBinaries:
	rm  -f ${BINARIES}/*

cleanSources:
	rm -f ${SOURCES}/*
