.PHONY=all pdf html clean

TITLE=Statebox core
SRC=../src/Intro.lidr \
    ../src/Category.lidr \
    ../src/Functor.lidr \
    ../src/NaturalTransformation.lidr
OUT=main
PANDOC=pandoc

all: pdf html

pdf:
	${PANDOC} --verbose --metadata pagetitle="${TITLE}" -f markdown+lhs+raw_tex \
	          -H header.tex -s -o ${OUT}.pdf ${SRC}

html:
	${PANDOC} --verbose --metadata pagetitle="${TITLE}" -f markdown+lhs+raw_tex \
	          -s -o ${OUT}.html ${SRC}

clean:
	rm -f ${OUT}.{html,pdf}
