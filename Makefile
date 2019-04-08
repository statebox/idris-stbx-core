.PHONY=all pdf html clean

all: pdf html

pdf:
	$(MAKE) -C docs pdf

html:
	$(MAKE) -C docs html

clean:
	$(MAKE) -C docs clean
