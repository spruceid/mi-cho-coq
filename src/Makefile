
all: semantics.vo macros.vo

.depend:
	coqdep *.v > $@

-include .depend

%.vo: %.v
	coqc $<

clean:
	rm -f *.vo *.glob .depend


