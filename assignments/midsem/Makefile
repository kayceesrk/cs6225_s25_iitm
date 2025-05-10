.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq:
	$(COQC) MidtermSig.v

clean:
	rm -f *.vo* *.glob *~ .*.aux
