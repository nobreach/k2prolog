# We assume that logen and bta are in PATH already. Otherwise set them explicitly as above.
LOGEN=logen
#BTABIN=/Volumes/Data/projects/logen-bta/bin/bta
BTABIN=bta
BTA=${BTABIN} -scc
# you can use the following options to disable local/global termination checking:
BTAOPTS=-ng -nl
LOGENOPTS=-v -w
LOGENOPTS=-v

# Tests (use goals test1, test2 or test3) ; Note test1 does not work yet
GOAL=test1
FILE=imp_bti
FILE=imp_bti_tagged
test_bti: $(FILE)_spec.pl Makefile
	sicstus -l $(FILE)_spec.pl --goal "$(GOAL)__0(X),print(X),nl,halt."
$(FILE)_spec.pl: $(FILE).pl.ann Makefile
	echo "Running LOGEN: "
	${LOGEN} $(FILE).pl "$(GOAL)(X)" -ap --spec_file $(FILE)_spec.pl $(LOGENOPTS)
$(FILE).pl.ann2: $(FILE).pl Makefile
	echo "Running BTA for $(GOAL): "
	${BTA} $(FILE).pl -o $(FILE).pl.ann2 --entry "$(GOAL)(d)." --lib "assoc"


test: imp_spec.pl Makefile
	sicstus -l imp_spec.pl --goal "$(GOAL)__0(X),print(X),nl,halt."
imp_spec.pl: imp.pl.ann Makefile
	echo "Running LOGEN: "
	${LOGEN} imp.pl "$(GOAL)(X)" -ap --spec_file imp_spec.pl -v
imp.pl.ann: imp.pl Makefile
	echo "Running BTA for $(GOAL): "
	${BTA} imp.pl -o imp.pl.ann --entry "$(GOAL)(d)." --lib "assoc"

# Clean
clean:
	find . -name "*.ann"  -exec rm {} \;
	find . -name "*.ast"  -exec rm {} \;
	find . -name "*.itf"  -exec rm {} \;
	find . -name "*.po"  -exec rm {} \;
	find . -name "*.spec"  -exec rm {} \;
	find . -name "*.orig"  -exec rm {} \;
	find . -name "*.gx"  -exec rm {} \;
	find . -name "*.cpx"  -exec rm {} \;
	rm imp_spec.pl