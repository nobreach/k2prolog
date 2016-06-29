# We assume that logen and bta are in PATH already. Otherwise set them explicitly as above.
LOGEN=logen
#BTABIN=/Volumes/Data/projects/logen-bta/bin/bta
BTABIN=bta
BTA=${BTABIN} -scc

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

# Tests (use goals test1, test2 or test3)

test: imp_spec.pl
	sicstus -l imp_spec.pl --goal "test3__0(X),print(X),halt."
imp_spec.pl: imp.pl.ann
	echo "Running LOGEN: "
	${LOGEN} imp.pl "test3(X)" -ap --spec_file imp_spec.pl -v
imp.pl.ann: imp.pl
	echo "Running BTA: "
	${BTA} imp.pl -o imp.pl.ann --entry "test3(d)." --lib "assoc"
