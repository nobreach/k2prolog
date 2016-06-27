#BTABIN=/Volumes/Data/projects/logen-bta/bin/bta

# We assume that logen and bta are in PATH already. Otherwise set them explicitly as above.
LOGEN=logen
BTABIN=bta
BTA=${BTABIN} -scc

test1: imp-and-prolog-rewriter_logen.pl
	sicstus -l imp-and-prolog-rewriter_logen.pl --goal "rewrite(conf(k([assign(var(x),6)]), state([]) ),X),halt."

imp-and-prolog-rewriter_logen.pl: imp-and-prolog-rewriter.pl.ann imp-and-prolog-rewriter.pl
	${LOGEN} imp-and-prolog-rewriter.pl "rewrite(conf(k([assign(var(x),6)]), state([])),X)." --spec_file imp-and-prolog-rewriter_logen.pl -vv

imp-and-prolog-rewriter.pl.ann: imp-and-prolog-rewriter.pl Makefile
	${BTA} -ng imp-and-prolog-rewriter.pl -o imp-and-prolog-rewriter.pl.ann --entry " rewrite(conf(k([assign(var(x),6)]), state([])),X)."  --lib "assoc" --lib "logarr"

#
#ics_gx: php_001_gx_sics.pl
#	echo "Running hand-adapted generating extension in SICStus"
#	sicstus -l php_001_gx_sics.pl --goal "test(X)."

clean:
	find . -name "*.ast"  -exec rm {} \;
	find . -name "*.itf"  -exec rm {} \;
	find . -name "*.po"  -exec rm {} \;
	find . -name "*.spec"  -exec rm {} \;
	find . -name "*.orig"  -exec rm {} \;
	find . -name "*.gx"  -exec rm {} \;
	find . -name "*.cpx"  -exec rm {} \;
	rm imp-and-prolog-rewriter_logen.pl

