all: Makefile.coq mk_depgraph mk_axiom_finder
	@for i in $$(find . -name '*.v' | sed 's/^\.\///' | grep '^Theory'); do	\
	    if ! grep -q $$i _CoqProject; then			\
		echo NOT IN _CoqProject: $$i;			\
	    fi;							\
	done
	make -k -j$(JOBS) -f Makefile.coq $(CMD) # TIMECMD=time

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

mk_depgraph: _CoqProject
	./mk_DepGraph.v.rb

axiom_finder: _CoqProject mk_axiom_finder enable_axiom_finder
	(make all | tee axioms_found.log) && \
	echo 'Begin: sed /^Closed under the global context/d axioms_found.log' && \
	sed '/^Closed under the global context/d' axioms_found.log && \
	echo 'End: sed /^Closed under the global context/d axioms_found.log'; \
	make disable_axiom_finder

enable_axiom_finder: _CoqProject mk_axiom_finder
	(grep '^AxiomFinder.v' _CoqProject || (echo 'AxiomFinder.v' >> _CoqProject))

disable_axiom_finder: _CoqProject mk_axiom_finder
	(grep '^AxiomFinder.v' _CoqProject && (sed -i.bak '/^AxiomFinder.v/d' _CoqProject))

mk_axiom_finder: _CoqProject
	./mk_AxiomFinder.v.rb

check_universe_polymorphism: _CoqProject Makefile.coq
	@for i in $$(find . -name '*.v' | sed 's/^\.\///' | grep '^Theory'); do	\
	    if ! grep -q 'Set Universe Polymorphism' $$i; then			\
		echo Missing 'Set Universe Polymorphism': $$i;			\
	    fi;							\
	done

env:
	eval $(opam env)

install: _CoqProject Makefile.coq
	make -f makefile.coq coqlib=$(coqlib) install

doc: _CoqProject Makefile.coq
	make -k -j$(JOBS) -f Makefile.coq gallinahtml
	# use just 'html' to include proofs in docs

validate: _CoqProject Makefile.coq
	make -k -j$(JOBS) -f Makefile.coq validate

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	@find . \( -name '*.glob' -o				\
		  -name '*.v.d' -o				\
		  -name '*.vo' -o				\
		  -name '*.hi' -o				\
		  -name '*.o' -o				\
		  -name '.*.aux' -o				\
		  -name '*.hp' -o				\
		  -name 'result' -o				\
		  -name 'dist' \) -print0 | xargs -0 rm -fr

fullclean: clean
	rm -f Makefile.coq

todo:
	@find . \( \( -name coq-haskell -o -name fiat \) -prune \)   \
	  -o -name '*.v'					   | \
		xargs egrep -i -Hn '(abort|admit|undefined|jww)'   | \
		      egrep -v '(Definition undefined|DEFERRED)'   | \
		      egrep -v '(old|new|research|Pending|todo)/'	     \
	    || echo "No pending tasks!"

tree:
	tree -P "*.v" .

cloc:
	cloc Coq Embed FixF Instance Lists PushThrough.v Theory

hide_deprecated:
	echo "Renaming contends of 'Deprecated' to '*.v_hidden'"; \
	find Deprecated -name '*.v' -exec rename .v .v_hidden {} +

show_deprecated:
	echo "Renaming contends of 'Deprecated' from '*.v_hidden'"; \
	find Deprecated -name '*.v_hidden' -exec rename .v_hidden .v {} +

depgraph_dot: all
	dpd2dot -without-defs graph.dpd

depgraph_svg: depgraph_dot
	dot -Tsvg graph.dot > graph.svg

depgraph_show: depgraph_dot
	xdot graph.dot

unused: all
	dpdusage graph.dpd

