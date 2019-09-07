lightyear:
	git clone https://github.com/ziman/lightyear
	cd lightyear
	idris --install lightyear.ipkg
	cd ..
	rm -rf lightyear

graphviz:
	git clone https://gitlab.com/mgttlinger/idris-graphviz
	cd idris-graphviz
	idris --install graphviz.ipkg
	cd ..
	rm -rf idris-graphviz

build: $(wildcard **/*.idr)
	idris --build rewrite.ipkg

test: build
	idris --testpkg rewrite.ipkg

clean:
	idris --clean rewrite.ipkg
