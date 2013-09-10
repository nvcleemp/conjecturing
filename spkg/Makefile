conjecturing-%.spkg: 
	cp -r base conjecturing-$*
	cp -r ../c conjecturing-$*/src
	cd conjecturing-$* && hg init && hg add * && hg commit -m "Initial version"
	sage --pkg conjecturing-$*
	rm -r conjecturing-$*
