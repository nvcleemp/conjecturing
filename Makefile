all: expressions copy

expressions:
	$(MAKE) -C c

copy: expressions
	cp c/build/expressions ~
	cp sage/conjecturing.py ~

