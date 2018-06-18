all: cocalc

expressions:
	$(MAKE) -C c

cocalc: expressions
	@echo "The files expressions and conjecturing.py will be copied to the home directory."
	@echo ""

	@while [ -z "$$CONTINUE" ]; do \
	   read -r -p "Type anything but Y or y to cancel this. [y/N]: " CONTINUE; \
	done ; \
	[ $$CONTINUE = "y" ] || [ $$CONTINUE = "Y" ] || (echo "Exiting."; exit 1;)

	cp c/build/expressions ~
	cp sage/conjecturing.py ~

