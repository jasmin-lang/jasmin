# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := Arithmetica
SUBDIRS  :=
INCFLAGS := -R src $(NAME) -R src/3rdparty $(NAME)
COQFILES := \
	src/3rdparty/finmap.v \
	src/3rdparty/Coqlib.v \
	src/3rdparty/Integers.v \
	src/pos_map.v \
	src/gen_map.v \
	src/strings.v \
	src/word.v \
	src/dmasm_utils.v \
	src/dmasm_type.v \
	src/dmasm_var.v \
	src/dmasm_expr.v \
	src/dmasm_sem.v \
	src/dmasm_Ssem.v \
	src/dmasm_Ssem_props.v \
	src/symbolic_expr.v \
	src/symbolic_expr_opt.v \
	src/dmasm_logic.v \
	src/equiv_sem.v \
	src/allocation.v \
	src/inlining.v \
	src/constant_prop.v \
	src/unrolling.v \
	src/dead_code.v \
	src/array_expansion.v \
	src/compiler.v

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f src/*.glob src/*.d src/*.vo

this-distclean::
	rm -f $(shell find . -name '*~')

# --------------------------------------------------------------------
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = arithmetica.v
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
