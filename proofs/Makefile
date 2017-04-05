# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := Jasmin
SUBDIRS  :=
INCFLAGS := -R src $(NAME) -R src/3rdparty $(NAME)
COQFILES := \
	src/3rdparty/Coqlib.v \
	src/3rdparty/Integers.v \
	src/3rdparty/ssrring.v \
	src/pos_map.v \
	src/gen_map.v \
	src/strings.v \
	src/word.v \
	src/dmasm_utils.v \
	src/dmasm_type.v \
	src/dmasm_var.v \
	src/dmasm_expr.v \
	src/memory.v \
	src/dmasm_sem.v \
	src/compiler_util.v \
	src/allocation.v \
	src/inlining.v \
	src/unrolling.v \
	src/constant_prop.v \
	src/dead_code.v \
	src/array_expansion.v \
	src/stack_alloc.v \
	src/linear.v \
	src/zmod_setoid.v \
	src/dmasm_Ssem.v \
	src/dmasm_Ssem_props.v \
	src/dmasm_logic.v \
	src/dmasm_wp.v \
	src/dmasm_wp_while.v \
	src/equiv_sem.v \
	src/compiler.v \
	src/extraction.v

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
DISTDIR = jasmin
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
