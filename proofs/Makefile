# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := Jasmin
SUBDIRS  :=
INCFLAGS := -R src $(NAME) -R src/3rdparty $(NAME) -R src/logic $(NAME) -R src/compiler $(NAME)
COQFILES := \
	src/3rdparty/Coqlib.v \
	src/3rdparty/Integers.v \
	src/3rdparty/ssrring.v \
	src/compiler/allocation.v \
	src/compiler/array_expansion.v \
	src/compiler/compiler_util.v \
	src/compiler/compiler.v \
	src/compiler/constant_prop.v \
	src/compiler/dead_code.v \
	src/compiler/inlining.v \
	src/compiler/linear.v \
	src/compiler/stack_alloc.v \
	src/compiler/unrolling.v \
	src/logic/equiv_sem.v \
	src/logic/logic.v \
	src/logic/Ssem.v \
	src/logic/Ssem_props.v \
	src/logic/wp.v \
	src/logic/wp_while.v \
	src/expr.v \
	src/extraction.v \
	src/gen_map.v \
	src/memory.v \
	src/sem.v \
	src/strings.v \
	src/type.v \
	src/utils.v \
	src/var.v \
	src/word.v

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
