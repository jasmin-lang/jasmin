# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := Arithmetica
SUBDIRS  :=
INCFLAGS := -R src $(NAME) -R src/3rdparty $(NAME)
COQFILES := \
	src/3rdparty/finmap.v \
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
	src/extraction.v \
	src/zmod_setoid.v \
	src/dmasm_Ssem.v \
	src/dmasm_Ssem_props.v \
	src/dmasm_logic.v \
	src/equiv_sem.v


#	src/compiler.v \


#	src/proof_utils.v \
	src/proof_sem.v \
	src/proof_add.v \
	src/proof_4limb_add_25519.v \
	src/proof_4limb_mul_25519.v

#	src/stack_alloc.v \
	src/linear.v \


#	src/symbolic_expr.v \
	src/symbolic_expr_opt.v


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
