PACKAGE := Frontend
SUBDIRS = 

# type in sources here
SOURCES = Frontend.ml
MLI = 

include $(top_srcdir)/m4/Makefile.am.vars

# overwrite some variables

# CMO - all compiled objects
CMO := $(SORTED:.ml=.cmo) 

# OCaml parser call with flags
AM_P4FLAGS := -pp "$(CAMLP4O) $(PARSER_INCLUDES) pa_js.cmo"
AM_BFLAGS += -rectypes -annot
AM_OFLAGS += -rectypes -annot -cclib "-static"

# overwrite some variables
PXFLAGS = $(P4FLAGS)
CAMLPXLIB = $(CAMLP4LIB)
MODULE_INCLUDES += -I $(CAMLP4LIB) -I ../../common -I ../../semantics -I ../base -I ../../js


# add extra compiled libraries used for linking
EXTRA_CMA += Common.cma Semantics.cma E.cma Js_frontend.cma

TARGET := $(MLI) $(CMO) META $(BYTE) Frontend.js
CLEAN_EXTRA += $(BYTE) $(NATIVE)

%.js: %.byte
	js_of_ocaml -o E.js $<; cp E.js ../../web

include $(top_srcdir)/m4/Makefile.am.targets

# overwrite some targets

install-data-am: $(TARGET)
if HAVE_OCAMLFIND
	if test "$(SITELIBDIR)" != ""; then \
	    $(mkinstalldirs) $(SITELIBDIR); \
	    $(OCAMLFIND) install -destdir $(SITELIBDIR) $(PACKAGE) $(TARGET); \
	else \
	    $(OCAMLFIND) install $(PACKAGE) $(TARGET); \
	fi
else
	if test "$(SITELIBDIR)" = ""; then \
	    installdir=$(OCAMLLIB)/site-lib/$(PACKAGE); \
	else \
	    installdir=$(SITELIBDIR)/$(PACKAGE); \
	fi; \
	$(mkinstalldirs) $$installdir; \
	for i in $(TARGET); do \
	    $(INSTALL_DATA) $$i $$installdir/$$i; \
	done
endif

#install-exec-am: $(BYTE) $(NATIVE)
#	$(mkinstalldirs) ${bindir}
#	$(INSTALL_PROGRAM) $(BYTE) ${bindir}/$(BYTE)
#	$(INSTALL_PROGRAM) $(NATIVE) ${bindir}/$(PACKAGE)$(EXEEXT)

uninstall-am:
if HAVE_OCAMLFIND
	if test "$(SITELIBDIR)" = ""; then \
	    $(OCAMLFIND) remove $(PACKAGE); \
	else \
	    rm -fR $(SITELIBDIR)/$(PACKAGE); \
	fi
else
	if test "$(SITELIBDIR)" = ""; then \
	    rm -fR $(OCAMLLIB)/site-lib/$(PACKAGE); \
	else \
	    rm -fR $(SITELIBDIR)/$(PACKAGE); \
	fi
endif
#	rm -f ${bindir}/$(BYTE) ${bindir}/$(PACKAGE)$(EXEEXT)

include $(top_srcdir)/m4/Makefile.am.rules
