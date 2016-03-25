PACKAGE := E
SUBDIRS = 

# type in sources here
SOURCES = E.ml E.jsf.ml 
MLI = 

include $(top_srcdir)/m4/Makefile.am.vars

# overwrite some variables

# CMO - all compiled objects
CMO := $(SORTED:.ml=.cmo)

# OCaml parser call with flags
AM_P5FLAGS := -pp "$(CAMLP5O) $(PARSER_INCLUDES) pa_checked.cmo pa_ostap.cmo pa_log.cmo pa_gt.cmo -L `camlp5o -where` $(LOG) $(DOC)"
AM_BFLAGS += -rectypes -annot
AM_OFLAGS += -rectypes -annot -cclib "-static"

# overwrite some variables
PXFLAGS = $(P5FLAGS)
CAMLPXLIB = $(CAMLP5LIB)
MODULE_INCLUDES += -I $(CAMLP5LIB) -I ../common -I ../js -I ../semantics

# add extra compiled libraries used for linking
EXTRA_CMA += Common.cma Semantics.cma Js_frontend.cma 

TARGET := $(MLI) $(CMO) META $(BYTE) tex E.js web_install
CLEAN_EXTRA += $(BYTE) $(NATIVE)

TEXFILES = E E_BS_S E_SS_S E_BS_NS E_SS_NS
tex: 
	for f in $(TEXFILES) ; do TEXINPUTS=../tex//: pdflatex $$f.tex; done

%.js: %.byte
	js_of_ocaml -o E.js $<

web_install:
	cp E.js ../web/js; for f in $(TEXFILES) ; do cp $$f.pdf ../web/pdf ; done

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
