MATHJAX = "http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"
HSTYLE = tango
FLAGS = --standalone --toc --toc-depth=2 --mathjax=$(MATHJAX) --highlight-style ${HSTYLE}
FILTER = ../scripts/includes.hs
STYLE = css/style.css

.PHONY: all

all: dmasm.html

%.html: %.md $(FILTER)
	pandoc -fmarkdown -c ${STYLE} ${FLAGS} --filter ${FILTER} -o $@ $<
