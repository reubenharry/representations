HS_SOURCES := $(shell git ls-files '*.hs')
ORMOLU ?= .cabal/bin/ormolu

.PHONY: format format-check

format:
	$(ORMOLU) --mode inplace $(HS_SOURCES)

format-check:
	$(ORMOLU) --mode check $(HS_SOURCES)
