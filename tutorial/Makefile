ISABELLE_VERSION ?= Isabelle2025-2
ISABELLE_HOME    ?= /Applications/$(ISABELLE_VERSION).app/bin
ISABELLE         := $(ISABELLE_HOME)/isabelle

AUTOCORRODE_DIR  := $(realpath $(CURDIR)/..)
TUTORIAL_DIR     := $(CURDIR)
PDF_NAME         ?= autocorrode_tutorial.pdf

ISABELLE_FLAGS ?= -b

# Parent session image to inherit. Built once via `make heaps`.
PARENT_IMAGE     := AutoCorrode

# All -d directories so isabelle can resolve sessions.
DIRS             := -d .. -d .

define CHECK_ISABELLE
	@if [ ! -x "$(ISABELLE)" ]; then \
	  echo "error: '$(ISABELLE)' not found or not executable." >&2; \
	  echo "Set ISABELLE_HOME, e.g. make ISABELLE_HOME=/path/to/Isabelle/bin $@" >&2; \
	  exit 1; \
	fi
endef

.PHONY: all heaps build clean jedit

# Default: build heaps if missing, then build the tutorial.
all: build

# Build (or refresh) the upstream AutoCorrode parent heap. Slow the first
# time, fast afterwards. Re-run if upstream theories change.
heaps:
	$(CHECK_ISABELLE)
	$(ISABELLE) build $(DIRS) -b $(PARENT_IMAGE)

# Build the tutorial session, inheriting the AutoCorrode parent image.
build:
	$(CHECK_ISABELLE)
	$(ISABELLE) build $(ISABELLE_FLAGS) $(DIRS) -l $(PARENT_IMAGE) AutoCorrodeTutorial
	cp output/document.pdf $(PDF_NAME)
	@echo "Wrote $(PDF_NAME)"

view: build
	open $(PDF_NAME)

clean:
	$(CHECK_ISABELLE)
	$(ISABELLE) build $(DIRS) -c AutoCorrodeTutorial
	rm -f $(PDF_NAME)

# Open the tutorial in jEdit for interactive editing.
jedit:
	$(CHECK_ISABELLE)
	$(ISABELLE) jedit $(DIRS) -l $(PARENT_IMAGE) *.thy
