# Makefile for the ic2 component (isabelle ic2: start / check / status / stop).
#
# This component is plain Isabelle/Scala: there is no proof session to build.
# `isabelle scala_build` compiles lib/ic2.jar from the sources in
# etc/build.props, but it only builds components that are *registered*, so the
# `register` step below must run first.

ISABELLE_VERSION ?= Isabelle2025-2
ISABELLE_HOME ?= /Applications/$(ISABELLE_VERSION).app/bin
ISABELLE ?= $(ISABELLE_HOME)/isabelle

# This directory (absolute), so `make` works from anywhere.
COMPONENT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

.PHONY: all build register jar test test-unit test-e2e clean help

all: build

# Register this directory as an Isabelle component. Idempotent: `components -u`
# de-duplicates, so re-running is harmless. Required before `scala_build` can
# see the component, and before `isabelle ic2` is runnable.
register:
	$(ISABELLE) components -u $(COMPONENT_DIR)

# Compile lib/ic2.jar. Depends on registration; scala_build only rebuilds when
# sources changed (use `make jar` to force a fresh build).
build: register
	$(ISABELLE) scala_build

# Force a fresh rebuild of the jar.
jar: register
	$(ISABELLE) scala_build -f

# Run the full test suite (unit + e2e). The first e2e run builds the HOL heap.
test: build
	$(ISABELLE) ic2_test all

test-unit: build
	$(ISABELLE) ic2_test unit

test-e2e: build
	$(ISABELLE) ic2_test e2e

# Remove the build artifact. (It is checked in, so this leaves it for git to
# show as deleted; `make build` regenerates it.)
clean:
	$(RM) $(COMPONENT_DIR)/lib/ic2.jar

help:
	@echo "Targets:"
	@echo "  build      register the component and compile lib/ic2.jar (default)"
	@echo "  register   register this directory as an Isabelle component (idempotent)"
	@echo "  jar        force a fresh rebuild of the jar"
	@echo "  test       run unit + e2e tests (first e2e run builds the HOL heap)"
	@echo "  test-unit  run unit tests only (fast, no Isabelle session)"
	@echo "  test-e2e   run end-to-end tests only"
	@echo "  clean      remove the built jar"
	@echo ""
	@echo "Variables (override on the command line):"
	@echo "  ISABELLE_VERSION (default $(ISABELLE_VERSION))"
	@echo "  ISABELLE_HOME    (default $(ISABELLE_HOME))"
	@echo "  ISABELLE         (default \$$(ISABELLE_HOME)/isabelle)"
