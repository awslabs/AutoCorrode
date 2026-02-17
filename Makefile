######################################################################
#                                                                    #
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. #
# SPDX-License-Identifier: MIT                                       #
#                                                                    #
# Makefile for Isabelle/HOL AutoCorrode sessions                     #
#                                                                    #
######################################################################

.DEFAULT_GOAL: jedit
.PHONY: register-afp-components build jedit conformance-gen conformance-test conformance conformance-clean

# Set this to the Isabelle installation root or bin directory
ISABELLE_HOME?=/Applications/Isabelle2025-2.app/bin
ISABELLE?=$(if $(wildcard $(ISABELLE_HOME)/bin/isabelle),$(ISABELLE_HOME)/bin/isabelle,$(ISABELLE_HOME)/isabelle)
# Set this to your home directory
USER_HOME?=$(HOME)
# Set this to where you maintain, or want to maintain, AFP dependencies
AFP_COMPONENT_BASE?=./dependencies/afp
# Set this option to accept `sorry`'ed proofs
ifdef QUICK_AND_DIRTY
	ISABELLE_FLAGS += -o quick_and_dirty
endif

HOST=$(shell uname -s)
ifeq ($(HOST),Darwin)
	AVAILABLE_CORES?=$(shell sysctl -n hw.physicalcpu)
else ifeq ($(HOST),Linux)
	AVAILABLE_CORES?=$(shell nproc)
else
	$(error Unsupported host platform)
endif

# -j 1 determines amount of parallel jobs,
# threads=n sets amount of cores per job. We are building a single
# session, so we want 1 job with as much cores as are available
ISABELLE_FLAGS?=-b -j 1 -o "threads=$(AVAILABLE_CORES)" -v
ISABELLE_JEDIT_FLAGS?=

jedit: register-afp-components
	$(ISABELLE) jedit $(ISABELLE_JEDIT_FLAGS) -l HOL -d . ./AutoCorrode.thy  &

register-afp-components:
	@if [ ! -d "$(AFP_COMPONENT_BASE)/Word_Lib" ]; then \
		echo "Error: AFP component directory not found: $(AFP_COMPONENT_BASE)/Word_Lib"; \
		echo "Hint: checkout AFP and set AFP_COMPONENT_BASE to the AFP theories root (for example: afp/thys)."; \
		exit 1; \
	fi
	$(ISABELLE) components -u $(AFP_COMPONENT_BASE)/Word_Lib

build: register-afp-components
	$(ISABELLE) build $(ISABELLE_FLAGS) -d . AutoCorrode

# Conformance Testing targets
# These validate that μRust HOL semantics match real Rust behaviour

conformance-gen: register-afp-components
	@echo "Generating conformance tests from HOL definitions..."
	$(ISABELLE) build $(ISABELLE_FLAGS) -d . Conformance_Testing

conformance-test:
	@echo "Running conformance tests against Rust..."
	cd Conformance_Testing/rust_harness && cargo test

conformance: conformance-gen conformance-test
	@echo "Conformance testing complete."

conformance-clean: register-afp-components
	@echo "Cleaning conformance test artifacts..."
	rm -rf Conformance_Testing/rust_harness/target
	rm -f Conformance_Testing/rust_harness/src/lib.rs
	$(ISABELLE) build -c -d . Conformance_Testing || true
