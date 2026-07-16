######################################################################
#                                                                    #
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. #
# SPDX-License-Identifier: MIT                                       #
#                                                                    #
# Makefile for Isabelle/HOL AutoCorrode sessions                     #
#                                                                    #
######################################################################

.DEFAULT_GOAL: jedit
.PHONY: register-afp-components build jedit tutorial \
        build-ic2 ic2 ic2-status ic2-stop

# Set this to the directory containing the Isabelle2025-2 binary
ISABELLE_HOME?=/Applications/Isabelle2025-2.app/bin
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

ISABELLE_FLAGS += $(ISABELLE_REMOTE)
ISABELLE_JEDIT_FLAGS += $(ISABELLE_REMOTE)

jedit: register-afp-components
	$(ISABELLE_HOME)/isabelle jedit $(ISABELLE_JEDIT_FLAGS) -l HOL -d . ./AutoCorrode.thy  &

register-afp-components:
	$(ISABELLE_HOME)/isabelle components -u $(AFP_COMPONENT_BASE)/Word_Lib

build: register-afp-components
	$(ISABELLE_HOME)/isabelle build $(ISABELLE_FLAGS) -d . AutoCorrode

# Build the slide-deck tutorial in tutorial/. Inherits the AutoCorrode
# parent heap, so run `make build` first if it isn't built yet.
tutorial: register-afp-components
	$(MAKE) -C tutorial ISABELLE_HOME=$(ISABELLE_HOME) build

#######################################
# ic2 headless session server (I/R)
#######################################
# `make ic2` starts a warm, headless PIDE daemon (ic2) for the full AutoCorrode
# session: the HOL heap is loaded and AutoCorrode's theories are
# checked/developed against it via `isabelle ic2 check ...` or the I/R REPL.
# `make ic2-status` surveys running servers and `make ic2-stop` shuts this one
# down. See ic2/README.md for the CLI.
#
# ic2 is plain Isabelle/Scala (no proof session to build): the component must be
# registered and lib/ic2.jar compiled once via ic2/Makefile before these targets
# work. build-ic2 delegates there (idempotent).

# Server name, so `make ic2-stop` / `-status` and `isabelle ic2` agree on the slot.
IC2_NAME ?= AutoCorrode

# Flags for `isabelle ic2 server start`. --daemon detaches and returns once the
# warm session is ready. Override IC2_FLAGS to run in the foreground, or to add
# --mcp / --no-iq / -N (no build) / -o ... etc.
IC2_FLAGS ?= --daemon
# Proxy `server start` to the same remote host as build/jedit, if configured.
IC2_FLAGS += $(ISABELLE_REMOTE)

# Register the ic2 component and (re)build lib/ic2.jar. Idempotent.
build-ic2:
	$(MAKE) -C ic2 ISABELLE_HOME=$(ISABELLE_HOME) build

# Start a daemonised ic2 server for the full AutoCorrode session, on the HOL
# heap. Run `make build` first to have the AutoCorrode heap ready; otherwise the
# cold build runs in the background (see ic2/README.md).
ic2: register-afp-components build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server start $(IC2_FLAGS) -n $(IC2_NAME) -d . -l HOL
	@echo ''
	@echo '  ic2 server "$(IC2_NAME)" launched. Follow its console (build progress + logs) with:'
	@echo '      $(ISABELLE_HOME)/isabelle ic2 server attach -n $(IC2_NAME)'
	@echo '  Status: make ic2-status   |   Stop: make ic2-stop'
	@echo ''

# Survey every running ic2 server.
ic2-status: build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server status

# Stop the server (override IC2_NAME to target a differently-named one).
ic2-stop: build-ic2
	$(ISABELLE_HOME)/isabelle ic2 server stop -n $(IC2_NAME)
