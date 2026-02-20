######################################################################
#                                                                    #
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. #
# SPDX-License-Identifier: MIT                                       #
#                                                                    #
# Makefile for Isabelle/HOL AutoCorrode sessions                     #
#                                                                    #
######################################################################

.DEFAULT_GOAL: jedit
.PHONY: register-afp-components build jedit

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
