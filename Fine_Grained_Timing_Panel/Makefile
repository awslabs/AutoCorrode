# Makefile for the Fine-Grained Timing panel component

ifndef V
.SILENT:
endif

COMPONENT_DIR := $(shell pwd)
FINE_GRAINED_TIMING_DIR ?= $(COMPONENT_DIR)/../Fine_Grained_Timing
ISABELLE_HOME ?= /Applications/Isabelle2025-2.app
ifneq ($(wildcard $(ISABELLE_HOME)/bin/isabelle),)
ISABELLE_INSTALLATION_HOME := $(abspath $(ISABELLE_HOME))
else ifneq ($(wildcard $(ISABELLE_HOME)/isabelle),)
ISABELLE_INSTALLATION_HOME := $(abspath $(ISABELLE_HOME)/..)
else
$(warning Cannot find Isabelle under $(ISABELLE_HOME)/bin/isabelle or $(ISABELLE_HOME)/isabelle; treating ISABELLE_HOME as the installation root)
ISABELLE_INSTALLATION_HOME := $(abspath $(ISABELLE_HOME))
endif
ISABELLE ?= $(ISABELLE_INSTALLATION_HOME)/bin/isabelle
JEDIT_DIR := $(shell ls -d $(ISABELLE_INSTALLATION_HOME)/contrib/jedit-* 2>/dev/null | head -1)
JEDIT_JAR ?= $(JEDIT_DIR)/jedit5.7.0-patched/jedit.jar
SCALA_HOME ?= $(ISABELLE_INSTALLATION_HOME)/contrib/scala-3.3.4
SCALAC ?= $(SCALA_HOME)/bin/scalac
SCALA_FLAGS ?= -deprecation -feature -unchecked -Werror -Wunused:imports,privates,locals,params -Xlint:all -Wvalue-discard -Wnonunit-statement
SCALA ?= $(SCALA_HOME)/bin/scala
ISABELLE_JAR ?= $(ISABELLE_INSTALLATION_HOME)/lib/classes/isabelle.jar
JAVA_HOME ?= $(shell $(ISABELLE) getenv -b JAVA_HOME 2>/dev/null)
JAR ?= $(if $(JAVA_HOME),$(JAVA_HOME)/bin/jar,jar)
JAVA_ENV = $(if $(JAVA_HOME),JAVA_HOME="$(JAVA_HOME)" PATH="$(JAVA_HOME)/bin:$$PATH",)

BUILD_DIR ?= $(COMPONENT_DIR)/build
CLASSES_DIR ?= $(BUILD_DIR)/classes
TEST_CLASSES_DIR ?= $(BUILD_DIR)/test-classes
JAR_FILE ?= $(BUILD_DIR)/fine_grained_timing.jar
INSTALL_DIR ?= $(HOME)/.isabelle/Isabelle2025-2/jedit/jars

SCALA_SOURCES := $(wildcard src/*.scala)
RESOURCE_FILES := $(wildcard resources/*)
TEST_SOURCES := $(wildcard test/*.scala)
TEST_CLASSPATH = $(CLASSES_DIR):$(TEST_CLASSES_DIR):$(JEDIT_JAR):$(ISABELLE_JAR)

.PHONY: all build test session-test register install clean uninstall

all: build

build: $(JAR_FILE)
	echo "Fine-Grained Timing plugin built: $(JAR_FILE)"

test: build $(TEST_CLASSES_DIR)/.compiled
	echo "Running timing model tests..."
	$(ISABELLE) scala \
		-classpath "$(CLASSES_DIR):$(TEST_CLASSES_DIR)" \
		FineGrainedTimingTest
	echo "Running timing scope tests..."
	$(JAVA_ENV) $(SCALA) \
		-classpath "$(TEST_CLASSPATH)" \
		FineGrainedTimingScopeTest
	echo "Running timing hierarchy tests..."
	$(JAVA_ENV) $(SCALA) \
		-classpath "$(TEST_CLASSPATH)" \
		FineGrainedTimingHierarchyTest
	echo "Running timing tree-table tests..."
	$(JAVA_ENV) $(SCALA) -Djava.awt.headless=true \
		-classpath "$(TEST_CLASSPATH)" \
		FineGrainedTimingTreeTableTest
	echo "Fine-Grained Timing Scala tests passed."

session-test:
	$(ISABELLE) build -d "$(FINE_GRAINED_TIMING_DIR)" \
		Fine_Grained_Timing_Test

register:
	$(ISABELLE) components -u "$(COMPONENT_DIR)"

install: register $(JAR_FILE)
	echo "Installing Fine-Grained Timing plugin to $(INSTALL_DIR)..."
	mkdir -p $(INSTALL_DIR)
	@set -eu; \
	tmp_jar="$(INSTALL_DIR)/.fine_grained_timing.jar.tmp.$$"; \
	cp "$(JAR_FILE)" "$$tmp_jar"; \
	mv -f "$$tmp_jar" "$(INSTALL_DIR)/fine_grained_timing.jar"
	echo "Restart Isabelle/jEdit to load the updated plugin and options."

$(JAR_FILE): $(CLASSES_DIR)/.compiled $(CLASSES_DIR)/.resources
	echo "Creating Fine-Grained Timing plugin JAR..."
	$(JAVA_ENV) cd $(CLASSES_DIR) && $(JAR) cf $(JAR_FILE) .

$(CLASSES_DIR)/.compiled: $(SCALA_SOURCES) | $(CLASSES_DIR)
	echo "Compiling Fine-Grained Timing Scala sources..."
	$(JAVA_ENV) $(SCALAC) \
		$(SCALA_FLAGS) \
		-classpath "$(JEDIT_JAR):$(ISABELLE_JAR)" \
		-d $(CLASSES_DIR) \
		$(SCALA_SOURCES)
	touch $@

$(CLASSES_DIR)/.resources: $(RESOURCE_FILES) | $(CLASSES_DIR)
	echo "Copying Fine-Grained Timing resources..."
	cp -r resources/* $(CLASSES_DIR)/
	touch $@

$(TEST_CLASSES_DIR)/.compiled: $(TEST_SOURCES) $(CLASSES_DIR)/.compiled | $(TEST_CLASSES_DIR)
	echo "Compiling Fine-Grained Timing tests..."
	$(JAVA_ENV) $(SCALAC) \
		$(SCALA_FLAGS) \
		-classpath "$(CLASSES_DIR):$(JEDIT_JAR):$(ISABELLE_JAR)" \
		-d $(TEST_CLASSES_DIR) \
		$(TEST_SOURCES)
	touch $@

$(CLASSES_DIR):
	mkdir -p $(CLASSES_DIR)

$(TEST_CLASSES_DIR):
	mkdir -p $(TEST_CLASSES_DIR)

clean:
	rm -rf $(BUILD_DIR)

uninstall:
	rm -f $(INSTALL_DIR)/fine_grained_timing.jar
