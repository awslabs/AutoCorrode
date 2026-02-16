# Makefile for Proxy Plugin

ifndef V
.SILENT:
endif

PLUGIN_DIR := $(shell pwd)
ISABELLE_HOME ?= /Applications/Isabelle2025-2.app
JEDIT_DIR := $(shell ls -d $(ISABELLE_HOME)/contrib/jedit-* 2>/dev/null | head -1)
JEDIT_JAR ?= $(JEDIT_DIR)/jedit5.7.0-patched/jedit.jar
SCALA_HOME ?= $(ISABELLE_HOME)/contrib/scala-3.3.4
SCALAC ?= $(SCALA_HOME)/bin/scalac
ISABELLE_JAR ?= $(ISABELLE_HOME)/lib/classes/isabelle.jar

BUILD_DIR ?= $(PLUGIN_DIR)/build
CLASSES_DIR ?= $(BUILD_DIR)/classes
JAR_FILE ?= $(BUILD_DIR)/ip_plugin.jar
INSTALL_DIR ?= $(HOME)/.isabelle/Isabelle2025-2/jedit/jars

SCALA_SOURCES := $(wildcard src/*.scala)
RESOURCE_FILES := $(wildcard resources/*)

.PHONY: all build install clean uninstall help debug

all:
	echo "Building Proxy Plugin..."
	$(MAKE) build

build: $(JAR_FILE)
	echo "Plugin built: $(JAR_FILE)"

$(JAR_FILE): $(CLASSES_DIR)/.compiled $(CLASSES_DIR)/.resources
	echo "Creating JAR..."
	cd $(CLASSES_DIR) && jar cf $(JAR_FILE) .

$(CLASSES_DIR)/.compiled: $(SCALA_SOURCES) | $(CLASSES_DIR)
	echo "Compiling..."
	$(SCALAC) \
		-classpath "$(JEDIT_JAR):$(ISABELLE_JAR)" \
		-d $(CLASSES_DIR) \
		$(SCALA_SOURCES)
	touch $@

$(CLASSES_DIR)/.resources: $(RESOURCE_FILES) | $(CLASSES_DIR)
	echo "Copying resources..."
	cp -r resources/* $(CLASSES_DIR)/
	touch $@

$(CLASSES_DIR):
	mkdir -p $(CLASSES_DIR)

install: $(JAR_FILE)
	echo "Installing to $(INSTALL_DIR)..."
	mkdir -p $(INSTALL_DIR)
	cp $(JAR_FILE) $(INSTALL_DIR)/
	echo "Installed. Restart Isabelle/jEdit to activate."

clean:
	rm -rf $(BUILD_DIR)

uninstall:
	rm -f $(INSTALL_DIR)/ip_plugin.jar

help:
	echo "Targets: all build install clean uninstall help debug"
	echo ""
	echo "Variables:"
	echo "  V=1              Verbose output"
	echo "  ISABELLE_HOME    Isabelle installation (default: $(ISABELLE_HOME))"
	echo "  INSTALL_DIR      Plugin install dir (default: $(INSTALL_DIR))"

debug:
	echo "ISABELLE_HOME = $(ISABELLE_HOME)"
	echo "JEDIT_JAR     = $(JEDIT_JAR)"
	echo "ISABELLE_JAR  = $(ISABELLE_JAR)"
	echo "SCALAC        = $(SCALAC)"
	echo "SCALA_SOURCES = $(SCALA_SOURCES)"
