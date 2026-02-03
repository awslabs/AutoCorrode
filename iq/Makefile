# Makefile for I/Q Plugin

# Verbose control
ifndef V
.SILENT:
endif

# Paths (configurable via environment variables)
PLUGIN_DIR := $(shell pwd)
ISABELLE_HOME ?= /Applications/Isabelle2025-2.app
JEDIT_DIR := $(shell ls -d $(ISABELLE_HOME)/contrib/jedit-* 2>/dev/null | head -1)
JEDIT_JAR ?= $(JEDIT_DIR)/jedit5.7.0-patched/jedit.jar
SCALA_HOME ?= $(ISABELLE_HOME)/contrib/scala-3.3.4
SCALAC ?= $(SCALA_HOME)/bin/scalac
ISABELLE_JAR ?= $(ISABELLE_HOME)/lib/classes/isabelle.jar

# Output directories (configurable via environment variables)
BUILD_DIR ?= $(PLUGIN_DIR)/build
CLASSES_DIR ?= $(BUILD_DIR)/classes
JAR_FILE ?= $(BUILD_DIR)/iq_plugin.jar
INSTALL_DIR ?= $(HOME)/.isabelle/Isabelle2025/jedit/jars

# Source files
SCALA_SOURCES := $(wildcard src/*.scala)
RESOURCE_FILES := $(wildcard resources/*)

# Default target
.PHONY: all
all:
	echo "Building I/Q Plugin..."
	$(MAKE) build

# Build target
.PHONY: build
build: $(JAR_FILE)
	echo "Plugin built successfully!"
	echo "JAR file: $(JAR_FILE)"

# Create JAR file
$(JAR_FILE): $(CLASSES_DIR)/.compiled $(CLASSES_DIR)/.resources
	echo "Creating JAR file..."
	cd $(CLASSES_DIR) && jar cf $(JAR_FILE) .

# Compile Scala sources
$(CLASSES_DIR)/.compiled: $(SCALA_SOURCES) | $(CLASSES_DIR)
	echo "Compiling Scala sources..."
	$(SCALAC) \
		-classpath "$(JEDIT_JAR):$(ISABELLE_JAR)" \
		-d $(CLASSES_DIR) \
		$(SCALA_SOURCES)
	touch $@

# Copy resources
$(CLASSES_DIR)/.resources: $(RESOURCE_FILES) | $(CLASSES_DIR)
	echo "Copying resources..."
	cp -r resources/* $(CLASSES_DIR)/
	touch $@

# Create build directories
$(CLASSES_DIR):
	mkdir -p $(CLASSES_DIR)

# Install target
.PHONY: install
install: $(JAR_FILE)
	echo "Installing I/Q plugin to $(INSTALL_DIR)..."
	mkdir -p $(INSTALL_DIR)
	cp $(JAR_FILE) $(INSTALL_DIR)/
	echo "Plugin built and installed successfully!"
	echo "JAR file: $(JAR_FILE)"
	echo "Installed to: $(INSTALL_DIR)/iq_plugin.jar"
	echo ""
	echo "To use the plugin:"
	echo "1. Start Isabelle/jEdit: $(ISABELLE_HOME)/bin/isabelle jedit"
	echo "2. Go to Utilities -> Global Options -> Plugin Manager"
	echo "3. The I/Q Plugin should be listed and active"
	echo "4. Go to Utilities -> I/Q Server Log to open the dockable"

# Clean target
.PHONY: clean
clean:
	echo "Cleaning build directory..."
	rm -rf $(BUILD_DIR)

# Uninstall target
.PHONY: uninstall
uninstall:
	echo "Uninstalling I/Q plugin..."
	rm -f $(INSTALL_DIR)/iq_plugin.jar
	echo "Plugin uninstalled."

# Help target
.PHONY: help
help:
	echo "I/Q Plugin Makefile"
	echo ""
	echo "Available targets:"
	echo "  all       - Build the plugin (default)"
	echo "  build     - Build the plugin JAR file"
	echo "  install   - Build and install the plugin"
	echo "  clean     - Remove build directory"
	echo "  uninstall - Remove installed plugin"
	echo "  help      - Show this help message"
	echo "  debug     - Show build configuration variables"
	echo ""
	echo "Configurable environment variables:"
	echo "  V             - Show individual commands (default: off)"
	echo "  INSTALL_DIR   - Installation directory (default: $(INSTALL_DIR))"
	echo "  ISABELLE_HOME - Isabelle installation path (default: $(ISABELLE_HOME))"
	echo "  SCALA_HOME    - Scala installation path (default: $(SCALA_HOME))"
	echo "  SCALAC        - Scala compiler path (default: $(SCALAC))"
	echo "  BUILD_DIR     - Build output directory (default: $(BUILD_DIR))"
	echo ""
	echo "Examples:"
	echo "  make                              # Build with quiet output"
	echo "  V=1 make                          # Build with verbose output"
	echo "  INSTALL_DIR=/tmp make install     # Install to custom directory"
	echo "  ISABELLE_HOME=/opt/isabelle make  # Use different Isabelle installation"

# Debug target to show variables
.PHONY: debug
debug:
	echo "Build configuration:"
	echo "  PLUGIN_DIR    = $(PLUGIN_DIR)"
	echo "  ISABELLE_HOME = $(ISABELLE_HOME)"
	echo "  JEDIT_JAR     = $(JEDIT_JAR)"
	echo "  SCALA_HOME    = $(SCALA_HOME)"
	echo "  SCALAC        = $(SCALAC)"
	echo "  ISABELLE_JAR  = $(ISABELLE_JAR)"
	echo "  BUILD_DIR     = $(BUILD_DIR)"
	echo "  CLASSES_DIR   = $(CLASSES_DIR)"
	echo "  JAR_FILE      = $(JAR_FILE)"
	echo "  INSTALL_DIR   = $(INSTALL_DIR)"
	echo "  SCALA_SOURCES = $(SCALA_SOURCES)"
	echo "  RESOURCE_FILES = $(RESOURCE_FILES)"
