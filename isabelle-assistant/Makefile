# Makefile for Isabelle Assistant Plugin

ifndef V
.SILENT:
endif

PLUGIN_DIR := $(shell pwd)
ISABELLE_HOME ?= /Applications/Isabelle2025-2.app
ISABELLE ?= $(if $(wildcard $(ISABELLE_HOME)/bin/isabelle),$(ISABELLE_HOME)/bin/isabelle,$(ISABELLE_HOME)/isabelle)
JEDIT_DIR := $(shell ls -d $(ISABELLE_HOME)/contrib/jedit-* 2>/dev/null | head -1)
JEDIT_JAR ?= $(JEDIT_DIR)/jedit5.7.0-patched/jedit.jar
SCALA_HOME ?= $(ISABELLE_HOME)/contrib/scala-3.3.4
SCALAC ?= $(SCALA_HOME)/bin/scalac
SCALAC_FLAGS ?= -deprecation -feature -unchecked -Werror
ISABELLE_JAR ?= $(ISABELLE_HOME)/lib/classes/isabelle.jar
JAVA_HOME ?= $(shell $(ISABELLE) getenv -b JAVA_HOME 2>/dev/null)
JAVA ?= $(if $(JAVA_HOME),$(JAVA_HOME)/bin/java,java)
JAR ?= $(if $(JAVA_HOME),$(JAVA_HOME)/bin/jar,jar)
JAVA_ENV = $(if $(JAVA_HOME),JAVA_HOME="$(JAVA_HOME)" PATH="$(JAVA_HOME)/bin:$$PATH",)
SCALA_SWING_JAR ?= $(SCALA_HOME)/lib/scala-swing_3-3.0.0.jar
SCALA3_LIB_JAR := $(wildcard $(SCALA_HOME)/lib/scala3-library_3-*.jar)
SCALA2_LIB_JAR := $(wildcard $(SCALA_HOME)/lib/scala-library-*.jar)
SCALA_XML_JAR := $(wildcard $(SCALA_HOME)/lib/scala-xml_3-*.jar)

# AWS SDK JARs
LIB_JARS = $(wildcard lib/*.jar)
LIB_CLASSPATH = $(shell echo $(LIB_JARS) | tr ' ' ':')

BUILD_DIR ?= $(PLUGIN_DIR)/build
CLASSES_DIR ?= $(BUILD_DIR)/classes
JAR_FILE ?= $(BUILD_DIR)/isabelle_assistant.jar
INSTALL_DIR ?= $(HOME)/.isabelle/Isabelle2025-2/jedit/jars

# I/Q Plugin (dependency for proof verification features)
IQ_DIR := $(PLUGIN_DIR)/../iq
IQ_JAR := $(INSTALL_DIR)/iq_plugin.jar
IQ_BUILD_JAR := $(IQ_DIR)/build/iq_plugin.jar
IQ_CLASSPATH = $(firstword $(wildcard $(IQ_JAR) $(IQ_BUILD_JAR)))

SCALA_SOURCES := $(wildcard src/*.scala)
RESOURCE_FILES := $(wildcard resources/*)
PROMPT_FILES := $(shell find prompts -type f 2>/dev/null)

TEST_SOURCES := $(wildcard src/test/scala/*.scala)
SCALATEST_JARS = $(wildcard lib/test/*.jar)
TEST_CLASSPATH = $(shell echo $(SCALATEST_JARS) | tr ' ' ':')

.PHONY: all build install clean uninstall help debug check-deps iq-build iq-install iq-clean test check-test-sanity verify-test-coverage fetch-test-deps

all: check-deps iq-install build

iq-build:
	echo "Building I/Q plugin..."
	$(MAKE) -C $(IQ_DIR) build

iq-install: iq-build
	echo "Installing I/Q plugin..."
	$(MAKE) -C $(IQ_DIR) INSTALL_DIR=$(INSTALL_DIR) install

iq-clean:
	$(MAKE) -C $(IQ_DIR) clean

check-deps:
	@if ! ls lib/*.jar >/dev/null 2>&1; then \
		echo "No dependency JARs found in lib/, fetching now..."; \
		./fetch-deps.sh; \
	fi
	@if ! ls lib/*.jar >/dev/null 2>&1; then \
		echo "ERROR: Dependency fetch did not populate lib/"; \
		exit 1; \
	fi

build: iq-build check-deps $(JAR_FILE)
	echo "Plugin built successfully: $(JAR_FILE)"

$(JAR_FILE): $(CLASSES_DIR)/.compiled $(CLASSES_DIR)/.resources $(CLASSES_DIR)/.libs
	echo "Creating JAR..."
	cd $(CLASSES_DIR) && $(JAVA_ENV) $(JAR) cf $(JAR_FILE) .

$(CLASSES_DIR)/.libs: $(LIB_JARS) | $(CLASSES_DIR)
	echo "Extracting library JARs..."
	cd $(CLASSES_DIR) && for jar in $(LIB_JARS); do $(JAVA_ENV) $(JAR) xf ../../$$jar 2>/dev/null || true; done
	rm -rf $(CLASSES_DIR)/META-INF/maven $(CLASSES_DIR)/META-INF/*.SF $(CLASSES_DIR)/META-INF/*.RSA
	touch $@

$(CLASSES_DIR)/.compiled: $(SCALA_SOURCES) | $(CLASSES_DIR)
	echo "Compiling..."
	$(JAVA_ENV) $(SCALAC) \
		$(SCALAC_FLAGS) \
		-classpath "$(JEDIT_JAR):$(ISABELLE_JAR):$(SCALA_SWING_JAR):$(LIB_CLASSPATH):$(IQ_CLASSPATH)" \
		-d $(CLASSES_DIR) \
		$(SCALA_SOURCES)
	touch $@

$(CLASSES_DIR)/.resources: $(RESOURCE_FILES) $(PROMPT_FILES) | $(CLASSES_DIR)
	echo "Copying resources..."
	cp -r resources/* $(CLASSES_DIR)/ 2>/dev/null || true
	cp -r prompts $(CLASSES_DIR)/ 2>/dev/null || true
	touch $@

$(CLASSES_DIR):
	mkdir -p $(CLASSES_DIR)

ISABELLE_SETTINGS_DIR ?= $(HOME)/.isabelle/Isabelle2025-2/etc
COMPONENT_LINE := init_component "$(PLUGIN_DIR)"

install: iq-install $(JAR_FILE)
	echo "Installing to $(INSTALL_DIR)..."
	mkdir -p $(INSTALL_DIR)
	cp $(JAR_FILE) $(INSTALL_DIR)/
	mkdir -p $(ISABELLE_SETTINGS_DIR)
	grep -qxF '$(COMPONENT_LINE)' $(ISABELLE_SETTINGS_DIR)/settings 2>/dev/null || echo '$(COMPONENT_LINE)' >> $(ISABELLE_SETTINGS_DIR)/settings
	echo "Installed. Restart Isabelle/jEdit to load the plugin."

clean: iq-clean
	rm -rf $(BUILD_DIR)

TEST_CLASSES_DIR ?= $(BUILD_DIR)/test-classes

test: build fetch-test-deps check-test-sanity verify-test-coverage
	echo "Compiling tests..."
	mkdir -p $(TEST_CLASSES_DIR)
	$(JAVA_ENV) $(SCALAC) \
		$(SCALAC_FLAGS) \
		-classpath "$(JEDIT_JAR):$(ISABELLE_JAR):$(SCALA_SWING_JAR):$(LIB_CLASSPATH):$(IQ_CLASSPATH):$(CLASSES_DIR):$(TEST_CLASSPATH)" \
		-d $(TEST_CLASSES_DIR) \
		$(TEST_SOURCES)
	echo "Running tests..."
	$(JAVA_ENV) $(JAVA) -cp "$(CLASSES_DIR):$(TEST_CLASSES_DIR):$(TEST_CLASSPATH):$(JEDIT_JAR):$(ISABELLE_JAR):$(SCALA_SWING_JAR):$(LIB_CLASSPATH):$(SCALA3_LIB_JAR):$(SCALA2_LIB_JAR):$(SCALA_XML_JAR)" \
		org.scalatest.tools.Runner -R $(TEST_CLASSES_DIR) -oD

check-test-sanity:
	@set -eu; \
	if command -v rg >/dev/null 2>&1; then \
		if rg -n '^\s*pending\s*($|//)' src/test/scala; then echo "ERROR: pending tests are not allowed"; exit 1; fi; \
		if rg -n '\.pending\s*(\(|$$)' src/test/scala; then echo "ERROR: pending tests are not allowed"; exit 1; fi; \
		if rg -n '\bignore\s*\(' src/test/scala; then echo "ERROR: ignored tests are not allowed"; exit 1; fi; \
		if rg -n '\bTODO\b|\bFIXME\b' src/test/scala; then echo "ERROR: TODO/FIXME left in test sources"; exit 1; fi; \
		if rg -n '\bcatch\b' src/test/scala; then echo "ERROR: catch blocks in tests hide failures; use explicit assertions/intercepts"; exit 1; fi; \
	else \
		if grep -R -n -E '^[[:space:]]*pending[[:space:]]*($$|//)' src/test/scala; then echo "ERROR: pending tests are not allowed"; exit 1; fi; \
		if grep -R -n -E '\.pending[[:space:]]*(\(|$$)' src/test/scala; then echo "ERROR: pending tests are not allowed"; exit 1; fi; \
		if grep -R -n -E '\bignore[[:space:]]*\(' src/test/scala; then echo "ERROR: ignored tests are not allowed"; exit 1; fi; \
		if grep -R -n -E '\bTODO\b|\bFIXME\b' src/test/scala; then echo "ERROR: TODO/FIXME left in test sources"; exit 1; fi; \
		if grep -R -n -E '\bcatch\b' src/test/scala; then echo "ERROR: catch blocks in tests hide failures; use explicit assertions/intercepts"; exit 1; fi; \
	fi

verify-test-coverage:
	@if command -v rg >/dev/null 2>&1; then \
		CHECK_CMD='rg -q -w'; \
	else \
		CHECK_CMD='grep -R -q -w'; \
	fi; \
	for module in GoalExtractor PromptLoader IQIntegration AssistantOptions AssistantTools AssistantStatusSubscription VerificationCache LLMResponseCache ResponseParser PayloadBuilder BedrockModels ErrorHandler TargetParser ProofTextUtil ChatAction SuggestAction; do \
		$$CHECK_CMD "$$module" src/test/scala || { \
			echo "ERROR: missing test ownership for module $$module"; \
			exit 1; \
		}; \
	done

fetch-test-deps:
	@if ! ls lib/test/*.jar >/dev/null 2>&1; then \
		echo "Downloading ScalaTest JARs..."; \
		mkdir -p lib/test; \
		for jar in \
			"org/scalatest/scalatest_3/3.2.17/scalatest_3-3.2.17.jar" \
			"org/scalatest/scalatest-core_3/3.2.17/scalatest-core_3-3.2.17.jar" \
			"org/scalatest/scalatest-funsuite_3/3.2.17/scalatest-funsuite_3-3.2.17.jar" \
			"org/scalatest/scalatest-matchers-core_3/3.2.17/scalatest-matchers-core_3-3.2.17.jar" \
			"org/scalatest/scalatest-shouldmatchers_3/3.2.17/scalatest-shouldmatchers_3-3.2.17.jar" \
			"org/scalactic/scalactic_3/3.2.17/scalactic_3-3.2.17.jar" \
			"org/scalatest/scalatest-compatible/3.2.17/scalatest-compatible-3.2.17.jar"; \
		do \
			filename=$$(basename "$$jar"); \
			if [ ! -f "lib/test/$$filename" ]; then \
				echo "  Downloading $$filename..."; \
				curl -sL "https://repo1.maven.org/maven2/$$jar" -o "lib/test/$$filename"; \
			fi; \
		done; \
	fi

uninstall:
	rm -f $(INSTALL_DIR)/isabelle_assistant.jar
	echo "Plugin uninstalled."

help:
	echo "Isabelle Assistant Plugin"
	echo ""
	echo "Targets:"
	echo "  all        - Build I/Q, check deps, build Assistant (default)"
	echo "  build      - Build the Assistant plugin JAR"
	echo "  install    - Build and install both I/Q and Assistant"
	echo "  clean      - Clean both I/Q and Assistant build directories"
	echo "  uninstall  - Remove installed Assistant plugin"
	echo "  iq-build   - Build I/Q plugin only"
	echo "  iq-install - Install I/Q plugin only"
	echo "  iq-clean   - Clean I/Q build directory only"
	echo "  debug      - Show configuration"
	echo ""
	echo "First run ./fetch-deps.sh to download AWS SDK JARs"

debug:
	echo "ISABELLE_HOME = $(ISABELLE_HOME)"
	echo "JEDIT_JAR     = $(JEDIT_JAR)"
	echo "ISABELLE_JAR  = $(ISABELLE_JAR)"
	echo "SCALA_HOME    = $(SCALA_HOME)"
	echo "SCALAC_FLAGS  = $(SCALAC_FLAGS)"
	echo "JAVA_HOME     = $(JAVA_HOME)"
	echo "JAVA          = $(JAVA)"
	echo "JAR           = $(JAR)"
	echo "LIB_JARS      = $(LIB_JARS)"
	echo "IQ_JAR        = $(IQ_JAR)"
	echo "IQ_AVAILABLE  = $(if $(IQ_CLASSPATH),yes,no)"
	echo "INSTALL_DIR   = $(INSTALL_DIR)"
