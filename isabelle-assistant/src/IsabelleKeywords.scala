/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Canonical database of Isabelle/HOL keywords with categorization.
 * This is the single source of truth for all keyword matching operations.
 * All ad-hoc keyword Sets throughout the codebase should reference this object.
 */
object IsabelleKeywords {
  
  /** Keyword categories for different use cases. */
  sealed trait Category
  case object ProofStarter extends Category     // Starts a proof: lemma, theorem, etc.
  case object ProofStep extends Category        // Proof steps: have, show, fix, assume, etc.
  case object ProofCloser extends Category      // Closes a proof: qed, done, sorry, oops
  case object ProofMethod extends Category      // Proof methods: by, apply, proof, using
  case object ProofControl extends Category     // Proof structuring: then, hence, moreover, etc.
  case object Definition extends Category       // Definitions: definition, fun, primrec, etc.
  case object TypeDecl extends Category         // Type declarations: datatype, record, etc.
  case object Inductive extends Category        // Inductive definitions
  case object Specification extends Category    // Specifications: assumes, shows, fixes, etc.
  case object TheoryStructure extends Category  // Theory structure: imports, begin, section, etc.
  case object LogicKeyword extends Category     // Logic keywords: if, then, else, case, etc.
  case object BuiltinType extends Category      // Built-in types: nat, bool, list, etc.
  
  case class Entry(name: String, categories: Set[Category])
  
  /** Complete canonical keyword database. */
  val all: List[Entry] = List(
    // Proof starters
    Entry("lemma", Set(ProofStarter)),
    Entry("theorem", Set(ProofStarter)),
    Entry("corollary", Set(ProofStarter)),
    Entry("proposition", Set(ProofStarter)),
    Entry("schematic_goal", Set(ProofStarter)),
    
    // Proof steps
    Entry("have", Set(ProofStep)),
    Entry("show", Set(ProofStep)),
    Entry("fix", Set(ProofStep)),
    Entry("assume", Set(ProofStep)),
    Entry("obtain", Set(ProofStep)),
    Entry("note", Set(ProofStep)),
    Entry("next", Set(ProofStep)),
    Entry("from", Set(ProofStep)),
    Entry("with", Set(ProofStep)),
    
    // Proof closers
    Entry("qed", Set(ProofCloser)),
    Entry("done", Set(ProofCloser)),
    Entry("sorry", Set(ProofCloser)),
    Entry("oops", Set(ProofCloser)),
    
    // Proof methods
    Entry("by", Set(ProofMethod)),
    Entry("apply", Set(ProofMethod)),
    Entry("proof", Set(ProofMethod)),
    Entry("using", Set(ProofMethod)),
    
    // Proof control/structuring
    Entry("then", Set(ProofControl)),
    Entry("hence", Set(ProofControl)),
    Entry("thus", Set(ProofControl)),
    Entry("moreover", Set(ProofControl)),
    Entry("ultimately", Set(ProofControl)),
    Entry("also", Set(ProofControl)),
    Entry("finally", Set(ProofControl)),
    
    // Definitions
    Entry("definition", Set(Definition)),
    Entry("fun", Set(Definition)),
    Entry("function", Set(Definition)),
    Entry("primrec", Set(Definition)),
    Entry("abbreviation", Set(Definition)),
    Entry("lift_definition", Set(Definition)),
    
    // Type declarations
    Entry("datatype", Set(TypeDecl)),
    Entry("codatatype", Set(TypeDecl)),
    Entry("type_synonym", Set(TypeDecl)),
    Entry("record", Set(TypeDecl)),
    Entry("typedef", Set(TypeDecl)),
    
    // Inductive definitions
    Entry("inductive", Set(Inductive)),
    Entry("coinductive", Set(Inductive)),
    Entry("nominal_inductive", Set(Inductive)),
    
    // Specifications
    Entry("assumes", Set(Specification)),
    Entry("shows", Set(Specification)),
    Entry("fixes", Set(Specification)),
    Entry("obtains", Set(Specification)),
    Entry("where", Set(Specification)),
    Entry("for", Set(Specification)),
    Entry("and", Set(Specification)),
    Entry("is", Set(Specification)),
    Entry("defines", Set(Specification)),
    Entry("declares", Set(Specification)),
    
    // Theory structure
    Entry("theory", Set(TheoryStructure)),
    Entry("imports", Set(TheoryStructure)),
    Entry("begin", Set(TheoryStructure)),
    Entry("end", Set(TheoryStructure)),
    Entry("section", Set(TheoryStructure)),
    Entry("subsection", Set(TheoryStructure)),
    Entry("subsubsection", Set(TheoryStructure)),
    Entry("chapter", Set(TheoryStructure)),
    Entry("locale", Set(TheoryStructure)),
    Entry("context", Set(TheoryStructure)),
    Entry("class", Set(TheoryStructure)),
    Entry("instance", Set(TheoryStructure)),
    Entry("subclass", Set(TheoryStructure)),
    Entry("interpretation", Set(TheoryStructure)),
    Entry("instantiation", Set(TheoryStructure)),
    Entry("setup", Set(TheoryStructure)),
    Entry("method", Set(TheoryStructure)),
    Entry("open", Set(TheoryStructure)),
    Entry("includes", Set(TheoryStructure)),
    Entry("overloading", Set(TheoryStructure)),
    Entry("notation", Set(TheoryStructure)),
    Entry("no_notation", Set(TheoryStructure)),
    Entry("named_theorems", Set(TheoryStructure)),
    Entry("text", Set(TheoryStructure)),
    Entry("txt", Set(TheoryStructure)),
    Entry("lemmas", Set(TheoryStructure)),
    Entry("theorems", Set(TheoryStructure)),
    Entry("declare", Set(TheoryStructure)),
    Entry("structure", Set(TheoryStructure)),
    Entry("ML", Set(TheoryStructure)),
    Entry("ML_val", Set(TheoryStructure)),
    
    // Logic keywords
    Entry("if", Set(LogicKeyword)),
    Entry("then", Set(LogicKeyword)),
    Entry("else", Set(LogicKeyword)),
    Entry("case", Set(LogicKeyword)),
    Entry("of", Set(LogicKeyword)),
    Entry("let", Set(LogicKeyword)),
    Entry("in", Set(LogicKeyword)),
    
    // Built-in types
    Entry("nat", Set(BuiltinType)),
    Entry("int", Set(BuiltinType)),
    Entry("bool", Set(BuiltinType)),
    Entry("list", Set(BuiltinType)),
    Entry("set", Set(BuiltinType)),
    Entry("option", Set(BuiltinType)),
    Entry("string", Set(BuiltinType)),
    Entry("real", Set(BuiltinType)),
    Entry("prop", Set(BuiltinType)),
    Entry("unit", Set(BuiltinType))
  )
  
  /** All keyword names (for fast lookup). */
  lazy val allKeywords: Set[String] = all.map(_.name).toSet
  
  /** Keywords that start a proof (lemma, theorem, corollary, etc.). */
  lazy val proofStarters: Set[String] = 
    all.filter(_.categories.contains(ProofStarter)).map(_.name).toSet
  
  /** Keywords that close a proof (qed, done, sorry, oops). */
  lazy val proofClosers: Set[String] = 
    all.filter(_.categories.contains(ProofCloser)).map(_.name).toSet
  
  /** Keywords that represent proof steps (have, show, fix, etc.). */
  lazy val proofSteps: Set[String] = 
    all.filter(_.categories.contains(ProofStep)).map(_.name).toSet
  
  /** Keywords that introduce proof methods (by, apply, proof, using). */
  lazy val proofMethods: Set[String] = 
    all.filter(_.categories.contains(ProofMethod)).map(_.name).toSet
  
  /** Keywords for proof structuring (then, moreover, ultimately, etc.). */
  lazy val proofControl: Set[String] = 
    all.filter(_.categories.contains(ProofControl)).map(_.name).toSet
  
  /** Definition forms (definition, fun, primrec, etc.). */
  lazy val definitionForms: Set[String] = 
    all.filter(_.categories.contains(Definition)).map(_.name).toSet
  
  /** Type declaration keywords (datatype, record, etc.). */
  lazy val typeDeclarations: Set[String] = 
    all.filter(_.categories.contains(TypeDecl)).map(_.name).toSet
  
  /** Inductive definition keywords. */
  lazy val inductiveKeywords: Set[String] = 
    all.filter(_.categories.contains(Inductive)).map(_.name).toSet
  
  /** Specification keywords (assumes, shows, fixes, etc.). */
  lazy val specificationKeywords: Set[String] = 
    all.filter(_.categories.contains(Specification)).map(_.name).toSet
  
  /** Theory structure keywords (theory, imports, section, etc.). */
  lazy val theoryStructure: Set[String] = 
    all.filter(_.categories.contains(TheoryStructure)).map(_.name).toSet
  
  /** Logic keywords (if, then, else, case, etc.). */
  lazy val logicKeywords: Set[String] = 
    all.filter(_.categories.contains(LogicKeyword)).map(_.name).toSet
  
  /** Built-in types (nat, bool, list, etc.). */
  lazy val builtinTypes: Set[String] = 
    all.filter(_.categories.contains(BuiltinType)).map(_.name).toSet
  
  /** Keywords suitable for syntax highlighting (excludes logic keywords that are too common). */
  lazy val forSyntaxHighlighting: Set[String] = 
    (proofStarters ++ proofSteps ++ proofClosers ++ proofMethods ++ proofControl ++ 
     definitionForms ++ typeDeclarations ++ inductiveKeywords ++ specificationKeywords ++ 
     theoryStructure)
  
  /** Keywords that represent "entities" that can be named and documented. */
  lazy val entityKeywords: Set[String] = 
    proofStarters ++ definitionForms ++ typeDeclarations ++ inductiveKeywords ++ 
    Set("locale", "class", "instantiation", "interpretation")
  
  /** Keywords that open a proof context (for depth tracking). */
  lazy val proofOpeners: Set[String] = proofStarters ++ Set("proof")

  /** Names of built-in automated proof methods (the arguments to `by`,
    * `apply`, and `proof`). Not theory-level keywords, but used as a
    * shared vocabulary across code extraction, pattern detection, and
    * strategy heuristics. Kept here so all call sites share a single
    * source of truth.
    */
  val automatedProofMethods: Set[String] = Set(
    "simp",
    "auto",
    "blast",
    "force",
    "metis",
    "meson",
    "arith",
    "linarith"
  )
}