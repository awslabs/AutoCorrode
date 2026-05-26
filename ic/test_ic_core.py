#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""Unit tests for I/C core logic. No I/R REPL required."""

import unittest

from ic_core import (
    normalize_theory_id, parse_theory_file, file_content_hash, ml_escape,
    split_body_by_offsets, resolve_dependencies, topological_sort,
    BodyCommand, FileEntry, TheoryHeader,
    FileImport, HeapImport, ExternalImport,
)


class TestNormalization(unittest.TestCase):

    def test_plain(self):
        self.assertEqual(normalize_theory_id("Foo"), "Foo")

    def test_strip_thy(self):
        self.assertEqual(normalize_theory_id("Foo.thy"), "Foo")

    def test_strip_quotes(self):
        self.assertEqual(normalize_theory_id('"Foo"'), "Foo")

    def test_path_basename(self):
        self.assertEqual(normalize_theory_id("sub/Main"), "Main")

    def test_quoted_path(self):
        self.assertEqual(
            normalize_theory_id('"HOL-Library/Multiset"'),
            "Multiset")

    def test_whitespace(self):
        self.assertEqual(normalize_theory_id("  Foo  "), "Foo")


class TestTheoryParsing(unittest.TestCase):

    def test_simple_theory(self):
        text = (
            "theory Foo\n"
            "  imports Main\n"
            "begin\n"
            'definition foo where "foo = (42::nat)"\n'
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.name, "Foo")
        self.assertEqual(header.imports, ["Main"])
        self.assertIn("definition foo", header.body)
        self.assertGreater(header.body_start_line, 0)

    def test_multiple_imports(self):
        text = (
            "theory Bar\n"
            '  imports Main "HOL-Library.Multiset" Utils\n'
            "begin\n"
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.name, "Bar")
        self.assertEqual(
            header.imports,
            ["Main", "HOL-Library.Multiset", "Utils"])

    def test_empty_body(self):
        text = "theory Empty\n  imports Main\nbegin\nend\n"
        header = parse_theory_file(text)
        self.assertEqual(header.name, "Empty")
        self.assertEqual(header.body.strip(), "")

    def test_body_start_line(self):
        text = (
            "theory Foo\n"       # line 1
            "  imports Main\n"   # line 2
            "begin\n"            # line 3
            "definition x\n"     # line 4
            "end\n"              # line 5
        )
        header = parse_theory_file(text)
        # body starts at the char right after 'begin' on line 3
        # that's the newline ending line 3, so body_start_line = 3
        # (the body text starts with \n, then definition on line 4)
        self.assertIn(header.body_start_line, [3, 4])

    def test_no_theory_keyword(self):
        with self.assertRaises(ValueError):
            parse_theory_file("not a theory file")

    def test_imports_with_comment_block(self):
        """Isabelle \\<comment> block in imports should be ignored."""
        text = (
            "theory Foo\n"
            "  imports\n"
            "    Main\n"
            "    \\<comment> \\<open>some comment\\<close>\n"
            "    Utils\n"
            "begin\n"
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.imports, ["Main", "Utils"])

    def test_imports_with_nested_comment(self):
        """Nested \\<open>...\\<close> in comment should be handled."""
        text = (
            "theory Foo\n"
            "  imports\n"
            "    Main\n"
            "    \\<comment> \\<open>outer \\<open>nested\\<close> end\\<close>\n"
            "    Utils\n"
            "begin\n"
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.imports, ["Main", "Utils"])

    def test_imports_with_ml_comment(self):
        """(* ... *) comment in imports should be ignored."""
        text = (
            "theory Foo\n"
            "  imports A (* B *) C\n"
            "begin\nend\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.imports, ["A", "C"])

    def test_imports_with_keywords_block(self):
        """keywords block in header should not be parsed as imports."""
        text = (
            "theory Foo\n"
            "  imports Main\n"
            '  keywords "dummy_kw" :: thy_decl\n'
            "begin\n"
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.imports, ["Main"])
        self.assertTrue(header.has_keywords)

    def test_no_keywords_flag(self):
        """Theory without keywords block has has_keywords=False."""
        text = "theory Foo\n  imports Main\nbegin\nend\n"
        self.assertFalse(parse_theory_file(text).has_keywords)

    def test_multiline_imports(self):
        text = (
            "theory Foo\n"
            "  imports\n"
            "    Main\n"
            "    Utils\n"
            "begin\n"
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertEqual(header.imports, ["Main", "Utils"])

    def test_body_with_nested_end(self):
        """Body containing 'end' inside a proof should not truncate."""
        text = (
            "theory Foo\n"
            "  imports Main\n"
            "begin\n"
            "lemma True\n"
            "proof\n"
            "  show True by simp\n"
            "qed\n"
            "end\n"
        )
        header = parse_theory_file(text)
        self.assertIn("lemma True", header.body)
        self.assertIn("qed", header.body)


class TestMLEscape(unittest.TestCase):

    def test_basic(self):
        self.assertEqual(ml_escape('hello'), 'hello')

    def test_quotes(self):
        self.assertEqual(ml_escape('"foo"'), '\\"foo\\"')

    def test_newlines(self):
        self.assertEqual(ml_escape('a\nb'), 'a\\nb')

    def test_backslash(self):
        self.assertEqual(ml_escape('a\\b'), 'a\\\\b')

    def test_tabs(self):
        self.assertEqual(ml_escape('a\tb'), 'a\\tb')

    def test_isabelle_symbol(self):
        self.assertEqual(ml_escape('\\<forall>'), '\\\\<forall>')

    def test_carriage_return_stripped(self):
        self.assertEqual(ml_escape('a\rb'), 'ab')


class TestCommandSplitting(unittest.TestCase):

    def test_single_command(self):
        body = 'definition foo where "foo = 1"'
        cmds = split_body_by_offsets(body, [1], body_start_line=4)
        self.assertEqual(len(cmds), 1)
        self.assertEqual(cmds[0].text, body.strip())
        self.assertEqual(cmds[0].file_line, 4)

    def test_multiple_commands(self):
        body = 'definition foo where "foo = 1"\nlemma "foo > 0" by simp'
        off2 = body.index('lemma') + 1  # 1-based
        cmds = split_body_by_offsets(body, [1, off2], body_start_line=4)
        self.assertEqual(len(cmds), 2)
        self.assertIn("definition", cmds[0].text)
        self.assertIn("lemma", cmds[1].text)
        self.assertEqual(cmds[0].file_line, 4)
        self.assertEqual(cmds[1].file_line, 5)

    def test_empty_offsets(self):
        cmds = split_body_by_offsets("some text", [], body_start_line=1)
        self.assertEqual(len(cmds), 0)

    def test_multiline_command(self):
        body = 'lemma foo:\n  "True"\n  by simp\ndefinition bar where "bar = 1"'
        off2 = body.index('definition') + 1
        cmds = split_body_by_offsets(body, [1, off2], body_start_line=4)
        self.assertEqual(len(cmds), 2)
        self.assertIn("lemma foo", cmds[0].text)
        self.assertIn("by simp", cmds[0].text)
        self.assertEqual(cmds[0].file_line, 4)
        self.assertEqual(cmds[1].file_line, 7)

    def test_whitespace_only_not_included(self):
        body = '  \n  \n  definition foo where "foo = 1"'
        off = body.index('definition') + 1
        cmds = split_body_by_offsets(body, [off], body_start_line=4)
        self.assertEqual(len(cmds), 1)
        self.assertIn("definition", cmds[0].text)


class TestTopologicalSort(unittest.TestCase):

    def test_linear(self):
        graph = {"A": set(), "B": {"A"}, "C": {"B"}}
        order = topological_sort(graph)
        self.assertEqual(order, ["A", "B", "C"])

    def test_diamond(self):
        graph = {"A": set(), "B": {"A"}, "C": {"A"}, "D": {"B", "C"}}
        order = topological_sort(graph)
        self.assertLess(order.index("A"), order.index("B"))
        self.assertLess(order.index("A"), order.index("C"))
        self.assertLess(order.index("B"), order.index("D"))
        self.assertLess(order.index("C"), order.index("D"))

    def test_cycle(self):
        graph = {"A": {"B"}, "B": {"A"}}
        with self.assertRaises(ValueError) as ctx:
            topological_sort(graph)
        self.assertIn("cycle", str(ctx.exception).lower())

    def test_single(self):
        self.assertEqual(topological_sort({"A": set()}), ["A"])

    def test_independent(self):
        graph = {"A": set(), "B": set(), "C": set()}
        order = topological_sort(graph)
        self.assertEqual(sorted(order), ["A", "B", "C"])

    def test_three_node_cycle(self):
        graph = {"A": {"C"}, "B": {"A"}, "C": {"B"}}
        with self.assertRaises(ValueError) as ctx:
            topological_sort(graph)
        self.assertIn("cycle", str(ctx.exception).lower())


    def test_duplicate_deps_in_list(self):
        """Duplicate deps in list values should not cause false cycle."""
        graph = {"A": [], "B": ["A", "A"], "C": ["B"]}
        order = topological_sort(graph)
        self.assertEqual(order, ["A", "B", "C"])

    def test_cycle_resolved_imports(self):
        """Cycle detection with ResolvedImport keys and list values."""
        a = FileImport(QualifiedTheory("s.A"))
        b = FileImport(QualifiedTheory("s.B"))
        graph = {a: [b], b: [a]}
        with self.assertRaises(ValueError) as ctx:
            topological_sort(graph)
        self.assertIn("cycle", str(ctx.exception).lower())


class TestDependencyResolution(unittest.TestCase):

    def test_heap_and_file_deps(self):
        files = {
            QualifiedTheory("S.Base"): FileEntry(
                path="/tmp/Base.thy",
                header=TheoryHeader("Base", ["Main"], "", 0),
                session_name="S"),
            QualifiedTheory("S.Utils"): FileEntry(
                path="/tmp/Utils.thy",
                header=TheoryHeader("Utils", ["Base", "Main"], "", 0),
                session_name="S"),
        }
        order, _ = resolve_dependencies(files, {"Main", "HOL"})
        file_imports = [ri for ri in order if isinstance(ri, FileImport)]
        heap_imports = [ri for ri in order if isinstance(ri, HeapImport)]
        self.assertEqual([ri.qualified for ri in file_imports],
                         [QualifiedTheory("S.Base"),
                          QualifiedTheory("S.Utils")])
        self.assertIn("Main", [ri.name for ri in heap_imports])

    def test_qualified_heap_import(self):
        files = {
            QualifiedTheory("S.Foo"): FileEntry(
                path="/tmp/Foo.thy",
                header=TheoryHeader(
                    "Foo", ["Main", "HOL-Library.Multiset"], "", 0),
                session_name="S"),
        }
        order, _ = resolve_dependencies(files, {"Main"})
        file_imports = [ri for ri in order if isinstance(ri, FileImport)]
        external = [ri for ri in order if isinstance(ri, ExternalImport)]
        self.assertEqual([ri.qualified for ri in file_imports],
                         [QualifiedTheory("S.Foo")])
        self.assertIn("HOL-Library.Multiset",
                       [ri.name for ri in external])

    def test_alphabetical_build_order(self):
        """Build order is alphabetical for same-level deps.

        test_over_eager_parents relies on OE_B being processed before OE_C
        so that OE_C's REPL would incorrectly receive OE_B as a parent.
        """
        files = {
            qt("OE_A", "s"): mock_entry("OE_A", "s", ["Main"], 1),
            qt("OE_B", "s"): mock_entry("OE_B", "s", ["Main"], 1),
            qt("OE_C", "s"): mock_entry("OE_C", "s", ["OE_A"], 1),
            qt("OE_Target", "s"): mock_entry("OE_Target", "s", ["OE_B", "OE_C"], 1),
        }
        order, _ = resolve_dependencies(files, {"Main"})
        file_names = [ri.qualified.theory_name for ri in order
                      if isinstance(ri, FileImport)]
        self.assertEqual(file_names,
                         ["OE_A", "OE_B", "OE_C", "OE_Target"])

    def test_external_import(self):
        """Unknown import resolves as ExternalImport."""
        files = {
            QualifiedTheory("S.Foo"): FileEntry(
                path="/tmp/Foo.thy",
                header=TheoryHeader("Foo", ["NonExistent"], "", 0),
                session_name="S"),
        }
        order, _ = resolve_dependencies(files, {"Main"})
        external = [ri for ri in order if isinstance(ri, ExternalImport)]
        self.assertEqual(len(external), 1)
        self.assertEqual(external[0].name, "NonExistent")



class TestContentHash(unittest.TestCase):

    def test_deterministic(self):
        h1 = file_content_hash("hello world")
        h2 = file_content_hash("hello world")
        self.assertEqual(h1, h2)

    def test_different_content(self):
        h1 = file_content_hash("hello")
        h2 = file_content_hash("world")
        self.assertNotEqual(h1, h2)

    def test_length(self):
        h = file_content_hash("test")
        self.assertEqual(len(h), 16)


from ic_check import parse_repls_output, ReplInfo


class TestParseReplsOutput(unittest.TestCase):

    def test_empty(self):
        self.assertEqual(parse_repls_output(""), ({}, {}))

    def test_single_current(self):
        text = "  > ic.HOL.Foo (3 steps, from theory Main)"
        result, busy = parse_repls_output(text)
        self.assertEqual(len(result), 1)
        info = result["ic.HOL.Foo"]
        self.assertEqual(info.step_count, 3)
        self.assertEqual(info.stale_count, 0)
        self.assertEqual(info.origin, "theory Main")
        self.assertTrue(info.is_current)

    def test_multiple(self):
        text = (
            "  > ic.S.A (3 steps, from theory Main+ic.S.Dep)\n"
            "    ic.S.B (5 steps, 2 stale, from theory Main)\n"
        )
        result, busy = parse_repls_output(text)
        self.assertEqual(len(result), 2)
        self.assertTrue(result["ic.S.A"].is_current)
        self.assertFalse(result["ic.S.B"].is_current)
        self.assertEqual(result["ic.S.B"].stale_count, 2)

    def test_non_ics_filtered(self):
        text = (
            "    myrepl (1 steps, from theory Main)\n"
            "    ic.S.A (2 steps, from theory Main)\n"
        )
        result, busy = parse_repls_output(text)
        self.assertEqual(len(result), 1)
        self.assertIn("ic.S.A", result)

    def test_singular_step(self):
        text = "    ic.S.X (1 step, from theory Main)"
        result, busy = parse_repls_output(text)
        self.assertEqual(result["ic.S.X"].step_count, 1)

    def test_complex_origin(self):
        text = "    ic.S.A (10 steps, from theory Main+ic.S.B+ic.S.C)"
        result, busy = parse_repls_output(text)
        self.assertEqual(result["ic.S.A"].origin, "theory Main+ic.S.B+ic.S.C")


from ic_core import (
    QualifiedTheory,
    DiamondStrategy, SkipPlan, LoadFilePlan,
    CheckPlan, IncrementalPlan, SegmentInitPlan, RecoverErrorPlan,
    InHeap, ReplClean, ReplChanged, ReplCachedError, NoRepl,
    FileLoaded, FileNotLoaded, HeapStale, HeapStaleDep,
    SegmentDiff, ChangeInfo, LineInfo,
)
from ic_check import (
    CheckContext, theory_name_from_repl,
    propagate_staleness, resolve_diamonds, build_plans,
    assign_init_strategies,
)


def qt(name, session="s"):
    """Shorthand for QualifiedTheory in tests."""
    return QualifiedTheory(f"{session}.{name}")


def fi(name, session="s"):
    """Shorthand for FileImport in tests."""
    return FileImport(QualifiedTheory(f"{session}.{name}"))


def assign_plans(ctx, deps_in_order, classifications):
    """Test helper: classify → propagate → build → diamonds → init strategies."""
    classes = dict(classifications)
    rebase_rebuilding = propagate_staleness(
        classes, deps_in_order, ctx.files,
        markers=ctx.markers, active_repls=ctx.active_repls)
    plans = build_plans(classes, deps_in_order,
                        always_stepwise=ctx.always_stepwise)
    resolve_diamonds(plans, classes, deps_in_order, ctx)
    assign_init_strategies(plans, rebase_rebuilding, ctx.dep_graph, deps_in_order)
    return plans


def mock_entry(name, session, imports, n_lines):
    """Build a FileEntry with a body of n_lines lines."""
    body = "\n".join(f'definition x{i} where "x{i} = ({i}::nat)"'
                     for i in range(n_lines))
    return FileEntry(
        path=f"/mock/{name}.thy",
        header=TheoryHeader(name=name, imports=imports,
                            body=body, body_start_line=3),
        session_name=session,
    )


def mock_ctx(files, active_repls, loaded_theories=None):
    """Build a CheckContext with mock data (no REPL connection)."""
    ctx = CheckContext(repl=None)  # type: ignore[arg-type]
    ctx.files = files
    ctx.active_repls = active_repls
    ctx.loaded_theories = loaded_theories or {"Main"}
    ctx.diamond_strategy = DiamondStrategy.HEURISTIC
    # Populate markers for active REPLs (simulates stepped markers)
    for rn, info in active_repls.items():
        name = rn.removeprefix("ic.")
        ctx.markers[name] = SteppedMarker(
            "0000000000000000", info.step_count, None)
    return ctx


class TestTheoryNameFromRepl(unittest.TestCase):

    def test_session_and_name(self):
        qt = theory_name_from_repl("ic.session.Name")
        self.assertEqual(qt.name, "session.Name")
        self.assertEqual(qt.theory_name, "Name")
        self.assertEqual(qt.session_name, "session")

    def test_no_session(self):
        qt = theory_name_from_repl("ic.Name")
        self.assertEqual(qt.name, "Name")


def mock_classifications(files, active_repls, deps):
    """Build FileClassification dict from mock data.

    deps should be a list of ResolvedImport (FileImport).
    """
    result = {}
    for ri in deps:
        qt = ri.qualified if isinstance(ri, FileImport) else None
        if qt and qt.repl_name in active_repls:
            result[ri] = ReplClean(qt)
        else:
            result[ri] = NoRepl(qt)
    return result


class TestGlobalDiamondResolution(unittest.TestCase):
    """Unit tests for global diamond resolution. No I/R REPL required."""

    def test_single_repl_picks_reload(self):
        """A(5,REPL) <- B(1,pending), C(10,pending). RELOAD=5, REPL=11 -> RELOAD."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 5),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["A"], 10),
            qt("D"): mock_entry("D", "s", ["B", "C"], 1),
        }
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory Main", False)}
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("B"), fi("C"), fi("D")])
        plans = assign_plans(ctx, [fi("A"), fi("B"), fi("C"), fi("D")], c)
        self.assertIsInstance(plans[fi("B")], LoadFilePlan)
        self.assertIsInstance(plans[fi("C")], LoadFilePlan)
        # A's REPL downgraded to LOAD_FILE (RELOAD resolves the conflict)
        self.assertIsInstance(plans[fi("A")], LoadFilePlan)

    def test_single_repl_picks_repl(self):
        """A(20,REPL) <- B(1,pending), C(2,pending). RELOAD=20, REPL=3 -> REPL."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 20),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["A"], 2),
            qt("D"): mock_entry("D", "s", ["B", "C"], 1),
        }
        active = {"ic.s.A": ReplInfo("ic.s.A", 20, 0, "theory Main", False)}
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("B"), fi("C"), fi("D")])
        plans = assign_plans(ctx, [fi("A"), fi("B"), fi("C"), fi("D")], c)
        self.assertIsInstance(plans[fi("B")], CheckPlan)
        self.assertIsInstance(plans[fi("C")], CheckPlan)
        # A keeps its REPL (REPL strategy)
        self.assertIsInstance(plans[fi("A")], SkipPlan)

    def test_two_independent_repls(self):
        """A(2,REPL)<-B(10,pending), X(10,REPL)<-Y(2,pending). Different groups."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 2),
            qt("B"): mock_entry("B", "s", ["A"], 10),
            qt("X"): mock_entry("X", "s", ["Main"], 10),
            qt("Y"): mock_entry("Y", "s", ["X"], 2),
            qt("T"): mock_entry("T", "s", ["B", "Y"], 1),
        }
        active = {
            "ic.s.A": ReplInfo("ic.s.A", 2, 0, "theory Main", False),
            "ic.s.X": ReplInfo("ic.s.X", 10, 0, "theory Main", False),
        }
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("X"), fi("B"), fi("Y"), fi("T")])
        plans = assign_plans(ctx, [fi("A"), fi("X"), fi("B"), fi("Y"), fi("T")], c)
        self.assertIsInstance(plans[fi("B")], LoadFilePlan)   # A small → RELOAD
        self.assertIsInstance(plans[fi("Y")], CheckPlan)   # X large → REPL

    def test_connected_via_shared_pending_dep(self):
        """A(3,REPL), B(3,REPL) independent. C(1,pending) imports both -> one group."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 3),
            qt("B"): mock_entry("B", "s", ["Main"], 3),
            qt("C"): mock_entry("C", "s", ["A", "B"], 1),
            qt("T"): mock_entry("T", "s", ["C"], 1),
        }
        active = {
            "ic.s.A": ReplInfo("ic.s.A", 3, 0, "theory Main", False),
            "ic.s.B": ReplInfo("ic.s.B", 3, 0, "theory Main", False),
        }
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("B"), fi("C"), fi("T")])
        plans = assign_plans(ctx, [fi("A"), fi("B"), fi("C"), fi("T")], c)
        # RELOAD=3+3=6, REPL=1. REPL wins.
        self.assertIsInstance(plans[fi("C")], CheckPlan)

    def test_connected_via_dependency(self):
        """A(2,REPL), B(2,REPL,imports A). C(10,pending,imports B) -> one group."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 2),
            qt("B"): mock_entry("B", "s", ["A"], 2),
            qt("C"): mock_entry("C", "s", ["B"], 10),
            qt("T"): mock_entry("T", "s", ["C"], 1),
        }
        active = {
            "ic.s.A": ReplInfo("ic.s.A", 2, 0, "theory Main", False),
            "ic.s.B": ReplInfo("ic.s.B", 2, 0, "theory Main+ic.s.A", False),
        }
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("B"), fi("C"), fi("T")])
        plans = assign_plans(ctx, [fi("A"), fi("B"), fi("C"), fi("T")], c)
        # RELOAD=2+2=4, REPL=10. RELOAD wins.
        self.assertIsInstance(plans[fi("C")], LoadFilePlan)

    def test_cascade_both_repls_and_pending(self):
        """A(1,REPL), B(1,REPL,imports A). C(1,pending,imports B), D(1,pending,imports A)."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["B"], 1),
            qt("D"): mock_entry("D", "s", ["A"], 1),
            qt("T"): mock_entry("T", "s", ["C", "D"], 1),
        }
        active = {
            "ic.s.A": ReplInfo("ic.s.A", 1, 0, "theory Main", False),
            "ic.s.B": ReplInfo("ic.s.B", 1, 0, "theory Main+ic.s.A", False),
        }
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("B"), fi("C"), fi("D"), fi("T")])
        plans = assign_plans(ctx, [fi("A"), fi("B"), fi("C"), fi("D"), fi("T")], c)
        # RELOAD=1+1=2, REPL=1+1=2. Tie -> RELOAD.
        self.assertIsInstance(plans[fi("C")], LoadFilePlan)
        self.assertIsInstance(plans[fi("D")], LoadFilePlan)

    def test_no_conflicts_all_repl(self):
        """No diamond conflicts -> A stays REUSE_REPL."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 5),
            qt("T"): mock_entry("T", "s", ["A"], 1),
        }
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory Main", False)}
        ctx = mock_ctx(files, active)

        c = mock_classifications(files, active, [fi("A"), fi("T")])
        plans = assign_plans(ctx, [fi("A"), fi("T")], c)
        self.assertIsInstance(plans[fi("A")], SkipPlan)


class TestStalenesssPropagation(unittest.TestCase):
    """Unit tests for propagate_staleness. No I/R REPL required."""

    def test_linear_chain(self):
        """A(NoRepl) -> B(ReplClean) -> C(ReplClean): both B and C become NoRepl."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["B"], 1),
        }
        classes = {
            fi("A"): NoRepl(qt("A")),
            fi("B"): ReplClean(qt("B")),
            fi("C"): ReplClean(qt("C")),
        }
        propagate_staleness(classes, [fi("A"), fi("B"), fi("C")], files, {}, {})
        self.assertIsInstance(classes[fi("A")], NoRepl)
        self.assertIsInstance(classes[fi("B")], NoRepl)
        self.assertIsInstance(classes[fi("C")], NoRepl)

    def test_no_propagation(self):
        """All ReplClean with no rebuilding deps -> no changes."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["Main"], 1),
        }
        classes = {
            fi("A"): ReplClean(qt("A")),
            fi("B"): ReplClean(qt("B")),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("A")], ReplClean)
        self.assertIsInstance(classes[fi("B")], ReplClean)

    def test_partial_propagation(self):
        """A(ReplChanged) -> B(ReplClean,imports A): B becomes NoRepl.
        C(ReplClean,imports Main): C stays ReplClean."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["Main"], 1),
        }
        classes = {
            fi("A"): ReplChanged(qt("A"), None, 0, (0, 0), None, ""),
            fi("B"): ReplClean(qt("B")),
            fi("C"): ReplClean(qt("C")),
        }
        propagate_staleness(classes, [fi("A"), fi("B"), fi("C")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], NoRepl)
        self.assertIsInstance(classes[fi("C")], ReplClean)

    def test_diamond_propagation(self):
        """A(NoRepl), B(ReplClean,imports A), C(ReplClean,imports A): both stale."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["A"], 1),
        }
        classes = {
            fi("A"): NoRepl(qt("A")),
            fi("B"): ReplClean(qt("B")),
            fi("C"): ReplClean(qt("C")),
        }
        propagate_staleness(classes, [fi("A"), fi("B"), fi("C")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], NoRepl)
        self.assertIsInstance(classes[fi("C")], NoRepl)

    def test_qualified_import(self):
        """Import as 'session.A' (qualified) still triggers staleness."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["s.A"], 1),
        }
        classes = {
            fi("A"): NoRepl(qt("A")),
            fi("B"): ReplClean(qt("B")),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], NoRepl)

    def test_file_not_loaded_propagates(self):
        """A(FileNotLoaded) -> B(FileLoaded): B becomes FileNotLoaded."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
        }
        classes = {
            fi("A"): FileNotLoaded(qt("A")),
            fi("B"): FileLoaded(qt("B")),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], FileNotLoaded)

    def test_file_loaded_no_propagation(self):
        """A(FileLoaded), B(FileLoaded,imports A): no change when A is up to date."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
        }
        classes = {
            fi("A"): FileLoaded(qt("A")),
            fi("B"): FileLoaded(qt("B")),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("A")], FileLoaded)
        self.assertIsInstance(classes[fi("B")], FileLoaded)

    def test_file_not_loaded_propagates_to_repl(self):
        """A(FileNotLoaded) -> B(ReplClean): B becomes NoRepl."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
        }
        classes = {
            fi("A"): FileNotLoaded(qt("A")),
            fi("B"): ReplClean(qt("B")),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], NoRepl)

    def test_heap_stale_propagates(self):
        """A(HeapStale) -> B(ReplClean): B becomes NoRepl."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
        }
        classes = {
            fi("A"): HeapStale(qt("A"), SegmentDiff(
                "s.A:1", [], 0, "abc", LineInfo(1, 1))),
            fi("B"): ReplClean(qt("B")),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], NoRepl)

    def test_heap_repl_clean_becomes_heap_stale_dep(self):
        """A(NoRepl) -> B(ReplClean, in_heap): B becomes HeapStaleDep, not NoRepl."""
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
        }
        classes = {
            fi("A"): NoRepl(qt("A")),
            fi("B"): ReplClean(qt("B"), in_heap=True),
        }
        propagate_staleness(classes, [fi("A"), fi("B")], files, {}, {})
        self.assertIsInstance(classes[fi("B")], HeapStaleDep)

    def test_in_heap_with_non_heap_dep(self):
        """InHeap dep becomes HeapStaleDep if any file dep is not InHeap.

        A heap theory can only trust its heap version if all its file
        deps are also InHeap. If a dep has a stepped REPL (ReplClean),
        the heap version may be stale.
        """
        files = {
            qt("A"): mock_entry("A", "s", ["Main"], 1),
            qt("B"): mock_entry("B", "s", ["A"], 1),
            qt("C"): mock_entry("C", "s", ["B"], 1),
        }
        classes = {
            fi("A"): ReplClean(qt("A"), in_heap=True),
            fi("B"): InHeap(qt("B")),
            fi("C"): InHeap(qt("C")),
        }
        propagate_staleness(classes, [fi("A"), fi("B"), fi("C")], files, {}, {})
        # A stays ReplClean (not converted)
        self.assertIsInstance(classes[fi("A")], ReplClean)
        # B becomes HeapStaleDep (dep A is not InHeap)
        self.assertIsInstance(classes[fi("B")], HeapStaleDep)
        # C cascades via rebuilding (B is now in rebuilding set)
        self.assertIsInstance(classes[fi("C")], HeapStaleDep)


class TestBuildPlans(unittest.TestCase):
    """Unit tests for build_plans. No I/R REPL required."""

    def test_classification_types(self):
        """Each classification type maps to the expected DepPlan."""
        classes = {
            fi("A"): InHeap(qt("A")),
            fi("B"): ReplClean(qt("B")),
            fi("C"): NoRepl(qt("C")),
            fi("E"): FileLoaded(qt("E")),
            fi("F"): FileNotLoaded(qt("F")),
            fi("D"): ReplChanged(qt("D"), None, 0,
                             step_range=(1, 5), new_header=None,
                             content_hash=""),
        }
        plans = build_plans(classes, [fi("A"), fi("B"), fi("C"), fi("E"), fi("F"), fi("D")], set())
        self.assertIsInstance(plans[fi("A")], SkipPlan)
        self.assertIsInstance(plans[fi("B")], SkipPlan)
        self.assertIsInstance(plans[fi("C")], LoadFilePlan)
        self.assertIsInstance(plans[fi("E")], SkipPlan)
        self.assertIsInstance(plans[fi("F")], LoadFilePlan)
        self.assertIsInstance(plans[fi("D")], IncrementalPlan)

    def test_repl_changed_preserves_change_info(self):
        """IncrementalPlan from ReplChanged carries change_info and step_range."""
        change = ChangeInfo([], [], 0, LineInfo(1, 1))
        classes = {
            fi("A"): ReplChanged(qt("A"), change, 0,
                             step_range=(1, 3), new_header=None,
                             content_hash=""),
        }
        plans = build_plans(classes, [fi("A")], set())
        self.assertIsInstance(plans[fi("A")], IncrementalPlan)
        self.assertIs(plans[fi("A")].change_info, change)
        self.assertEqual(plans[fi("A")].step_range, (1, 3))

    def test_heap_stale_maps_to_segment_init(self):
        """HeapStale maps to SegmentInitPlan with SegmentDiff."""
        diff = SegmentDiff("s.A:3", ["cmd1"], 5, "abc123", LineInfo(3, 5))
        classes = {
            fi("A"): HeapStale(qt("A"), diff),
        }
        plans = build_plans(classes, [fi("A")], set())
        self.assertIsInstance(plans[fi("A")], SegmentInitPlan)
        self.assertEqual(plans[fi("A")].diff.segment_spec, "s.A:3")
        self.assertEqual(plans[fi("A")].diff.tail, ["cmd1"])
        self.assertEqual(plans[fi("A")].diff.content_hash, "abc123")


from ic_check import (
    serialize_marker, parse_marker, parse_symtab_output,
    SteppedMarker, LoadedMarker, HeapVerifiedMarker,
)


class TestMarkerSerialization(unittest.TestCase):
    """Unit tests for marker serialization/parsing round-trips."""

    def test_stepped_marker_round_trip(self):
        m = SteppedMarker("abcdef0123456789", 5, None)
        text = serialize_marker(m)
        parsed = parse_marker(text)
        self.assertEqual(parsed, m)

    def test_stepped_marker_with_segment(self):
        m = SteppedMarker("abcdef0123456789", 3, "S.Theory:42")
        text = serialize_marker(m)
        parsed = parse_marker(text)
        self.assertEqual(parsed, m)

    def test_loaded_marker_round_trip(self):
        m = LoadedMarker("abcdef0123456789")
        text = serialize_marker(m)
        parsed = parse_marker(text)
        self.assertEqual(parsed, m)

    def test_loaded_marker_with_deps_round_trip(self):
        m = LoadedMarker("abcdef0123456789", {"S.Dep": "1111", "S.Dep2": "2222"})
        text = serialize_marker(m)
        parsed = parse_marker(text)
        self.assertEqual(parsed, m)

    def test_heap_verified_marker_round_trip(self):
        m = HeapVerifiedMarker("abcdef0123456789")
        text = serialize_marker(m)
        parsed = parse_marker(text)
        self.assertEqual(parsed, m)


class TestSymtabOutput(unittest.TestCase):
    """Unit tests for parsing ic_symtab_get_all output."""

    def test_empty(self):
        self.assertEqual(parse_symtab_output(""), {})

    def test_single_stepped(self):
        m = SteppedMarker("abcdef0123456789", 5, None)
        raw = f"S.Foo\t{serialize_marker(m)}"
        result = parse_symtab_output(raw)
        self.assertEqual(result, {"S.Foo": m})

    def test_multiple_entries(self):
        m1 = SteppedMarker("aaa", 3, "S.T:42", {"S.Dep": "bbb"})
        m2 = LoadedMarker("ccc")
        m3 = HeapVerifiedMarker("ddd")
        raw = "\n".join([
            f"S.A\t{serialize_marker(m1)}",
            f"S.B\t{serialize_marker(m2)}",
            f"S.C\t{serialize_marker(m3)}",
        ])
        result = parse_symtab_output(raw)
        self.assertEqual(result, {"S.A": m1, "S.B": m2, "S.C": m3})

    def test_blank_lines_skipped(self):
        m = LoadedMarker("abcdef0123456789")
        raw = f"\n\nS.Foo\t{serialize_marker(m)}\n\n"
        result = parse_symtab_output(raw)
        self.assertEqual(result, {"S.Foo": m})

    def test_malformed_line_skipped(self):
        m = LoadedMarker("abcdef0123456789")
        raw = f"no-tab-here\nS.Foo\t{serialize_marker(m)}"
        result = parse_symtab_output(raw)
        self.assertEqual(result, {"S.Foo": m})

    def test_unparseable_value_skipped(self):
        m = LoadedMarker("abcdef0123456789")
        raw = f"S.Bad\tgarbage\nS.Good\t{serialize_marker(m)}"
        result = parse_symtab_output(raw)
        self.assertEqual(result, {"S.Good": m})

    def test_round_trip_all_marker_types(self):
        """serialize_marker -> tab format -> parse_symtab_output for each type."""
        markers = {
            "S.Stepped": SteppedMarker("aaa", 10, None, {"S.D": "bbb"}),
            "S.Segment": SteppedMarker("ccc", 3, "S.T:7"),
            "S.Loaded": LoadedMarker("ddd"),
            "S.Heap": HeapVerifiedMarker("eee"),
        }
        raw = "\n".join(f"{k}\t{serialize_marker(v)}"
                        for k, v in markers.items())
        self.assertEqual(parse_symtab_output(raw), markers)


from ic_check import (
    pin_deps_from_origin, removal_order, expand_with_pin_dependents,
    has_persistent_repl, BusyReplInfo,
)
from ic_core import ReplCachedError


class TestPinDepsFromOrigin(unittest.TestCase):
    """Unit tests for pin_deps_from_origin. No I/R REPL required."""

    def test_two_pins(self):
        self.assertEqual(pin_deps_from_origin("pin@ic.S.A+pin@ic.S.B"),
                         ["ic.S.A", "ic.S.B"])

    def test_mixed_heap_and_pin(self):
        self.assertEqual(pin_deps_from_origin("Main+pin@ic.S.A"),
                         ["ic.S.A"])

    def test_no_pins(self):
        self.assertEqual(pin_deps_from_origin("Main"), [])

    def test_segment_origin(self):
        self.assertEqual(pin_deps_from_origin("DiamondStale.DIS_X:3"), [])

    def test_pin_with_comma_suffix(self):
        """Comma after pin ref should not be included in the name."""
        self.assertEqual(pin_deps_from_origin("pin@ic.S.A, pinned"),
                         ["ic.S.A"])

    def test_two_pins_with_annotation(self):
        """Multiple pins followed by annotation text."""
        self.assertEqual(
            pin_deps_from_origin("pin@ic.S.A+pin@ic.S.B, pinned [stale]"),
            ["ic.S.A", "ic.S.B"])


class TestRemovalOrder(unittest.TestCase):
    """Unit tests for removal_order. No I/R REPL required."""

    def test_linear_chain(self):
        """A(no deps), B(pin@A), C(pin@B) -> removal order is [C, B, A]."""
        origins = {
            "A": "theory Main",
            "B": "pin@A",
            "C": "pin@B",
        }
        order = removal_order(origins, {"A", "B", "C"})
        self.assertEqual(order, ["C", "B", "A"])

    def test_diamond(self):
        """A(no deps), B(pin@A), C(pin@A), D(pin@B+pin@C) -> D first, then B/C, then A."""
        origins = {
            "A": "theory Main",
            "B": "pin@A",
            "C": "pin@A",
            "D": "pin@B+pin@C",
        }
        order = removal_order(origins, {"A", "B", "C", "D"})
        # D must come first (depends on B and C)
        self.assertEqual(order[0], "D")
        # A must come last (B and C depend on it)
        self.assertEqual(order[-1], "A")
        # B and C are in the middle (order between them doesn't matter)
        self.assertIn("B", order[1:3])
        self.assertIn("C", order[1:3])

    def test_no_deps(self):
        """All independent -> any order."""
        origins = {
            "A": "theory Main",
            "B": "theory Main",
            "C": "theory Main",
        }
        order = removal_order(origins, {"A", "B", "C"})
        self.assertEqual(sorted(order), ["A", "B", "C"])

    def test_single(self):
        origins = {"A": "theory Main"}
        order = removal_order(origins, {"A"})
        self.assertEqual(order, ["A"])


class TestExpandWithPinDependents(unittest.TestCase):
    """Unit tests for expand_with_pin_dependents. No I/R REPL required."""

    def test_direct_dependent(self):
        """A being removed, B has origin 'pin@A' -> expanded includes B."""
        origins = {
            "A": "theory Main",
            "B": "pin@A",
        }
        result = expand_with_pin_dependents(origins, {"A"})
        self.assertEqual(result, {"A", "B"})

    def test_no_dependent(self):
        """A being removed, B has origin 'Main' -> expanded is just {A}."""
        origins = {
            "A": "theory Main",
            "B": "theory Main",
        }
        result = expand_with_pin_dependents(origins, {"A"})
        self.assertEqual(result, {"A"})

    def test_transitive_expansion(self):
        """A removed, B has 'pin@A', C has 'pin@B' -> expands to {A, B, C}.

        The function iterates the dict, mutating `expanded` in-place.
        When B is processed before C, B gets added (depends on A), then
        C gets added (depends on B which is now in expanded).
        """
        origins = {
            "A": "theory Main",
            "B": "pin@A",
            "C": "pin@B",
        }
        result = expand_with_pin_dependents(origins, {"A"})
        self.assertEqual(result, {"A", "B", "C"})


class TestHasPersistentRepl(unittest.TestCase):
    """Unit tests for has_persistent_repl. No I/R REPL required."""

    def test_repl_changed(self):
        """ReplChanged classification -> True."""
        ri = fi("A")
        c = ReplChanged(qt("A"), None, 0, (0, 0), None, "")
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory Main", False)}
        markers = {"s.A": SteppedMarker("abc", 5, None)}
        self.assertTrue(has_persistent_repl(ri, c, active, markers, {}))

    def test_repl_cached_error(self):
        """ReplCachedError classification -> True."""
        ri = fi("A")
        c = ReplCachedError(qt("A"), [], 3, LineInfo(1, 1))
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory Main", False)}
        markers = {"s.A": SteppedMarker("abc", 5, None)}
        self.assertTrue(has_persistent_repl(ri, c, active, markers, {}))

    def test_no_repl_persistent_if_imports_match(self):
        """NoRepl with existing non-segment REPL + matching imports -> True."""
        ri = fi("A")
        c = NoRepl(qt("A"))
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory s.Main", False)}
        markers = {"s.A": SteppedMarker("abc", 5, None)}
        files = {qt("A"): mock_entry("A", "s", ["Main"], 1)}
        self.assertTrue(has_persistent_repl(ri, c, active, markers, files))

    def test_no_repl_not_persistent_if_imports_changed(self):
        """NoRepl with existing REPL but imports changed -> False."""
        ri = fi("A")
        c = NoRepl(qt("A"))
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory s.Main", False)}
        markers = {"s.A": SteppedMarker("abc", 5, None)}
        files = {qt("A"): mock_entry("A", "s", ["Main", "Extra"], 1)}
        self.assertFalse(has_persistent_repl(ri, c, active, markers, files))

    def test_no_repl_with_segment_repl(self):
        """NoRepl with segment REPL (SteppedMarker with segment_spec set) -> False."""
        ri = fi("A")
        c = NoRepl(qt("A"))
        active = {"ic.s.A": ReplInfo("ic.s.A", 5, 0, "theory Main", False)}
        markers = {"s.A": SteppedMarker("abc", 5, "s.A:3")}
        self.assertFalse(has_persistent_repl(ri, c, active, markers, {}))

    def test_no_repl_without_existing_repl(self):
        """NoRepl without existing REPL -> False."""
        ri = fi("A")
        c = NoRepl(qt("A"))
        active = {}
        markers = {}
        self.assertFalse(has_persistent_repl(ri, c, active, markers, {}))

    def test_in_heap(self):
        """InHeap classification -> False."""
        ri = fi("A")
        c = InHeap(qt("A"))
        active = {}
        markers = {}
        self.assertFalse(has_persistent_repl(ri, c, active, markers, {}))

    def test_heap_import(self):
        """HeapImport (not FileImport) -> False."""
        ri = HeapImport("Main")
        c = InHeap(qt("A"))  # classification doesn't matter
        active = {}
        markers = {}
        self.assertFalse(has_persistent_repl(ri, c, active, markers, {}))


class TestParseReplsOutputBusy(unittest.TestCase):
    """Unit tests for parse_repls_output busy line parsing."""

    def test_busy_line_parsed(self):
        """Busy lines populate BusyReplInfo with the new fields."""
        text = (
            "    ic.S.A (3 steps, from theory Main)\n"
            "    ic.S.B (4 steps, from theory Main+ic.S.A,"
            " busy [step] 0.4s)\n"
        )
        active, busy = parse_repls_output(text)
        self.assertEqual(len(active), 1)
        self.assertIn("ic.S.A", active)
        self.assertEqual(len(busy), 1)
        info = busy["ic.S.B"]
        self.assertEqual(info.name, "ic.S.B")
        self.assertEqual(info.origin, "theory Main+ic.S.A")
        self.assertEqual(info.step_count, 4)
        self.assertEqual(info.stale_count, 0)
        self.assertEqual(info.operation, "step")
        self.assertEqual(info.elapsed, "0.4s")

    def test_busy_non_ic_filtered(self):
        """Busy non-ic.* REPLs are filtered out."""
        text = (
            "    myrepl (1 steps, from theory Main, busy [step] 0.1s)\n"
            "    ic.S.X (1 steps, from theory Main, busy [step] 0.1s)\n"
        )
        active, busy = parse_repls_output(text)
        self.assertEqual(len(busy), 1)
        self.assertIn("ic.S.X", busy)
        self.assertNotIn("myrepl", busy)

    def test_mixed_active_and_busy(self):
        """Both normal and busy lines are parsed correctly."""
        text = (
            "  > ic.S.A (5 steps, from theory Main)\n"
            "    ic.S.B (2 steps, 1 stale, from theory Main+ic.S.A)\n"
            "    ic.S.C (7 steps, from theory pin@ic.S.A+pin@ic.S.B,"
            " busy [step] 1.5s)\n"
        )
        active, busy = parse_repls_output(text)
        self.assertEqual(len(active), 2)
        self.assertEqual(len(busy), 1)
        self.assertTrue(active["ic.S.A"].is_current)
        self.assertFalse(active["ic.S.B"].is_current)
        self.assertEqual(active["ic.S.B"].stale_count, 1)
        self.assertEqual(busy["ic.S.C"].origin,
                          "theory pin@ic.S.A+pin@ic.S.B")
        self.assertEqual(busy["ic.S.C"].step_count, 7)

    def test_busy_with_stale_count(self):
        """Optional ', N stale' clause is captured on busy lines."""
        text = ("    ic.S.A (5 steps, 2 stale, from theory Main,"
                " busy [replay] 1.2s)\n")
        active, busy = parse_repls_output(text)
        self.assertEqual(len(busy), 1)
        info = busy["ic.S.A"]
        self.assertEqual(info.step_count, 5)
        self.assertEqual(info.stale_count, 2)
        self.assertEqual(info.operation, "replay")
        self.assertEqual(info.elapsed, "1.2s")

    def test_busy_all_operations(self):
        """All five operation tags from ir.ML are recognized."""
        ops = ["step", "edit", "replay", "rebase", "merge"]
        lines = [f"    ic.S.{op} (1 steps, from theory Main,"
                 f" busy [{op}] 0.0s)\n"
                 for op in ops]
        active, busy = parse_repls_output("".join(lines))
        self.assertEqual(len(busy), len(ops))
        for op in ops:
            self.assertEqual(busy[f"ic.S.{op}"].operation, op)

    def test_live_origin_does_not_capture_pinned(self):
        """', pinned' / ', pinned [stale]' are excluded from origin."""
        text = (
            "    ic.S.A (5 steps, from theory Main, pinned)\n"
            "    ic.S.B (5 steps, from theory Main, pinned [stale])\n"
        )
        active, _busy = parse_repls_output(text)
        self.assertEqual(active["ic.S.A"].origin, "theory Main")
        self.assertEqual(active["ic.S.B"].origin, "theory Main")


if __name__ == "__main__":
    unittest.main()
