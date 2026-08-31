"""Heap-free Isabelle command-span and proof-depth approximation.

The lexer recognizes enough of Isabelle's outer syntax to keep command
keywords inside comments, strings, and cartouches out of the command stream.
Command classifications come from ``keywords`` declarations in theory headers.
"""

import bisect
import os


THY_GOALS = {"thy_goal", "thy_goal_defn", "thy_goal_stmt"}
PRF_GOALS = {
    "prf_goal", "prf_asm_goal", "prf_script_goal",
    "prf_script_asm_goal",
}
TERMINAL_QEDS = {"qed", "qed_script"}
NON_COMMAND_KINDS = {"", "before_command", "quasi_command"}


# This is sufficient for useful output even when no Isabelle installation or
# project source tree can be found. Scanning theory headers extends it with all
# package and project-specific commands.
CORE_KEYWORD_KINDS = {
    "theory": "thy_begin",
    "chapter": "document_heading",
    "section": "document_heading",
    "subsection": "document_heading",
    "subsubsection": "document_heading",
    "paragraph": "document_heading",
    "subparagraph": "document_heading",
    "text": "document_body",
    "txt": "document_body",
    "text_raw": "document_raw",
    "ML": "thy_decl",
    "end": "thy_end",
    "theorem": "thy_goal_stmt",
    "lemma": "thy_goal_stmt",
    "corollary": "thy_goal_stmt",
    "proposition": "thy_goal_stmt",
    "schematic_goal": "thy_goal_stmt",
    "interpretation": "thy_goal",
    "global_interpretation": "thy_goal",
    "sublocale": "thy_goal",
    "subclass": "thy_goal",
    "instance": "thy_goal",
    "interpret": "prf_goal",
    "have": "prf_goal",
    "hence": "prf_goal",
    "show": "prf_asm_goal",
    "thus": "prf_asm_goal",
    "consider": "prf_goal",
    "obtain": "prf_asm_goal",
    "subgoal": "prf_script_goal",
    "proof": "prf_block",
    "{": "prf_open",
    "}": "prf_close",
    "next": "next_block",
    "qed": "qed_block",
    "by": "qed",
    "..": "qed",
    ".": "qed",
    "sorry": "qed",
    "\\<proof>": "qed",
    "done": "qed_script",
    "oops": "qed_global",
    "notepad": "thy_decl_block",
}


def _skip_quoted(source, start, quote):
    index = start + 1
    while index < len(source):
        if source[index] == "\\":
            if source.startswith("\\<", index):
                end = source.find(">", index + 2)
                index = len(source) if end < 0 else end + 1
            else:
                index += 2
        elif source[index] == quote:
            return index + 1
        else:
            index += 1
    return len(source)


def _skip_comment(source, start):
    index = start + 2
    depth = 1
    while index < len(source) and depth:
        if source.startswith("(*", index):
            depth += 1
            index += 2
        elif source.startswith("*)", index):
            depth -= 1
            index += 2
        else:
            index += 1
    return index


def _skip_verbatim(source, start):
    end = source.find("*}", start + 2)
    return len(source) if end < 0 else end + 2


def _cartouche_delimiter(source, index):
    if source.startswith("\\<open>", index):
        return "open", 7
    if source.startswith("\\<close>", index):
        return "close", 8
    if source[index:index + 1] == "\u2039":
        return "open", 1
    if source[index:index + 1] == "\u203a":
        return "close", 1
    return None, 0


def _skip_cartouche(source, start):
    index = start
    depth = 0
    while index < len(source):
        delimiter, width = _cartouche_delimiter(source, index)
        if delimiter == "open":
            depth += 1
            index += width
        elif delimiter == "close":
            depth -= 1
            index += width
            if depth == 0:
                return index
        else:
            index += 1
    return len(source)


def _string_value(raw):
    """Decode quote escapes while preserving Isabelle ``\\<symbol>`` forms."""
    value = []
    index = 1
    stop = max(1, len(raw) - 1)
    while index < stop:
        if raw[index] == "\\" and not raw.startswith("\\<", index):
            index += 1
            if index >= stop:
                break
        value.append(raw[index])
        index += 1
    return "".join(value)


def _scan_name_end(source, start):
    end = start + 1
    while end < len(source):
        if source[end].isalnum() or source[end] in "_'":
            end += 1
        elif (source[end] == "." and end + 1 < len(source) and
              (source[end + 1].isalnum() or source[end + 1] in "_'" or
               source.startswith("\\<", end + 1))):
            end += 1
        elif (source.startswith("\\<", end) and
              not source.startswith(("\\<open>", "\\<close>"), end)):
            close = source.find(">", end + 2)
            if close < 0:
                break
            end = close + 1
        else:
            break
    return end


def lex_outer_tokens(source, stop_at_begin=False):
    """Return outer-syntax atoms outside comments and text literals.

    Tokens are dictionaries with ``text``, ``kind``, ``start``, and ``end``.
    Quoted strings are retained as ``kind == "string"`` for parsing theory
    header keyword declarations, but are never considered command keywords.
    """
    tokens = []
    index = 0
    length = len(source)
    while index < length:
        char = source[index]
        if char.isspace():
            index += 1
        elif source.startswith("(*", index):
            index = _skip_comment(source, index)
        elif source.startswith("{*", index):
            index = _skip_verbatim(source, index)
        elif char == '"':
            end = _skip_quoted(source, index, '"')
            raw = source[index:end]
            tokens.append({
                "text": _string_value(raw), "kind": "string",
                "start": index, "end": end,
            })
            index = end
        elif char == "`":
            index = _skip_quoted(source, index, "`")
        else:
            delimiter, _ = _cartouche_delimiter(source, index)
            if delimiter == "open":
                index = _skip_cartouche(source, index)
                continue
            if source.startswith("\\<", index):
                end = source.find(">", index + 2)
                end = length if end < 0 else end + 1
                tokens.append({
                    "text": source[index:end], "kind": "atom",
                    "start": index, "end": end,
                })
                index = end
            elif (char.isalnum() or char in "_'" or
                  (char in "?$" and index + 1 < length and
                   (source[index + 1].isalnum() or
                    source[index + 1] in "_'"))):
                end = _scan_name_end(source, index)
                text = source[index:end]
                tokens.append({
                    "text": text, "kind": "atom",
                    "start": index, "end": end,
                })
                index = end
                if stop_at_begin and text == "begin":
                    break
            else:
                end = index + 1
                while end < length:
                    if source[end].isspace():
                        break
                    if source.startswith(("(*", "{*", "\\<"), end):
                        break
                    delimiter, _ = _cartouche_delimiter(source, end)
                    if delimiter:
                        break
                    if source[end].isalnum() or source[end] in "_'\"`":
                        break
                    end += 1
                tokens.append({
                    "text": source[index:end], "kind": "atom",
                    "start": index, "end": end,
                })
                index = end
    return tokens


def parse_keyword_declarations(source):
    """Extract ``command -> kind`` entries from a theory header."""
    tokens = lex_outer_tokens(source, stop_at_begin=True)
    declarations = {}
    in_keywords = False
    names = []
    category = None
    expect_category = False

    def finish_group():
        if category:
            for name in names:
                declarations[name] = category

    for token in tokens:
        text = token["text"]
        if not in_keywords:
            if token["kind"] == "atom" and text == "keywords":
                in_keywords = True
            elif token["kind"] == "atom" and text == "begin":
                break
            continue

        if token["kind"] == "atom" and text in ("begin", "abbrevs"):
            finish_group()
            break
        if token["kind"] == "atom" and text == "and":
            finish_group()
            names = []
            category = None
            expect_category = False
        elif token["kind"] == "atom" and text == "::":
            expect_category = True
        elif expect_category:
            category = text
            expect_category = False
        elif category is None and token["kind"] == "string":
            names.append(text)

    return declarations


def collect_keyword_kinds(roots):
    """Collect command classifications from ``.thy`` headers below roots."""
    kinds = dict(CORE_KEYWORD_KINDS)
    seen = set()
    for root in roots:
        if not root:
            continue
        root = os.path.realpath(root)
        if root in seen or not os.path.isdir(root):
            continue
        seen.add(root)
        for directory, subdirs, files in os.walk(root):
            subdirs[:] = [
                name for name in subdirs
                if not name.startswith(".") and name not in ("heaps", "log")
            ]
            for name in files:
                if not name.endswith(".thy"):
                    continue
                path = os.path.join(directory, name)
                try:
                    with open(path, "r", errors="replace") as stream:
                        header = stream.read(64 * 1024)
                except OSError:
                    continue
                for command, kind in parse_keyword_declarations(header).items():
                    kinds.setdefault(command, kind)
    return kinds


def _symbol_char_positions(text):
    positions = [0]
    index = 0
    while index < len(text):
        if text.startswith("\\<", index):
            end = text.find(">", index + 2)
            index = index + 1 if end < 0 else end + 1
        else:
            index += 1
        positions.append(index)
    return positions


def _symbol_offset(positions, char_index):
    return bisect.bisect_left(positions, char_index) + 1


def _close_goal(stack):
    if not stack:
        return
    if stack[-1]["kind"] != "goal":
        stack.pop()
        return
    goal = stack.pop()
    for _ in range(goal.get("cleanup", 0)):
        if stack:
            stack.pop()


def _is_theory_mode_kind(category):
    return (
        category is not None and
        (category.startswith("thy_") or
         category.startswith("document_") or category == "diag")
    )


def _apply_depth_transition(stack, name, category, next_category=None):
    if name == "notepad":
        stack.extend(({"kind": "notepad"}, {"kind": "block"}))
    elif name == "subgoal":
        stack.extend((
            {"kind": "subgoal_block"}, {"kind": "subgoal_block"},
            {"kind": "goal", "cleanup": 2},
        ))
    elif category in THY_GOALS:
        # Some package commands are conservatively declared thy_goal for PIDE
        # scheduling but prove their result internally and return to theory
        # mode. A following theory command demonstrates that behavior.
        if stack or not _is_theory_mode_kind(next_category):
            stack.append({"kind": "goal"})
    elif category in PRF_GOALS:
        stack.append({"kind": "goal"})
    elif category == "prf_block":
        stack.append({"kind": "proof"})
    elif category == "prf_open":
        stack.extend(({"kind": "block"}, {"kind": "block"}))
    elif category == "prf_close":
        if stack:
            stack.pop()
        if stack:
            stack.pop()
    elif category == "qed_block":
        if stack and stack[-1]["kind"] == "proof":
            stack.pop()
        _close_goal(stack)
    elif category in TERMINAL_QEDS:
        _close_goal(stack)
    elif category == "qed_global":
        stack.clear()
    elif category == "thy_end" and stack:
        # The only ordinary theory-end command in a proof state closes notepad.
        stack.clear()


def infer_commands(source, keyword_kinds, timed_commands=()):
    """Parse command spans and annotate keyword-derived pre/post depths.

    ``timed_commands`` is an iterable of ``(offset, name)`` pairs. Timed
    commands missing from the available keyword registry are merged into the
    stream so that timing data is never silently dropped.
    """
    positions = _symbol_char_positions(source)
    by_offset = {}
    theory = None
    tokens = lex_outer_tokens(source)

    for index, token in enumerate(tokens):
        if token["kind"] != "atom":
            continue
        name = token["text"]
        category = keyword_kinds.get(name)
        if category is None or category in NON_COMMAND_KINDS:
            continue
        offset = _symbol_offset(positions, token["start"])
        by_offset[offset] = {
            "offset": offset,
            "name": name,
            "category": category,
            "source_start": token["start"],
        }
        if name == "theory" and theory is None:
            for following in tokens[index + 1:]:
                if following["kind"] in ("atom", "string"):
                    theory = following["text"]
                    break

    for offset, name in timed_commands:
        existing = by_offset.get(offset)
        if existing is not None:
            # Timing names are symbol-decoded, while local source and keyword
            # declarations may use encoded symbols such as apply\<tau>. Keep
            # the parsed category but use the DB name for timing-key lookup.
            existing["name"] = name
        else:
            by_offset[offset] = {
                "offset": offset,
                "name": name,
                "category": keyword_kinds.get(name),
                "source_start": positions[
                    min(max(offset - 1, 0), len(positions) - 1)],
            }

    commands = sorted(by_offset.values(), key=lambda command: command["offset"])
    for index, command in enumerate(commands):
        command["source_stop"] = (
            commands[index + 1]["source_start"]
            if index + 1 < len(commands) else len(source))

    stack = []
    for index, command in enumerate(commands):
        command["pre_depth"] = len(stack)
        next_category = (
            commands[index + 1].get("category")
            if index + 1 < len(commands) else None)
        _apply_depth_transition(
            stack, command["name"], command.get("category"), next_category)
        command["post_depth"] = len(stack)
    return theory, commands
