#!/usr/bin/env python3
"""audit.py — the claim audit: one status per paper row of Robinson/Paper/Statements.lean, from Lean's own output.
Version 0.40, 2026-11-04: AUDIT.md and CLAIMS.json are written at the project root (the published layout).
Version 0.30, 2026-11-04: no time stamp in AUDIT.md and CLAIMS.json: a rerun on the same build rewrites every output
  byte for byte, so a Git checkout stays clean. A reader runs `LEAN_RUN_LOCK=none LEAN_RUN_GATE=none scripts/audit.py`.
Version 0.20, 2026-11-04: the whole audit (read sources, freshness, Lean, reports) runs while holding the compile lock.
Version 0.10, 2026-11-04: first; adapted from an earlier project's claim audit (facts and checks are explicit binders).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Usage:  scripts/audit.py           the audit: `scripts/lean_run.sh lake env python3 scripts/audit.py --locked`, so the
                                   sources are read and one `lean` run of a generated file is made while the shared
                                   compile lock is held (no build can change the .olean files in between)
        scripts/audit.py --test    self-test (no Lean)
        (--locked is that inner step; it refuses to run unless started that way)
Needs built .olean files for Robinson.Paper.Statements and its imports (scripts/check.sh builds them first);
refuses to run on stale ones. The generated file only reads the environment: no row is changed, nothing assumed.

Status of a row (from `#print axioms` and the elaborated type; the source text never decides a status):
  FAIL: <reason>       an axiom other than propext, Classical.choice, Quot.sound and sorryAx; or a fact/check that
                       occurs in the type other than as the exact type of a binder; or a binder whose type is a named
                       proposition that is not a registered fact (Robinson/NotFormalized.lean) or check
                       (Robinson/ComputerChecked.lean)
  not proved yet       the axioms include sorryAx (its own body, or a row it uses, is unfinished)
  PROVED GIVEN <list>  no sorryAx; the row takes these facts/checks as explicit binders
  PROVED               no sorryAx and no fact/check binder
Outputs: AUDIT.md and CLAIMS.json at the project root; audit_axioms.lean (generated) and audit_output.log in scripts/.
Exit 1 if any FAIL.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

SCRIPTS = Path(__file__).resolve().parent
PROJECT = SCRIPTS.parent
LIB = "Robinson"
NAMESPACE = LIB + ".Paper"
ROOT_MODULE = NAMESPACE + ".Statements"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
SORRY_AXIOM = "sorry" + "Ax"   # spelled in two parts so the token scan of check.sh does not flag this file
NOT_PROVED = "not proved yet"
STATEMENTS = PROJECT / LIB / "Paper/Statements.lean"
FACTS_FILE = PROJECT / LIB / "NotFormalized.lean"
CHECKS_FILE = PROJECT / LIB / "ComputerChecked.lean"
FACT_MARKERS = ("NOT FORMALIZED",)
CHECK_MARKERS = ("COMPUTER-CHECKED", "NOT proved in Lean")
HELPER = SCRIPTS / "audit_checks.lean.inc"
RUNNER = SCRIPTS / "lean_run.sh"
GENERATED = SCRIPTS / "audit_axioms.lean"
LOG = SCRIPTS / "audit_output.log"
REPORT = PROJECT / "AUDIT.md"
CLAIMS = PROJECT / "CLAIMS.json"
OLEAN_ROOT = Path(".lake/build/lib/lean")   # relative to the project; read only (modification times)
VERSION = "0.40"
LOCK_MARK = "CLAIM_AUDIT_UNDER_LOCK"   # set by main_audit for the inner step


def fail(message):
    raise SystemExit("AUDIT FAILED: " + message)


def mask_comments(text):
    """Preserve offsets/newlines while removing nested Lean comments and strings."""
    chars = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                chars[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                chars[i:i+2] = "  "; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                if text[i] == '"': string = False
                i += 1
        elif text.startswith("/-", i):
            chars[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            chars[i:end] = " " * (end-i); i = end
        elif text[i] == '"':
            chars[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string:
        fail("unterminated comment/string")
    return "".join(chars)


def doc_before(text, offset):
    match = re.search(r"/--((?:(?!-/).)*)-/\s*\Z", text[:offset], re.S)
    return " ".join(match.group(1).split()) if match else ""


def parse_statements(text):
    """Plain, line-start theorem declarations, as the Statements contract requires."""
    clean = mask_comments(text)
    heads = list(re.finditer(r"^theorem\s+([A-Za-z_][\w']*)(?=\s)", clean, re.M))
    if len(heads) != len(re.findall(r"\btheorem\b", clean)):
        fail("unsupported theorem syntax; use plain line-start theorem declarations")
    if re.search(r"\b(?:lemma|example|axiom|opaque|def|abbrev|constant|instance)\b", clean):
        fail("Statements may contain only theorem rows, imports, namespaces and comments")
    items = []
    for head in heads:
        if ":=" not in clean[head.end():].split("\ntheorem", 1)[0]:
            fail("missing := for " + head.group(1))
        items.append({"name": head.group(1), "doc": doc_before(text, head.start()),
                      "line": text[:head.start()].count("\n") + 1})
    names = [item["name"] for item in items]
    if not names or len(names) != len(set(names)):
        fail("empty or duplicate theorem inventory")
    return items


def parse_registry(text, prefix, markers):
    """The `def <prefix>… : Prop` of a registry file (facts or checks), each with its docstring markers."""
    clean = mask_comments(text)
    items = []
    for match in re.finditer(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w']*)(.*?):=", clean, re.S | re.M):
        name, signature = match.group(1), match.group(2)
        doc = doc_before(text, match.start())
        if name.startswith(prefix) or markers[0] in doc:
            if not name.startswith(prefix) or not re.fullmatch(r"\s*:\s*Prop\s*", signature):
                fail(f"must be `def {prefix}… : Prop` (no parameters): {name}")
            missing = [marker for marker in markers if marker not in doc]
            if missing:
                fail(f"{name}: docstring lacks {missing}")
            items.append({"name": LIB + "." + name, "doc": doc})
    names = [item["name"] for item in items]
    if not names or len(names) != len(set(names)):
        fail(f"empty or duplicate {prefix} registry")
    return items


def module_path(module, suffix):
    return Path(*module.split(".")).with_suffix(suffix)


def import_closure(project, root_module):
    """The project modules imported (transitively) by root_module, root included."""
    closure, pending = set(), [root_module]
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        closure.add(module)
        source = project / module_path(module, ".lean")
        if not source.is_file():
            fail("missing source of module " + module)
        pending += direct_imports(project, module)
    return closure


def direct_imports(project, module):
    clean = mask_comments((project / module_path(module, ".lean")).read_text(encoding="utf-8"))
    return re.findall(r"^import\s+(" + LIB + r"(?:\.[\w']+)*)\s*$", clean, re.M)


def stale_modules(project, root_module):
    """Modules of the closure whose .olean is missing, older than its source, or older than the .olean of a
    project module it imports (then Lake would rebuild it; an approximation of Lake's own rule by file times)."""
    stale = []
    for module in sorted(import_closure(project, root_module)):
        source = project / module_path(module, ".lean")
        olean = project / OLEAN_ROOT / module_path(module, ".olean")
        imported = [project / OLEAN_ROOT / module_path(dep, ".olean") for dep in direct_imports(project, module)]
        if not olean.is_file() or olean.stat().st_mtime < source.stat().st_mtime or \
           any(dep.is_file() and olean.stat().st_mtime < dep.stat().st_mtime for dep in imported):
            stale.append(module)
    return stale


def olean_times(project, root_module):
    """Modification times of the closure's .olean files (None if missing)."""
    times = {}
    for module in import_closure(project, root_module):
        olean = project / OLEAN_ROOT / module_path(module, ".olean")
        times[module] = olean.stat().st_mtime_ns if olean.is_file() else None
    return times


def audit_lean(names, registered, helper):
    lines = ["-- Generated by scripts/audit.py; do not edit.", "import " + ROOT_MODULE, "import Lean",
             "set_option maxHeartbeats 0", helper]
    lines += [f"run_cmd RobinsonAudit.inspectRegistered ``{name}" for name in registered]
    for name in names:
        lines += [f"#print axioms {NAMESPACE}.{name}",
                  f'run_cmd RobinsonAudit.inspect ``{NAMESPACE}.{name} "{name}"']
    return "\n".join(lines) + "\n"


def parse_axioms(output, names):
    result = {}
    pattern = r"'([\w.']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, output, re.S):
        if not match.group(1).startswith(NAMESPACE + "."):
            continue
        name = match.group(1).removeprefix(NAMESPACE + ".")
        if name in result:
            fail("duplicate axiom output for " + name)
        result[name] = {a.strip() for a in (match.group(2) or "").split(",") if a.strip()}
    if set(names) != set(result):
        fail("missing/unexpected axiom rows: " + str(set(names) ^ set(result)))
    return result


def csv_names(field):
    return [name for name in field.split(",") if name]


def parse_rows(output, names):
    result = {}
    for match in re.finditer(r"RBROW\|([^|\n]+)\|([^|\n]*)\|([^|\n]*)\|([^|\n]*)\|([^|\n]*)\|END", output):
        name, tags, binders, uses, kind = match.groups()
        if name in result:
            fail("duplicate row inspection for " + name)
        if kind != "theorem":
            fail(f"row {name} is not a theorem ({kind})")
        result[name] = {"tags": set(csv_names(tags)), "binders": list(dict.fromkeys(csv_names(binders))),
                        "uses": {used.removeprefix(NAMESPACE + ".") for used in csv_names(uses)}}
    if set(result) != set(names):
        fail("missing/unexpected row inspections: " + str(set(names) ^ set(result)))
    return result


def check_registered(output, registered):
    found = {}
    for match in re.finditer(r"RBREG\|([^|\n]+)\|([^|\n]*)\|([^|\n]*)\|END", output):
        found[match.group(1)] = (match.group(2), match.group(3))
    for name in registered:
        if found.get(name) != ("def", "true"):
            fail(f"{name} must be a definition of type Prop in Lean; got {found.get(name)}")


def short(name):
    return name.removeprefix(LIB + ".")


def classify(axioms, tags, binders, registry):
    extra = axioms - STANDARD - {SORRY_AXIOM}
    if extra:
        return "FAIL: axiom " + ", ".join(sorted(extra))
    unregistered = (tags | set(binders)) - registry
    if unregistered:
        return "FAIL: not a registered fact or check: " + ", ".join(sorted(map(short, unregistered)))
    loose = tags - set(binders)
    if loose:
        return "FAIL: fact/check not taken as an exact binder: " + ", ".join(sorted(map(short, loose)))
    if SORRY_AXIOM in axioms:
        return NOT_PROVED
    if binders:
        return "PROVED GIVEN " + ", ".join(map(short, binders))
    return "PROVED"


def category(status):
    for word in ("FAIL", "PROVED GIVEN", NOT_PROVED):
        if status.startswith(word):
            return word
    return status


def waiting_on(rows):
    """For each unproved row, the rows it uses directly that are unproved too (none: its own body is open)."""
    unproved = {row["name"] for row in rows if row["status"] == NOT_PROVED}
    for row in rows:
        uses = row.pop("uses")
        row["waits_on"] = sorted(uses & unproved) if row["name"] in unproved else []


def cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def axiom_list(axioms):
    return ", ".join(sorted(axioms, key=lambda name: (name not in STANDARD, name.lower()))) or "none"


def render(rows, facts, checks):
    counts = {key: 0 for key in ("PROVED", "PROVED GIVEN", NOT_PROVED, "FAIL")}
    for row in rows:
        counts[category(row["status"])] += 1
    totals = f"rows {len(rows)}; " + "; ".join(f"{key} {value}" for key, value in counts.items())
    table = ["| # | Row | Status | Fact/Check binders | Axioms | Unproved rows it uses |", "|---|---|---|---|---|---|"]
    for i, row in enumerate(rows, 1):
        waits = ", ".join(row["waits_on"]) or ("(its own body)" if row["status"] == NOT_PROVED else "—")
        table.append(f'| {i} | `{cell(row["name"])}` | {cell(row["status"])} | {cell(", ".join(map(short, row["binders"])) or "—")} | '
                     f'{cell(axiom_list(row["axioms"]))} | {cell(waits)} |')
    registry = ["", "## Published facts (not formalized) and computer checks (checked by computer, NOT proved in Lean)", "",
                "Each is an ordinary `def … : Prop`, never an axiom; a row that uses one takes it as a binder.", "",
                "| Name | Kind | Rows taking it as a binder |", "|---|---|---|"]
    for item, kind in [(fact, "fact") for fact in facts] + [(check, "check") for check in checks]:
        users = sum(item["name"] in row["binders"] for row in rows)
        registry.append(f'| `{short(item["name"])}` | {kind} | {users} |')
    text = (f"# Claim audit of {NAMESPACE}\nVersion {VERSION}. Generated by scripts/audit.py from Lean output.\n\n"
            f"Totals: {totals}.\n\n"
            "Status comes from `#print axioms` and the elaborated type, never from the source text. "
            "The audit does not judge whether a row says what the paper says.\n\n" + "\n".join(table + registry) + "\n")
    return text, counts


def run_lean(content):
    """Inner step only: the lock and the priority gate are already held (see main)."""
    if not GENERATED.exists() or GENERATED.read_text() != content:
        GENERATED.write_text(content)
    command = ["lean", str(GENERATED.relative_to(PROJECT))]
    proc = subprocess.run(command, cwd=PROJECT, capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    LOG.write_text(output)
    if proc.returncode:
        fail(f"Lean failed (exit {proc.returncode}); see scripts/audit_output.log\n" + output[-4000:])
    return output


def main_audit_locked():
    """The audit proper; started by main_audit under the lock, the gate and `lake env`."""
    if os.environ.get(LOCK_MARK) != "1":
        fail("--locked is the inner step of scripts/audit.py; run scripts/audit.py")
    stale = stale_modules(PROJECT, ROOT_MODULE)
    if stale:
        fail("stale or missing .olean for: " + ", ".join(stale) +
             "\n  build first: scripts/lean_run.sh lake build " + ROOT_MODULE)
    built = olean_times(PROJECT, ROOT_MODULE)
    items = parse_statements(STATEMENTS.read_text(encoding="utf-8"))
    facts = parse_registry(FACTS_FILE.read_text(encoding="utf-8"), "Fact", FACT_MARKERS)
    checks = parse_registry(CHECKS_FILE.read_text(encoding="utf-8"), "Check", CHECK_MARKERS)
    registry = {item["name"] for item in facts + checks}
    names = [item["name"] for item in items]
    output = run_lean(audit_lean(names, sorted(registry), HELPER.read_text(encoding="utf-8")))
    # Under the lock nothing should rebuild; this catches a build that does not take the lock.
    if olean_times(PROJECT, ROOT_MODULE) != built:
        fail("an .olean of the audited modules was rebuilt during the audit (a build without the lock?); run it again")
    check_registered(output, registry)
    axioms = parse_axioms(output, names)
    inspected = parse_rows(output, names)
    rows = [dict(item, axioms=sorted(axioms[item["name"]]), binders=inspected[item["name"]]["binders"],
                 uses=inspected[item["name"]]["uses"],
                 status=classify(axioms[item["name"]], inspected[item["name"]]["tags"],
                                 inspected[item["name"]]["binders"], registry))
            for item in items]
    waiting_on(rows)
    report, counts = render(rows, facts, checks)
    REPORT.write_text(report)
    CLAIMS.write_text(json.dumps({"version": VERSION, "namespace": NAMESPACE, "counts": counts,
                                  "rows": rows, "facts": facts, "checks": checks}, indent=2, ensure_ascii=False) + "\n")
    print(f"AUDIT: rows {len(rows)}, " + ", ".join(f"{key} {value}" for key, value in counts.items()))
    for row in rows:
        if row["status"].startswith("FAIL"):
            print(f'  {row["name"]}: {row["status"]}')
    if counts["FAIL"]:
        raise SystemExit(1)


def expect_failure(function, *args):
    try:
        function(*args)
    except SystemExit:
        return
    raise AssertionError(f"{function.__name__} accepted bad input {args!r}")


def test_parsers():
    sample = ("/-- Formula | bound. -/\ntheorem foo' : True := by trivial\nopen Classical in\n"
              "/-- uses a fact. -/\ntheorem bar (h : FactA) : True :=\n  trivial\nend Robinson.Paper\n")
    rows = parse_statements(sample)
    assert [row["name"] for row in rows] == ["foo'", "bar"] and rows[1]["doc"] == "uses a fact." and rows[1]["line"] == 5
    for bad in ['theorem foo : True := by trivial\n theorem hidden : True := by trivial',
                'lemma hidden : True := by trivial', 'def helper : Nat := 1\ntheorem foo : True := trivial', '']:
        expect_failure(parse_statements, bad)
    facts = parse_registry('/-- NOT FORMALIZED: x. -/\ndef FactA : Prop := True\n/-- helper -/\ndef aux : Nat := 1\n',
                           "Fact", FACT_MARKERS)
    assert [fact["name"] for fact in facts] == ["Robinson.FactA"]
    checks = parse_registry('/-- COMPUTER-CHECKED: p. NOT proved in Lean. -/\ndef Check_1 : Prop := True\n',
                            "Check", CHECK_MARKERS)
    assert checks[0]["name"] == "Robinson.Check_1"
    for bad in ['/-- NOT FORMALIZED. -/\ndef FactA (n : Nat) : Prop := True\n', 'def FactA : Prop := True\n',
                '/-- NOT FORMALIZED. -/\ndef Other : Prop := True\n', '/-- helper -/\ndef aux : Nat := 1\n']:
        expect_failure(parse_registry, bad, "Fact", FACT_MARKERS)
    expect_failure(parse_registry, '/-- COMPUTER-CHECKED. -/\ndef Check_1 : Prop := True\n', "Check", CHECK_MARKERS)
    assert "theorem" not in mask_comments('/- outer /- theorem -/ more -/ "theorem"')


def test_lean_output_parsers():
    names = ["foo'", "bar"]
    out = ("'Robinson.Paper.foo'' depends on axioms: [propext,\n Classical.choice]\n"
           "'Robinson.Paper.bar' does not depend on any axioms\n'Robinson.Other' depends on axioms: [x]\n"
           "RBROW|foo'|||Robinson.Paper.bar|theorem|END\nRBROW|bar|Robinson.FactA|Robinson.FactA,Robinson.FactA||theorem|END\n"
           "RBREG|Robinson.FactA|def|true|END\n")
    axioms = parse_axioms(out, names)
    assert axioms == {"foo'": {"propext", "Classical.choice"}, "bar": set()}
    rows = parse_rows(out, names)
    assert rows["bar"] == {"tags": {"Robinson.FactA"}, "binders": ["Robinson.FactA"], "uses": set()}
    assert rows["foo'"]["uses"] == {"bar"}
    check_registered(out, {"Robinson.FactA"})
    expect_failure(check_registered, out.replace("|def|", "|axiom|"), {"Robinson.FactA"})
    expect_failure(parse_axioms, out, names + ["gone"])
    expect_failure(parse_rows, out.replace("|theorem|END\nRBROW|bar", "|other|END\nRBROW|bar"), names)
    generated = audit_lean(names, ["Robinson.FactA"], "-- helper")
    assert "#print axioms Robinson.Paper.foo'" in generated and 'inspect ``Robinson.Paper.bar "bar"' in generated
    assert generated.splitlines()[1] == "import Robinson.Paper.Statements"


def test_classify():
    registry = {"Robinson.FactA", "Robinson.Check_1"}
    std = {"propext", "Classical.choice", "Quot.sound"}
    assert classify(std, set(), [], registry) == "PROVED"
    assert classify(set(), set(), [], registry) == "PROVED"
    given = classify(std, {"Robinson.FactA", "Robinson.Check_1"}, ["Robinson.Check_1", "Robinson.FactA"], registry)
    assert given == "PROVED GIVEN Check_1, FactA"
    assert classify(std | {SORRY_AXIOM}, {"Robinson.FactA"}, ["Robinson.FactA"], registry) == NOT_PROVED
    assert classify(std | {"evil"}, set(), [], registry).startswith("FAIL: axiom evil")
    assert classify({"evil", SORRY_AXIOM}, set(), [], registry).startswith("FAIL")       # FAIL beats sorry
    assert classify(std, {"Robinson.FactA"}, [], registry).startswith("FAIL: fact/check not taken")  # in the conclusion
    assert classify(std, set(), ["Robinson.SomeProp"], registry).startswith("FAIL: not a registered")
    assert classify(std, {"Robinson.FactZ"}, ["Robinson.FactZ"], registry).startswith("FAIL: not a registered")
    assert classify({SORRY_AXIOM}, set(), ["True"], registry).startswith("FAIL")          # named hypothesis


def test_render_and_waiting():
    rows = [{"name": "a", "status": NOT_PROVED, "uses": {"b"}, "binders": [], "axioms": [SORRY_AXIOM]},
            {"name": "b", "status": NOT_PROVED, "uses": set(), "binders": ["Robinson.FactA"], "axioms": [SORRY_AXIOM]},
            {"name": "c|d", "status": "PROVED GIVEN FactA", "uses": {"b"}, "binders": ["Robinson.FactA"],
             "axioms": ["propext"]},
            {"name": "e", "status": "FAIL: axiom evil", "uses": set(), "binders": [], "axioms": ["evil"]}]
    waiting_on(rows)
    assert rows[0]["waits_on"] == ["b"] and rows[1]["waits_on"] == [] and rows[2]["waits_on"] == []
    json.dumps(rows)                                               # every row can be written to CLAIMS.json
    report, counts = render(rows, [{"name": "Robinson.FactA", "doc": ""}], [])
    assert counts == {"PROVED": 0, "PROVED GIVEN": 1, NOT_PROVED: 2, "FAIL": 1}
    assert "Totals: rows 4; PROVED 0; PROVED GIVEN 1; not proved yet 2; FAIL 1." in report
    assert report.splitlines()[1] == f"Version {VERSION}. Generated by scripts/audit.py from Lean output."  # no stamp
    assert "`c\\|d`" in report and "(its own body)" in report
    assert "| `FactA` | fact | 2 |" in report


def test_freshness():
    with tempfile.TemporaryDirectory(dir=SCRIPTS, prefix=".audit-test.") as name:
        root = Path(name)
        (root / LIB / "Paper").mkdir(parents=True)
        (root / LIB / "Defs.lean").write_text("theorem x : True := trivial\n")
        (root / LIB / "Paper/Statements.lean").write_text(f"import {LIB}.Defs\nimport Mathlib\n-- import {LIB}.Gone\n")
        assert import_closure(root, ROOT_MODULE) == {ROOT_MODULE, LIB + ".Defs"}
        assert stale_modules(root, ROOT_MODULE) == [LIB + ".Defs", ROOT_MODULE]          # no oleans yet
        for module in (LIB + ".Defs", ROOT_MODULE):
            olean = root / OLEAN_ROOT / module_path(module, ".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            olean.write_text("olean")
        assert stale_modules(root, ROOT_MODULE) == []
        before = olean_times(root, ROOT_MODULE)
        rebuilt = root / OLEAN_ROOT / module_path(ROOT_MODULE, ".olean")
        os.utime(rebuilt, ns=(before[ROOT_MODULE] + 10**9, before[ROOT_MODULE] + 10**9))
        assert olean_times(root, ROOT_MODULE) != before
        dependency = root / OLEAN_ROOT / module_path(LIB + ".Defs", ".olean")
        os.utime(dependency, ns=(before[ROOT_MODULE] + 2 * 10**9, before[ROOT_MODULE] + 2 * 10**9))
        assert stale_modules(root, ROOT_MODULE) == [ROOT_MODULE]  # an import's .olean is newer than its own
        source = root / LIB / "Defs.lean"
        later = time.time() + 60
        os.utime(source, (later, later))
        assert stale_modules(root, ROOT_MODULE) == [LIB + ".Defs", ROOT_MODULE]          # a source newer than its .olean


def test_inner_step_refuses_without_lock():
    saved = os.environ.pop(LOCK_MARK, None)
    try:
        expect_failure(main_audit_locked)
    finally:
        if saved is not None:
            os.environ[LOCK_MARK] = saved


def main_test():
    test_inner_step_refuses_without_lock()
    test_parsers()
    test_lean_output_parsers()
    test_classify()
    test_render_and_waiting()
    test_freshness()
    print("PASS: audit parsers, registry contracts, statuses (FAIL / not proved yet / PROVED GIVEN / PROVED), "
          "olean freshness, report cells and totals")


def main_audit():
    """Hold the compile lock for the whole audit: the inner step reads the sources and runs Lean in one window."""
    command = [str(RUNNER), "lake", "env", "python3", str(Path(__file__).resolve().relative_to(PROJECT)), "--locked"]
    proc = subprocess.run(command, cwd=PROJECT, env=dict(os.environ, **{LOCK_MARK: "1"}))
    raise SystemExit(proc.returncode)


def main():
    if sys.argv[1:] == ["--test"]:
        main_test()
    elif sys.argv[1:] == ["--locked"]:
        main_audit_locked()
    elif not sys.argv[1:]:
        main_audit()
    else:
        fail("usage: scripts/audit.py [--test]")


if __name__ == "__main__":
    main()
