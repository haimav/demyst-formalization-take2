#!/usr/bin/env python3
"""Axiom audit: `#print axioms` for every (non-private) theorem, lemma, def and named instance.

Usage (from the repository root, after `lake build`):
    python3 scripts/axiom_audit.py

Generates `.lake/AxiomAudit.lean`, runs it with `lake env lean`, and reports every declaration
that depends on an axiom other than Lean's standard `propext`, `Classical.choice`, `Quot.sound`
(in particular `sorryAx`). Exits with status 1 if any is found.
"""
import glob, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STD = {"propext", "Classical.choice", "Quot.sound"}

names = []
for f in sorted(glob.glob(os.path.join(ROOT, "TubalAlgebra", "**", "*.lean"), recursive=True)):
    ns = []
    for line in open(f, encoding="utf-8").read().split("\n"):
        m = re.match(r"^namespace (\S+)", line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r"^end (\S+)", line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:noncomputable\s+)?"
                     r"(theorem|lemma|def|abbrev|instance)\s+([^\s:\[\(\{]+)", line)
        if m:
            nm = m.group(2)
            names.append(nm[len("_root_."):] if nm.startswith("_root_.") else ".".join(ns + [nm]))

audit = os.path.join(ROOT, ".lake", "AxiomAudit.lean")
with open(audit, "w", encoding="utf-8") as fh:
    fh.write("import TubalAlgebra\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
out = subprocess.run(["lake", "env", "lean", audit], cwd=ROOT, capture_output=True, text=True)
txt = out.stdout + out.stderr
found = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", txt, re.M)
found += [(n, "") for n in re.findall(r"^'(.+)' does not depend on any axioms", txt, re.M)]
bad = [(n, a) for n, a in found if not {x.strip() for x in a.split(",") if x.strip()} <= STD]
print(f"declarations audited: {len(names)}; reported: {len(found)}")
if "error" in txt:
    print(txt); sys.exit(1)
if bad or len(found) != len(names):
    for n, a in bad:
        print("NON-STANDARD:", n, a)
    sys.exit(1)
print("OK: every declaration depends only on propext, Classical.choice, Quot.sound")
