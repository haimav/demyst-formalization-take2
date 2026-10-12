#!/usr/bin/env python3
"""Annotate every Lean declaration named in `mapping.md` with its location.

Usage (from the repository root):
    python3 scripts/update_mapping_locations.py

For each backticked Lean name in `mapping.md` (outside the "Paper" column of the tables) that
resolves to a declaration of the project, a link `[path:line](path#Lline)` is inserted right
after it (for an applied term such as `starMC M a b`, the head symbol is located; one-letter
names are skipped). The script is idempotent: previously inserted links are removed and recomputed, so it
can be re-run whenever the sources change.
"""
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAPPING = os.path.join(ROOT, "mapping.md")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([^\s:\[\(\{]+)")
LINK = re.compile(r" \(\[TubalAlgebra/[^\]]*:\d+\]\([^)]*\)\)")
TICK = re.compile(r"`([^`]+)`")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")


def index_declarations():
    """Map fully qualified declaration names to (relative path, line)."""
    index = {}
    for path in sorted(glob.glob(os.path.join(ROOT, "TubalAlgebra", "**", "*.lean"),
                            recursive=True)):
        rel = os.path.relpath(path, ROOT)
        namespaces = []
        for lineno, line in enumerate(open(path, encoding="utf-8").read().split("\n"), 1):
            m = re.match(r"^namespace (\S+)", line)
            if m:
                namespaces.append(m.group(1))
                continue
            m = re.match(r"^end (\S+)", line)
            if m and namespaces and namespaces[-1] == m.group(1):
                namespaces.pop()
                continue
            m = DECL.match(line)
            if m:
                name = m.group(2)
                full = name[len("_root_."):] if name.startswith("_root_.") \
                    else ".".join(namespaces + [name])
                index.setdefault(full, (rel, lineno))
    return index


def resolve(token, index):
    if token in index:
        return index[token]
    if "Tubal." + token in index:
        return index["Tubal." + token]
    hits = [k for k in index if k.endswith("." + token)]
    if len(hits) == 1:
        return index[hits[0]]
    return None


def annotate(text, index, unresolved):
    def repl(m):
        tok = m.group(1)
        # for an applied term such as `starMC M a b`, locate its head symbol
        head = tok.split(" ")[0]
        if not IDENT.match(head) or len(head) < 2:
            return m.group(0)
        if head != tok and resolve(head, index) is None:
            return m.group(0)
        tok = head
        loc = resolve(tok, index)
        if loc is None:
            unresolved.add(tok)
            return m.group(0)
        rel, line = loc
        return f"{m.group(0)} ([{rel}:{line}]({rel}#L{line}))"
    return TICK.sub(repl, text)


def main():
    index = index_declarations()
    unresolved = set()
    out = []
    for line in open(MAPPING, encoding="utf-8").read().split("\n"):
        line = LINK.sub("", line)
        if line.startswith("|") and not set(line.replace("|", "")) <= set("-: "):
            cells = line.split("|")
            # cells[0] is empty, cells[1] is the "Paper" column; annotate the rest.
            if len(cells) > 3 and not cells[1].strip().startswith("Paper"):
                cells[2:-1] = [annotate(c, index, unresolved) for c in cells[2:-1]]
            line = "|".join(cells)
        elif not line.startswith("#"):
            line = annotate(line, index, unresolved)
        out.append(line)
    open(MAPPING, "w", encoding="utf-8").write("\n".join(out))
    print(f"indexed {len(index)} declarations")
    print("not linked (not a declaration of this project):", ", ".join(sorted(unresolved)))


if __name__ == "__main__":
    sys.exit(main())
