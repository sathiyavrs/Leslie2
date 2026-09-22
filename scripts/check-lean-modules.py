#!/usr/bin/env python3
"""Check that the module paths the prose points at still exist.

Two kinds of pointer name a Lean file, and nothing else verifies either.
``checkdecls`` reads only the harvested ``\\lean``/``\\leandecl`` declarations
and ``check-lean-prose.py`` only the ``\\mathrm{...}`` tokens, so a renamed or
moved file leaves a dead pointer behind with no build failure.

* The blueprint links into the generated API documentation with
  ``\\leanmodule{Path/To/Module}``, which the web macros turn into a doc-gen
  URL. A path may name a module file (``Leslie2/Results`` for
  ``Leslie2/Results.lean``) or a library root (``Leslie2Protocols`` for
  ``Leslie2Protocols.lean``).
* Module docstrings and the guides of ``Leslie2Protocols`` cite a file by its
  path, as ``ABA/Gather/Composition.lean`` or ``Framework/SynchronisedProduct.lean``. A citation
  is written relative to whichever directory makes it read naturally, so it
  resolves when some file in the tree carries it as a trailing path.

Run from the repository root::

    python3 scripts/check-lean-modules.py
"""

import re
import sys
from pathlib import Path

MODULE = re.compile(r"\\leanmodule\{([^}]*)\}")
# A file path cited in prose: one or more directory segments then a .lean file.
# The lookbehind keeps a longer path from matching at one of its own segments.
FILE_CITE = re.compile(r"(?<![\w/])((?:[A-Z][A-Za-z0-9_]*/)+[A-Z][A-Za-z0-9_]*\.lean)\b")
# Predecessor repositories this one cites but does not contain.
FOREIGN = ("Leslie/", "Leslie_LTS/")
# The library whose citations this check owns.  Leslie2/ and Leslie2Extra/ are
# outside it, and the root README with them.
CITING = "Leslie2Protocols"


def module_paths(src: Path) -> dict[str, list[str]]:
    """Every ``\\leanmodule{...}`` path, mapped to the files it appears in."""
    paths: dict[str, list[str]] = {}
    for path in sorted(src.rglob("*.tex")):
        for target in MODULE.findall(path.read_text(encoding="utf-8", errors="replace")):
            paths.setdefault(target.strip(), []).append(str(path))
    return paths


def file_citations(repo: Path) -> dict[str, list[str]]:
    """Every ``Dir/File.lean`` path cited in a docstring or a guide."""
    cites: dict[str, list[str]] = {}
    root = repo / CITING
    for path in sorted(root.rglob("*.lean")) + sorted(root.rglob("*.md")):
        for target in FILE_CITE.findall(path.read_text(encoding="utf-8", errors="replace")):
            if target.startswith(FOREIGN):
                continue
            cites.setdefault(target, []).append(str(path.relative_to(repo)))
    return cites


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    status = 0

    targets = module_paths(repo / "blueprint" / "src")
    missing = {t: v for t, v in targets.items() if not (repo / f"{t}.lean").is_file()}
    print(f"blueprint module links: {len(targets)}, resolved: {len(targets) - len(missing)}")
    for target, files in sorted(missing.items()):
        where = ", ".join(sorted({Path(f).name for f in files}))
        print(
            f"error: \\leanmodule{{{target}}} names no Lean file ({where}); "
            "the module was renamed, moved, or misspelled",
            file=sys.stderr,
        )
        status = 1

    cites = file_citations(repo)
    tree = {str(p.relative_to(repo)) for p in repo.rglob("*.lean")}
    unresolved = {
        t: v
        for t, v in cites.items()
        if not any(f == t or f.endswith("/" + t) for f in tree)
    }
    print(f"prose file citations: {len(cites)}, resolved: {len(cites) - len(unresolved)}")
    for target, files in sorted(unresolved.items()):
        where = ", ".join(sorted({Path(f).name for f in files})[:4])
        print(
            f"error: {target} names no Lean file ({where}); "
            "the module was renamed, moved, or misspelled",
            file=sys.stderr,
        )
        status = 1

    return status


if __name__ == "__main__":
    sys.exit(main())
