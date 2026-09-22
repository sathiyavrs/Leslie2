#!/usr/bin/env python3
"""Check that the ABA folders are imported in the order the guides state.

``Leslie2Protocols/ABA/README.md`` and ``CLAUDE.md`` give the folders of the
ABA development in import order and state that no folder imports one below it:
``Vocabulary/`` is written over by everything, ``GhostErasure/`` writes over
everything. Lean enforces only that the import graph is acyclic, so a file may
reach upwards through a chain the guides forbid and the build stays green.

The order is the rank table below. ``Results.lean`` is a file at the ABA root
and carries a rank of its own. ``GBCA/ABDY/`` and ``GBCA/AFW/`` are sub-folders
with ranks of their own, and they straddle ``Composition/``; ``Implementation/ABDY/``
and ``Implementation/AFW/`` are sub-folders with ranks of their own as well. Any
other sub-folder carries its parent folder's rank. An import is a violation when
the rank of the imported module exceeds the rank of the importing file. Imports of
``Leslie2Protocols.Framework``, of the core library and of Mathlib sit below
every ABA folder and are ignored.

Run from the repository root::

    python3 scripts/check-folder-order.py
"""

import re
import sys
from pathlib import Path

# The library the check owns, and the development inside it.
LIBRARY = "Leslie2Protocols"
DEVELOPMENT = "ABA"
# The folders in import order. A name with a slash is a sub-folder that carries
# a rank of its own; `Results.lean` is a file at the development's root.
ORDER = (
    "Vocabulary",
    "Specifications",
    "Implementation",
    "ReliableBroadcast",
    "Gather",
    "GBCA",
    "GBCA/ABDY",
    "Composition",
    "GBCA/AFW",
    "HybridRefinesSpecification",
    "Implementation/ABDY",
    "Implementation/AFW",
    "Results.lean",
    "GhostErasure",
)
RANK = {name: index for index, name in enumerate(ORDER)}
IMPORT = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)


def rank_of(parts: tuple[str, ...]) -> int | None:
    """The rank of a module, given its path components below ``ABA/``.

    The components are directory names followed by the file's own name, as
    ``("GBCA", "ABDY", "RefinesSpecification")`` or ``("Results",)``. The
    longest prefix that the table names carries the rank, so a sub-folder the
    table omits takes its parent folder's rank.
    """
    if len(parts) == 1:
        return RANK.get(f"{parts[0]}.lean")
    for length in (2, 1):
        if len(parts) > length:
            name = "/".join(parts[:length])
            if name in RANK:
                return RANK[name]
    return None


def imported_rank(module: str) -> int | None:
    """The rank of an imported module, or ``None`` when it sits below them all."""
    parts = module.split(".")
    if parts[:2] != [LIBRARY, DEVELOPMENT]:
        return None
    return rank_of(tuple(parts[2:]))


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / LIBRARY / DEVELOPMENT
    status = 0
    files = 0
    imports = 0

    for path in sorted(root.rglob("*.lean")):
        parts = path.relative_to(root).with_suffix("").parts
        here = rank_of(parts)
        if here is None:
            print(
                f"error: {path.relative_to(repo)} sits in no folder of the import order; "
                "add its folder to the rank table of this script and to the guides",
                file=sys.stderr,
            )
            status = 1
            continue
        files += 1
        for module in IMPORT.findall(path.read_text(encoding="utf-8", errors="replace")):
            there = imported_rank(module)
            if there is None:
                continue
            imports += 1
            if there > here:
                print(
                    f"error: {path.relative_to(repo)} is {ORDER[here]} and imports "
                    f"{module}, which is {ORDER[there]}, below it in the import order",
                    file=sys.stderr,
                )
                status = 1

    tally = f"folder order: {files} files, {imports} ABA imports"
    print(tally if status else f"{tally}, ok")
    return status


if __name__ == "__main__":
    sys.exit(main())
