#!/usr/bin/env python3
"""Check that splitting files leaves the constants of `Leslie2Protocols` alone.

``scripts/DumpConstants.lean`` writes a fingerprint of the library: one
tab-separated row per constant, carrying the user-facing name, the module, the
number of universe parameters, the hash of the type, the hash of a definition's
value, the simp flag and the instance flag. Moving a declaration from one file
to another is allowed to change the module and nothing else.

This check dumps the current tree, compares it against a reference dump taken
before the split, and fails on any constant whose fingerprint differs. The
module column is exempt: a constant that carries the same fingerprint under a
different module is counted as moved and reported in the summary line.

A split may also rename a declaration, add one, or remove one. Each is declared
rather than inferred: ``--map`` takes a two-column file of ``old<TAB>new``
names, applied to the reference; ``--removed`` and ``--added`` take one name per
line, struck from the reference and from the current dump respectively.

Run from the repository root::

    python3 scripts/check-constant-drift.py
    python3 scripts/check-constant-drift.py --map renames.tsv --added new-names.txt
"""

import argparse
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DUMP = REPO / "scripts" / "DumpConstants.lean"
REFERENCE = REPO / ".lake" / "file-split" / "constants-base.tsv"
# The fingerprint columns, in the order the dump writes them after the module.
COLUMNS = ("level count", "type", "value", "simp", "instance")
# The difference each column reports when it is the one that changed.
DIFFERENCE = {
    "level count": "level count changed",
    "type": "type changed",
    "value": "value changed",
    "simp": "simp changed",
    "instance": "instance changed",
}


def parse(text: str) -> dict[str, list[tuple[str, tuple[str, ...]]]]:
    """The rows of a dump, grouped by name as ``(module, fingerprint)`` pairs."""
    rows: dict[str, list[tuple[str, tuple[str, ...]]]] = defaultdict(list)
    for line in text.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if "._sparseCasesOn_" in fields[0]:
            continue  # a match splitter, realized in whichever module first needs it
        if len(fields) != 2 + len(COLUMNS):
            raise SystemExit(f"error: a dump row has {len(fields)} fields: {line!r}")
        rows[fields[0]].append((fields[1], tuple(fields[2:])))
    return rows


def dump_current() -> str:
    """The fingerprint of the tree as it stands."""
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(DUMP.relative_to(REPO))],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stderr)
        raise SystemExit("error: the dump did not run")
    return result.stdout


def read_names(path: Path | None) -> Counter:
    """One name per line, with blank lines and ``#`` comments dropped."""
    if path is None:
        return Counter()
    names = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            names.append(line)
    return Counter(names)


def read_map(path: Path | None) -> dict[str, str]:
    """The rename map, as ``old`` to ``new``."""
    if path is None:
        return {}
    renames = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        fields = line.split("\t")
        if len(fields) != 2:
            raise SystemExit(f"error: a rename row is not two columns: {line!r}")
        renames[fields[0]] = fields[1]
    return renames


def strike(rows: dict[str, list], names: Counter, what: str) -> int:
    """Remove the declared names from a dump. Returns the number struck."""
    struck = 0
    for name, count in names.items():
        held = rows.get(name, [])
        if len(held) < count:
            print(
                f"error: {name} is declared {what} {count} times but the dump holds "
                f"it {len(held)} times",
                file=sys.stderr,
            )
        taken = min(count, len(held))
        del held[:taken]
        struck += taken
        if not held:
            rows.pop(name, None)
    return struck


def rename(rows: dict[str, list], renames: dict[str, str]) -> None:
    """Apply the rename map to the reference's names."""
    for old, new in renames.items():
        if old not in rows:
            print(f"error: {old} is declared renamed but the reference has no such name",
                  file=sys.stderr)
            continue
        rows.setdefault(new, []).extend(rows.pop(old))


def compare(reference: dict[str, list], current: dict[str, list]) -> tuple[int, int, int]:
    """Compare two dumps. Returns the constants compared, the moved, and the failures."""
    compared = 0
    moved = 0
    failures = 0

    for name in sorted(set(reference) | set(current)):
        here = list(reference.get(name, []))
        there = list(current.get(name, []))
        compared += len(here)

        # A constant whose module and fingerprint both hold is unchanged.
        for row in list(here):
            if row in there:
                here.remove(row)
                there.remove(row)
        # A constant whose fingerprint holds under another module has moved.
        for row in list(here):
            match = next((other for other in there if other[1] == row[1]), None)
            if match is not None:
                here.remove(row)
                there.remove(match)
                moved += 1
        # What is left differs in at least one column.
        here.sort()
        there.sort()
        for row, other in zip(here, there):
            for index, column in enumerate(COLUMNS):
                if row[1][index] != other[1][index]:
                    print(
                        f"{DIFFERENCE[column]}: {name} ({row[0]} -> {other[0]}): "
                        f"{row[1][index]} -> {other[1][index]}",
                        file=sys.stderr,
                    )
                    failures += 1
        for row in here[len(there):]:
            print(f"missing: {name} ({row[0]})", file=sys.stderr)
            failures += 1
        for other in there[len(here):]:
            print(f"added: {name} ({other[0]})", file=sys.stderr)
            failures += 1

    return compared, moved, failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--reference", type=Path, default=REFERENCE,
                        help="the dump taken before the split")
    parser.add_argument("--current", type=Path, default=None,
                        help="a dump of the current tree; taken by this script when absent")
    parser.add_argument("--map", type=Path, default=None,
                        help="a two-column file of old and new names")
    parser.add_argument("--added", type=Path, default=None,
                        help="the names the split adds, one per line")
    parser.add_argument("--removed", type=Path, default=None,
                        help="the names the split removes, one per line")
    args = parser.parse_args()

    if not args.reference.is_file():
        raise SystemExit(f"error: the reference dump {args.reference} does not exist")
    reference = parse(args.reference.read_text(encoding="utf-8"))
    if args.current is None:
        current = parse(dump_current())
    else:
        current = parse(args.current.read_text(encoding="utf-8"))

    rename(reference, read_map(args.map))
    strike(reference, read_names(args.removed), "removed")
    strike(current, read_names(args.added), "added")

    compared, moved, failures = compare(reference, current)
    if failures:
        print(f"constant drift: {compared} constants, {moved} moved, {failures} differences")
        return 1
    print(f"constant drift: {compared} constants, {moved} moved, ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
