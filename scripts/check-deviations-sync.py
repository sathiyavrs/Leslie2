#!/usr/bin/env python3
"""Check that the two registries of deviations agree with their tables and with each other.

The registry of deviations from the source blueprint exists once per edition:
deviations.tex in the default edition, deviations-full.tex in the full one.
Each file opens with an overview table, written by hand, of the labels in use
and a headline each, followed by a deviations environment whose entries are
\\deviation{label}{headline} and the entry's fields. The default edition carries
the fields \\departure and \\reason, the full edition \\departure, \\reason and
\\following. A closing sentence lists the labels not in use.

The table is a second copy of the labels and headlines, and the full edition a
second copy of the registry, so nothing but this check keeps them in step. It
asserts, per file, that the table rows equal the entries in order, that every
entry carries exactly its edition's fields with non-empty arguments, that the
environment holds entries alone and no blank line, and that the entry labels
and the closing sentence's labels cover D1 to D36 exactly; across the files, it
asserts that the labels and headlines agree.

Usage: python3 scripts/check-deviations-sync.py
Exits 0 and prints "N/N entries in sync" when every check passes, else lists
the drifts and exits 1.
"""
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT = os.path.join(REPO, 'blueprint', 'src', 'deviations.tex')
FULL = os.path.join(REPO, 'blueprint', 'src', 'deviations-full.tex')

FIELDS = {DEFAULT: ['departure', 'reason'],
          FULL: ['departure', 'reason', 'following']}
LABEL = re.compile(r"D\d+|D12\$'\$")
LABEL_RANGE = range(1, 37)
BEGIN = r'\begin{deviations}'
END = r'\end{deviations}'
ENTRY = re.compile(r'\\deviation(?![A-Za-z])')
FIELD = re.compile(r'\\(departure|reason|following)(?![A-Za-z])')


def balanced(s, i):
    """Given s[i] == '{', return the index just past the matching '}'."""
    depth = 0
    while i < len(s):
        if s[i] == '{':
            depth += 1
        elif s[i] == '}':
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError('unbalanced brace')


def argument(s, i):
    """Read one braced argument at s[i], after whitespace; return (text, end)."""
    while i < len(s) and s[i] in ' \t\n':
        i += 1
    if i >= len(s) or s[i] != '{':
        raise ValueError('expected a braced argument at offset %d' % i)
    j = balanced(s, i)
    return s[i + 1:j - 1], j


def collapse(s):
    """Collapse runs of whitespace to one space and strip the ends."""
    return re.sub(r'\s+', ' ', s).strip()


def strip_comments(s):
    """Remove TeX comments, keeping escaped percent signs."""
    return re.sub(r'(?<!\\)%.*', '', s)


def environment(text, drifts, name):
    """Return the body of the single deviations environment and its start offset."""
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        drifts.append('%s: expected one deviations environment, found %d'
                      % (name, text.count(BEGIN)))
        return None, None
    start = text.index(BEGIN) + len(BEGIN)
    return text[start:text.index(END)], start


def entries(text, drifts, name):
    """The entries of the single deviations environment.

    Returns a list of (label, headline, [(field, argument), ...]).
    """
    body, _ = environment(text, drifts, name)
    if body is None:
        return []
    for line in body.split('\n')[1:-1]:
        if not line.strip():
            drifts.append('%s: blank line inside the deviations environment' % name)
            break
    result = []
    matches = list(ENTRY.finditer(body))
    if not matches:
        drifts.append('%s: no \\deviation entries' % name)
        return []
    if strip_comments(body[:matches[0].start()]).strip():
        drifts.append('%s: material before the first \\deviation' % name)
    for n, m in enumerate(matches):
        stop = matches[n + 1].start() if n + 1 < len(matches) else len(body)
        try:
            label, i = argument(body, m.end())
            headline, i = argument(body, i)
        except ValueError as e:
            drifts.append('%s: entry %d: %s' % (name, n + 1, e))
            continue
        fields = []
        rest = body[i:stop]
        j = 0
        while True:
            r = strip_comments(rest[j:])
            if not r.strip():
                break
            fm = FIELD.match(rest, j + len(rest[j:]) - len(rest[j:].lstrip()))
            if not fm:
                drifts.append('%s: %s: material that is not a field' % (name, collapse(label)))
                break
            try:
                arg, j = argument(rest, fm.end())
            except ValueError as e:
                drifts.append('%s: %s: \\%s: %s' % (name, collapse(label), fm.group(1), e))
                break
            fields.append((fm.group(1), collapse(arg)))
        result.append((collapse(label), collapse(headline), fields))
    return result


def table_rows(text, drifts, name):
    """The rows (label, headline) of the single tabular before the environment."""
    head = text.split(BEGIN)[0]
    if text.count(r'\begin{tabular}') != 1 or head.count(r'\end{tabular}') != 1:
        drifts.append('%s: expected one tabular before the environment, found %d'
                      % (name, text.count(r'\begin{tabular}')))
        return []
    i = head.index(r'\begin{tabular}') + len(r'\begin{tabular}')
    _, i = argument(head, i)
    table = head[i:head.index(r'\end{tabular}')]
    rows = []
    for row in strip_comments(table).split('\\\\'):
        row = collapse(row.replace(r'\hline', ''))
        if not row:
            continue
        cells = [collapse(c) for c in row.split('&')]
        if len(cells) != 2:
            drifts.append('%s: table row with %d cells: %s' % (name, len(cells), row))
            continue
        if cells == ['Label', 'Headline']:
            continue
        rows.append(tuple(cells))
    return rows


def closing_labels(text, drifts, name):
    """The labels the closing sentence names as not in use."""
    tail = collapse(strip_comments(text.split(END)[-1]))
    m = re.search(r'The labels (.*?) are not in use', tail)
    if not m:
        drifts.append('%s: no closing sentence naming the labels not in use' % name)
        return []
    return re.findall(r'D\d+', m.group(1))


def number(label):
    """The number a label carries, D12$'$ read as 12."""
    return int(re.match(r'D(\d+)', label).group(1))


def check_file(path, drifts):
    """Check one registry; return its entries."""
    name = os.path.relpath(path, REPO)
    text = open(path, encoding='utf-8').read()
    found = entries(text, drifts, name)
    labels = [e[0] for e in found]
    for lab in labels:
        if not LABEL.fullmatch(lab):
            drifts.append('%s: malformed label %s' % (name, lab))
    for lab in sorted(set(labels)):
        if labels.count(lab) > 1:
            drifts.append('%s: label %s used %d times' % (name, lab, labels.count(lab)))
    rows = table_rows(text, drifts, name)
    if [r[0] for r in rows] != labels:
        drifts.append('%s: table labels %s differ from entry labels %s'
                      % (name, [r[0] for r in rows], labels))
    for (rl, rh), (el, eh, _) in zip(rows, found):
        if rl == el and rh != eh:
            drifts.append('%s: %s: table headline "%s" differs from entry headline "%s"'
                          % (name, el, rh, eh))
    want = FIELDS[path]
    for lab, _, fields in found:
        got = [f for f, _ in fields]
        if got != want:
            drifts.append('%s: %s: fields %s, expected %s' % (name, lab, got, want))
        for f, arg in fields:
            if not arg:
                drifts.append('%s: %s: empty \\%s' % (name, lab, f))
    if path == DEFAULT and re.search(r'\\following(?![A-Za-z])', strip_comments(text)):
        drifts.append('%s: \\following in the default edition' % name)
    unused = closing_labels(text, drifts, name)
    unused_numbers = [number(x) for x in unused]
    entry_numbers = [number(x) for x in labels]
    covered = unused_numbers + entry_numbers
    if 12 not in covered:
        covered.append(12)
    if sorted(covered) != list(LABEL_RANGE):
        drifts.append('%s: entry labels, D12 and the labels not in use cover %s, not D1 to D36'
                      % (name, sorted(covered)))
    return found


def main():
    drifts = []
    missing = [p for p in (DEFAULT, FULL) if not os.path.exists(p)]
    for p in missing:
        drifts.append('missing %s' % os.path.relpath(p, REPO))
    if not missing:
        default = check_file(DEFAULT, drifts)
        full = check_file(FULL, drifts)
        a = [(l, h) for l, h, _ in default]
        b = [(l, h) for l, h, _ in full]
        if [x[0] for x in a] != [x[0] for x in b]:
            drifts.append('labels differ across editions: %s against %s'
                          % ([x[0] for x in a], [x[0] for x in b]))
        for (la, ha), (lb, hb) in zip(a, b):
            if la == lb and ha != hb:
                drifts.append('%s: headline "%s" in the default edition, "%s" in the full one'
                              % (la, ha, hb))
    if drifts:
        for d in drifts:
            print(d)
        sys.exit(1)
    print('%d/%d entries in sync' % (len(default), len(full)))


if __name__ == '__main__':
    main()
