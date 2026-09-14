#!/usr/bin/env python3
"""Check that each content root states a node after everything its \\uses names.

The two content roots input their nodes in a fixed order. A reader meets a
statement only after the statements it depends on, so the input order must be a
topological sort of the \\uses relation. This check reads the \\input order of
each root, resolves every \\uses entry of every environment in the node files to
the node that carries that \\label, and fails on any entry whose node is input
later.

Usage: python3 scripts/check-uses-order.py
"""
import os
import re
import sys

SRC = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                   'blueprint', 'src')
ROOTS = {'content.tex': 'nodes-min', 'content-full.tex': 'nodes'}
INPUT = re.compile(r'\\input\{(nodes(?:-min)?)/([A-Za-z0-9\-]+)\}')
LABEL = re.compile(r'\\label\{([^}]*)\}')
USES = re.compile(r'\\uses\{([^}]*)\}')


def main():
    bad = []
    for root, nodedir in ROOTS.items():
        order = [m.group(2) for m in
                 INPUT.finditer(open(os.path.join(SRC, root)).read())
                 if m.group(1) == nodedir]
        rank, owner = {}, {}
        for i, name in enumerate(order):
            text = open(os.path.join(SRC, nodedir, name + '.tex')).read()
            for lab in LABEL.findall(text):
                rank[lab], owner[lab] = i, name
        for i, name in enumerate(order):
            text = open(os.path.join(SRC, nodedir, name + '.tex')).read()
            for group in USES.findall(text):
                for lab in (u.strip() for u in group.split(',') if u.strip()):
                    if lab not in rank:
                        bad.append('%s: %s uses unknown label %s'
                                   % (root, name, lab))
                    elif rank[lab] > i:
                        bad.append('%s: %s uses %s, stated later in %s'
                                   % (root, name, lab, owner[lab]))
        print('%s: %d nodes in input order' % (root, len(order)))
    for b in bad:
        print(b, file=sys.stderr)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
