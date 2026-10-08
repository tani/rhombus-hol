#!/usr/bin/env python3
"""Compare two HOL_QUOTE_DUMP logs site by site (per file, in source order).

Setting HOL_QUOTE_DUMP=1 makes every `hol:` expansion print its typed term
(`HOLDUMP<TAB>srcloc<TAB>json`). Compile before and after a change to the
quotations (rewrite, regeneration, macro change) and compare the logs:

    HOL_QUOTE_DUMP=1 raco make -j 4 rhombus/hol/define.rhm rhombus/hol/tests/*.rhm \\
        rhombus/hol/tests/upstream/*.rhm > before.log      # force a full recompile
    ... change ...
    HOL_QUOTE_DUMP=1 raco make ... > after.log
    python3 tools/hol_light_golden/compare_quote_dumps.py before.log after.log

Every site must be identical; the exit status is nonzero otherwise.
"""
import re, sys, collections

LINE = re.compile(r'^HOLDUMP\tSrcloc\(Path\("([^"]+)"\), (\d+), (\d+), (\d+), (\d+)\)\t(.*)$')


def load(path):
    d = collections.defaultdict(list)
    for line in open(path, errors='replace'):
        m = LINE.match(line.rstrip('\n'))
        if m:
            f, ln, col, pos, span, js = m.groups()
            d[f].append((int(pos), int(ln), js))
    for f in d:
        d[f].sort()
    return d


old, new = load(sys.argv[1]), load(sys.argv[2])
bad = 0
for f in sorted(set(old) | set(new)):
    a, b = old.get(f, []), new.get(f, [])
    if len(a) != len(b):
        print('COUNT', f, len(a), len(b)); bad += 1
        continue
    for (pa, la, ja), (pb, lb, jb) in zip(a, b):
        if ja != jb:
            bad += 1
            print('DIFF', f.split('/rhombus/')[-1], 'old line', la, 'new line', lb)
print('sites before', sum(map(len, old.values())), 'after', sum(map(len, new.values())), 'differing', bad)
sys.exit(1 if bad else 0)
