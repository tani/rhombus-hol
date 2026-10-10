#!/usr/bin/env python3
"""Compare an eval.rhm run with Appendix B of the paper.

    python3 tools/boyer_moore_eval/compare.py RUN.tsv [--rows]

Matches the arithmetic conjectures of the run (upstream testset/arith.ml)
with the paper's "HOL Light Test Set" rows (appendix_b.tsv) by their text,
ignoring spaces and parentheses, and prints how the two results agree, the
classes of the failures, and the proof times. With --rows, every matched
row as well.
"""
import csv, os, re, statistics, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))

def norm(t):
    return re.sub(r'[\s()]', '', t)

def read_tsv(path, comment=False):
    with open(path) as f:
        lines = [l for l in f if not (comment and l.startswith('#') and not l.startswith('#\t'))]
    rows = list(csv.reader(lines, delimiter='\t'))
    head = [h.lstrip('#') for h in rows[0]]
    return [dict(zip(head, r)) for r in rows[1:] if r]

def main(argv):
    run = read_tsv(argv[0])
    paper = read_tsv(os.path.join(HERE, 'appendix_b.tsv'), comment=True)
    port = {norm(r['theorem']): r for r in run if r['set'] == 'arith'}
    pairs, unmatched = [], []
    for p in paper:
        r = port.pop(norm(p['theorem']), None)
        (pairs.append((p, r)) if r else unmatched.append(p))
    print(f"matched {len(pairs)} of the paper's {len(paper)} rows; "
          f"{len(unmatched)} paper rows and {len(port)} port conjectures unmatched")
    for p in unmatched:
        print('  paper only:', p['theorem'])
    for r in port.values():
        print('  port only: ', r['theorem'], f"({r['class']})")
    agree = collections.Counter()
    for p, r in pairs:
        agree[(p['proved'] == 'true', r['result'] == 'true')] += 1
    print('\n             port proved  port failed')
    print(f"paper proved {agree[(True, True)]:11}  {agree[(True, False)]:11}")
    print(f"paper failed {agree[(False, True)]:11}  {agree[(False, False)]:11}")
    for title, sel in (('proved by the paper, not by the port', (True, False)),
                       ('proved by the port, not by the paper', (False, True))):
        rows = [(p, r) for p, r in pairs if (p['proved'] == 'true', r['result'] == 'true') == sel]
        print(f'\n{title}:')
        for p, r in rows:
            print(f"  {p['#'] if '#' in p else p.get('', '?'):>3} {r['class']:9} {r['time']:>7}s  {p['theorem']}")
    print('\nfailure classes (all port conjectures):')
    for s in ('arith', 'list'):
        c = collections.Counter(r['class'] for r in run if r['set'] == s)
        print(f'  {s:5}', ', '.join(f'{k} {v}' for k, v in sorted(c.items(), key=lambda kv: -kv[1])))
    print('\nproof times of proved conjectures (s):')
    for s in ('arith', 'list'):
        t = [float(r['time']) for r in run if r['set'] == s and r['result'] == 'true']
        if t:
            print(f'  {s:5} n={len(t)} median {statistics.median(t):.3f} mean {statistics.mean(t):.3f} max {max(t):.3f}')
    t = [float(p['time']) for p, _ in pairs if p['proved'] == 'true']
    print(f"  paper n={len(t)} median {statistics.median(t):.3f} mean {statistics.mean(t):.3f} max {max(t):.3f}")
    both = [(int(p['steps']), int(r['steps']), int(p['inds']), int(r['inds'])) for p, r in pairs
            if p['proved'] == 'true' and r['result'] == 'true']
    same = sum(1 for a, b, c, d in both if a == b and c == d)
    print(f'\nproved by both: {len(both)}; same steps and inductions in {same}')
    if '--rows' in argv:
        print('\nrow  paper          port')
        for p, r in pairs:
            print(f"{p.get('', p.get('#','')):>3}  {p['proved']:6} {p['steps'] or '-':>4}/{p['inds'] or '-':<2}  "
                  f"{r['class']:9} {r['steps']:>4}/{r['inds']:<2}  {p['theorem']}")
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
