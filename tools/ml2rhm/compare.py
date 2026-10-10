#!/usr/bin/env python3
"""Compare tools/ml2rhm output with the hand-maintained port.

    python3 tools/ml2rhm/compare.py HOL-LIGHT-DIR GENERATED-DIR [--defs MODULE]

For each module of the port it prints
  similarity  token similarity of the generated module and rhombus/hol's
              (2 * common / (generated + port)), comments and imports aside
  generated   literalness of the generated module, as measure.py scores it
  port        literalness of the hand-maintained module
With --defs MODULE, the per-definition similarity of one module.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'literalness'))
import measure as M  # noqa: E402


def body_tokens(path, mod, ml_names):
    src = open(path).read()
    body = '\n'.join(l for l in src.split('\n') if not l.lstrip().startswith('//'))
    if '\nexport:' in body:
        body = body[body.index('\nexport:'):]
    return M.toks_rh(body, mod, ml_names)


def ratio(a, b):
    return 100.0 * 2 * M.lcs(a, b) / max(len(a) + len(b), 1)


def main(argv):
    hol, gen = argv[0], argv[1]
    if '--defs' in argv:
        mod = argv[argv.index('--defs') + 1]
        ml_src = open(os.path.join(hol, mod + '.ml')).read()
        names = set(M.toks_ml(M.strip_ml_comments(ml_src)))
        port = dict(M.rh_defs(open(os.path.join(M.RH, M.RHFILE.get(mod, mod + '.rhm'))).read(), mod))
        mine = dict(M.rh_defs(open(os.path.join(gen, M.RHFILE.get(mod, mod + '.rhm'))).read(), mod))
        rows = []
        for n, b in mine.items():
            if n in port:
                a = M.toks_rh(b, mod, names); c = M.toks_rh(port[n], mod, names)
                rows.append((ratio(a, c), len(c), n))
        for s, size, n in sorted(rows):
            print(f'{s:6.1f}% {size:5} tokens  {n}')
        return 0
    print(f"{'module':32} {'similarity':>10} {'generated':>10} {'port':>6}")
    tot = [0, 0, 0, 0, 0, 0]
    for mod in M.ORDER:
        ml = os.path.join(hol, mod + '.ml')
        rh = os.path.join(M.RH, M.RHFILE.get(mod, mod + '.rhm'))
        gn = os.path.join(gen, M.RHFILE.get(mod, mod + '.rhm'))
        if not (os.path.exists(ml) and os.path.exists(rh) and os.path.exists(gn)):
            continue
        a = M.toks_ml(M.strip_ml_comments(open(ml).read()))
        names = set(a)
        g = body_tokens(gn, os.path.basename(mod), names)
        p = body_tokens(rh, os.path.basename(mod), names)
        common = M.lcs(g, p)
        lit_g = M.lcs(a, g); lit_p = M.lcs(a, p)
        print(f'{mod:32} {200.0 * common / max(len(g) + len(p), 1):9.1f}% '
              f'{100.0 * lit_g / max(len(a), 1):9.1f}% {100.0 * lit_p / max(len(a), 1):5.1f}%')
        for i, v in enumerate((common, len(g), len(p), lit_g, lit_p, len(a))):
            tot[i] += v
    print(f"{'TOTAL':32} {200.0 * tot[0] / max(tot[1] + tot[2], 1):9.1f}% "
          f'{100.0 * tot[3] / max(tot[5], 1):9.1f}% {100.0 * tot[4] / max(tot[5], 1):5.1f}%')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
