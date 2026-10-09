#!/usr/bin/env python3
"""How literally does each rhombus/hol module follow the pinned HOL Light source?

    python3 tools/literalness/measure.py /path/to/hol-light            # report
    python3 tools/literalness/measure.py /path/to/hol-light --check    # also fail
                                         on a logic-layer drop below baseline.json
    python3 tools/literalness/measure.py /path/to/hol-light --update   # rewrite
                                         baseline.json from the current sources
    python3 tools/literalness/measure.py /path/to/hol-light --defs MODULE
                                         # per-definition scores of one module

For each module it compares the sequence of identifiers, string literals and
quotations of the OCaml source with that of the Rhombus port, after removing
what the translation changes by design: comments, OCaml type annotations,
`PairList`, keywords, and the port's renamings (`then_tac` is THEN,
`module_NAME_vN` is NAME, `x_prime` is x'). The score of a module is the
share of its HOL Light tokens that appear in the same order in the port
(longest common subsequence). It also counts toplevel definitions found by
name and in order, and quotations that are textually identical.

Layers (AGENTS.md): `lib` is the library layer, whose implementation may use
Rhombus/Racket functions; every other module is the logic layer.
"""
import collections
import difflib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RH = os.path.normpath(os.path.join(HERE, '..', '..', 'rhombus', 'hol'))
BASELINE = os.path.join(HERE, 'baseline.json')
ORDER = ("lib fusion basics nets printer preterm parser equal bool drule tactics itab simp theorems "
         "ind_defs class trivia canon meson firstorder metis thecops quot impconv pair compute "
         "nums recursion arith wf calc_num normalizer grobner ind_types lists realax calc_int "
         "realarith real calc_rat int sets iterate cart define").split()
RHFILE = {}
LIBRARY_LAYER = {'lib'}
TOLERANCE = 0.5   # percentage points a logic-layer score may drop

OPS = {'then_tac': 'THEN', 'then_list': 'THENL', 'or_tac': 'ORELSE',
       'then_conv': 'THENC', 'or_conv': 'ORELSEC'}
NOISE = {'PairList', 'def', 'fun', 'let', 'in', 'and', 'match', 'with', 'function', 'if',
         'then', 'else', 'try', 'catch', 'when', 'rec', 'cond', 'block', 'Failure', 'exn',
         'throw', 'Some', 'None', 'true', 'false', 'unit', 'begin', 'end', 'o', 'fst', 'snd',
         'I', 'K', 'C', 'W', '_'}
TYPES = {'term', 'thm', 'hol_type', 'list', 'string', 'int', 'bool', 'unit', 'option', 'conv',
         'tactic', 'thm_tactic', 'thm_tactical', 'goal', 'instantiation', 'term_label', 'net',
         'array', 'float', 'char', 'num', 'ref', 'pretype', 'preterm', 'lexcode',
         'justification', 'goalstack', 'refinement', 'goalstate', 'Hashtbl', 't', 'exn',
         'a', 'b', 'c'}


def strip_ml_comments(s):
    out = []; i = 0; depth = 0; n = len(s)
    while i < n:
        if s.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth and s.startswith('*)', i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if s[i] == '`':
            j = s.index('`', i + 1)
            out.append(s[i:j + 1]); i = j + 1; continue
        m = re.match(r"'(?:\\.|[^\\'])'", s[i:i + 5])
        if m and (i == 0 or not re.match(r"[\w']", s[i - 1])):
            out.append(s[i:i + m.end()]); i += m.end(); continue
        if s[i] == '"':
            j = i + 1
            while s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            out.append(s[i:j + 1]); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)


def norm_name(n, mod):
    n = n.replace('_prime', "'")
    m = re.match(r'^(?:\w+?_)?(.+?)_v\d+$', n)
    if m:
        n = m.group(1)
        if n.startswith(mod + '_'):
            n = n[len(mod) + 1:]
    return n


def open_local_of(cur):
    """Whether the definition being read ends in an open `let ... in`."""
    lines = [x for x in cur[1] if x.strip()]
    return bool(re.search(r"\bin\s*$", lines[-1])) if lines else False


def ml_defs(src):
    """Toplevel `let` definitions, inside `module ... struct` bodies too."""
    s = strip_ml_comments(src)
    defs = []; cur = None; stack = []
    for l in s.split('\n'):
        if not l.strip():
            if cur:
                cur[1].append(l)
            continue
        ind = len(l) - len(l.lstrip(' '))
        if re.match(r"^\s*module\b.*=\s*struct\b", l):
            if cur:
                defs.append(cur); cur = None
            stack.append([ind, None]); continue
        if stack and l.strip().startswith('end') and ind == stack[-1][0]:
            if cur:
                defs.append(cur); cur = None
            stack.pop(); continue
        if stack and stack[-1][1] is None:
            stack[-1][1] = ind
        body = stack[-1][1] if stack else 0
        m = (re.match(r"^\s*let\s+(?:rec\s+)?\(?([A-Za-z_][\w']*)", l)
             or re.match(r"^\s*and\s+\(?([A-Za-z_][\w']*)", l) if cur and not open_local_of(cur) else
             re.match(r"^\s*let\s+(?:rec\s+)?\(?([A-Za-z_][\w']*)", l))
        open_local = (cur is not None and not ''.join(cur[1]).rstrip().endswith(';;')
                      and re.search(r"\bin\s*$", [x for x in cur[1] if x.strip()][-1]))
        if ind == body and m and not open_local and not re.match(r"^\s*let\s+_\s*=", l):
            if cur:
                defs.append(cur)
            cur = [m.group(1), [l]]
        elif ind == body and not l.lstrip().startswith(('and ', '|', ')', ']', 'in ', 'with', 'else', 'then')):
            if cur:
                defs.append(cur); cur = None
        elif cur is not None:
            cur[1].append(l)
    if cur:
        defs.append(cur)
    return [(n, '\n'.join(b)) for n, b in defs]


def rh_defs(src, mod):
    """Toplevel `def`/`fun` definitions, inside `namespace` bodies too."""
    defs = []; cur = None; ns = []
    for l in src.split('\n'):
        if not l.strip():
            if cur:
                cur[1].append(l)
            continue
        ind = len(l) - len(l.lstrip(' '))
        while ns and ind <= ns[-1] and not l.lstrip().startswith('//'):
            ns.pop()
        if re.match(r'^ *namespace\b', l):
            if cur:
                defs.append(cur); cur = None
            ns.append(ind); continue
        body = ns[-1] + 2 if ns else 0
        m = re.match(r'^ *(def|fun)\s+(?:mutable\s+)?(?:\[([^\]]*)\]|([A-Za-z_]\w*|#\{[^}]*\}))', l)
        if m and ind == body:
            if cur:
                defs.append(cur)
            name = m.group(2).split(',')[0].strip() if m.group(2) else m.group(3)
            cur = [norm_name(name, mod), [l]]
        elif cur is not None and (ind > body or l.lstrip().startswith(('//', '| '))):
            cur[1].append(l)
        elif cur is not None:
            defs.append(cur); cur = None
    if cur:
        defs.append(cur)
    return [(n, '\n'.join(b)) for n, b in defs]


def toks_ml(body):
    out = []
    # A record field bound to a variable of its own name, as in
    # `{head = head}`, is punned on the Rhombus side.
    body = re.sub(r"\b([a-z_][\w']*)\s*=\s*\1\b(?=\s*[;}])", r"\1", body)
    for m in re.finditer(r'`[^`]*`|"(?:[^"\\]|\\.)*"|[A-Za-z_][\w\']*', body):
        t = m.group(0)
        if t[0] == '`':
            out.append('Q:' + ' '.join(t[1:-1].split()))
        elif t[0] == '"':
            out.append('S:' + t)
        elif t not in NOISE and t not in TYPES:
            out.append(t)
    return out


def toks_rh(body, mod, ml_names):
    out = []
    pat = r'@hol\|\{(?:(?!\}\|).)*\}\||"(?:[^"\\]|\\.)*"|#\{[^}]*\}|[A-Za-z_]\w*'
    for m in re.finditer(pat, body, re.S):
        t = m.group(0)
        if t.startswith('@hol'):
            out.append('Q:' + ' '.join(t[6:-2].split())); continue
        if t[0] == '"':
            out.append('S:' + t); continue
        if t.startswith('#{'):
            t = t[2:-1].strip('|')
        t = OPS.get(t, t)
        if t in NOISE or t in TYPES or t.startswith('arg_'):
            continue
        t = norm_name(t, mod)
        if t.startswith(mod + '_') and t[len(mod) + 1:] in ml_names:
            t = t[len(mod) + 1:]
        out.append(t)
    return out


def lcs(a, b):
    return sum(x.size for x in difflib.SequenceMatcher(None, a, b, autojunk=False).get_matching_blocks())


def measure(hol):
    rows = {}
    for mod in ORDER:
        ml = os.path.join(hol, mod + '.ml')
        rh = os.path.join(RH, RHFILE.get(mod, mod + '.rhm'))
        if not (os.path.exists(ml) and os.path.exists(rh)):
            continue
        ml_src = open(ml).read(); rh_src = open(rh).read()
        a = toks_ml(strip_ml_comments(ml_src))
        body = '\n'.join(l for l in rh_src.split('\n') if not l.lstrip().startswith('//'))
        if '\nexport:' in body:
            body = body[body.index('\nexport:'):]
        c = toks_rh(body, mod, set(a))
        md = [n for n, _ in ml_defs(ml_src)]
        rd = [n for n, _ in rh_defs(rh_src, mod)]
        qa = [t for t in a if t.startswith('Q:')]
        qc = [t for t in c if t.startswith('Q:')]
        rows[mod] = {
            'layer': 'library' if mod in LIBRARY_LAYER else 'logic',
            'tokens': len(a), 'common': lcs(a, c),
            'score': round(100 * lcs(a, c) / max(len(a), 1), 1),
            'defs': len(md), 'defs_found': sum(1 for n in md if n in set(rd)),
            'defs_in_order': lcs(md, rd),
            'quotes': len(qa), 'quotes_same': lcs(qa, qc),
        }
    return rows


def report(rows):
    print(f"{'module':12} {'layer':8} {'score':>6} {'defs found/order/HL':>20} {'quotes same/HL':>15}")
    tot = collections.Counter()
    for mod, r in rows.items():
        for k in ('tokens', 'common', 'defs', 'defs_found', 'defs_in_order', 'quotes', 'quotes_same'):
            tot[k] += r[k]
        print(f"{mod:12} {r['layer']:8} {r['score']:5.1f}% "
              f"{r['defs_found']:6}/{r['defs_in_order']:5}/{r['defs']:<6}  "
              f"{r['quotes_same']:6}/{r['quotes']:<6}")
    print(f"{'TOTAL':12} {'':8} {100 * tot['common'] / tot['tokens']:5.1f}% "
          f"{tot['defs_found']:6}/{tot['defs_in_order']:5}/{tot['defs']:<6}  "
          f"{tot['quotes_same']:6}/{tot['quotes']:<6}")


def defs_report(hol, mod, threshold=100.0):
    """Toplevel definitions of one module: missing ones, then the least literal."""
    ml_src = open(os.path.join(hol, mod + '.ml')).read()
    rh_src = open(os.path.join(RH, RHFILE.get(mod, mod + '.rhm'))).read()
    names = set(toks_ml(strip_ml_comments(ml_src)))
    rmap = collections.defaultdict(list)
    for n, b in rh_defs(rh_src, mod):
        rmap[n].append(b)
    used = collections.Counter(); rows = []; missing = []
    for n, b in ml_defs(ml_src):
        if used[n] >= len(rmap[n]):
            missing.append(n); continue
        a = toks_ml(strip_ml_comments(b)); c = toks_rh(rmap[n][used[n]], mod, names)
        used[n] += 1
        rows.append((round(100 * lcs(a, c) / max(len(a), 1), 1), len(a), n))
    print('not found in the port:', ' '.join(missing) or '-')
    for score, size, n in sorted(rows):
        if score < threshold:
            print(f'{score:6.1f}% {size:5} tokens  {n}')


def main(argv):
    if not argv or argv[0].startswith('-'):
        print(__doc__); return 2
    if '--defs' in argv:
        defs_report(argv[0], argv[argv.index('--defs') + 1], 90.0)
        return 0
    rows = measure(argv[0])
    report(rows)
    if '--update' in argv:
        json.dump({m: r['score'] for m, r in rows.items()}, open(BASELINE, 'w'), indent=1, sort_keys=True)
        print('baseline written to', BASELINE)
    if '--check' in argv:
        base = json.load(open(BASELINE))
        bad = [(m, base[m], r['score']) for m, r in rows.items()
               if r['layer'] == 'logic' and m in base and r['score'] < base[m] - TOLERANCE]
        for m, b, s in bad:
            print(f'REGRESSION {m}: {s}% < baseline {b}%')
        if bad:
            return 1
        print('logic layer: no module below its baseline')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
