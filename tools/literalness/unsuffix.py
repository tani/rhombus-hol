# Usage: python3 tools/literalness/unsuffix.py MODULE.rhm UPSTREAM.ml [-v]
# Strip translator-added numeric suffixes (th_lp_5 -> th_lp) from local
# names inside each toplevel definition of a .rhm module, when the base name
# occurs in the upstream .ml file and the suffixed one does not.
import re, sys
rhm, ml = sys.argv[1], sys.argv[2]
up = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", open(ml).read()))
src = open(rhm).read()
# Split into toplevel chunks (a line at column 0 starts a chunk).
lines = src.split('\n')
chunks, cur = [], []
for ln in lines:
    if ln and not ln[0].isspace() and cur:
        chunks.append(cur); cur = []
    cur.append(ln)
chunks.append(cur)
toplevel = set()
for c in chunks:
    m = re.match(r"(?:def|fun)\s+(?:mutable\s+)?([A-Za-z_][A-Za-z0-9_]*)", c[0])
    if m: toplevel.add(m.group(1))
# Mask strings and @hol quotes when renaming.
tokre = re.compile(r'@hol\|\{.*?\}\||"(?:\\.|[^"\\])*"|//[^\n]*|[A-Za-z_][A-Za-z0-9_]*', re.S)
def up_name(n): return n.replace('_prime', "'")
out, renames, skipped = [], 0, []
for c in chunks:
    text = '\n'.join(c)
    head = re.match(r"(?:def|fun)\s+(?:mutable\s+)?([A-Za-z_][A-Za-z0-9_]*)", c[0])
    own = head.group(1) if head else None
    idents = set(m.group(0) for m in tokre.finditer(text) if re.match(r'[A-Za-z_]', m.group(0)) and not m.group(0).startswith('@'))
    mp = {}
    for n in idents:
        m = re.fullmatch(r"(.*?)_(\d+)", n)
        if not m or n == own or n in toplevel: continue
        base = m.group(1)
        if up_name(n) in up or up_name(base) not in up: continue
        if base in toplevel and base != own: continue
        if base in idents: skipped.append((own, n)); continue
        mp[n] = base
    # Merge several suffixed names into one base only when their extents
    # in the text do not overlap (separate scopes such as match clauses).
    pos = {}
    for m in tokre.finditer(text):
        pos.setdefault(m.group(0), []).append(m.start())
    groups = {}
    for n, b in mp.items(): groups.setdefault(b, []).append(n)
    for b, ns in groups.items():
        if len(ns) > 1:
            iv = sorted((min(pos[n]), max(pos[n])) for n in ns)
            if any(iv[i][1] > iv[i+1][0] for i in range(len(iv)-1)):
                for n in ns: del mp[n]; skipped.append((own, n))
    if mp:
        def sub(m):
            t = m.group(0)
            return mp.get(t, t)
        text = tokre.sub(sub, text); renames += len(mp)
    out.append(text)
open(rhm, 'w').write('\n'.join(out))
print(rhm, renames, 'names; skipped', len(skipped)); [print('  skip', o, n) for o, n in skipped] if '-v' in sys.argv else None
