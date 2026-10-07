#!/usr/bin/env python3
"""Rewrite hol_term(...) constructor quotations into hol: / hol_type: forms.

quote.ml and capture.ml print HOL Light terms as hol_term(...) calls over the
typed constructor AST (Var, Const, Comb, Abs, Forall, Eq, App, Tvar, Fun, ...).
This script turns each such call in the given files into the Rhombus-native
quotation of rhombus/hol/private/hol_quote.rhm, in place:

    python3 tools/hol_light_golden/to_hol.py FILE.rhm ...

Operators, binders, if and typed numerals are recovered from the constants
they stand for; the remaining names are declared with var/const, using
`as` where a HOL name is not an identifier, occurs at several types, or is
shadowed by a binder. The elaborated hol: form denotes the same term.
"""
import re, sys

def skip_string(s, i):
    # s[i] == '"'
    j = i + 1
    while s[j] != '"':
        j += 2 if s[j] == '\\' else 1
    return j + 1

def match_group(s, i):
    """s[i] is an opener; return index after matching closer."""
    pairs = {'(': ')', '[': ']', '{': '}'}
    stack = [pairs[s[i]]]
    j = i + 1
    while stack:
        c = s[j]
        if c == '"':
            j = skip_string(s, j); continue
        if c == '/' and s.startswith('//', j):
            j = s.index('\n', j); continue
        if c == '#' and s.startswith('#{', j):
            # racket identifier escape: skip to matching }
            k = s.index('}', j); j = k + 1; continue
        if c in pairs: stack.append(pairs[c])
        elif c in ')]}':
            if c != stack[-1]:
                raise ValueError(f'unbalanced at {j}')
            stack.pop()
        j += 1
    return j


# ---- tokenizer/parser for the hol_term constructor syntax
TOK=re.compile(r'\s*(?:(?P<str>"(?:[^"\\]|\\.)*")|(?P<id>[A-Za-z_][A-Za-z0-9_]*)|(?P<p>[(),\[\]]))',re.S)
def tokenize(s):
    pos=0;out=[]
    while True:
        m=TOK.match(s,pos)
        if not m:
            if s[pos:].strip()=='' : break
            raise ValueError('bad token at '+repr(s[pos:pos+30]))
        pos=m.end()
        if m.group('str') is not None: out.append(('s',bytes(m.group('str')[1:-1],'utf-8').decode('unicode_escape')))
        elif m.group('id'): out.append(('i',m.group('id')))
        else: out.append(('p',m.group('p')))
        if pos>=len(s): break
    return out
class P:
    def __init__(s,toks): s.t=toks; s.i=0
    def peek(s): return s.t[s.i] if s.i<len(s.t) else None
    def eat(s,v=None):
        x=s.t[s.i]; s.i+=1
        if v and x[1]!=v: raise ValueError(f'expected {v} got {x}')
        return x
    def node(s):
        k,v=s.eat()
        if k=='s': return ('str',v)
        if k=='i':
            if s.peek()==('p','('):
                s.eat('('); args=[]
                if s.peek()!=('p',')'):
                    while True:
                        args.append(s.node())
                        if s.peek()==('p',','): s.eat(','); continue
                        break
                s.eat(')'); return (v,args)
            return (v,None)
        if v=='[':
            items=[]
            if s.peek()!=('p',']'):
                while True:
                    items.append(s.node())
                    if s.peek()==('p',','): s.eat(','); continue
                    break
            s.eat(']'); return ('list',items)
        raise ValueError(v)
def parse(s):
    p=P(tokenize(s)); n=p.node()
    if p.i!=len(p.t): raise ValueError('trailing')
    return n
# ---- types: ('tv',name) | ('ty',name,(args))
BOOL=('ty','bool',()); 
def fun(a,b): return ('ty','fun',(a,b))
def ty(n):
    k,a=n
    if k in('Tvar','Tyvar'): return ('tv',a[0][1])
    if k=='Fun': return fun(ty(a[0]),ty(a[1]))
    if k=='Bool' : return BOOL
    if k=='Num': return ('ty','num',())
    if k=='Real': return ('ty','real',())
    if k=='Int': return ('ty','int',())
    if k=='Tyapp': return ('ty',a[0][1],tuple(ty(x) for x in a[1][1]))
    raise ValueError('type '+k)
# ---- terms: ('v',n,ty) ('c',n,ty) ('comb',f,x) ('abs',v,b)
def tyof(t):
    if t[0] in('v','c'): return t[2]
    if t[0]=='comb': return tyof(t[1])[2][1]
    if t[0]=='abs': return fun(t[1][2],tyof(t[2]))
def mkc(n,t): return ('c',n,t)
def binop(name,ty_,a,b): return ('comb',('comb',mkc(name,fun(ty_,fun(ty_,BOOL))),a),b)
def term(n,env=()):
    k,a=n
    if k=='Var': return ('v',a[0][1],ty(a[1]))
    if k=='Const': return ('c',a[0][1],ty(a[1]))
    if k=='Comb': return ('comb',term(a[0],env),term(a[1],env))
    if k=='Abs': return ('abs',term(a[0],env),term(a[1],env))
    if k=='Ref':
        nm=a[0][1]
        for (bn,bt) in env:
            if bn==nm: return ('v',bn,bt)
        raise ValueError('unbound Ref '+nm)
    if k in ('Lambda','Forall','Exists','ExistsUnique'):
        nm=a[0][1]; t=ty(a[1]); v=('v',nm,t)
        body=term(a[2],((nm,t),)+env)
        ab=('abs',v,body)
        if k=='Lambda': return ab
        q={'Forall':'!','Exists':'?','ExistsUnique':'?!'}[k]
        return ('comb',mkc(q,fun(fun(t,BOOL),BOOL)),ab)
    if k=='Eq': return binop('=',ty(a[0]),term(a[1],env),term(a[2],env))
    if k in('And','Or','Implies','Iff'):
        return binop({'And':'/\\','Or':'\\/','Implies':'==>','Iff':'='}[k],BOOL,term(a[0],env),term(a[1],env))
    if k=='Not': return ('comb',mkc('~',fun(BOOL,BOOL)),term(a[0],env))
    if k=='True': return mkc('T',BOOL)
    if k=='False': return mkc('F',BOOL)
    if k=='App':
        f=term(a[0],env)
        for x in a[1][1]: f=('comb',f,term(x,env))
        return f
    raise ValueError('term '+k)
def find_calls(src, name='hol_term('):
    i=0
    while True:
        j=src.find(name,i)
        if j<0: return
        if j>0 and (src[j-1].isalnum() or src[j-1] in '_.'): i=j+1; continue
        a0=j+len(name)-1; a1=match_group(src,a0)
        yield j,a1,src[a0+1:a1-1]
        i=a1

IDENT = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*$')
RESERVED = {'var', 'const', 'forall', 'exists', 'exists1', 'fun', 'if', 'as', 'hol', 'hol_type', '_'}
SYMBOL_NAMES = {
    '!': 'forall_c', '?': 'exists_c', '?!': 'exists1_c', '+': 'plus', '-': 'minus', '*': 'times',
    '<': 'lt', '<=': 'le', '>': 'gt', '>=': 'ge', '/\\': 'conj', '\\/': 'disj', '==>': 'imp',
    '=': 'eq', '~': 'neg', ',': 'comma', '$': 'dollar', '..': 'dotdot', '@': 'select',
    '<=_c': 'le_c', '<_c': 'lt_c', '=_c': 'eq_c', '>=_c': 'ge_c', '>_c': 'gt_c', '==': 'eqeq',
    '<<': 'll', '<<<': 'lll', '<<=': 'lle', '_': 'underscore',
}

def valid_ident(n):
    return bool(IDENT.match(n)) and n not in RESERVED

def sanitize(n):
    if n in SYMBOL_NAMES: return SYMBOL_NAMES[n]
    m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)('+)$", n)
    if m:
        k = len(m.group(2))
        return m.group(1) + '_prime' + ('' if k == 1 else str(k))
    s = re.sub(r'[^A-Za-z0-9_]+', '_', n).strip('_').lower()
    if not s or not re.match(r'[A-Za-z_]', s): s = 'v_' + s
    if s in RESERVED: s = s + '_'
    return s

def str_lit(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'

# ---------------------------------------------------------------- types
TYID = re.compile(r'^[A-Z][A-Za-z0-9_]*$')
def show_tyvar(n):
    if TYID.match(n): return n
    if re.match(r'^\?[0-9]+$', n): return '#{' + n + '}'
    return '#{|' + n + '|}'

def show_type(t, left_of_arrow=False):
    if t[0] == 'tv': return show_tyvar(t[1])
    name, args = t[1], t[2]
    if name == 'fun':
        s = show_type(args[0], True) + ' -> ' + show_type(args[1])
        return '(' + s + ')' if left_of_arrow else s
    surface = {'prod': 'pair'}.get(name, name)
    if not args: return surface
    return surface + '(' + ', '.join(show_type(a) for a in args) + ')'

# ---------------------------------------------------------------- surface tree
NUM = ('ty', 'num', ()); INT = ('ty', 'int', ()); REAL = ('ty', 'real', ())
ARITH = {}
for t, names in [(NUM, {'+': '+', '-': '-', '*': '*', '<': '<', '<=': '<=', '>': '>', '>=': '>='}),
                 (INT, {'int_add': '+', 'int_sub': '-', 'int_mul': '*', 'int_lt': '<', 'int_le': '<=', 'int_gt': '>', 'int_ge': '>='}),
                 (REAL, {'real_add': '+', 'real_sub': '-', 'real_mul': '*', 'real_div': '/', 'real_lt': '<', 'real_le': '<=', 'real_gt': '>', 'real_ge': '>='})]:
    for c, op in names.items():
        res = BOOL if op in ('<', '<=', '>', '>=') else t
        ARITH[(c, fun(t, fun(t, res)))] = op
NEG = {('int_neg', fun(INT, INT)), ('real_neg', fun(REAL, REAL))}
INJ = {('int_of_num', fun(NUM, INT)): 'int', ('real_of_num', fun(NUM, REAL)): 'real'}
NUMNUM = fun(NUM, NUM)
LOGIC = {('/\\', fun(BOOL, fun(BOOL, BOOL))): '&&', ('\\/', fun(BOOL, fun(BOOL, BOOL))): '||',
         ('==>', fun(BOOL, fun(BOOL, BOOL))): '==>'}
QUANT = {'!': 'forall', '?': 'exists', '?!': 'exists1'}

def strip_comb(t):
    args = []
    while t[0] == 'comb':
        args.append(t[2]); t = t[1]
    return t, args[::-1]

def numeral_value(t):
    """Value of a canonical NUMERAL bits term, else None."""
    if not (t[0] == 'comb' and t[1] == ('c', 'NUMERAL', NUMNUM)): return None
    def bits(b):
        if b == ('c', '_0', NUM): return 0
        if b[0] == 'comb' and b[1] in (('c', 'BIT0', NUMNUM), ('c', 'BIT1', NUMNUM)):
            v = bits(b[2])
            if v is None: return None
            if v == 0 and b[1][1] == 'BIT0': return None   # non-canonical
            return 2 * v + (1 if b[1][1] == 'BIT1' else 0)
        return None
    return bits(t[2])

class Converter:
    """Phase 1 builds a surface tree whose refs are entities; phase 2 names them."""
    def __init__(self):
        self.next_bid = 0

    def surface(self, t, scope):
        k = t[0]
        if k == 'v':
            for (n, ty), bid in reversed(scope):
                if n == t[1] and ty == t[2]: return ('ref', ('b', bid))
            return ('ref', ('var', t[1], t[2]))
        if k == 'c':
            if t == ('c', 'T', BOOL): return ('truth', True)
            if t == ('c', 'F', BOOL): return ('truth', False)
            return ('ref', ('const', t[1], t[2]))
        if k == 'abs':
            return self.binder('fun', t, scope)
        v = numeral_value(t)
        if v is not None: return ('numeral', v, 'num')
        f, args = strip_comb(t)
        if f[0] == 'c':
            key = (f[1], f[2])
            if len(args) == 1 and key in INJ:
                v = numeral_value(args[0])
                if v is not None: return ('numeral', v, INJ[key])
            if len(args) == 1 and f[1] in QUANT and args[0][0] == 'abs' \
               and f[2] == fun(fun(args[0][1][2], BOOL), BOOL):
                return self.binder(QUANT[f[1]], args[0], scope)
            if len(args) == 2 and key in LOGIC:
                return ('op2', LOGIC[key], self.surface(args[0], scope), self.surface(args[1], scope))
            if len(args) == 2 and f[1] == '=' and f[2][0] == 'ty' and f[2][1] == 'fun' \
               and f[2][2][1] == fun(f[2][2][0], BOOL):
                op = '<=>' if f[2][2][0] == BOOL else '=='
                return ('op2', op, self.surface(args[0], scope), self.surface(args[1], scope))
            if len(args) == 2 and key in ARITH:
                return ('op2', ARITH[key], self.surface(args[0], scope), self.surface(args[1], scope))
            if len(args) == 1 and key in NEG:
                return ('op1', '-', self.surface(args[0], scope))
            if len(args) == 1 and key == ('~', fun(BOOL, BOOL)):
                a = args[0]
                fa, aa = strip_comb(a)
                if fa[0] == 'c' and fa[1] == '=' and len(aa) == 2 and fa[2] == fun(tyof(aa[0]), fun(tyof(aa[0]), BOOL)):
                    return ('op2', '!=', self.surface(aa[0], scope), self.surface(aa[1], scope))
                return ('op1', '!', self.surface(a, scope))
            if len(args) == 3 and f[1] == 'COND':
                T = tyof(args[1])
                if f[2] == fun(BOOL, fun(T, fun(T, T))):
                    return ('if', self.surface(args[0], scope), self.surface(args[1], scope), self.surface(args[2], scope))
        return ('app', self.surface(f, scope), [self.surface(a, scope) for a in args])

    def binder(self, kind, t, scope):
        binds = []
        cur = t
        sc = list(scope)
        while True:
            v = cur[1]; n, ty = v[1], v[2]; body = cur[2]
            bid = self.next_bid; self.next_bid += 1
            binds.append([bid, n, ty])
            sc.append(((n, ty), bid))
            if kind == 'fun' and body[0] == 'abs':
                cur = body; continue
            if kind != 'fun':
                f, args = strip_comb(body)
                if f[0] == 'c' and QUANT.get(f[1]) == kind and len(args) == 1 and args[0][0] == 'abs' \
                   and f[2] == fun(fun(args[0][1][2], BOOL), BOOL):
                    cur = args[0]; continue
            return ['binder', kind, binds, self.surface(body, sc)]

def free_refs(n):
    """Entities referenced in n and not bound inside n."""
    k = n[0]
    if k == 'ref': return {n[1]}
    if k in ('truth', 'numeral'): return set()
    if k == 'app':
        out = free_refs(n[1])
        for a in n[2]: out |= free_refs(a)
        return out
    if k == 'op2': return free_refs(n[2]) | free_refs(n[3])
    if k == 'op1': return free_refs(n[2])
    if k == 'if': return free_refs(n[1]) | free_refs(n[2]) | free_refs(n[3])
    if k == 'binder':
        return free_refs(n[3]) - {('b', b[0]) for b in n[2]}

def assign_names(root):
    """Name global entities and binders; returns (names, decls)."""
    names = {}; decls = []; used = set()
    order = []
    def collect(n):
        k = n[0]
        if k == 'ref':
            if n[1][0] != 'b' and n[1] not in order: order.append(n[1])
        elif k == 'app':
            collect(n[1]); [collect(a) for a in n[2]]
        elif k == 'op2': collect(n[2]); collect(n[3])
        elif k == 'op1': collect(n[2])
        elif k == 'if': collect(n[1]); collect(n[2]); collect(n[3])
        elif k == 'binder': collect(n[3])
    collect(root)
    for ent in sorted(order, key=lambda e: 0 if e[0] == 'var' else 1):
        kind, hn, ty_ = ent
        base = hn if valid_ident(hn) else sanitize(hn)
        s = base; i = 2
        while s in used:
            s = f'{base}_{i}'; i += 1
        used.add(s); names[ent] = s
        decls.append((kind, s, hn, ty_))
    def walk(n):
        k = n[0]
        if k == 'app': walk(n[1]); [walk(a) for a in n[2]]
        elif k == 'op2': walk(n[2]); walk(n[3])
        elif k == 'op1': walk(n[2])
        elif k == 'if': walk(n[1]); walk(n[2]); walk(n[3])
        elif k == 'binder':
            binds = n[2]
            body_free = free_refs(n[3])
            for i, b in enumerate(binds):
                bid, hn, ty_ = b[0], b[1], b[2]
                later = {('b', x[0]) for x in binds[i + 1:]}
                visible = body_free - later - {('b', bid)}
                taken = {names[e] for e in visible if e in names}
                base = hn if valid_ident(hn) else sanitize(hn)
                s = base; j = 2
                while s in taken:
                    s = f'{base}_{j}'; j += 1
                names[('b', bid)] = s
            walk(n[3])
    walk(root)
    return names, decls

# ---------------------------------------------------------------- printing
CLASS = {'*': 'mul', '/': 'mul', '+': 'add', '-': 'add', '<': 'cmp', '<=': 'cmp', '>': 'cmp', '>=': 'cmp',
         '==': 'eqv', '!=': 'eqv', '&&': 'and', '||': 'or', '==>': 'imp', '<=>': 'iff'}
STRONGER = {
    'mul': {'add', 'cmp', 'eqv', 'and', 'or', 'imp', 'iff'},
    'add': {'cmp', 'eqv', 'and', 'or', 'imp', 'iff'},
    'cmp': {'and', 'or', 'imp', 'iff'},
    'eqv': {'and', 'or', 'imp', 'iff'},
    'not': {'and', 'or', 'eqv', 'imp', 'iff'},
    'neg': {'add', 'cmp', 'eqv', 'and', 'or', 'imp', 'iff'},
    'and': {'or', 'imp', 'iff'},
    'or': {'imp', 'iff'},
    'imp': {'iff'},
    'iff': set(),
}
LEFT_ASSOC = {'mul', 'add', 'and', 'or'}

def node_class(n):
    if n[0] == 'op2': return CLASS[n[1]]
    if n[0] == 'op1': return 'not' if n[1] == '!' else 'neg'
    return None

def needs_parens_operand(child, parent_cls, side):
    if child[0] in ('binder', 'if'): return True
    c = node_class(child)
    if c is None: return False
    if parent_cls in STRONGER.get(c, set()): return False
    if c == parent_cls:
        if side == 'left' and c in LEFT_ASSOC: return False
        if side == 'right' and c == 'imp': return False
    return True

WIDTH = 96
NAMES = {}

def binder_head(n):
    kind, binds = n[1], n[2]
    def one(b):
        bid, hol, ty = b
        s = NAMES[('b', bid)]
        return f'{s} :: {show_type(ty)}'
    if kind == 'fun' or len(binds) > 1:
        return f'{kind} (' + ', '.join(one(b) for b in binds) + '):'
    return f'{kind} {one(binds[0])}:'

def inline(n):
    k = n[0]
    if k == 'ref': return NAMES[n[1]]
    if k == 'truth': return '#true' if n[1] else '#false'
    if k == 'numeral': return f'({n[1]} :: {n[2]})'
    if k == 'app':
        f = n[1]
        fs = inline(f) if f[0] in ('ref', 'app') else '(' + inline(f) + ')'
        return fs + '(' + ', '.join(inline(a) for a in n[2]) + ')'
    if k == 'op2':
        c = CLASS[n[1]]
        l = inline(n[2]); r = inline(n[3])
        if needs_parens_operand(n[2], c, 'left'): l = '(' + l + ')'
        if needs_parens_operand(n[3], c, 'right'): r = '(' + r + ')'
        return f'{l} {n[1]} {r}'
    if k == 'op1':
        x = n[2]; xs = inline(x)
        if x[0] in ('op1', 'op2', 'binder', 'if'): xs = '(' + xs + ')'
        return n[1] + xs
    if k == 'binder':
        return binder_head(n) + ' ' + inline(n[3])
    if k == 'if':
        c = n[1]; cs = inline(c)
        if c[0] in ('binder', 'if'): cs = '(' + cs + ')'
        def branch(b):
            bs = inline(b)
            return '(' + bs + ')' if b[0] == 'if' else bs
        return f'if {cs} | {branch(n[2])} | {branch(n[3])}'

def shift(lines, p):
    return [p + lines[0]] + [' ' * len(p) + l for l in lines[1:]]

def paren(lines):
    if len(lines) == 1: return ['(' + lines[0] + ')']
    out = shift(lines, '(')
    out[-1] = out[-1] + ')'
    return out

def fmt(n, indent):
    s = inline(n)
    if indent + len(s) <= WIDTH: return [s]
    k = n[0]
    if k == 'binder':
        return [binder_head(n)] + ['  ' + l for l in fmt(n[3], indent + 2)]
    if k == 'if':
        c = n[1]; cl = fmt(c, indent + 3)
        if c[0] in ('binder', 'if'): cl = paren(cl)
        out = shift(cl, 'if ')
        for br in (n[2], n[3]):
            bl = fmt(br, indent + 2)
            if br[0] == 'if' and len(bl) == 1: bl = paren(bl)
            out += shift(bl, '| ')
        return out
    if k == 'op2':
        # flatten a left-associative run of the same operator class
        c = CLASS[n[1]]
        items = []   # (op, node, side)
        cur = n
        while cur[0] == 'op2' and CLASS[cur[1]] == c and c in LEFT_ASSOC:
            items.append((cur[1], cur[3])); cur = cur[2]
        if items:
            first = cur; items = items[::-1]
        else:
            first = n[2]; items = [(n[1], n[3])]
        def operand(x, side):
            ls = fmt(x, indent + 2)
            # a multi-line operator operand gets its own group, since the
            # continuation lines of one group must share a column
            if needs_parens_operand(x, c, side) or (len(ls) > 1 and x[0] == 'op2'):
                return paren(ls)
            return ls
        out = operand(first, 'left')
        if c == 'imp':
            # right-associative chain
            out = operand(n[2], 'left')
            rest = n[3]
            seq = [('==>', rest)]
            while rest[0] == 'op2' and rest[1] == '==>':
                seq[-1] = ('==>', rest[2]); seq.append(('==>', rest[3])); rest = rest[3]
            for i, (op, x) in enumerate(seq):
                side = 'right' if i == len(seq) - 1 else 'left'
                ls = fmt(x, indent + 2 + len(op) + 1)
                if needs_parens_operand(x, c, side) or (len(ls) > 1 and x[0] == 'op2'): ls = paren(ls)
                out += ['  ' + l for l in shift(ls, op + ' ')]
            return out
        for op, x in items:
            ls = fmt(x, indent + 2 + len(op) + 1)
            if needs_parens_operand(x, c, 'right') or (len(ls) > 1 and x[0] == 'op2'): ls = paren(ls)
            out += ['  ' + l for l in shift(ls, op + ' ')]
        return out
    if k == 'op1':
        x = n[2]; ls = fmt(x, indent + 1)
        if x[0] in ('op1', 'op2', 'binder', 'if'): ls = paren(ls)
        return shift(ls, n[1])
    if k == 'app':
        f = n[1]
        fl = fmt(f, indent) if f[0] in ('ref', 'app') else paren(fmt(f, indent + 1))
        out = list(fl)
        out[-1] = out[-1] + '('
        args = n[2]
        for i, a in enumerate(args):
            al = fmt(a, indent + 2)
            if i < len(args) - 1: al[-1] = al[-1] + ','
            out += ['  ' + l for l in al]
        out.append(')')
        return out
    return [s]

def convert(node):
    """node: parsed hol_term argument. Returns list of lines of a `hol:` or `hol_type:` form."""
    if node[0] in ('Tvar', 'Fun', 'Bool', 'Num', 'Real', 'Int', 'Tyapp', 'Tyvar'):
        return ['hol_type: ' + show_type(ty(node))]
    global NAMES
    t = term(node)
    body = Converter().surface(t, [])
    NAMES, decls = assign_names(body)
    lines = ['hol:']
    for kind, s, n, tyv in decls:
        a = '' if s == n else ' as ' + (n if valid_ident(n) else str_lit(n))
        lines.append(f'  {kind} {s}{a} :: {show_type(tyv)}')
    lines += ['  ' + l for l in fmt(body, 2)]
    return lines

def render_at(node, col, json=False):
    """Replacement text for a hol_term(...) call starting at column col."""
    lines = convert(node)
    if lines[0].startswith('hol_type:'):
        return ('(hol_type_json: ' + lines[0][len('hol_type: '):] + ')') if json else lines[0] if False else (
            '(hol_type_json: ' + lines[0][len('hol_type: '):] + ')' if json else '(' + lines[0] + ')')
    head = '(hol_json:' if json else '(hol:'
    pad = ' ' * (col + 3)
    body = [pad + l[2:] for l in lines[1:]]
    return head + '\n' + '\n'.join(body) + ')'

def replace_all(src):
    """Rewrite every hol_term(...) call in src into hol:/hol_type: forms."""
    out = []; i = 0; n = 0
    for j, a1, arg in find_calls(src):
        node = parse(arg)
        ls = src.rfind('\n', 0, j) + 1
        col = j - ls
        before = src[ls:j]
        after_line = src[a1:src.find('\n', a1) if src.find('\n', a1) >= 0 else len(src)]
        bare = (before.rstrip().endswith('(') and src[a1:a1 + 1] == ')') \
            or (re.match(r'^\s*(def|let)\s+[\w\[\], ]+\s*=\s*$', before) and after_line.strip() == '')
        lines = convert(node)
        # a quote of a single variable or constant, whose body is just the
        # declared name, goes on one line: `hol: var x :: A; x`; it is never
        # longer than the hol_term(Var(...)) call it replaces
        one = 'hol: ' + lines[1][2:] + '; ' + lines[2][2:] if len(lines) == 3 \
            and lines[1].startswith(('  var ', '  const ')) \
            and lines[1].split()[1] == lines[2].strip() else None
        if one and not bare: one = '(' + one + ')'
        if lines[0].startswith('hol_type:'):
            text = lines[0] if bare else '(' + lines[0] + ')'
        elif one:
            text = one
        elif bare:
            # inside the enclosing parentheses, or as a whole definition
            # right-hand side: indent from the paren or the line start
            base = col + 2 if before.rstrip().endswith('(') else len(before) - len(before.lstrip()) + 2
            text = 'hol:\n' + '\n'.join(' ' * base + l[2:] for l in lines[1:])
        else:
            text = '(hol:\n' + '\n'.join(' ' * (col + 3) + l[2:] for l in lines[1:]) + ')'
        out.append(src[i:j]); out.append(text); i = a1; n += 1
    out.append(src[i:])
    return ''.join(out), n


if __name__ == '__main__':
    for path in sys.argv[1:]:
        src = open(path).read()
        new, n = replace_all(src)
        if n:
            open(path, 'w').write(new)
        print(f'{path}: {n} quotation(s)')
