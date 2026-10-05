"""Compare every exported theorem with the pinned original OCaml runtime.

Only bound term variables and polymorphic type-variable names are normalized;
free variable names, constants, type constructors, hypotheses, and conclusions
must agree. Loading a module replays all its original proof scripts.
"""
from pathlib import Path
import json, subprocess, sys, os, gzip

ROOT=Path(__file__).resolve().parents[2]
STAGE=Path(os.environ.get('HOL_PORT_STAGE','/tmp/hol-port'))
MODULES=['bool','simp','theorems','ind_defs','class']
if sys.argv[1:]==['--all']:
    sys.path.insert(0,str(ROOT/'tools/translate'))
    from prepare import MODULES
elif len(sys.argv)>1: MODULES=sys.argv[1:]

def canonical(th):
    tyvars={}
    def ty(t):
        if t[0]=='Tyvar':
            if t[1] not in tyvars: tyvars[t[1]]=len(tyvars)
            return ('tv',tyvars[t[1]])
        return ('tc',t[1],tuple(ty(x) for x in t[2]))
    def tm(t,bound=()):
        k=t[0]
        if k=='Var':
            key=(t[1],json.dumps(t[2]))
            if key in bound: return ('bound',bound.index(key),ty(t[2]))
            return ('free',t[1],ty(t[2]))
        if k=='Const': return ('constant',t[1],ty(t[2]))
        if k=='Comb': return ('application',tm(t[1],bound),tm(t[2],bound))
        if k=='Abs':
            v=t[1]; key=(v[1],json.dumps(v[2]))
            return ('lambda',ty(v[2]),tm(t[2],(key,)+bound))
        raise ValueError(k)
    return (tuple(tm(t) for t in th[0]),tm(th[1]))

def main():
    expected={}
    axiom_keys={'class:ETA_AX','class:SELECT_AX','nums:INFINITY_AX'}
    allowed_axioms={}
    path=STAGE/'quotes.jsonl'
    recorded=path.read_text() if path.exists() else gzip.open(ROOT/'tools/translate/data/quotes.jsonl.gz','rt').read()
    for line in recorded.splitlines():
        key,source,value=json.loads(line)
        if source=='theorem' and key in axiom_keys:allowed_axioms[key]=value
        if source=='theorem' and key.split(':')[0] in MODULES: expected[key]=value
    if not expected: raise RuntimeError('No original exported theorem records')
    lines=['#lang rhombus','import: "theory_serialization.rhm" open',
           'import: "../../rhombus/hol/fusion.rhm" as Kernel']
    for i,m in enumerate(MODULES):
        lines.append(f'import: "../../rhombus/hol/{m}.rhm" as Theory{i}')
    for key in expected:
        m,n=key.split(':',1); i=MODULES.index(m)
        safe=n.replace("'",'_prime')
        lines.append(f'emit_theorem({json.dumps(key)},Theory{i}.{safe})')
    lines += ['fun emit_axioms(items,n):', '  match items',
              '  | PairList []: #void', '  | PairList [th,&tail]:',
              '      emit_theorem("kernel_axiom:" +& to_string(n),th)',
              '      emit_axioms(tail,n+1)', 'emit_axioms(Kernel.axioms(),0)']
    generated=ROOT/'differential/tests/foundations_cases.rhm'
    generated.write_text('\n'.join(lines)+'\n')
    result=subprocess.run(['racket',str(generated)],capture_output=True,text=True,
                          timeout=int(os.environ.get('HOL_THEORY_TIMEOUT','120')))
    if result.returncode: raise RuntimeError(result.stderr)
    actual={}
    actual_axioms=[]
    for line in result.stdout.splitlines():
        if '\t' in line:
            key,value=line.split('\t',1)
            if key.startswith('kernel_axiom:'):actual_axioms.append(json.loads(value))
            else:actual[key]=json.loads(value)
    if expected.keys()!=actual.keys(): raise RuntimeError('Theorem record coverage mismatch')
    mismatches=[key for key in expected if canonical(expected[key])!=canonical(actual[key])]
    axiom_names=[]
    for axiom in actual_axioms:
        matches=[key for key,value in allowed_axioms.items() if canonical(value)==canonical(axiom)]
        if len(matches)!=1:raise RuntimeError('Unexpected kernel axiom')
        axiom_names.append(matches[0])
    if len(set(axiom_names))!=len(axiom_names):raise RuntimeError('Duplicate kernel axiom')
    report={'upstream_revision':'cba9198db76e9dfb89cbd653df9412d01f65b22a',
            'theorem_count':len(expected),'per_module':{m:sum(k.startswith(m+':') for k in expected) for m in MODULES},
            'mismatches':mismatches,'axioms':axiom_names,
            'normalization':'bound term names and polymorphic type-variable names'}
    out=ROOT/'differential/results/foundations.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False))
    return bool(mismatches)

if __name__=='__main__': sys.exit(main())
