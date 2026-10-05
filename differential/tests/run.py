#!/usr/bin/env python3
"""Run the pinned differential probe. Requires Racket+rhombus-lib and OCaml >=4.14.
RACKET, OCAMLC and OCAML_NATIVE can override executable paths. OCAMLLIB may be set.
"""
import os,subprocess,pathlib,json,sys
p=pathlib.Path(__file__).resolve().parents[1]
(p/'results').mkdir(exist_ok=True)
racket=os.environ.get('RACKET','racket'); ocamlc=os.environ.get('OCAMLC','ocamlc')
def call(*args,**kw):return subprocess.run(args,check=True,**kw)
call(sys.executable,str(p/'tests/prepare_oracle.py'))
call(sys.executable,str(p/'tests/generate_tests.py'))
call(ocamlc,'-w','-8','-c',str(p/'tests/oracle_kernel.ml'))
call(ocamlc,'-w','-8','-I',str(p/'tests'),'-o',str(p/'tests/oracle.byte'),str(p/'tests/oracle_kernel.cmo'),str(p/'tests/oracle_cases.ml'))
runner=os.environ.get('OCAMLRUN')
cmd=[runner,str(p/'tests/oracle.byte')] if runner else [str(p/'tests/oracle.byte')]
with open(p/'results/ocaml.tsv','w') as f:subprocess.run(cmd,check=True,stdout=f)
with open(p/'results/rhombus.tsv','w') as f:call(racket,str(p/'tests/cases.rhm'),stdout=f)
a=(p/'results/ocaml.tsv').read_text().splitlines();b=(p/'results/rhombus.tsv').read_text().splitlines()
expected=json.loads((p/'results/cases.json').read_text())['cases']
if len(a)!=len(expected) or len(b)!=len(expected):raise AssertionError('Missing test output')
bad=[{'id':expected[i],'ocaml':x,'rhombus':y} for i,(x,y) in enumerate(zip(a,b)) if x!=y]
with open(p/'results/privacy.txt','w') as f:call(racket,'reflection.rkt',cwd=p/'tests',stdout=f)
summary={'cases':len(expected),'matched':len(expected)-len(bad),'mismatches':bad,'seed':271828,'privacy_checks':24,'oracle':'all pinned fusion.ml with documented host syntax lowerings'}
(p/'results/summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2));sys.exit(bool(bad))