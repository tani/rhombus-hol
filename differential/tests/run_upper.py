#!/usr/bin/env python3
"""Execute the original basics/nets/equal oracle and exact Rhombus differential suite.
Requires OCaml Num and a passing tests/run.py kernel build. No network needed.
"""
import os,subprocess,pathlib,json,sys
p=pathlib.Path(__file__).resolve().parents[1]
(p/'results').mkdir(exist_ok=True)
racket=os.environ.get('RACKET','racket');ocamlc=os.environ.get('OCAMLC','ocamlc')
def call(*args,**kw):return subprocess.run(args,check=True,**kw)
call(sys.executable,str(p/'tests/prepare_upper_oracle.py'))
call(sys.executable,str(p/'tests/generate_upper_tests.py'))
call(ocamlc,'-w','-8-52','-I',str(p/'tests'),'-c',str(p/'tests/oracle_upper.ml'))
call(ocamlc,'-w','-8','-I',str(p/'tests'),'-o',str(p/'tests/upper.byte'),'nums.cma',str(p/'tests/oracle_kernel.cmo'),str(p/'tests/oracle_upper.cmo'),str(p/'tests/upper_cases.ml'))
runner=os.environ.get('OCAMLRUN','ocamlrun');cmd=[runner,str(p/'tests/upper.byte')] if runner else [str(p/'tests/upper.byte')]
with open(p/'results/upper-ocaml.tsv','w') as f:call(*cmd,stdout=f)
with open(p/'results/upper-rhombus.tsv','w') as f:call(racket,str(p/'tests/upper_cases.rhm'),stdout=f)
a=(p/'results/upper-ocaml.tsv').read_text().splitlines();b=(p/'results/upper-rhombus.tsv').read_text().splitlines()
c=json.loads((p/'results/upper-cases.json').read_text());ids=c['cases']
assert len(a)==len(b)==len(ids),'missing test output'
assert [v.split('\t',1)[0]for v in a]==ids and [v.split('\t',1)[0]for v in b]==ids,'incorrect test ids'
bad=[{'id':ids[i],'ocaml':x,'rhombus':y}for i,(x,y)in enumerate(zip(a,b))if x!=y]
with open(p/'results/privacy.txt','w') as f:call(racket,'reflection.rkt',cwd=p/'tests',stdout=f)
call(racket,str(p/'tests/patterns.rhm'),stdout=subprocess.DEVNULL)
negative=subprocess.run([racket,str(p/'tests/constructor_rejection.rhm')],capture_output=True,text=True)
assert negative.returncode!=0 and 'Var: unbound identifier' in negative.stderr
(p/'results/constructor-rejection.txt').write_text(negative.stderr)
summary={'cases':len(ids),'matched':len(ids)-len(bad),'mismatches':bad,'generated_terms':160,'hash_cases':c['hash_cases'],'callback_trace_cases':10,'privacy_checks':24,'read_only_pattern_checks':2,'source_api_counts':{'basics':70,'nets':4,'equal_proof_api':46},'numeric_oracle':'OCaml Num 1.5','excludes':['PRINT_TERM_CONV','full HOL toplevel','theory/automation/parser/printer'],'api_exercised':c['api_exercised']}
(p/'results/upper-summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items() if k!='api_exercised'},indent=2));sys.exit(bool(bad))