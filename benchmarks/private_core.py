#!/usr/bin/env python3
"""Compare private implementations locally, with identical engine differential cases."""
import argparse,json,os,pathlib,shutil,subprocess,time,statistics,hashlib
p=argparse.ArgumentParser();p.add_argument('baseline',type=pathlib.Path);p.add_argument('experiment',type=pathlib.Path);p.add_argument('--output',type=pathlib.Path,default=pathlib.Path('benchmarks/results.json'));a=p.parse_args()
roots={k:v.resolve() for k,v in [('baseline',a.baseline),('experiment',a.experiment)]}
env=dict(os.environ,HOL_ENGINE_ONLY='1');records=[];summaries={}
harness_files=('generate_tests.py','generate_upper_tests.py','run.py','run_upper.py')
harness_digests={}
for name in harness_files:
 digests={label:hashlib.sha256((root/'differential/tests'/name).read_bytes()).hexdigest() for label,root in roots.items()}
 if len(set(digests.values())) != 1:raise SystemExit('Apply the same harness to both checkouts: '+name)
 harness_digests[name]=next(iter(digests.values()))
def round_float(n): return float(f"{n:.4f}")
out=a.output.resolve();out.parent.mkdir(parents=True,exist_ok=True)
def measure(label,phase,round,cmd,cwd):
 log=out.parent/f'{label}-{phase}-{round}.log'
 start=time.monotonic()
 with log.open('w') as f:
  child=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
  _,status,usage=os.wait4(child.pid,0)
  child.returncode=os.waitstatus_to_exitcode(status)
 row=dict(variant=label,phase=phase,round=round,seconds=round_float(time.monotonic()-start),maxrss_kib=usage.ru_maxrss,exit_code=child.returncode)
 records.append(row);print(json.dumps(row),flush=True)
 out.write_text(json.dumps(dict(records=records,summaries=summaries),indent=2))
 return child.returncode
# Compile dependencies shared by both variants once, outside measurements.
for label,root in roots.items():
 if measure(label,'preflight',0,['raco','make','rhombus/hol/equal.rhm'],root):raise SystemExit('preflight failed: '+label)
for round in range(1,4):
 for label,root in roots.items():
  for d in list((root/'rhombus').rglob('compiled')):
   if d.exists():shutil.rmtree(d)
  if measure(label,'cold-compile',round,['raco','make','rhombus/hol/equal.rhm'],root):raise SystemExit('compile failed: '+label)
for label,root in roots.items():
 for suite in ['kernel','upper']:
  script='run.py' if suite=='kernel' else 'run_upper.py'
  measure(label,suite+'-harness',1,['python3','differential/tests/'+script],root)
  summary='summary.json' if suite=='kernel' else 'upper-summary.json'
  summaries[label+'-'+suite]=json.loads((root/'differential/results'/summary).read_text())
 if measure(label,'probe-compile',0,['raco','make','differential/tests/cases.rhm','differential/tests/upper_cases.rhm'],root):raise SystemExit('probe compile failed')
for round in range(1,4):
 for label,root in roots.items():
  for suite,file in [('kernel','cases.rhm'),('upper','upper_cases.rhm')]:
   measure(label,suite+'-warm',round,['racket','differential/tests/'+file],root)
medians={label:{phase:statistics.median(r['seconds'] for r in records if r['variant']==label and r['phase']==phase) for phase in ['cold-compile','kernel-warm','upper-warm']} for label in roots}
report=dict(records=records,summaries=summaries,medians=medians,harness_sha256=harness_digests,refs={k:subprocess.check_output(['git','rev-parse','HEAD'],cwd=v,text=True).strip() for k,v in roots.items()},method='3 cold core compiles; common 1296+2452 differential cases; 3 compiled warm probes. 164 private hash and 2 removed frontend cases excluded. atoms ordering remains exact; no mismatches normalized.',versions={tool:subprocess.check_output([tool,flag],env=env,text=True).strip() for tool,flag in [('racket','--version'),('ocamlc','-version')]})
out.write_text(json.dumps(report,indent=2));print(json.dumps(medians,indent=2),flush=True)
