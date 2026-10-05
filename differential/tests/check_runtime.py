"""Check OCaml-compatible randomness and effectful partial application order."""
import json, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

def main():
    code = '''#lang rhombus
import: "../../rhombus/hol/private/compat.rhm" open
import: "../../rhombus/hol/private/ocaml_random.rhm" open
ocaml_random_init(0)
for (i in 0 .. 100):« println("random:" +& to_string(ocaml_random_bits())) »
ocaml_random_init(-1)
for (i in 0 .. 100):« println("random:" +& to_string(ocaml_random_int(101))) »
let seen=Box(PairList [])
fun f(x):
  seen.value := PairList.cons(x,seen.value)
  fun(a): x+a
let folded=itlist(f)(PairList [1,2,3])(0)
println("partial_itlist:" +& to_string(seen.value))
seen.value := PairList []
let ended=end_itlist(f)(PairList [1,2,3,4])
println("partial_end_itlist:" +& to_string(seen.value))
'''
    path = Path(__file__).with_name('runtime_cases.rhm')
    path.write_text(code)
    try:
        run = subprocess.run(['racket',str(path)], capture_output=True, text=True, timeout=60)
        if run.returncode: raise RuntimeError(run.stderr)
        lines = run.stdout.splitlines()
        actual = [int(x.split(':',1)[1]) for x in lines if x.startswith('random:')]
        expected = json.loads((ROOT/'differential/upstream/random-4.14.1.json').read_text())
        if actual != expected: raise AssertionError('OCaml random stream mismatch')
        partial = [x for x in lines if x.startswith('partial_')]
        if partial != ['partial_itlist:PairList[1, 2, 3]', 'partial_end_itlist:PairList[1, 2, 3]']:
            raise AssertionError(partial)
        print(json.dumps({'random_values':len(actual),'partial_application_traces':len(partial)}))
    finally:
        path.unlink(missing_ok=True)

if __name__ == '__main__': main()
