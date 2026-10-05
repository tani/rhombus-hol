"""Compare stateful AVL traversal traces recorded with OCaml 4.14.1.

The oracle source is stdlib_order_oracle.ml. This catches changes in traversal
that affect Metis's random model callbacks despite equal set/map contents.
"""
import json, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools/translate'))
from translate import Translator

EXPECTED = {
    'set_exists': '7,2,1,5,3,4,6,9,8,',
    'set_for_all': '7,2,1,5,3,4,6,9,8,',
    'map_exists': '7,2,1,5,3,4,6,9,8,',
    'map_merge': '9,8,7,6,5,4,3,2,1,',
}

def main():
    ast = [
        ['module', 'Cmp', ['struct', [['value', 'nonrec', [[['var','compare'], ['id','compare']]]]]]],
        ['module', 'S', ['moduleapply', ['moduleid','Set.Make'], ['moduleid','Cmp']]],
        ['module', 'M', ['moduleapply', ['moduleid','Map.Make'], ['moduleid','Cmp']]],
    ]
    t = Translator('stdlib_test', {})
    code = t.translate(ast, [])
    code = code.replace('"private/', '"../../rhombus/hol/private/')
    for name in ['fusion','basics','nets','equal','bool','drule','tactics','itab','simp']:
        code = code.replace('"'+name+'.rhm"', '"../../rhombus/hol/'+name+'.rhm"')
    code += '''
let keys=PairList [7,2,9,1,5,8,3,6,4]
let s=rev_itlist(S.add)(keys)(S.empty)
let m=rev_itlist(fun(k): fun(m): M.add(k)(10*k)(m))(keys)(M.empty)
fun trace(name,visit):
  print(name +& ":")
  visit(fun(k): print(k);print(","))
  println("")
trace("set_exists",fun(f): S.exists(fun(k): f(k);#false)(s))
trace("set_for_all",fun(f): S.for_all(fun(k): f(k);#true)(s))
trace("map_exists",fun(f): M.exists(fun(k): fun(_): f(k);#false)(m))
trace("map_merge",fun(f): M.merge(fun(k): fun(x): fun(_): f(k);x)(m)(m))
'''
    path = Path(__file__).with_name('stdlib_cases.rhm')
    path.write_text(code)
    try:
        result = subprocess.run(['racket',str(path)], capture_output=True, text=True, timeout=60)
        if result.returncode: raise RuntimeError(result.stderr)
        actual = dict(line.split(':',1) for line in result.stdout.splitlines()
                      if line.split(':',1)[0] in EXPECTED)
        if actual != EXPECTED: raise AssertionError({'expected':EXPECTED,'actual':actual})
        print(json.dumps({'ocaml_version':'4.14.1','matched_callback_traces':len(EXPECTED)}))
    finally:
        path.unlink(missing_ok=True)

if __name__ == '__main__': main()
