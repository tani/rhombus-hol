"""Prepare mechanical ASTs and quotation recording using the pinned original.

Camlp5 is only an offline source-reading dependency; generated Rhombus modules
construct HOL terms directly and replay the original proofs.
"""
from pathlib import Path
import os, subprocess, json

ROOT = Path(__file__).resolve().parents[2]
UPSTREAM = Path(os.environ.get('HOL_LIGHT_SOURCE', '/tmp/hol-light-full'))
STAGE = Path(os.environ.get('HOL_PORT_STAGE', '/tmp/hol-port'))
STAGE.mkdir(exist_ok=True)
MODULES = ['bool', 'simp', 'theorems', 'ind_defs', 'class', 'trivia', 'canon', 'meson',
           'firstorder', 'metis', 'thecops', 'quot', 'impconv', 'pair',
           'compute', 'nums', 'recursion', 'arith', 'wf', 'calc_num',
           'normalizer', 'grobner', 'ind_types', 'lists', 'realax',
           'calc_int', 'realarith', 'real', 'calc_rat', 'int', 'sets',
           'iterate', 'cart', 'define']

def run(args, **kw):
    return subprocess.run(args, check=True, text=True, **kw)

def prepare():
    for name in ['fusion', 'basics', 'nets', 'equal', 'drule', 'tactics', 'itab']:
        (ROOT/'differential/upstream'/f'{name}.ml').write_bytes((UPSTREAM/f'{name}.ml').read_bytes())
    run(['ocamlc', '-I', '+compiler-libs', 'ocamlcommon.cma',
         str(ROOT/'tools/translate/ast.ml'), '-o', str(STAGE/'ast.byte')])
    from prepare_stdlib import prepare as prepare_stdlib
    prepare_stdlib(run)
    # Internal type inference and finite partial functions have no quotations.
    # Do not instrument or stage these before the OCaml recorder is loaded.
    for name in ['preterm', 'lib']:
        src=UPSTREAM/f'{name}.ml'
        (ROOT/'differential/upstream'/src.name).write_bytes(src.read_bytes())
        ast=STAGE/f'{name}.ast'
        run([os.environ.get('CAMLP5_RUNNER', 'camlp5r'), '-I',
             os.environ.get('CAMLP5_LIB', subprocess.check_output(['ocamlc','-where'],text=True).strip()+'/camlp5'), '-I', str(UPSTREAM),
             'pa_j.cmo', str(src), '-o', str(ast)], stdout=subprocess.DEVNULL)
        with (STAGE/f'{name}.json').open('w') as out:
            run(['ocamlrun',str(STAGE/'ast.byte'),'json',str(ast)],stdout=out)
    for name in MODULES:
        src=UPSTREAM/f'{name}.ml'
        target=ROOT/'differential/upstream'/src.name
        target.write_bytes(src.read_bytes())
        ast=STAGE/f'{name}.ast'
        run([os.environ.get('CAMLP5_RUNNER', 'camlp5r'), '-I',
             os.environ.get('CAMLP5_LIB', subprocess.check_output(['ocamlc','-where'],text=True).strip()+'/camlp5'), '-I', str(UPSTREAM),
             'pa_j.cmo', str(src), '-o', str(ast)], stdout=subprocess.DEVNULL)
        with (STAGE/f'{name}.ml').open('w') as out:
            run(['ocamlrun',str(STAGE/'ast.byte'),'instrument',str(ast),name],stdout=out)
        with (STAGE/f'{name}.json').open('w') as out:
            run(['ocamlrun',str(STAGE/'ast.byte'),'json',str(ast)],stdout=out)
        from translate import names
        parsed=json.loads((STAGE/f'{name}.json').read_text())
        exports=dict.fromkeys(n for item in parsed if item[0]=='value' for p,_ in item[2] for n in names(p))
        quotations={}
        def collect(node):
            if isinstance(node,list):
                if node and node[0]=='quote': quotations[node[3]]=(node[1],node[2])
                for child in node:collect(child)
        collect(parsed)
        with (STAGE/f'{name}.ml').open('a') as out:
            for exported in exports:
                out.write('record_export '+json.dumps(name+':'+exported)+' '+json.dumps(exported)+';;\n')
            for offset,(kind,source) in quotations.items():
                out.write(('record_unused_term' if kind=='parse_term' else 'record_unused_type')+' '+json.dumps(name+':'+str(offset))+' '+json.dumps(source)+';;\n')
    bootstrap='''#directory "+compiler-libs";;
#directory "+camlp5";;
#directory "+camlp-streams";;
#load "nums.cma";;
#load "camlp_streams.cma";;
#load "camlp5o.cma";;
let loaded = ref [];;
let rec needs s =
 if List.mem s !loaded then () else (
  let staged = Filename.concat STAGE s in
  let file = if Sys.file_exists staged then staged else Filename.concat SOURCE s in
  if not(Toploop.use_silently Format.err_formatter (Toploop.File file)) then failwith ("Load failed: "^s);
  loaded := s :: !loaded);;
let loads = needs;;
let loadt = needs;;
#use BIGNUM;;
#load SYNTAX;;
#use SYSTEM;;
let float_sqrt = sqrt;;
let float_fabs = abs_float;;
needs "parser.ml";;
needs "equal.ml";;
let offline_compose = (o);;
let offline_upto = (--);;
#use RECORDER;;
needs "simp.ml";;
needs "define.ml";;
close_out quote_channel;;
print_endline "QUOTATIONS_COMPLETE";;
'''
    for key,value in {'STAGE':STAGE,'SOURCE':UPSTREAM,'BIGNUM':UPSTREAM/'bignum_num.ml',
                      'SYNTAX':UPSTREAM/'pa_j.cmo','SYSTEM':UPSTREAM/'system.ml',
                      'RECORDER':ROOT/'tools/translate/record_quotes.ml'}.items():
        bootstrap=bootstrap.replace(key,json.dumps(str(value)))
    (STAGE/'bootstrap.ml').write_text(bootstrap)

if __name__=='__main__': prepare()
