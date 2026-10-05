from pathlib import Path
import re,json
base=Path(__file__).resolve().parents[1]
lib=(base/'upstream/lib.ml').read_text()
lib=lib[:lib.index('(* String operations')].rsplit('(* ------------------------------------------------------------------------- *)',1)[0]
# Replace comment blocks first, preserving newline counts; change only host syntax.
strip=lambda s:re.sub(r'\(\*.*?\*\)',lambda m:'\n'*m[0].count('\n'),s,flags=re.S)
lib=strip(lib)
lib=lib.replace('let (o) =','let compose =').replace('((=) 0 o compare x)','(compose ((=) 0) (compare x))')
fusion=strip((base/'upstream/fusion.ml').read_text())
fusion=fusion.replace('union o tyvars','compose union tyvars').replace('union o frees','compose union frees')
names=['I','K','C','W','F_F','REFL','TRANS','MK_COMB','ABS','BETA','ASSUME','EQ_MP','DEDUCT_ANTISYM_RULE','INST_TYPE','INST','P']
def lower(s):
 def token(m):
  t=m[0]; return 'p_'+t if t in names else t
 return re.sub(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z_0-9]*',token,s)
lib=lower(lib);fusion=lower(fusion)
# qmap and rev_assocd are later in lib, outside numeric/system sections.
original=(base/'upstream/lib.ml').read_text()
extra=[]
for n in ['rev_assocd','qmap']:
 m=re.search(r'let rec '+n+r'\b.*?;;',original,re.S);extra.append(strip(m[0]))
(base/'tests/oracle_kernel.ml').write_text('let needs _ = ();;\n'+lib+'\n'+'\n'.join(extra)+'\n'+fusion)
(base/'results/oracle-lowerings.json').write_text(json.dumps({'uppercase_value_identifiers':names,'infix_o_to_compose':['index','tyvars','freesl'],'comments':'removed preserving newline counts','lib':'original nonnumeric prefix plus original rev_assocd and qmap','kernel':'all of original fusion.ml, module signature and abstraction preserved'},indent=2))