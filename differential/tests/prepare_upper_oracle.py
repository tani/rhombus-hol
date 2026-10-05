from pathlib import Path
import re,json,runpy
p=Path(__file__).resolve().parents[1]
d=runpy.run_path(str(p/'tests/prepare_oracle.py'));strip=d['strip'];lower=d['lower']
lib=(p/'upstream/lib.ml').read_text()
extra=[]
for n in ['implode','explode']:
 extra.append(strip(re.search(r'let (?:rec )?'+n+r'\b.*?;;',lib,re.S)[0]))
fpf=lib[lib.index("type ('a,'b)func ="):lib.index('let (|=>)')]
fpf=fpf[:fpf.rfind('(* ------------------------------------------------------------------------- *)')]
fpf=strip(fpf).replace('(|->)','fpf_define')
b=strip((p/'upstream/basics.ml').read_text())
repl={'((aconv tm) o snd)':'(compose (aconv tm) snd)','(not o (vfree_in v) o snd)':'(compose not (compose (vfree_in v) snd))','(genvar o type_of)':'(compose genvar type_of)','(union o frees)':'(compose union frees)','(tm |-> ())':'(fpf_define tm ())'}
for a,z in repl.items():b=b.replace(a,z)
n=strip((p/'upstream/nets.ml').read_text())
s=strip((p/'upstream/preterm.ml').read_text());s=re.search(r'let hide_constant,unhide_constant,is_hidden =.*?;;',s,re.S)[0]
e=strip((p/'upstream/equal.ml').read_text());e=e[:e.index('let PRINT_TERM_CONV')]
repl={'rand o rator':'compose rand rator','fst o dest_eq':'compose fst dest_eq','snd o dest_eq':'compose snd dest_eq','(fst o dest_var)':'(compose fst dest_var)','RATOR_CONV o RAND_CONV':'compose RATOR_CONV RAND_CONV','(lhand o concl)':'(compose lhand concl)','(genvar o type_of)':'(compose genvar type_of)','c1 ORELSEC c2':'ORELSEC c1 c2','c1 THENC c2':'THENC c1 c2','((conv THENC (REPEATC conv)) ORELSEC ALL_CONV)':'(ORELSEC (THENC conv (REPEATC conv)) ALL_CONV)','conv ORELSEC ALL_CONV':'ORELSEC conv ALL_CONV','(conv ORELSEC (SUB_QCONV (ONCE_DEPTH_QCONV conv)))':'(ORELSEC conv (SUB_QCONV (ONCE_DEPTH_QCONV conv)))','(RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)':'(THENC (RAND_CONV BETA_CONV) (LAND_CONV BETA_CONV))'}
for a,z in repl.items():e=e.replace(a,z)
# Lower only value tokens in source; never constructor tokens or string literals.
more=['BETA_CONV','AP_TERM','AP_THM','SYM','ALPHA','ALPHA_CONV','GEN_ALPHA_CONV','MK_BINOP','NO_CONV','ALL_CONV','THENC','ORELSEC','FIRST_CONV','EVERY_CONV','REPEATC','CHANGED_CONV','TRY_CONV','RATOR_CONV','RAND_CONV','LAND_CONV','COMB2_CONV','COMB_CONV','ABS_CONV','BINDER_CONV','SUB_CONV','BINOP_CONV','BINOP2_CONV','ONCE_DEPTH_CONV','DEPTH_CONV','REDEPTH_CONV','TOP_DEPTH_CONV','TOP_SWEEP_CONV','THENQC','THENCQC','COMB_QCONV','REPEATQC','SUB_QCONV','ONCE_DEPTH_QCONV','DEPTH_QCONV','REDEPTH_QCONV','TOP_DEPTH_QCONV','TOP_SWEEP_QCONV','DEPTH_BINOP_CONV','PATH_CONV','PAT_CONV','PCONV','SYM_CONV','CONV_RULE','SUBS_CONV','BETA_RULE','GSYM','SUBS','CACHE_CONV','ALPHA_HACK']
names=set(d['names']+more)
def lower_upper(s):
 return re.sub(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z_0-9]*',lambda m:'p_'+m[0] if m[0] in names else m[0],s)
text='include Oracle_kernel;;\ninclude Num;;\nlet num = num_of_int;;\nlet num_0 = num 0 and num_1 = num 1 and num_2 = num 2;;\n'+'\n'.join(extra)+fpf+b+n+s+e
(p/'tests/oracle_upper.ml').write_text(lower_upper(text))
(p/'results/upper-oracle-lowerings.json').write_text(json.dumps({'source_files':['basics.ml','nets.ml','equal.ml','preterm.ml hidden constants','lib.ml strings and original Patricia tree'],'infix_host_syntax':'o/THENC/ORELSEC/|-> lowered to ordinary function applications','uppercase_value_identifiers':sorted(names),'numeric_oracle':'actual Num 1.5 library; original basics.ml numeric code unchanged','excluded':['PRINT_TERM_CONV (printer-dependent display)']},indent=2))