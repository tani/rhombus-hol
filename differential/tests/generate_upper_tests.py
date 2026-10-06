from pathlib import Path
import runpy,json,random,re,os
p=Path(__file__).resolve().parents[1];d=runpy.run_path(str(p/'tests/generate_tests.py'))
ty=d['ty'];tm=d['tm'];B=d['B'];A=d['A'];F=d['F'];vt=d['vt'];ab=d['ab'];ap=d['ap'];gen=d['gen']
ml=[d['mlhead'].replace('Oracle_kernel','Oracle_upper')+'exception Unchanged;;\nlet sint = string_of_int;;\nlet snty l = String.concat ";" (List.map sty l);;\n']
hash_checks = (p.parent/'rhombus/hol/private/term_hash.rhm').exists() and os.environ.get('HOL_ENGINE_ONLY') != '1'
imports = ''.join('import: "../../rhombus/hol/'+name+'" open\n' for name in ['basics.rhm','equal.rhm','nets.rhm'])
if hash_checks:
 imports += 'import: "../../rhombus/hol/private/term_hash.rhm" open\n'
rh=[d['rhhead']+'\n'+imports+'fun sint(n): to_string(n)\nfun snty(l): join(map(sty)(l))\n']

cases=[];coverage=set()

def split_stmts(h):
    parts=[];depth=0;cur='';q=None
    for c in h:
        if q:
            cur+=c
            if c==q:q=None
        elif c in '"\'':q=c;cur+=c
        elif c in '([{':depth+=1;cur+=c
        elif c in ')]}':depth-=1;cur+=c
        elif c==';' and depth==0:parts.append(cur.strip());cur=''
        else:cur+=c
    parts.append(cur.strip());return parts
def rh_fun(h):
    # A Rhombus lambda; "do: a; b" bodies become indented statements.
    if not h.startswith('do: '):return 'fun(): '+h
    st=[('let '+x[4:] if x.startswith('def ') else x) for x in split_stmts(h[4:])]
    return 'fun():\n'+'\n'.join('  '+x for x in st)
def add(i,m,h,api=None):
 ml.append('emit '+json.dumps(i)+' (fun () -> '+m+');;');rh.append(d['rh_emit'](i,rh_fun(h)));cases.append(i)
 if api:coverage.add(api)
def define(n,m,h):ml.append('let '+n+' = '+m+';;');rh.append('def '+n+' = '+h)
def list_(xs,L):return '['+';'.join(xs)+']' if L=='ml' else 'PairList ['+','.join(xs)+']'
def pair(x,y,L):return '('+x+','+y+')' if L=='ml' else '['+x+','+y+']'
# Same environment extension order in both runtimes, without adding axioms.
for n,arity in [('list',1),('num',0),('1',0),('tybit0',1),('tybit1',1)]:
 ml.append(f'new_type({json.dumps(n)},{arity});;');rh.append(f'new_type([{json.dumps(n)},{arity}])')
define('nty','mk_type("num",[])','mk_type(["num",PairList []])')
define('lty','mk_type("list",[aty])','mk_type(["list",PairList [aty]])')
funty=lambda x,y:'mk_fun_ty '+x+' ('+y+')'
funrh=lambda x,y:'mk_fun_ty('+x+')('+y+')'
for n,t in [('/\\',F(B,F(B,B))),('\\/',F(B,F(B,B))),('==>',F(B,F(B,B))),('~',F(B,B)),('!',F(F(A,B),B)),('?',F(F(A,B),B)),('?!',F(F(A,B),B)),('GEQ',F(A,F(A,B))),('GABS',F(F(A,B),A)),('LET',F(F(A,d['C']),F(A,d['C']))),('LET_END',F(A,A))]:
 ml.append('new_constant('+json.dumps(n)+','+ty(t,'ml')+');;');rh.append('new_constant(['+json.dumps(n)+','+ty(t,'rhm')+'])')
for n,m,h in [('CONS',funty('aty',funty('lty','lty')),funrh('aty',funrh('lty','lty'))),('NIL','lty','lty'),('_0','nty','nty'),('BIT0',funty('nty','nty'),funrh('nty','nty')),('BIT1',funty('nty','nty'),funrh('nty','nty')),('NUMERAL',funty('nty','nty'),funrh('nty','nty'))]:
 ml.append('new_constant('+json.dumps(n)+','+m+');;');rh.append('new_constant(['+json.dumps(n)+','+h+'])')
for name,node in [('x',vt('x',B)),('y',vt('y',B)),('z',vt('z',B)),('a',vt('a',A)),('f',vt('f',F(B,B))),('id',ab(vt('x',B),vt('x',B)))]:define(name,tm(node,'ml'),tm(node,'rhm'))
define('red','mk_comb(id,y)','mk_comb([id,y])')
define('nested','mk_comb(mk_abs(x,mk_comb(id,x)),red)','mk_comb([mk_abs([x,mk_comb([id,x])]),red])')
define('op','mk_const('+json.dumps("/\\")+',[])','mk_const(['+json.dumps("/\\")+',PairList []])')
define('form','mk_binop op x (mk_binop op y x)','mk_binop(op)(x)(mk_binop(op)(y)(x))')
# Hash boundaries: meaningful leaf budget, UTF-8, constructor tags, deep queue.
for i in range(160):
 node=gen(random.Random(i).choice([B,A,F(B,B)]),4);define('t'+str(i),tm(node,'ml'),tm(node,'rhm'))
 if hash_checks: add('hash-'+str(i),f'sint (Hashtbl.hash t{i})',f'sint(ocaml_term_hash(t{i}))','hash')
 for name,mm,hh,ser in [('variables',f'variables t{i}',f'variables(t{i})','sl'),('find_terms',f'find_terms is_var t{i}',f'find_terms(is_var)(t{i})','sl'),('find_term',f'find_term is_var t{i}',f'find_term(is_var)(t{i})','stm'),('free_in',f'free_in x t{i}',f'free_in(x)(t{i})','sb'),('strip_comb',f'list_mk_comb(strip_comb t{i})',f'list_mk_comb(strip_comb(t{i}))','stm'),('strip_abs',f'list_mk_abs(strip_abs t{i})',f'list_mk_abs(strip_abs(t{i}))','stm'),('subst',f'subst [y,x] t{i}',f'subst(PairList [[y,x]])(t{i})','stm'),('subst-share',f't{i} == subst [] t{i}',f't{i} === subst(PairList [])(t{i})','sb')]:
  add(name+'-'+str(i),ser+' ('+mm+')',ser+'('+hh+')',name.split('-')[0])
 for cn in ['BETA_CONV','ONCE_DEPTH_CONV','DEPTH_CONV','REDEPTH_CONV','TOP_DEPTH_CONV','TOP_SWEEP_CONV']:
  mm='p_'+cn+(' p_BETA_CONV' if cn!='BETA_CONV' else '');hh=cn+('(BETA_CONV)' if cn!='BETA_CONV' else '')
  add(cn+'-'+str(i),f'sth ({mm} t{i})',f'sth({hh}(t{i}))',cn)
if hash_checks:
 for i,n in enumerate(['λ','日本語','a'*255,'']):
  define('ut'+str(i),'mk_var('+json.dumps(n,ensure_ascii=False)+',bool_ty)','mk_var(['+json.dumps(n,ensure_ascii=False)+',bool_ty])');add('hash-unicode-'+str(i),f'sint(Hashtbl.hash ut{i})',f'sint(ocaml_term_hash(ut{i}))','hash')
# Directed successful and failing syntax operations.
ops=[('dest_fun_ty','snty [fst(dest_fun_ty(type_of id));snd(dest_fun_ty(type_of id))]','snty(PairList [fst(dest_fun_ty(type_of(id))),snd(dest_fun_ty(type_of(id)))])'),('occurs_in','sb(occurs_in bool_ty (type_of id))','sb(occurs_in(bool_ty)(type_of(id)))'),('tysubst','sty(tysubst [bool_ty,aty] (mk_fun_ty aty aty))','sty(tysubst(PairList [[bool_ty,aty]])(mk_fun_ty(aty)(aty)))'),('bndvar','stm(bndvar id)','stm(bndvar(id))'),('body','stm(body id)','stm(body(id))'),('variants','sl(variants [x;y] [x;y;x])','sl(variants(PairList [x,y])(PairList [x,y,x]))'),('alpha','stm(alpha z id)','stm(alpha(z)(id))'),('alpha-fail','stm(alpha x (mk_abs(y,x)))','stm(alpha(x)(mk_abs([y,x])))'),('type_match','snty(map fst (type_match (mk_fun_ty aty aty) (type_of id) []))','snty(map(fst)(type_match(mk_fun_ty(aty)(aty))(type_of(id))(PairList [])))'),('type_match-fail','snty(map fst(type_match(mk_fun_ty aty aty)(mk_fun_ty bool_ty aty)[]))','snty(map(fst)(type_match(mk_fun_ty(aty)(aty))(mk_fun_ty(bool_ty)(aty))(PairList [])))'),('mk_mconst','stm(mk_mconst("=",mk_fun_ty bool_ty (mk_fun_ty bool_ty bool_ty)))','stm(mk_mconst(["=",mk_fun_ty(bool_ty)(mk_fun_ty(bool_ty)(bool_ty))]))'),('mk_icomb','stm(mk_icomb(mk_const("=",[]),x))','stm(mk_icomb([mk_const(["=",PairList []]),x]))'),('list_mk_icomb','stm(list_mk_icomb "=" [x;y])','stm(list_mk_icomb("=")(PairList [x,y]))'),('thm_frees','sl(thm_frees(p_ASSUME form))','sl(thm_frees(ASSUME(form)))'),('make_args','sl(make_args "x" [x] [bool_ty;bool_ty])','sl(make_args("x")(PairList [x])(PairList [bool_ty,bool_ty]))'),('make_args-one','sl(make_args "x" [x] [bool_ty])','sl(make_args("x")(PairList [x])(PairList [bool_ty]))'),('find_path','find_path ((=) y) form','find_path(fun(t): t == y)(form)'),('follow_path','stm(follow_path "rrl" form)','stm(follow_path("rrl")(form))'),('atoms','sl(atoms form)','sl(atoms(form))'),('atoms-fail','sl(atoms a)','sl(atoms(a))')]
for n,m,h in ops:add(n,m,h,n.split('-')[0])
for name,cn in [('conj','/\\'),('disj','\\/'),('imp','==>')]:
 define(name,'mk_binary '+json.dumps(cn)+' (x,y)','mk_binary('+json.dumps(cn)+')([x,y])')
 add('is_'+name,'sb(is_'+name+' '+name+')','sb(is_'+name+'('+name+'))','is_'+name)
 add('dest_'+name,'sl(let l,r=dest_'+name+' '+name+' in [l;r])','do: def [l,r] = dest_'+name+'('+name+'); sl(PairList [l,r])','dest_'+name)
for name,cn in [('forall','!'),('exists','?'),('uexists','?!')]:
 define(name,'mk_binder '+json.dumps(cn)+' (x,conj)','mk_binder('+json.dumps(cn)+')([x,conj])')
 add('is_'+name,'sb(is_'+name+' '+name+')','sb(is_'+name+'('+name+'))','is_'+name)
 add('dest_'+name,'sl(let v,b=dest_'+name+' '+name+' in [v;b])','do: def [v,b] = dest_'+name+'('+name+'); sl(PairList [v,b])','dest_'+name)
 if name!='uexists':add('strip_'+name,'sl(fst(strip_'+name+' '+name+'))','sl(fst(strip_'+name+'('+name+')))','strip_'+name)
for n,m,h in [('is_binary','sb(is_binary "/\\\\" conj)','sb(is_binary("/\\\\")(conj))'),('dest_binary','sl(let l,r=dest_binary "/\\\\" conj in [l;r])','do: def [l,r] = dest_binary("/\\\\")(conj); sl(PairList [l,r])'),('is_binder','sb(is_binder "!" forall)','sb(is_binder("!")(forall))'),('dest_binder','stm(snd(dest_binder "!" forall))','stm(snd(dest_binder("!")(forall)))'),('is_binop','sb(is_binop op form)','sb(is_binop(op)(form))'),('dest_binop','stm(fst(dest_binop op form))','stm(fst(dest_binop(op)(form)))'),('list_mk_binop','stm(list_mk_binop op [x;y;z])','stm(list_mk_binop(op)(PairList [x,y,z]))'),('binops','sl(binops op form)','sl(binops(op)(form))'),('conjuncts','sl(conjuncts form)','sl(conjuncts(form))'),('disjuncts','sl(disjuncts disj)','sl(disjuncts(disj))')]:add(n,m,h,n)
define('neg','mk_comb(mk_const("~",[]),x)','mk_comb([mk_const(["~",PairList []]),x])')
add('is_neg','sb(is_neg neg)','sb(is_neg(neg))','is_neg');add('dest_neg','stm(dest_neg neg)','stm(dest_neg(neg))','dest_neg')
define('lis','list_mk_icomb "CONS" [x;mk_mconst("NIL",mk_type("list",[bool_ty]))]','list_mk_icomb("CONS")(PairList [x,mk_mconst(["NIL",mk_type(["list",PairList [bool_ty]])])])')
for n,m,h in [('is_cons','sb(is_cons lis)','sb(is_cons(lis))'),('dest_cons','stm(fst(dest_cons lis))','stm(fst(dest_cons(lis)))'),('is_list','sb(is_list lis)','sb(is_list(lis))'),('dest_list','sl(dest_list lis)','sl(dest_list(lis))')]:add(n,m,h,n)
define('numeral','list_mk_icomb "NUMERAL" [list_mk_icomb "BIT1" [list_mk_icomb "BIT0" [list_mk_icomb "BIT1" [list_mk_icomb "_0" []]]]]','list_mk_icomb("NUMERAL")(PairList [list_mk_icomb("BIT1")(PairList [list_mk_icomb("BIT0")(PairList [list_mk_icomb("BIT1")(PairList [list_mk_icomb("_0")(PairList [])])])])])')
add('dest_numeral','string_of_num(dest_numeral numeral)','sint(dest_numeral(numeral))','dest_numeral')
for i,n in enumerate([0,1,2,3,16,257,2**150+7]):add('finty-'+str(i),'sty(mk_finty(num_of_string "'+str(n)+'"))','sty(mk_finty('+str(n)+'))','mk_finty');add('finty-round-'+str(i),'string_of_num(dest_finty(mk_finty(num_of_string "'+str(n)+'")))','sint(dest_finty(mk_finty('+str(n)+')))','dest_finty')
add('finty-rational','sty(mk_finty(num_of_string "3/2"))','sty(mk_finty(3/2))','mk_finty')
define('gabs','mk_gabs(mk_comb(f,x),y)','mk_gabs([mk_comb([f,x]),y])')
for n,m,h in [('is_gabs','sb(is_gabs gabs)','sb(is_gabs(gabs))'),('dest_gabs','sl(let a,b=dest_gabs gabs in [a;b])','do: def [a,b] = dest_gabs(gabs); sl(PairList [a,b])'),('list_mk_gabs','stm(list_mk_gabs([x;y],z))','stm(list_mk_gabs([PairList [x,y],z]))'),('strip_gabs','sl(fst(strip_gabs gabs))','sl(fst(strip_gabs(gabs)))')]:add(n,m,h,n)
define('lettm','mk_let([x,y],conj)','mk_let([PairList [[x,y]],conj])');coverage.add('mk_let');coverage.add('mk_gabs')
add('is_let','sb(is_let lettm)','sb(is_let(lettm))','is_let');add('dest_let','stm(snd(dest_let lettm))','stm(snd(dest_let(lettm)))','dest_let')
# Every conversional exercised, including failures, alpha renaming and substitution.
for n,m,h in [('lhand','stm(lhand(mk_eq(x,y)))','stm(lhand(mk_eq([x,y])))'),('lhs','stm(lhs(mk_eq(x,y)))','stm(lhs(mk_eq([x,y])))'),('rhs','stm(rhs(mk_eq(x,y)))','stm(rhs(mk_eq([x,y])))'),('mk_primed_var','stm(mk_primed_var [x] (mk_var("=",bool_ty)))','stm(mk_primed_var(PairList [x])(mk_var(["=",bool_ty])))')]:add(n,m,h,n)
for cn,m,h in [('AP_TERM','p_AP_TERM f (p_REFL x)','AP_TERM(f)(REFL(x))'),('AP_THM','p_AP_THM(p_REFL id)y','AP_THM(REFL(id))(y)'),('SYM','p_SYM(p_BETA_CONV red)','SYM(BETA_CONV(red))'),('ALPHA','p_ALPHA id (mk_abs(z,z))','ALPHA(id)(mk_abs([z,z]))'),('ALPHA_CONV','p_ALPHA_CONV z id','ALPHA_CONV(z)(id)'),('GEN_ALPHA_CONV','p_GEN_ALPHA_CONV z forall','GEN_ALPHA_CONV(z)(forall)'),('MK_BINOP','p_MK_BINOP op (p_REFL x,p_REFL y)','MK_BINOP(op)([REFL(x),REFL(y)])'),('NO_CONV','p_NO_CONV x','NO_CONV(x)'),('ALL_CONV','p_ALL_CONV x','ALL_CONV(x)'),('THENC','p_THENC p_BETA_CONV p_ALL_CONV red','THENC(BETA_CONV)(ALL_CONV)(red)'),('ORELSEC','p_ORELSEC p_NO_CONV p_BETA_CONV red','ORELSEC(NO_CONV)(BETA_CONV)(red)'),('FIRST_CONV','p_FIRST_CONV [p_NO_CONV;p_BETA_CONV] red','FIRST_CONV(PairList [NO_CONV,BETA_CONV])(red)'),('FIRST_CONV-empty','p_FIRST_CONV [] x','FIRST_CONV(PairList [])(x)'),('EVERY_CONV','p_EVERY_CONV [p_BETA_CONV;p_ALL_CONV] red','EVERY_CONV(PairList [BETA_CONV,ALL_CONV])(red)'),('REPEATC','p_REPEATC p_BETA_CONV nested','REPEATC(BETA_CONV)(nested)'),('CHANGED_CONV','p_CHANGED_CONV p_ALL_CONV x','CHANGED_CONV(ALL_CONV)(x)'),('TRY_CONV','p_TRY_CONV p_NO_CONV x','TRY_CONV(NO_CONV)(x)'),('RATOR_CONV','p_RATOR_CONV p_ALL_CONV red','RATOR_CONV(ALL_CONV)(red)'),('RAND_CONV','p_RAND_CONV p_BETA_CONV nested','RAND_CONV(BETA_CONV)(nested)'),('LAND_CONV','p_LAND_CONV p_ALL_CONV form','LAND_CONV(ALL_CONV)(form)'),('COMB2_CONV','p_COMB2_CONV p_ALL_CONV p_BETA_CONV nested','COMB2_CONV(ALL_CONV)(BETA_CONV)(nested)'),('COMB_CONV','p_COMB_CONV p_ALL_CONV red','COMB_CONV(ALL_CONV)(red)'),('ABS_CONV','p_ABS_CONV(p_REDEPTH_CONV p_BETA_CONV)(mk_abs(x,nested))','ABS_CONV(REDEPTH_CONV(BETA_CONV))(mk_abs([x,nested]))'),('BINDER_CONV','p_BINDER_CONV p_ALL_CONV forall','BINDER_CONV(ALL_CONV)(forall)'),('SUB_CONV','p_SUB_CONV p_NO_CONV x','SUB_CONV(NO_CONV)(x)'),('BINOP_CONV','p_BINOP_CONV p_ALL_CONV form','BINOP_CONV(ALL_CONV)(form)'),('BINOP2_CONV','p_BINOP2_CONV p_ALL_CONV p_ALL_CONV form','BINOP2_CONV(ALL_CONV)(ALL_CONV)(form)'),('DEPTH_BINOP_CONV','p_DEPTH_BINOP_CONV op p_ALL_CONV form','DEPTH_BINOP_CONV(op)(ALL_CONV)(form)'),('PATH_CONV','p_PATH_CONV "r" p_BETA_CONV nested','PATH_CONV("r")(BETA_CONV)(nested)'),('PAT_CONV','p_PAT_CONV(mk_abs(x,mk_binop op x y)) p_BETA_CONV (mk_binop op red y)','PAT_CONV(mk_abs([x,mk_binop(op)(x)(y)]))(BETA_CONV)(mk_binop(op)(red)(y))'),('SYM_CONV','p_SYM_CONV(mk_eq(x,y))','SYM_CONV(mk_eq([x,y]))'),('CONV_RULE','p_CONV_RULE(p_REDEPTH_CONV p_BETA_CONV)(p_ASSUME(mk_eq(red,y)))','CONV_RULE(REDEPTH_CONV(BETA_CONV))(ASSUME(mk_eq([red,y])))'),('SUBS_CONV','p_SUBS_CONV [p_BETA_CONV red] (mk_binop op red red)','SUBS_CONV(PairList [BETA_CONV(red)])(mk_binop(op)(red)(red))'),('BETA_RULE','p_BETA_RULE(p_ASSUME(mk_eq(red,y)))','BETA_RULE(ASSUME(mk_eq([red,y])))'),('GSYM','p_GSYM(p_ASSUME(mk_eq(x,y)))','GSYM(ASSUME(mk_eq([x,y])))'),('SUBS','p_SUBS [p_BETA_CONV red] (p_ASSUME(mk_eq(red,y)))','SUBS(PairList [BETA_CONV(red)])(ASSUME(mk_eq([red,y])))')]:add(cn,'sth('+m+')','sth('+h+')',cn.split('-')[0])
# Explicit callback trace: OCaml tuple argument evaluation is right-to-left.
ml.append('let calls = ref [];; let trace t = calls := !calls @ [stm t]; p_REFL t;; let reset() = calls:=[];; let gettrace()=String.concat ";" !calls;;')
rh.append('def mutable calls = PairList []\nfun trace(t):\n  calls := append(calls)(PairList [stm(t)])\n  REFL(t)\nfun reset(): calls := PairList []\nfun gettrace(): join(calls)')
for cn,extra in [('COMB2_CONV',''),('COMB_CONV',''),('BINOP2_CONV',''),('BINOP_CONV',''),('DEPTH_BINOP_CONV','')]:
 args='trace trace' if '2' in cn else ('op trace' if cn=='DEPTH_BINOP_CONV' else 'trace');rargs='(trace)(trace)' if '2' in cn else ('(op)(trace)' if cn=='DEPTH_BINOP_CONV' else '(trace)');target='form' if 'BINOP' in cn else 'red'
 add('trace-'+cn,f'(reset(); ignore(p_{cn} {args} {target}); gettrace())',f'do: reset(); {cn}{rargs}({target}); gettrace()',cn)
# CACHE_CONV preserves successful theorem sharing, adapts alpha, retries Failure.
ml.append('let ccalls=ref 0;; let cached=p_CACHE_CONV(fun t -> incr ccalls; p_REFL t);; let cth=cached id;;')
rh.append('def mutable ccalls = 0\ndef cached = CACHE_CONV(fun(t): ccalls := ccalls+1; REFL(t))\ndef cth = cached(id)')
add('cache-sharing','sb(cached id == cth)','sb(cached(id) === cth)','CACHE_CONV')
add('cache-alpha','sth(cached(mk_abs(z,z)))','sth(cached(mk_abs([z,z])))','CACHE_CONV')
add('cache-count','sint(!ccalls)','sint(ccalls)','CACHE_CONV')
# Net insert/merge order, local variables and non-comparable conversion tips.
ml.append('let n1=enter [] (x,9) (enter [] (form,3) empty_net);; let n2=enter [x] (x,2) (enter [] (form,1) empty_net);;')
rh.append('def n1 = enter(PairList [])([x,9])(enter(PairList [])([form,3])(empty_net))\ndef n2 = enter(PairList [x])([x,2])(enter(PairList [])([form,1])(empty_net))')
for i,t in enumerate(['x','y','form','id','red']):add('net-'+str(i),'String.concat ";"(List.map sint(lookup '+t+' (merge_nets(n1,n2))))','join(map(sint)(lookup('+t+')(merge_nets([n1,n2]))))','nets')
# Assumption-dependent ABS_CONV fallback; the callback is invoked twice.
ml.append('let weaken t = p_EQ_MP(p_DEDUCT_ANTISYM_RULE(p_ASSUME x)(p_REFL t))(p_ASSUME x);;')
rh.append('fun weaken(t): EQ_MP(DEDUCT_ANTISYM_RULE(ASSUME(x))(REFL(t)))(ASSUME(x))')
add('abs-fallback','sth(p_ABS_CONV weaken id)','sth(ABS_CONV(weaken)(id))','ABS_CONV')
for cn in ['RATOR_CONV','RAND_CONV','COMB2_CONV','ABS_CONV','BINDER_CONV','BINOP_CONV','BINOP2_CONV','PATH_CONV','SYM_CONV','ALPHA']:
 args='p_ALL_CONV p_ALL_CONV' if '2' in cn else ('"r" p_ALL_CONV' if cn=='PATH_CONV' else ('x' if cn=='ALPHA' else ('' if cn=='SYM_CONV' else 'p_ALL_CONV')))
 rargs='(ALL_CONV)(ALL_CONV)' if '2' in cn else ('("r")(ALL_CONV)' if cn=='PATH_CONV' else ('(x)' if cn=='ALPHA' else ('' if cn=='SYM_CONV' else '(ALL_CONV)')))
 add('fail-'+cn,'sth(p_'+cn+' '+args+' x)','sth('+cn+rargs+'(x))',cn)
# Malformed proof-producing callback must not bypass kernel checks.
add('THENC-bad','sth(p_THENC p_ALL_CONV (fun _ -> p_REFL y) x)','sth(THENC(ALL_CONV)(fun(t): REFL(y))(x))','THENC')
for cn in ['ONCE_DEPTH_CONV','DEPTH_CONV','REDEPTH_CONV','TOP_DEPTH_CONV','TOP_SWEEP_CONV']:
 ml.append('reset();;');rh.append('reset()')
 add('trace-'+cn,'(ignore(p_'+cn+'(fun t -> ignore(trace t); p_BETA_CONV t) nested);gettrace())','do: '+cn+'(fun(t): trace(t); BETA_CONV(t))(nested); gettrace()',cn)
ml.append('let fcalls=ref 0;; let fc=p_CACHE_CONV(fun _ -> incr fcalls; failwith "cached failure");;')
rh.append('def mutable fcalls = 0\ndef fc = CACHE_CONV(fun(t): fcalls := fcalls+1; failwith("cached failure"))')
for i in range(2):add('cache-fail-'+str(i),'sth(fc x)','sth(fc(x))','CACHE_CONV')
add('cache-failure-count','sint(!fcalls)','sint(fcalls)','CACHE_CONV')
# Merge distinct closure tips without assuming functions support comparison.
ml.append('let funnet=merge_nets(enter [] (x,(fun t -> p_REFL t)) empty_net,enter [] (y,(fun t -> p_REFL t)) empty_net);;')
rh.append('def funnet = merge_nets([enter(PairList [])([x,fun(t): REFL(t)])(empty_net),enter(PairList [])([y,fun(t): REFL(t)])(empty_net)])')
add('net-functions','sint(length(lookup z funnet))','sint(length(lookup(z)(funnet)))','nets')
# Persistent tree rotations and union over many distinct edge keys.
ml.append('let bulk1=ref empty_net and bulk2=ref empty_net;;')
rh.append('def mutable bulk1 = empty_net\ndef mutable bulk2 = empty_net')
for i in range(64):
 n='key'+str(i);define(n,'mk_var("k'+str(i)+'",bool_ty)','mk_var(["k'+str(i)+'",bool_ty])')
 k='bulk1' if i%2==0 else 'bulk2'
 ml.append(k+':=enter ['+n+'] ('+n+','+str(i)+') !'+k+';;')
 rh.append(k+' := enter(PairList ['+n+'])(['+n+','+str(i)+'])('+k+')')
define('bulk','merge_nets(!bulk1,!bulk2)','merge_nets([bulk1,bulk2])')
for i in range(64):add('net-bulk-'+str(i),'String.concat ";"(List.map sint(lookup key'+str(i)+' bulk))','join(map(sint)(lookup(key'+str(i)+')(bulk)))','nets')
add('atoms-bulk','sl(atoms(list_mk_binop op ['+';'.join('key'+str(i) for i in range(64))+']))','sl(atoms(list_mk_binop(op)(PairList ['+','.join('key'+str(i) for i in range(64))+'])))','atoms')
# Narrow Failure handlers must propagate unrelated exceptions.
add('Unchanged','(try ignore(p_ORELSEC(fun _ -> raise Unchanged) p_ALL_CONV x); "swallowed" with Unchanged -> "Unchanged")','try: ORELSEC(fun(t): throw Unchanged())(ALL_CONV)(x); "swallowed"; ~catch Unchanged(): "Unchanged"','ORELSEC')
def rename(s):
 return re.sub(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z_0-9]*',lambda m:'q'+m[0] if m[0] in ['forall','exists'] else m[0],s)
(p/'tests/upper_cases.ml').write_text(rename('\n'.join(ml)));(p/'tests/upper_cases.rhm').write_text(rename('\n'.join(rh)));(p/'results/upper-cases.json').write_text(json.dumps({'cases':cases,'api_exercised':sorted(coverage),'hash_cases':164 if hash_checks else 0},indent=2))
print(len(cases))
