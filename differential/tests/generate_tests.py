from pathlib import Path
import random,json
p=Path(__file__).resolve().parents[1]; r=random.Random(271828)
# Public constructor API expressions in two languages.
def ty(t,L):
 if t[0]=='v':return ('mk_vartype '+json.dumps(t[1])) if L=='ml' else 'mk_vartype('+json.dumps(t[1])+')'
 if t[0]=='b':return 'bool_ty'
 args=[ty(t[1],L),ty(t[2],L)]
 return 'mk_type("fun",['+';'.join(args)+'])' if L=='ml' else 'mk_type(["fun",PairList ['+','.join(args)+']])'
B=('b',);A=('v','A');C=('v','B');F=lambda a,b:('f',a,b)
def vt(n,t):return ('var',n,t)
def ab(v,b):return ('abs',v,b,F(v[-1],b[-1]))
def ap(f,a):return ('comb',f,a,f[-1][2])
def tm(t,L):
 if t[0]=='var':return ('mk_var('+json.dumps(t[1])+','+ty(t[2],L)+')') if L=='ml' else 'mk_var(['+json.dumps(t[1])+','+ty(t[2],L)+'])'
 f='mk_abs' if t[0]=='abs' else 'mk_comb';a,b=tm(t[1],L),tm(t[2],L)
 return f+'('+a+','+b+')' if L=='ml' else f+'(['+a+','+b+'])'
def gen(t,depth,env=()):
 if depth==0 or r.random()<.4:
  candidates=[x for x in env if x[-1]==t];return r.choice(candidates) if candidates and r.random()<.6 else vt(r.choice(['x','y','z','x\'']),t)
 if t[0]=='f' and r.random()<.6:
  v=vt(r.choice(['x','y','z']),t[1]);return ab(v,gen(t[2],depth-1,env+(v,)))
 at=r.choice([B,A,C]);return ap(gen(F(at,t),depth-1,env),gen(at,depth-1,env))
ml=[];rh=[]
mlhead='''open Oracle_kernel;;
let rec sty = function Tyvar n -> "V("^n^")" | Tyapp(n,a) -> "T("^n^","^String.concat ";" (List.map sty a)^")";;
let rec stm = function Var(n,t) -> "v("^n^","^sty t^")" | Const(n,t) -> "c("^n^","^sty t^")" | Comb(f,a) -> "a("^stm f^","^stm a^")" | Abs(v,b) -> "l("^stm v^","^stm b^")";;
let sl l = String.concat ";" (List.map stm l);;
let sth th = let a,c = dest_thm th in "["^sl a^"]|-"^stm c;;
let sb b = if b then "true" else "false";;
let sn n = string_of_int (if n=0 then 0 else if n<0 then -1 else 1);;
let emit id f = print_endline(id^"\\t"^(try f() with Failure s -> "Failure:"^s));;
'''
rhhead='''#lang rhombus
import: "../../rhombus/hol/fusion.rhm" open
import: "../../rhombus/hol/private/compat.rhm" open
fun sty(t):
  if is_vartype(t)
  | "V(" +& dest_vartype(t) +& ")"
  | let [n,a] = dest_type(t)
    "T(" +& n +& "," +& join(map(sty)(a)) +& ")"
fun join(l):
  match l
  | PairList []: ""
  | PairList [h]: h
  | PairList [h, & t]: h +& ";" +& join(t)
fun stm(t):
  cond
  | is_var(t):
      def [n,ty] = dest_var(t)
      "v(" +& n +& "," +& sty(ty) +& ")"
  | is_const(t):
      def [n,ty] = dest_const(t)
      "c(" +& n +& "," +& sty(ty) +& ")"
  | is_comb(t):
      def [f,a] = dest_comb(t)
      "a(" +& stm(f) +& "," +& stm(a) +& ")"
  | ~else:
      def [v,b] = dest_abs(t)
      "l(" +& stm(v) +& "," +& stm(b) +& ")"
fun sl(l): join(map(stm)(l))
fun sth(th):
  def [a,c] = dest_thm(th)
  "[" +& sl(a) +& "]|-" +& stm(c)
fun sb(b): if b | "true" | "false"
fun sn(n): to_string(if n == 0 | 0 | (if n < 0 | -1 | 1))
fun emit(id,f):
  def value:
    try:
      f()
      ~catch Failure(s): "Failure:" +& s
  println(id +& "\\t" +& value)
'''
cases=[]

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
def add(id,m,h):
 ml.append('emit '+json.dumps(id)+' (fun () -> '+m+');;')
 rh.append('emit('+json.dumps(id)+','+rh_fun(h)+')');cases.append(id)
for i in range(180):
 t=gen(r.choice([B,A,C,F(A,A),F(B,B),F(A,B)]),3);u=gen(t[-1],2)
 for L,out in [('ml',ml),('rhm',rh)]:
  out.append(('let t'+str(i)+' = '+tm(t,L)+';;') if L=='ml' else 'def t'+str(i)+' = '+tm(t,L))
 add(f'frees-{i}',f'sl (frees t{i})',f'sl(frees(t{i}))')
 add(f'identity-vsubst-{i}',f'sb (vsubst [] t{i} == t{i})',f'sb(vsubst(PairList [])(t{i}) === t{i})')
 add(f'alpha-{i}',f'sn (alphaorder t{i} ({tm(u,"ml")}))',f'sn(alphaorder(t{i})({tm(u,"rhm")}))')
 v=vt('x',A);w=vt('y',A)
 add(f'vsubst-{i}',f'stm (vsubst [{tm(w,"ml")},{tm(v,"ml")}] t{i})',f'stm(vsubst(PairList [[{tm(w,"rhm")},{tm(v,"rhm")}]])(t{i}))')
 add(f'inst-{i}',f'stm (inst [bool_ty,aty;bool_ty,bty] t{i})',f'stm(inst(PairList [[bool_ty,aty],[bool_ty,bty]])(t{i}))')
 add(f'REFL-{i}',f'sth (p_REFL t{i})',f'sth(REFL(t{i}))')
 add(f'INST_TYPE-{i}',f'sth (p_INST_TYPE [bool_ty,aty;bool_ty,bty] (p_REFL t{i}))',f'sth(INST_TYPE(PairList [[bool_ty,aty],[bool_ty,bty]])(REFL(t{i})))')
# Directed capture and type-collapse adversaries; exact names are compared.
for i,t in enumerate([ab(vt('y',A),vt('x',A)),ab(vt('x',A),vt('x',C)),ab(vt('x',A),ab(vt('x',C),vt('x',A)))]):
 add(f'capture-{i}',f'stm (vsubst [{tm(vt("y",A),"ml")},{tm(vt("x",A),"ml")}] ({tm(t,"ml")}))',f'stm(vsubst(PairList [[{tm(vt("y",A),"rhm")},{tm(vt("x",A),"rhm")}]])({tm(t,"rhm")}))')
 add(f'collapse-{i}',f'stm (inst [bool_ty,aty;bool_ty,bty] ({tm(t,"ml")}))',f'stm(inst(PairList [[bool_ty,aty],[bool_ty,bty]])({tm(t,"rhm")}))')
# Primitive composition and negative checks.
xm=tm(vt('x',B),'ml');xh=tm(vt('x',B),'rhm');ym=tm(vt('y',B),'ml');yh=tm(vt('y',B),'rhm')
add('ASSUME',f'sth(p_ASSUME ({xm}))',f'sth(ASSUME({xh}))')
add('TRANS',f'sth(p_TRANS (p_REFL ({xm})) (p_REFL ({xm})))',f'sth(TRANS(REFL({xh}))(REFL({xh})))')
add('EQ_MP',f'sth(p_EQ_MP (p_REFL ({xm})) (p_ASSUME ({xm})))',f'sth(EQ_MP(REFL({xh}))(ASSUME({xh})))')
add('DEDUCT',f'sth(p_DEDUCT_ANTISYM_RULE (p_ASSUME ({xm})) (p_ASSUME ({ym})))',f'sth(DEDUCT_ANTISYM_RULE(ASSUME({xh}))(ASSUME({yh})))')
add('ABS',f'sth(p_ABS ({xm}) (p_REFL ({xm})))',f'sth(ABS({xh})(REFL({xh})))')
add('ABS-reject',f'sth(p_ABS ({xm}) (p_ASSUME (mk_eq({xm},{xm}))))',f'sth(ABS({xh})(ASSUME(mk_eq([{xh},{xh}]))))')
for name,m,h in [('bad-arity','mk_type("fun",[])','mk_type(["fun",PairList []])'),('unknown-type','mk_type("unknown",[])','mk_type(["unknown",PairList []])'),('bad-assume','p_ASSUME(mk_var("x",aty))','ASSUME(mk_var(["x",aty]))'),('BETA-reject','p_BETA(mk_comb(mk_abs('+xm+','+xm+'),'+ym+'))','BETA(mk_comb([mk_abs(['+xh+','+xh+']),'+yh+']))')]:
 add(name,'(ignore('+m+');"ok")','do: '+h+'; "ok"')
red=ap(ab(vt('x',B),vt('x',B)),vt('x',B))
add('BETA',f'sth(p_BETA({tm(red,"ml")}))',f'sth(BETA({tm(red,"rhm")}))')
add('MK_COMB',f'sth(p_MK_COMB(p_REFL(mk_abs({xm},{xm})),p_REFL({xm})))',f'sth(MK_COMB([REFL(mk_abs([{xh},{xh}])),REFL({xh})]))')
for nm,m,h in [('qmap','qmap (fun x->x) l == l','qmap(I)(l) === l'),('filter','filter (fun _->true) l == l','filter(fun(_): #true)(l) === l')]:
 ml.append('let l = [aty;bty] in emit "sharing-'+nm+'" (fun () -> sb('+m+'));;')
 rh.append('emit("sharing-'+nm+'",fun():\n  let l = PairList [aty,bty]\n  sb('+h+'))');cases.append('sharing-'+nm)

identity=ab(vt('x',A),vt('x',A)); im=tm(identity,'ml'); ih=tm(identity,'rhm')
add('new_basic_definition',f'sth(new_basic_definition(mk_eq(mk_var("identity",mk_fun_ty aty aty),{im})))',f'sth(new_basic_definition(mk_eq([mk_var(["identity",mk_fun_ty(aty)(aty)]),{ih}])))')
add('new_definition-duplicate',f'sth(new_basic_definition(mk_eq(mk_var("identity",mk_fun_ty aty aty),{im})))',f'sth(new_basic_definition(mk_eq([mk_var(["identity",mk_fun_ty(aty)(aty)]),{ih}])))')
add('new_definition-open',f'sth(new_basic_definition(mk_eq(mk_var("open_def",bool_ty),{xm})))',f'sth(new_basic_definition(mk_eq([mk_var(["open_def",bool_ty]),{xh}])))')
add('new_definition-hidden-type',f'sth(new_basic_definition(mk_eq(mk_var("hidden",bool_ty),mk_eq({im},{im}))))',f'sth(new_basic_definition(mk_eq([mk_var(["hidden",bool_ty]),mk_eq([{ih},{ih}])])))')
add('definitions-state','String.concat "!" (List.map sth (definitions()))','join(map(sth)(definitions()))')
ml.append('new_constant("predicate",mk_fun_ty bool_ty bool_ty);;')
rh.append('new_constant(["predicate",mk_fun_ty(bool_ty)(bool_ty)])')
ml.append('let witness = new_axiom(mk_comb(mk_const("predicate",[]),'+xm+'));;')
rh.append('def witness = new_axiom(mk_comb([mk_const(["predicate",PairList []]),'+xh+']))')
add('new_basic_type_definition','let a,b = new_basic_type_definition "subtype" ("abs_sub","rep_sub") witness in sth a^"!"^sth b','do: def [a,b] = new_basic_type_definition("subtype")(["abs_sub","rep_sub"])(witness); sth(a) +& "!" +& sth(b)')
add('typedef-duplicate','let a,b = new_basic_type_definition "subtype" ("abs_sub","rep_sub") witness in sth a^"!"^sth b','do: def [a,b] = new_basic_type_definition("subtype")(["abs_sub","rep_sub"])(witness); sth(a) +& "!" +& sth(b)')
add('constant-state-order','String.concat ";" (List.map (fun(n,t)->n^":"^sty t) (constants()))','join(map(fun([n,t]): n +& ":" +& sty(t))(constants()))')
add('type-state-order','String.concat ";" (List.map (fun(n,a)->n^":"^string_of_int a) (types()))','join(map(fun([n,a]): n +& ":" +& to_string(a))(types()))')
add('axioms-state','String.concat ";" (List.map sth (axioms()))','join(map(sth)(axioms()))')
add('INST-assumptions',f'sth(p_INST [{ym},{xm}] (p_ASSUME({xm})))',f'sth(INST(PairList [[{yh},{xh}]])(ASSUME({xh})))')
add('bad-subst-list',f'stm(vsubst [{xm},mk_abs({xm},{xm})] ({xm}))',f'stm(vsubst(PairList [[{xh},mk_abs([{xh},{xh}])]])({xh}))')
add('mk_comb-reject',f'stm(mk_comb({xm},{xm}))',f'stm(mk_comb([{xh},{xh}]))')
add('type_subst-first','sty(type_subst [bool_ty,aty;bty,aty] (mk_fun_ty aty bty))','sty(type_subst(PairList [[bool_ty,aty],[bty,aty]])(mk_fun_ty(aty)(bty)))')
add('type_subst-ignore-nonvariable','sty(type_subst [aty,bool_ty] bool_ty)','sty(type_subst(PairList [[aty,bool_ty]])(bool_ty))')
add('type_subst-identity','sb(type_subst [bool_ty,bty] (mk_fun_ty aty aty) == (mk_fun_ty aty aty))','sb(type_subst(PairList [[bool_ty,bty]])(mk_fun_ty(aty)(aty)) === mk_fun_ty(aty)(aty))')
# Identity is tested using the same allocated input, not two distinct constructors.
ml[-1]='let original = mk_fun_ty aty aty in emit "type_subst-identity" (fun () -> sb(type_subst [bool_ty,bty] original == original));;'
rh[-1]='emit("type_subst-identity",fun():\n  let original = mk_fun_ty(aty)(aty)\n  sb(type_subst(PairList [[bool_ty,bty]])(original) === original))'
(p/'tests/oracle_cases.ml').write_text(mlhead+'\n'.join(ml)+'\n')
(p/'tests/cases.rhm').write_text(rhhead+'\n'.join(rh)+'\n')
(p/'results/cases.json').write_text(json.dumps({'seed':271828,'cases':cases,'term_pool':180},indent=2))
print(len(cases),'cases generated')