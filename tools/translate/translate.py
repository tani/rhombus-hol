"""Translate the recorded OCaml AST without changing proof algorithms.

Fail closed for unimplemented syntax and missing quotation records. The
output uses explicit, inferred term/type constructors rather than a parser.
"""
from pathlib import Path
import json, re, sys, os, gzip

ROOT=Path(__file__).resolve().parents[2]
STAGE=Path(os.environ.get('HOL_PORT_STAGE','/tmp/hol-port'))
STAGE.mkdir(parents=True,exist_ok=True)
DATA=ROOT/'tools/translate/data'
def write_changed(path,text):
    text='\n'.join(line.rstrip() for line in text.splitlines())+'\n'
    if not path.exists() or path.read_text()!=text:path.write_text(text)
def read_data(name):
    local=STAGE/name
    if local.exists():return local.read_text()
    with gzip.open(DATA/(name+'.gz'),'rt') as f:return f.read()
CORE=['fusion','basics','nets','equal','bool','drule','tactics','itab','simp']
OPS={'then_':'THEN','thenl_':'THENL','orelse_':'ORELSE',
     'thenc_':'THENC','orelsec_':'ORELSEC','then_tcl_':'THEN_TCL',
     'orelse_tcl_':'ORELSE_TCL','f_f_':'F_F','@':'append',
     'not':'hol_not','!':'ref_get',':=':'ref_set','ref':'Box',
     '=':'hol_equal','<>':'hol_unequal','==':'hol_physical_equal',
     '!=':'hol_physical_unequal','+':'hol_add','-':'hol_sub',
     '*':'hol_mul','/':'hol_div','mod':'hol_mod','~-':'hol_neg',
     '<':'hol_lt','>':'hol_gt','<=':'hol_le','>=':'hol_ge',
     '^':'hol_concat','raise':'hol_raise','fst':'fst','snd':'snd',
     'List.map':'map','List.rev':'rev','List.length':'length',
     'String.length':'hol_string_length','String.get':'hol_string_get',
     'int_of_string':'hol_int_of_string','string_of_int':'hol_string_of_int',
     'compare':'hol_compare','max':'hol_max','min':'hol_min',
     'ignore':'hol_ignore','incr':'hol_incr','decr':'hol_decr',
     '++':'parser_sequence','>>':'parser_map','|||':'parser_choice','--':'hol_range',
     '|->':'fpf_define','Format.print_string':'hol_print_string',
     'Format.print_newline':'hol_print_newline','Format.print_flush':'hol_print_flush'}
OPS.update({'=/':'hol_equal','</':'hol_lt','>/':'hol_gt','<=/':'hol_le','>=/':'hol_ge',
            '+/':'hol_add','-/':'hol_sub','*/':'hol_mul','//':'hol_rat_div',
            'land':'hol_land','lor':'hol_lor','lxor':'hol_lxor','lsl':'hol_lsl','lsr':'hol_lsr',
            'Num.int_of_num':'hol_int_of_num','Char.code':'hol_char_code','Char.chr':'hol_char_chr',
            'String.get':'hol_string_get','String.concat':'hol_string_concat','<>/':'hol_unequal','+.':'hol_add','-.':'hol_sub','*.':'hol_mul','/.':'hol_rat_div'})
OPS['**']='power_num'
OPS['|>']='hol_pipe'
OPS['Lazy.force']='hol_force'
OPS['|=>']='fpf_singleton'
OPS['invalid_arg']='hol_invalid_arg'
OPS['print_endline']='hol_print_endline'
OPS['print_string']='hol_print_string'
OPS['pp_print_string']='OCamlFormat.pp_print_string'
OPS['||']='hol_or'
OPS['&&']='hol_and'
OPS.update({'Array.map':'hol_array_map','Array.of_list':'hol_array_of_list','String.escaped':'hol_string_escaped','Array.make':'hol_array_make','Array.get':'hol_array_get','Array.set':'hol_array_set','Array.fold_left':'hol_array_fold_left',
            'String.make':'hol_string_make','String.sub':'hol_string_sub',
            'Format.printf':'hol_printf','Format.fprintf':'hol_fprintf','Format.std_formatter':'hol_std_formatter',
            'Random.bits':'ocaml_random_bits','Random.int':'ocaml_random_int','Random.init':'ocaml_random_init','lnot':'hol_lnot',
            'int_of_float':'hol_int_of_float','float':'hol_float','float_of_int':'hol_float'})
for fn in ['map','rev','length','concat','exists','filter','find','fold_left','fold_right',
           'for_all','hd','iter','mem','mem_assoc','nth','partition','rev_append','sort','map2','assoc','concat_map','filter_map','fold_left2','fold_right2','mapi','rev_map','for_all2']:
    OPS['List.'+fn]='OCamlList.'+fn

def ind(s,n=2): return '\n'.join(' '*n+l for l in s.splitlines())
def safe(text):
    # An inline 'if' would swallow the enclosing alternatives' bars.
    return '('+text+')' if '\n' not in text and text.startswith('if ') else text
def alt(text):
    # One '|' alternative of an if/match: continuation lines align after the bar.
    first,*rest=safe(text).split('\n')
    return '| '+first+''.join('\n  '+l for l in rest)
def mkif(cond,a,b):
    if all('\n' not in t and ' | ' not in t for t in (cond,a,b)): return '(if '+cond+' | '+a+' | '+b+')'
    return 'if '+cond+'\n'+alt(a)+'\n'+alt(b)
def assign(head,text):
    return head+' = '+text if '\n' not in text else head+':\n'+ind(text)
def ident_safe(s):
    s=s.replace("'",'_prime')
    if s in ['values','def','cond']:s='hol_'+s
    return ''.join(c if c.isalnum() or c in '_.' else '_op'+format(ord(c),'x')+'_' for c in s)
def modalias(n):
    # Namespace under which a translated module is imported by later modules.
    a=''.join(w.capitalize() for w in n.split('_'))
    return 'Hol'+a if a in ['Int','Pair','List','Map','Set','String','Array','Box','Char'] else a
def unalias(a):
    for f in [*CORE,*(q.name.split('.')[0] for q in DATA.glob('*.json.gz'))]:
        if modalias(f)==a:return f
def is_alias(a): return unalias(a) is not None
def string(s): return json.dumps(s,ensure_ascii=False)
def support_names():
    names=set(OPS.values())|{'fun','let','def','if','match','block','try','for','class','import','export','when','unless','cond','values',
        'abs','math','println','print','to_string','max','min','sqrt','floor','ceiling','round','time','sort','error','void','displayln','Num','Char','Bytes','Path','Symbol','Keyword','Number','Boolean','Any','Function','Procedure','compare','error','begin','use','is_a','as','in','with','else','then','do','and','or','not',
        'List','Map','Array','Set','String','Int','Box','Pair','PairList'}
    for f in ['compat','theory_support','type_inference']:
        t=(ROOT/'rhombus/hol/private'/(f+'.rhm')).read_text()
        names|=set(re.findall(r"^(?:def|fun|class)\s+([A-Za-z_][\w']*)",t,re.M))|set(re.findall(r"^  ([A-Za-z_][\w']*)$",t,re.M))
    return names
SUPPORT=support_names()
def source_notice(module):
    path=ROOT/'differential/upstream'/f'{module}.ml'
    if not path.exists():return '// See the bundled upstream source for copyright notices.'
    header=re.match(r'(?:\s*\(\*.*?\*\))*',path.read_text(),re.S)[0]
    return '\n'.join(('// '+line.replace('(*','').replace('*)','').strip()).rstrip()
                     for line in header.splitlines() if line.strip())
def names(p):
    if p[0]=='var': return [p[1]]
    if p[0]=='alias': return names(p[1])+[p[2]]
    if p[0]=='tuple': return sum((names(q) for q in p[1]),[])
    if p[0]=='construct' and p[2] is not None: return names(p[2])
    if p[0]=='or': return names(p[1])
    if p[0]=='record': return sum((names(q) for _,q in p[1]),[])
    return []

def has_letmodule(x):
    if isinstance(x,list):
        return (len(x)>0 and x[0]=='letmodule') or any(has_letmodule(y) for y in x)
    return False

def pure(e):
    if e[0] in ['id','int','float','string','quote','fun','function','labelfun']:return True
    if e[0] in ['tuple','array']:return all(pure(x) for x in e[1])
    if e[0]=='construct':return e[2] is None or pure(e[2])
    if e[0]=='record':return e[2] is None and all(pure(v) for _,v in e[1])
    return False

def alternatives(p):
    from itertools import product
    if p[0]=='or':return alternatives(p[1])+alternatives(p[2])
    if p[0]=='alias':return [['alias',q,p[2]] for q in alternatives(p[1])]
    if p[0]=='tuple':return [['tuple',list(q)] for q in product(*(alternatives(x) for x in p[1]))]
    if p[0]=='construct' and p[2] is not None:return [['construct',p[1],q] for q in alternatives(p[2])]
    if p[0]=='record':return [['record',list(zip([n for n,_ in p[1]],qs))] for qs in product(*(alternatives(x) for _,x in p[1]))]
    return [p]

class Translator:
    def __init__(self,module,quotes):
        self.module=module; self.quotes=quotes; self.counter=0; self.cur=[]; self.fun_names=set(); self.let_names=set(); self.no_natural=False
        self.quote_module=module
        self.bridge=module not in CORE and module!='preterm'
        self.env={}; self.exports={}
        self.record_defs=[]
        self.class_values=set()
        self.module_env={}
        self.top_group={}
        self.reserved_names=set();self.other_reserved=set();self.redefined=set()
        self.used_binding_names=set()
        self.unresolved=set()
        self.namespace_values=set()
        self.versions={}
        self.arities={"Some":1,"Tyvar":1,"Tyapp":2,"Var":2,"Const":2,"Comb":2,"Abs":2}
        self.arities.update({'Fusion.'+n:k for n,k in self.arities.items() if n!='Some'})
        self.modules={};self.module_path=[];self.module_exports={}
    def fresh(self): self.counter+=1; return f'port_tmp_{self.counter}'
    def ident(self,s,env):
        if s in env: return ident_safe(env[s])
        safe=ident_safe(s)
        if safe in env:return ident_safe(env[safe])
        if '.' in s:
            head,rest=s.split('.',1)
            if head in self.module_env:return ident_safe(self.module_env[head]+'.'+rest)
            if head in env:return ident_safe(env[head]+'.'+rest)
        if s in OPS:
            target=OPS[s]
            return ident_safe(s) if target==s else self.ident(target,env)
        if re.fullmatch(r'[A-Za-z_][\w\']*(\.[A-Za-z_][\w\']*)*',s):
            if '.' not in s:self.unresolved.add(s)
            return ident_safe(s)
        raise ValueError(f'{self.module}: unknown operator/path {s}')
    def term(self,t):
        k=t[0]
        if k=='Tyvar': return f'Fusion.mk_vartype({string(t[1])})'
        if k=='Tyapp': return f'Fusion.mk_type([{string(t[1])}, PairList [{", ".join(self.term(x) for x in t[2])}]])'
        if k in ['Var','Const']:
            ctor='mk_var' if k=='Var' else 'mk_mconst'
            namespace='Fusion' if k=='Var' else 'Basics'
            return f'{namespace}.{ctor}([{string(t[1])}, {self.term(t[2])}])'
        if k in ['Comb','Abs']:
            ctor='mk_comb' if k=='Comb' else 'mk_abs'
            return f'Fusion.{ctor}([{self.term(t[1])}, {self.term(t[2])}])'
        raise ValueError(k)
    def pattern(self,p,env):
        k=p[0]
        if k=='any': return '_'
        if k=='var': return ident_safe(env.get(p[1],p[1]))
        if k=='alias': return self.pattern(p[1],env)+' as '+ident_safe(env.get(p[2],p[2]))
        if k in ['int','string']: return p[1] if k=='int' else string(p[1])
        if k=='tuple':
            ps=p[1]
            # OCaml tuples are Rhombus lists (OCaml lists are PairList).
            return '['+', '.join(self.pattern(q,env) for q in ps)+']'
        if k=='construct':
            c,arg=p[1:]
            if c=='[]': return 'PairList []'
            if c=='::': return 'PairList ['+self.pattern(arg[1][0],env)+', & '+self.pattern(arg[1][1],env)+']'
            if c in ['true','false']: return '#'+c
            if c=='()': return '#void'
            c=self.ident(c,env)
            if arg is not None and p[1] in ['Var','Const','Comb','Abs','Tyapp'] and '.' not in p[1] and arg[0]=='tuple' and len(arg[1])==2 and self.arities.get(c,self.arities.get(c.split('.')[-1],2))!=2:
                c='Fusion.'+p[1]
            if arg is None: return c+'()'
            arity=self.arities.get(c,self.arities.get(c.split('.')[-1],1))
            if arg[0]=='any':ps=[arg]*arity
            else:ps=arg[1] if arg[0]=='tuple' and arity!=1 else [arg]
            return c+'('+','.join(self.pattern(q,env) for q in ps)+')'
        if k=='or': return '('+self.pattern(p[1],env)+' || '+self.pattern(p[2],env)+')'
        if k=='record':
            if p[1][0][0]=='contents': return 'Box('+self.pattern(p[1][0][1],env)+')'
            given={n.split('.')[-1]:q for n,q in p[1]}
            cls,layout=self.record_class(given)
            return cls+'('+','.join(self.pattern(given[f],env) if f in given else '_' for f in layout)+')'
        raise ValueError(f'pattern {p}')
    def lines_of(self,e,env):
        # The statements an expression needs, then its value, as a block body.
        stmts,r=self.sub(lambda:self.expr(e,env))
        return '\n'.join(stmts+[r])
    def sub(self,fn):
        saved=self.cur;self.cur=[]
        try:r=fn()
        finally:stmts=self.cur;self.cur=saved
        return stmts,r
    def emit(self,text): self.cur.append(text)
    def hoist(self,text):
        v=self.fresh();self.emit(assign('let '+v,text));return v
    def atom(self,e,env):
        r=self.expr(e,env)
        return self.hoist(r) if '\n' in r else r
    def fun_text(self,name,params,body):
        head='fun'+((' '+ident_safe(name)) if name else '')+'('+params+')'
        return head+': '+body if '\n' not in body else head+':\n'+ind(body)
    def lambda_expr(self,params,body):
        # Anonymous functions are parenthesized inline when short, else a named local function.
        if '\n' not in body: return '('+self.fun_text(None,params,body)+')'
        v=self.fresh();self.emit(self.fun_text(v,params,body));return v
    def function(self,pattern,body,env,name=None):
        new=env.copy()
        for s in names(pattern): new[s]=s
        if len(alternatives(pattern))>1 and names(pattern):
            v=self.fresh()
            return self.fun_text(name,v,self.match(v,[(pattern,None,body)],new,fresh_scope=True))
        params='_' if pattern==['construct','()',None] else self.pattern(pattern,new)
        return self.fun_text(name,params,self.lines_of(body,new))
    def record_class(self,names):
        # OCaml resolves a label set to the latest record type declaring all of them.
        want=set(names)
        exact=[d for d in self.record_defs if set(d[1])==want]
        subset=[d for d in self.record_defs if want<=set(d[1])]
        found=exact or subset
        if not found: raise ValueError(f'{self.module}: no record type for fields {sorted(want)}')
        cls,layout,path=found[-1]
        here=self.module_path
        common=0
        while common<len(path) and common<len(here) and path[common]==here[common]:common+=1
        rest=path[common:] if common<len(path) and not (len(path)<=len(here) and here[:len(path)]==path) else []
        return '.'.join(list(rest)+[cls]),layout
    def local_name(self,s,natural,is_fun=False):
        # Keep OCaml's own name when no other binding can be captured by it. A local fun
        # and another local binding of the same name would clash in one Rhombus block.
        if natural and not self.no_natural and s not in SUPPORT and not s.startswith('port_') and s not in self.fun_names and not (is_fun and s in self.let_names):
            (self.fun_names if is_fun else self.let_names).add(s)
            return ident_safe(s)
        return self.fresh()+'_'+ident_safe(s)
    def binding(self,p,e,env,top=False,recursive=False,single=False):
        ns=names(p); new=env.copy()
        for s in ns:
            base=self.module+'_'+s
            if top:
                if s in self.top_group:new[s]=self.top_group[s]
                else:
                    self.versions[s]=self.versions.get(s,0)+1
                    new[s]=self.internal_binding(s,self.versions[s])
            else:new[s]=env[s] if recursive else self.local_name(s,single)
        scope=new if recursive else env
        if p[0]=='var' and e[0] in ['fun','function'] and (top or recursive):
            if e[0]=='fun':return self.function(e[1],e[2],scope,new[p[1]]),new
            v=self.fresh()
            return self.fun_text(new[p[1]],v,self.match(v,e[1],scope,fresh_scope=True)),new
        keyword='def' if top else 'let'
        value=self.lines_of(e,scope) if top else self.expr(e,scope)
        return assign(keyword+' '+self.pattern(p,new),value),new
    def internal_binding(self,name,version):
        plain=ident_safe(name)
        # Keep the HOL Light name unless it could capture a support or Rhombus binding.
        if not self.module_path and version==1 and plain==name and name not in SUPPORT and name not in self.other_reserved and name not in self.redefined and name not in self.used_binding_names and not name.startswith('port_') and name[0].isalpha():
            self.used_binding_names.add(name)
            return name
        candidate=self.module+'_'+name+('_v'+str(version) if version>1 else '')
        while ident_safe(candidate) in self.reserved_names or ident_safe(candidate) in self.used_binding_names:
            candidate='port_'+candidate
        self.used_binding_names.add(ident_safe(candidate))
        return candidate
    def ordered(self,args,env,fn=None):
        # OCaml evaluates arguments right to left, then the function. Only effectful or
        # multi-line operands are bound to temporaries, and only when order can matter.
        comp=[self.sub(lambda a=a:self.expr(a,env)) for a in args]
        fcomp=self.sub(lambda:self.expr(fn,env)) if fn is not None else None
        cx=[(not pure(a)) or '\n' in c[1] for a,c in zip(args,comp)]
        fcx=fn is not None and ((not pure(fn)) or '\n' in fcomp[1])
        many=sum(cx)>1 or (fcx and any(cx))
        out=[None]*len(args)
        for i in reversed(range(len(args))):
            stmts,r=comp[i]
            self.cur.extend(stmts)
            if cx[i] and (many or '\n' in r): r=self.hoist(r)
            out[i]=r
        if fn is None: return out,None,False
        stmts,fr=fcomp
        self.cur.extend(stmts)
        if fcx and (any(cx) or '\n' in fr): return out,self.hoist(fr),False
        return out,fr,True
    def ordered_constructor(self,ctor,args,env):
        vals,_,_=self.ordered(args,env)
        return '['+', '.join(vals)+']' if ctor=='[]' else ctor+'('+','.join(vals)+')'
    def expr(self,e,env):
        k=e[0]
        if k=='id': return self.ident(e[1],env)
        if k=='int': return e[1]
        if k=='float': return e[1]+'0' if e[1].endswith('.') else e[1]
        if k=='string': return string(e[1])
        if k=='quote':
            key=f'{self.quote_module}:{e[3]}'
            if key not in self.quotes: raise ValueError(f'missing quote {key} {e[2]}')
            encoded=json.dumps(self.quotes[key],ensure_ascii=False,separators=(',',':'))
            return self.ident('expand_quote',env)+'('+string(encoded)+')'
        if k=='tuple':
            es=e[1]
            return self.ordered_constructor('[]',es,env)
        if k=='array': return self.ordered_constructor('Array',e[1],env)
        if k=='construct':
            c,arg=e[1:]
            if c=='[]': return 'PairList []'
            if c=='::': return self.ordered_constructor('PairList.cons',arg[1],env)
            if c in ['true','false']: return '#'+c
            if c=='()': return '#void'
            c=self.ident(c,env)
            if arg is not None and e[1] in ['Var','Const','Comb','Abs','Tyapp'] and '.' not in e[1] and arg[0]=='tuple' and len(arg[1])==2 and self.arities.get(c,self.arities.get(c.split('.')[-1],2))!=2:
                c='Fusion.'+e[1]
            if arg is None: return c+'()'
            es=arg[1] if arg[0]=='tuple' and self.arities.get(c,self.arities.get(c.split('.')[-1],2))!=1 else [arg]
            kernel={'Var':'Fusion.mk_var','Const':'Basics.mk_mconst','Comb':'Fusion.mk_comb',
                    'Abs':'Fusion.mk_abs','Tyvar':'Fusion.mk_vartype','Tyapp':'Fusion.mk_type'}
            if c.startswith('Fusion.') and c.split('.')[-1] in kernel:
                return kernel[c.split('.')[-1]]+'('+(self.ordered_constructor('[]',es,env) if len(es)==2 else self.atom(es[0],env))+')'
            return self.ordered_constructor(c,es,env)
        if k=='apply':
            f,args=e[1:3]
            labels=e[3] if len(e)>3 else ['']*len(args)
            if f[0]=='id' and f[1] in ['&&','||'] and len(args)==2:
                left=self.atom(args[0],env)
                right=self.lines_of(args[1],env)
                if '\n' not in right: return '('+left+' '+f[1]+' '+right+')'
                return mkif(left,right,'#false') if f[1]=='&&' else mkif(left,'#true',right)
            outs,fs,inline_f=self.ordered(args,env,f)
            s=fs
            if inline_f and f[0] not in ['id','apply']: s='('+s+')'
            for arg_index,(a,label) in enumerate(zip(args,labels)):
                if label.startswith('?'):raise ValueError('optional argument forwarding')
                if label:s+='('+label+': '+outs[arg_index]+')';continue
                if a==['construct','()',None]: s=self.ident('hol_apply_unit',env)+'('+s+')'
                else: s+='('+outs[arg_index]+')'
            return s
        if k=='fun':
            new=env.copy()
            pattern=e[1]
            if len(alternatives(pattern))>1 and names(pattern):
                v=self.fresh()
                for n in names(pattern): new[n]=n
                return self.lambda_expr(v,self.match(v,[(pattern,None,e[2])],new,fresh_scope=True))
            for n in names(pattern): new[n]=n
            params='_' if pattern==['construct','()',None] else self.pattern(pattern,new)
            return self.lambda_expr(params,self.lines_of(e[2],new))
        if k=='labelfun':
            if e[2]!='labelled':raise ValueError('optional parameter')
            new=env.copy()
            for n in names(e[4]):new[n]=n
            return self.lambda_expr('~'+e[1]+': '+self.pattern(e[4],new),self.lines_of(e[5],new))
        if k=='function':
            v=self.fresh(); return self.lambda_expr(v,self.match(v,e[1],env,fresh_scope=True))
        if k=='let':
            _,r,bs,body=e; new=env.copy()
            if r=='rec':
                for p,b0 in bs:
                    for s in names(p): new[s]=self.local_name(s,len(bs)==1,b0[0] in ['fun','function'])
            base_env=env.copy()
            for p,b in bs:
                line,bound=self.binding(p,b,new if r=='rec' else base_env,recursive=r=='rec',single=len(bs)==1); self.emit(line)
                new.update({n:bound[n] for n in names(p)})
            return self.expr(body,new)
        if k=='if':
            cond=self.atom(e[1],env)
            then=self.lines_of(e[2],env)
            other='#void' if e[3] is None else self.lines_of(e[3],env)
            return mkif(cond,then,other)
        if k=='match': return self.match(self.atom(e[1],env),e[2],env)
        if k=='try':
            caught=self.fresh()
            cases=e[2]+[(['var',caught],None,['apply',['id','raise'],[['id',caught]]])]
            return 'try:\n'+ind(self.lines_of(e[1],env))+'\n  ~catch '+caught+':\n'+ind(self.match(caught,cases,env,fresh_scope=True),4)
        if k=='seq':
            self.emit(self.expr(e[1],env))
            return self.expr(e[2],env)
        if k=='field':
            base=self.atom(e[1],env)
            if e[1][0] not in ['id','field']: base='('+base+')'
            return base+('.value' if e[2]=='contents' else '.'+ident_safe(e[2].split('.')[-1]))
        if k=='record':
            given={n.split('.')[-1]:v for n,v in e[1]}
            cls,layout=self.record_class(given)
            if e[2] is not None:
                base=self.hoist(self.expr(e[2],env))
            fields=[f for f in layout if f in given]
            # OCaml evaluates the fields right to left, in layout order.
            vals,_,_=self.ordered([given[f] for f in fields],env)
            values=dict(zip(fields,vals))
            if e[2] is None:
                return cls+'('+','.join(values[f] for f in layout)+')'
            return base+'.port_update({'+','.join(string(ident_safe(f))+': '+values[f] for f in fields)+'})'
        if k=='letmodule':
            if e[2][0]=='moduleid':
                alias=e[1]; target=e[2][1]
                body=json.loads(json.dumps(e[3]).replace('"'+alias+'.','"'+target+'.'))
                return self.expr(body,env)
            key='.'.join(self.module_path+[e[1]])
            self.modules[key]=e[2]
            ns=self.module_body(e[1],e[2],env)
            new=env.copy();new[e[1]]=e[1]
            previous=self.module_env.copy();self.module_env[e[1]]=e[1]
            self.emit(ns)
            body=self.expr(e[3],new);self.module_env=previous
            return body
        if k=='lazy':
            return self.ident('hol_lazy',env)+'('+self.lambda_expr('',self.lines_of(e[1],env))+')'
        if k=='while':
            loop=self.fresh()
            cond=self.lines_of(e[1],env)
            body=self.lines_of(e[2],env)
            self.emit(self.fun_text(loop,'','if '+cond+'\n'+alt(body+'\n'+loop+'()')+'\n| #void'))
            return loop+'()'
        if k=='for':
            p,a,b,d,body=e[1:];start=self.fresh();end=self.fresh();loop=self.fresh();new=env.copy()
            for n in names(p):new[n]=n
            v=self.pattern(p,new)
            cond=v+('>' if d=='up' else '<')+end
            step=v+('+1' if d=='up' else '-1')
            self.emit(assign('let '+start,self.expr(a,env)))
            self.emit(assign('let '+end,self.expr(b,env)))
            self.emit(self.fun_text(loop,v,'if '+cond+'\n| #void\n'+alt(self.lines_of(body,new)+'\n'+loop+'('+step+')')))
            return loop+'('+start+')'
        if k=='assert': return mkif(self.atom(e[1],env),'#void','failwith("Assertion failed")')
        raise ValueError(f'{self.module}: unhandled expression {k}')
    def module_body(self,name,m,env):
        if m[0]=='moduleid':
            actual=self.ident(m[1],env)
            key,_=self.resolve_module(m[1])
            newkey='.'.join(self.module_path+[name])
            self.module_exports[newkey]=self.module_exports[key]
            for n in self.module_exports[key]:
                if actual+'.'+n in self.class_values:self.class_values.add(name+'.'+n)
                if actual+'.'+n in self.arities:self.arities[name+'.'+n]=self.arities[actual+'.'+n]
            if '.' in actual and is_alias(actual.split('.')[0]):
                head,rest=actual.split('.',1)
                target='\"'+unalias(head)+'.rhm\".'+rest
            else:target='.'+actual
            return 'import: '+target+' as '+name
        m=self.expand_module(m)
        if m[0]=='stdlib':return self.stdlib_module(name,m[1],m[2])
        if m[0]!='struct': raise ValueError('module '+str(m[:2]))
        child=Translator(self.module+'_'+name,self.quotes)
        child.quote_module=self.quote_module;child.env=env.copy();child.bridge=self.bridge
        child.class_values=self.class_values.copy()
        child.record_defs=self.record_defs
        child.module_env=self.module_env.copy()
        child.unresolved=self.unresolved
        child.modules=self.modules;child.module_exports=self.module_exports;child.arities=self.arities.copy()
        child.module_path=self.module_path+[name]
        body=child.translate(m[1],[],header=False)
        self.module_exports['.'.join(child.module_path)]=list(child.exports)
        for public,internal in child.exports.items():
            if internal in child.class_values:self.class_values.add(name+'.'+public)
        for ctor,n in child.arities.items():
            if ctor in child.exports or ('.' in ctor and ctor.split('.')[0] in child.exports):self.arities[name+'.'+ctor]=n
        exports=('export:\n'+ind('\n'.join(child.export_specs()))+'\n\n') if child.exports else ''
        return 'namespace '+name+':\n'+ind(exports+(body.strip() or 'def module_initialized = #void'))
    def resolve_module(self,path):
        for i in range(len(self.module_path),-1,-1):
            full='.'.join(self.module_path[:i]+[path])
            if full in self.modules:return full,self.modules[full]
        raise ValueError('unknown module '+path)
    def expand_module(self,m):
        if m[0]=='moduleid':return self.expand_module(self.resolve_module(m[1])[1])
        if m[0]!='moduleapply':return m
        f,a=m[1:]
        if f[0]!='moduleid' or a[0]!='moduleid':raise ValueError('non-identifier functor application')
        if f[1] in ['Map.Make','Set.Make']:return ['stdlib',f[1].split('.')[0],a[1]]
        _,fn=self.resolve_module(f[1])
        if fn[0]!='functor':raise ValueError('not a functor '+f[1])
        param,body=fn[1:]
        def sub(x):
            if isinstance(x,list):
                if x and x[0] in ['id','moduleid'] and isinstance(x[1],str) and x[1].startswith(param+'.'):
                    return [x[0],a[1]+x[1][len(param):]]+x[2:]
                if x and x[0]=='moduleid' and x[1]==param:return a
                return [sub(y) for y in x]
            return x
        return sub(body)
    def stdlib_module(self,name,kind,arg):
        # OCaml's AVL shape determines exists/for_all callback order, and the
        # Metis model callbacks consume randomness. Preserve the implementation.
        body=json.loads(read_data('stdlib_'+kind.lower()+'_subset.json'))
        def substitute(x):
            if isinstance(x,list):
                if x==['id','Ord.compare']:return ['id',arg+'.compare']
                return [substitute(y) for y in x]
            return x
        notice='// OCaml 4.14.1 '+kind+'.Make; Copyright 1996 INRIA, Xavier Leroy.\n'
        notice+='// LGPL 2.1 with OCaml linking exception; see tools/translate/stdlib.\n'
        return notice+self.module_body(name,['struct',substitute(body)],self.env)
    def match(self,s,cs,env,fresh_scope=False):
        if fresh_scope:
            stmts,r=self.sub(lambda:self.match(s,cs,env))
            return '\n'.join(stmts+[r])
        if all(g is None for _,g,_ in cs) or re.fullmatch(r"[A-Za-z_][\w']*",s): temp=s
        else:
            temp=self.fresh();self.emit('let '+temp+' = '+s)
        out='match '+temp
        for idx,(p,g,b) in enumerate(cs):
            new=env.copy()
            for n in names(p): new[n]=n
            body=self.lines_of(b,new)
            if g is not None:
                rest=self.match(temp,cs[idx+1:],env,fresh_scope=True) if idx+1<len(cs) else 'failwith("Pattern match failure")'
                gstmts,cond=self.sub(lambda:self.atom(g,new))
                body='\n'.join(gstmts+[mkif(cond,body,rest)])
            for option in alternatives(p):
                head='| '+self.pattern(option,new)
                out+='\n'+(head+': '+safe(body) if '\n' not in body else head+':\n'+ind(body,4))
        return out
    def export_specs(self):
        return [('rename '+ident_safe(internal)+' as '+ident_safe(s)) if internal in self.class_values else ident_safe(s) for s,internal in self.exports.items()]
    def translate(self,ast,deps,header=True):
        self.reserved_names={ident_safe(n) for i in ast if i[0]=='value'
                             for p,_ in i[2] for n in names(p)}
        self.reserved_names.update(ident_safe(i[1]) for i in ast if i[0] in ['module','exception'])
        self.reserved_names.update(ident_safe(self.module+'_ctor_'+c)
          for i in ast if i[0]=='types' for _,cs in i[1] for c,n in cs if isinstance(n,int))
        counts={}
        for i in ast:
            if i[0]=='value':
                for p,_ in i[2]:
                    for n in names(p):counts[n]=counts.get(n,0)+1
        self.redefined={n for n,c in counts.items() if c>1}
        self.other_reserved={ident_safe(i[1]) for i in ast if i[0] in ['module','exception']}
        self.other_reserved.update(c for i in ast if i[0]=='types' for _,cs in i[1] for c,n in cs)
        lines=['#lang rhombus', '// GENERATED FILE - DO NOT EDIT. Regenerate with tools/translate/translate.py.', '// Direct translation of the pinned HOL Light '+self.module+'.ml.',
               source_notice(self.module),
               '// Quotations are expanded offline; every proof is replayed here.',
               'import: "private/compat.rhm" open', 'import: "private/theory_support.rhm" as Host']
        core=CORE[:4] if self.module=='preterm' else (['fusion','basics','equal'] if self.module=='bool' else (CORE[:CORE.index(self.module)] if self.module in CORE else CORE))
        if not header: lines=[]
        else:
            for name in re.search(r'^export:\n((?:[ \t]+[^\n]*\n)+)',(ROOT/'rhombus/hol/private/theory_support.rhm').read_text(),re.M)[1].splitlines():
                name=name.strip()
                if re.fullmatch(r'\w+',name) and name not in OPS:self.env[name]='Host.'+name
            if self.bridge:
                lines.append('import: "private/type_inference.rhm" as TypeInference')
                if self.module=='ind_types':
                    lines.append('import: "private/type_specification.rhm" as NativeTypes')
                    self.env['parse_pretype']='NativeTypes.parse_pretype'
                source=(ROOT/'rhombus/hol/private/type_inference.rhm').read_text()
                for name in re.search(r'^export:\n((?:[ \t]+[^\n]*\n)+)',source,re.M)[1].splitlines():
                    name=name.strip().rsplit(' as ',1)[-1]
                    if re.fullmatch(r'\w+',name):self.env[name]='TypeInference.'+name
                aliases=dict(re.findall(r'\brename (\w+) as (\w+)',source))
                for ctor,args in re.findall(r'^class ([A-Za-z_]\w*)\(([^)]*)\)',source,re.M):
                    self.arities['TypeInference.'+aliases.get(ctor,ctor)]=len(args.split(',')) if args else 0
            for n in dict.fromkeys(core+deps):
                alias=modalias(n)
                lines.append('import: "'+n+'.rhm" as '+alias)
                source=(ROOT/f'rhombus/hol/{n}.rhm').read_text()
                metadata=STAGE/(n+'.namespaces.json')
                if metadata.exists() or (DATA/(n+'.namespaces.json.gz')).exists():
                    for path,namespaces in json.loads(read_data(n+'.namespaces.json')).items():
                        key=alias+'.'+path
                        self.module_exports[key]=namespaces
                        self.modules[key]=['external',key]
                match_exports=re.search(r'^export:\n((?:[ \t]+[^\n]*\n)+)',source,re.M)
                if not match_exports: raise ValueError('missing exports '+n)
                for name in match_exports[1].splitlines():
                    name=name.strip().rsplit(' as ',1)[-1]
                    if re.fullmatch(r'\w+',name) and name not in OPS:self.env[name]=alias+'.'+name
                    if alias+'.'+name in self.modules:self.module_env[name]=alias+'.'+name
                aliases=dict(re.findall(r'\brename (\w+) as (\w+)',source))
                for ctor,args in re.findall(r'^class ([A-Za-z_]\w*)\(([^)]*)\)',source,re.M):
                    self.arities[alias+'.'+aliases.get(ctor,ctor)]=len(args.split(',')) if args else 0
                for name in re.findall(r"^export bind\.macro '([A-Za-z_]\w*)",source,re.M): self.env[name]=alias+'.'+name
        for item in ast:
            if item[0]=='eval':
                e=item[1]
                if e[0]=='apply' and e[1]==['id','needs']: continue
                text=self.lines_of(e,self.env)
                lines.append(text if '\n' not in text else 'def '+self.fresh()+'_eval:\n'+ind(text)); continue
            if item[0]=='value':
                base_env=self.env.copy()
                for p,e in item[2]:
                    for name in names(p):
                        self.versions[name]=self.versions.get(name,0)+1
                        self.top_group[name]=self.internal_binding(name,self.versions[name])
                if item[1]=='rec':self.env.update(self.top_group)
                result_env=self.env.copy()
                for p,e in item[2]:
                    if os.environ.get('HOL_PORT_TRACE'):lines.append('println('+string(self.module+':'+','.join(names(p)))+')')
                    # A local module's exported names must not clash with enclosing local names.
                    self.no_natural=has_letmodule(e)
                    line,bound=self.binding(p,e,self.env if item[1]=='rec' else base_env,top=True,recursive=item[1]=='rec')
                    self.no_natural=False
                    result_env.update({n:bound[n] for n in names(p)})
                    lines.append(line)
                    for s in names(p): self.exports[s]=bound[s]
                self.env=result_env;self.top_group={}
                continue
            if item[0]=='open':
                if len(item)>1:
                    if item[1][0]!='moduleid':raise ValueError('open '+str(item))
                    path=item[1][1]
                    if path=='Format':
                        for n in ['pp_print_string','pp_print_type','print_string','open_vbox','close_box','print_break']:self.env[n]='Host.OCamlFormat.'+n
                    else:
                        actual=self.ident(path,self.env)
                        key,_=self.resolve_module(actual)
                        for n in self.module_exports.get(key,[]):self.env[n]=actual+'.'+ident_safe(n)
                continue
            if item[0]=='exception':
                arity=item[2] if len(item)>2 else 0
                lines.append('class '+item[1]+'('+','.join('field'+str(i) for i in range(arity))+')')
                self.exports[item[1]]=item[1]
                self.env[item[1]]=item[1]
                self.class_values.add(item[1]);self.arities[item[1]]=arity
                continue
            if item[0]=='modtype': continue
            if item[0]=='module':
                key='.'.join(self.module_path+[item[1]])
                self.modules[key]=item[2]
                if item[2][0]=='functor':continue # Specialize each concrete OCaml application.
                lines.append(self.module_body(item[1],item[2],self.env))
                self.namespace_values.add(item[1])
                self.env[item[1]]=item[1]
                self.module_env[item[1]]=item[1]
                self.exports[item[1]]=item[1]
                continue
            if item[0]=='include' and item[1]!=['moduleid','List']:
                name=self.fresh()+'_include'
                lines.append(self.module_body(name,item[1],self.env))
                for n in self.module_exports['.'.join(self.module_path+[name])]:
                    internal=self.module+'_include_'+ident_safe(n)
                    key='.'.join(self.module_path+[name,n])
                    if name+'.'+n in self.class_values:
                        internal=name+'.'+n
                        self.class_values.add(internal)
                    elif key in self.modules:
                        lines.append('import: .'+name+'.'+ident_safe(n)+' as '+internal)
                        self.namespace_values.add(internal)
                    else:lines.append('def '+internal+' = '+name+'.'+ident_safe(n))
                    self.env[n]=internal;self.exports[n]=internal
                continue
            if item[0]=='include' and item[1]==['moduleid','List']:
                std=['map','rev','length','concat','exists','filter','find','fold_left','fold_right',
                     'for_all','hd','iter','mem','mem_assoc','nth','partition','rev_append','sort','map2','assoc','concat_map','filter_map','fold_left2','fold_right2','mapi','rev_map','for_all2']
                for n in std:
                    internal=self.module+'_stdlib_'+n
                    lines.append('def '+internal+' = '+self.ident('OCamlList.'+n,self.env))
                    self.env[n]=internal;self.exports[n]=internal
                continue
            if item[0]=='types':
                fields={'Prover':['conv','augmentor'],'Simpset':['net','prover','provers','rewmaker']}
                for ty,cs in item[1]:
                    counts=[0,0]
                    record_fields=[c for c,n in cs if not isinstance(n,int)]
                    if record_fields:
                        cls=self.module+'_rec_'+ty
                        while ident_safe(cls) in self.used_binding_names or cls in self.reserved_names: cls='port_'+cls
                        self.used_binding_names.add(ident_safe(cls))
                        fs=[ident_safe(f) for f in record_fields]
                        self.record_defs.append((cls,record_fields,tuple(self.module_path)));self.exports[cls]=cls
                        self.class_values.add(cls)
                        lines.append('class '+cls+'('+', '.join(fs)+'):\n  extends '+self.ident('HolVariant',self.env)+'\n  override port_view(): PairList ['+', '.join('this.'+f for f in fs)+']\n  method port_update(updates):\n    '+cls+'('+', '.join('(if updates.has_key('+string(f)+') | updates['+string(f)+'] | this.'+f+')' for f in fs)+')')
                    for ctor,n in cs:
                        if not isinstance(n,int): continue # Host Map carries record labels directly.
                        internal=self.module+'_ctor_'+ctor
                        self.arities[ctor]=n;self.arities[internal]=n
                        self.class_values.add(internal)
                        kind=0 if n==0 else 1;tag=counts[kind];counts[kind]+=1
                        fs=fields.get(ctor,[f'field{i}' for i in range(n)])
                        lines.append('class '+internal+'('+', '.join(fs)+'):\n  extends '+self.ident('HolVariant',self.env)+'\n  override port_view(): ['+str(kind)+', ['+str(tag)+', PairList ['+', '.join('this.'+f for f in fs)+']]]')
                        self.exports[ctor]=internal
                        self.env[ctor]=internal
                continue
            raise ValueError(f'{self.module}: unsupported structure {item[0]}')
        for s,internal in self.exports.items():
            if s!=internal and internal not in self.class_values:
                if internal in self.namespace_values:lines.append('import: .'+ident_safe(internal)+' as '+ident_safe(s))
                else:lines.append('def '+ident_safe(s)+' = '+ident_safe(internal))
        if header: lines.insert(7,'export:\n'+ind('\n'.join(self.export_specs())))
        return '\n\n'.join(lines)+'\n'

def translate_type_support():
    t=Translator('preterm',{})
    text=t.translate(json.loads(read_data('preterm.json')),[])
    text=text.replace('private/compat.rhm','compat.rhm').replace('private/theory_support.rhm','theory_support.rhm')
    for name in CORE[:4]:text=text.replace('\"'+name+'.rhm\"','\"../'+name+'.rhm\"')
    write_changed(ROOT/'rhombus/hol/private/type_inference.rhm',text)

def translate_fpf_support():
    selected={'is_undefined','mapf','foldr','tryapplyd','undefine','combine','choose'}
    ast=json.loads(read_data('lib.json'))
    items=[i for i in ast if i[0]=='value' and
           any(n in selected for p,_ in i[2] for n in names(p))]
    t=Translator('fpf',{});t.bridge=False
    for n in ['raise','equal','unequal','physical_equal','lt','gt','le','add','sub','neg','land','lxor']:
        t.env['hol_'+n]='fpf_'+n
    for n in ['Empty','Leaf','Branch','undefined','foldl','applyd','apply','compare','ocaml_term_hash']:
        t.env[n]=n
    t.env['Hashtbl.hash']='ocaml_term_hash'
    t.arities.update({'Empty':0,'Leaf':2,'Branch':4})
    text=t.translate(items,[],header=False)
    path=ROOT/'rhombus/hol/private/atoms_map.rhm'
    prefix=path.read_text().split('fun fpf_is_undefined(',1)[0]
    # The existing core differential probes require silent imports even when
    # theory initialization tracing is requested.
    output='\n'.join(line for line in (prefix+text).splitlines()
                     if not line.startswith('println("fpf:'))+'\n'
    write_changed(path,output)

def translate(module,deps):
    quotes={}
    sys.path.insert(0,str(ROOT/'differential/tests'))
    from check_foundations import canonical
    for line in read_data('quotes.jsonl').splitlines():
        key,source,t=json.loads(line)
        if key in quotes and quotes[key]!=t:
            old=quotes[key]
            if source=='theorem' or t[0] in ['Tyvar','Tyapp'] or canonical([[],old])!=canonical([[],t]):
                raise ValueError('context-dependent quote '+key)
            continue # Alpha-equivalent binders and renamed inference variables.
        quotes[key]=t
    t=Translator(module,quotes)
    text=t.translate(json.loads(read_data(f'{module}.json')),deps)
    write_changed(ROOT/f'rhombus/hol/{module}.rhm',text)
    (STAGE/(module+'.namespaces.json')).write_text(json.dumps({k:v for k,v in t.module_exports.items() if not is_alias(k.split('.')[0])}))
    (STAGE/(module+'.unresolved.json')).write_text(json.dumps(sorted(t.unresolved)))

if __name__=='__main__':
    translate_type_support()
    translate_fpf_support()
    for i,module in enumerate(sys.argv[1:]): translate(module,sys.argv[1:i+1])
