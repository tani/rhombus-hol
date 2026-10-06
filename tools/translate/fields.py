"""Payload names taken from the pinned source declarations and use sites.

Keep positional layout unchanged. Unknown payloads fail generation instead of
silently falling back to numbered fields. Keys with an arity disambiguate
constructors whose payload layout differs between source modules.
"""

FIELDS = {
    'Utv': ['name'], 'Ptycon': ['name', 'arguments'], 'Stv': ['index'],
    'Varp': ['name', 'pretype'], 'Constp': ['name', 'pretype'],
    'Combp': ['operator', 'operand'], 'Absp': ['variable', 'body'],
    'Typing': ['term', 'pretype'],
    'Prover': ['conv', 'augmentor'],
    'Simpset': ['net', 'prover', 'provers', 'rewmaker'],
    'Fvar': ['index'], 'Fnapp': ['symbol', 'arguments'],
    'Atom': ['atom'], 'Conj': ['left', 'right'], 'Disj': ['left', 'right'],
    'Forallq': ['variable', 'body'],
    'Subgoal': ['goal', 'subgoals', 'rule', 'offset', 'local_instances'],
    'Tree': ['node'],
    'Left_to_right_iterator': ['entry', 'right', 'ancestors'],
    'Right_to_left_iterator': ['entry', 'left', 'ancestors'],
    'Map': ['compare_key', 'tree'], 'Set': ['map'],
    'Tr': ['rank', 'value', 'left', 'right'],
    'Heap': ['compare', 'size', 'root'],
    'Var': ['variable'], 'Fn:1': ['application'], 'Fn:2': ['symbol_arity', 'arguments'],
    'Subst:1': ['map'], 'Subst:2': ['substitution', 'theorem'],
    'Not': ['body'], 'And': ['left', 'right'], 'Or': ['left', 'right'],
    'Imp': ['antecedent', 'consequent'], 'Iff': ['left', 'right'],
    'Forall': ['variable', 'body'], 'Exists': ['variable', 'body'],
    'Thm': ['clause', 'inference'], 'Axiom': ['clause'], 'Assume': ['atom'],
    'Resolve': ['atom', 'left', 'right'], 'Refl': ['term'],
    'Equality': ['literal', 'path', 'replacement'],
    'Factor_edge': ['left', 'right'], 'Refl_edge': ['left', 'right'],
    'Joinable': ['substitution'], 'Valuation': ['map'], 'Array_table': ['array'],
    'Model_fn': ['symbol', 'arguments', 'elements'],
    'Function_perturbation': ['application', 'result'],
    'Relation_perturbation': ['application', 'polarity'],
    'Result': ['results'], 'Single': ['term', 'net'], 'Multiple': ['variables', 'functions'],
    'Net': ['parameters', 'size', 'net'], 'Weight': ['symbols', 'constant'],
    'Rewrite': ['rules'], 'Neq_convs': ['conversions'], 'Units': ['net'],
    'Clause': ['info'], 'Active': ['state'], 'Waiting': ['state'], 'Resolution': ['state'],
    'Contradiction': ['theorem'], 'Satisfiable': ['clauses'],
    'Decided': ['decision'], 'Undecided': ['resolution'],
    'Extension:2': ['clause', 'subproofs'],
    'Extension:3': ['clause', 'extension', 'subproofs'],
    'Lit': ['literal'], 'Mat': ['matrix'],
    'Decomposition': ['clause', 'reconstruction', 'subproofs'],
    'Litext': ['surrounding', 'clause'], 'Matext': ['index', 'surrounding', 'path'],
    'Zrator': ['operand', 'stack'], 'Zrand': ['operator', 'stack'],
    'Zabs': ['variable', 'stack'], 'Pvar': ['index'], 'Papp': ['head', 'arguments'],
    'Const': ['constant'], 'Clos': ['closure'], 'Bv': ['index'],
    'Cst': ['constant', 'rewrites'], 'App': ['operator', 'arguments'], 'Abs': ['body'],
    'Conv': ['conversion'], 'Try': ['entry'], 'Need_arg': ['database'],
    'Rw': ['rule'], 'Rws': ['database'], 'Conversion': ['conversion'], 'Rrules': ['theorems'],
    'Start': ['index'], 'Mmul': ['monomial', 'history'], 'Add': ['left', 'right'],
    'Axiom_eq': ['index'], 'Axiom_le': ['index'], 'Axiom_lt': ['index'],
    'Rational_eq': ['rational'], 'Rational_le': ['rational'], 'Rational_lt': ['rational'],
    'Square': ['term'], 'Eqmul': ['multiplier', 'certificate'],
    'Sum': ['left', 'right'], 'Product': ['left', 'right'],
    'Node': ['node'], 'More:4': ['key', 'value', 'right', 'enumeration'],
    'More:3': ['element', 'right', 'enumeration'], 'NotFound': ['left', 'right'],
    'Var_': ['name', 'type'], 'Const_': ['name', 'type', 'term'],
    'Comb_': ['operator', 'operand', 'type'], 'Abs_': ['variable', 'body', 'type'],
    'Vnet': ['index'], 'Lcnet': ['name', 'arity'], 'Cnet': ['name', 'arity'],
    'Lnet': ['arity'], 'Netnode': ['edges', 'tips'],
    'With_context': ['value', 'augment', 'diminish'],
}


def constructor_fields(name, arity):
    if not arity:
        return []
    fields = FIELDS.get(f'{name}:{arity}', FIELDS.get(name))
    if fields is None or len(fields) != arity:
        raise ValueError(f'Missing payload names for {name}/{arity}')
    return fields
