"""Select the original OCaml 4.14 AVL operations required by the theories.

The selection follows dependencies between unchanged AST value groups.
The bundled original sources retain their LGPL 2.1 linking exception.
"""
import json
from pathlib import Path
from translate import names, ROOT, STAGE

APIS = {
    'map': ['empty', 'is_empty', 'singleton', 'cardinal', 'find', 'add',
            'bindings', 'fold', 'filter', 'mem', 'merge', 'remove', 'map', 'exists'],
    'set': ['empty', 'is_empty', 'singleton', 'cardinal', 'elements', 'fold',
            'mem', 'compare', 'add', 'union', 'diff', 'choose', 'equal', 'exists',
            'remove', 'subset', 'inter', 'for_all'],
}

def references(tree):
    if not isinstance(tree, list): return set()
    if tree and tree[0] == 'id': return {tree[1]}
    return set().union(*(references(child) for child in tree))

def select(kind):
    ast = json.loads((STAGE / f'stdlib_{kind}.json').read_text())
    body = next(item[2][2][1] for item in ast if item[:2] == ['module', 'Make'])
    definitions = {name: item for item in body if item[0] == 'value'
                   for pattern, _ in item[2] for name in names(pattern)}
    selected = set(APIS[kind])
    while True:
        expanded = selected | set().union(*(
            references(definitions[name]) & definitions.keys() for name in selected))
        if expanded == selected: break
        selected = expanded
    subset = [item for item in body if item[0] == 'types' or
              (item[0] == 'value' and any(name in selected
                for pattern, _ in item[2] for name in names(pattern)))]
    (STAGE / f'stdlib_{kind}_subset.json').write_text(json.dumps(subset))

def prepare(run):
    for kind in APIS:
        with (STAGE / f'stdlib_{kind}.json').open('w') as out:
            run(['ocamlrun', str(STAGE / 'ast.byte'), 'source-json',
                 str(ROOT / f'tools/translate/stdlib/{kind}.ml')], stdout=out)
        select(kind)
