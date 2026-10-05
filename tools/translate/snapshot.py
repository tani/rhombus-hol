"""Save reproducible AST/quotation inputs and source hashes."""
from pathlib import Path
import gzip, hashlib, json
from prepare import MODULES
from translate import ROOT, STAGE, DATA

def main():
    DATA.mkdir(exist_ok=True)
    files = ['quotes.jsonl', 'preterm.json', 'lib.json',
             'stdlib_map_subset.json', 'stdlib_set_subset.json']
    files += [m+'.json' for m in MODULES]
    files += [m+'.namespaces.json' for m in MODULES if (STAGE/(m+'.namespaces.json')).exists()]
    for name in files:
        content = (STAGE/name).read_bytes()
        (DATA/(name+'.gz')).write_bytes(gzip.compress(content, mtime=0))
    sources = list((ROOT/'differential/upstream').glob('*.ml'))
    sources += list((ROOT/'tools/translate/stdlib').glob('*.ml'))
    manifest = {
        'revision': 'cba9198db76e9dfb89cbd653df9412d01f65b22a',
        'ocaml_version': '4.14.1',
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(sources)},
        'data_sha256': {name: hashlib.sha256((STAGE/name).read_bytes()).hexdigest() for name in files},
    }
    (DATA/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')

if __name__ == '__main__': main()
