"""Run generated nested modules to catch inherited binding capture."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/translate'))
from translate import Translator


def main():
    ast = [['module', 'Outer', ['struct', [
        ['value', 'nonrec', [[['var', 'compare'],
            ['fun', ['var', 'x'], ['fun', ['var', 'y'], ['int', '42']]]]]],
        ['module', 'Inner', ['struct', [
            ['value', 'nonrec', [[['var', 'compare'], ['id', 'compare']]]],
            ['module', 'Deeper', ['struct', [
                ['value', 'nonrec', [[['var', 'compare'], ['id', 'compare']]]],
            ]]],
        ]]],
    ]]]]
    code = Translator('scope_test', {}).translate(ast, [])
    code = code.replace('"private/', '"../../rhombus/hol/private/')
    for name in ['fusion', 'basics', 'nets', 'equal', 'bool', 'drule', 'tactics', 'itab', 'simp']:
        code = code.replace('"' + name + '.rhm"', '"../../rhombus/hol/' + name + '.rhm"')
    code += '\ncheck Outer.Inner.compare(1)(2) ~is 42\n'
    code += 'check Outer.Inner.Deeper.compare(3)(4) ~is 42\n'
    path = Path(__file__).with_name('scope_cases.rhm')
    path.write_text(code)
    try:
        result = subprocess.run(['racket', str(path)], capture_output=True, text=True, timeout=60)
        if result.returncode:
            raise RuntimeError(result.stderr)
        print('Inherited binding regression: 2 checks passed')
    finally:
        path.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
