"""Run generated nested modules to catch inherited binding capture."""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/translate'))
from translate import Translator


def main():
    ast = [['module', 'Outer', ['struct', [
        ['value', 'nonrec', [[['var', 'identity'], ['fun', ['var', 'x'], ['id', 'x']]]]],
        ['value', 'nonrec', [[['var', "sum'"],
            ['fun', ['var', 'x'], ['fun', ['var', 'y'],
                ['apply', ['id', '+'], [['id', 'x'], ['id', 'y']]]]]]]],
        ['value', 'nonrec', [[['var', 'total'],
            ['apply', ['id', "sum'"], [['int', '20'], ['int', '22']]]]]],
        ['value', 'nonrec', [[['var', 'compare'],
            ['fun', ['var', 'x'], ['fun', ['var', 'y'], ['int', '42']]]]]],
        ['module', 'Inner', ['struct', [
            ['value', 'nonrec', [[['var', 'identity'], ['id', 'identity']]]],
            ['value', 'nonrec', [[['var', 'compare'], ['id', 'compare']]]],
            ['module', 'Deeper', ['struct', [
                ['value', 'nonrec', [[['var', 'compare'], ['id', 'compare']]]],
            ]]],
        ]]],
        ['module', 'Copy', ['struct', [['include', ['moduleid', 'Inner']]]]],
    ]]]]
    code = Translator('scope_test', {}).translate(ast, [])
    code = code.replace('"private/', '"../../rhombus/hol/private/')
    for name in ['fusion', 'basics', 'nets', 'equal', 'bool', 'drule', 'tactics', 'itab', 'simp']:
        code = code.replace('"' + name + '.rhm"', '"../../rhombus/hol/' + name + '.rhm"')
    code += '\ncheck Outer.Inner.compare(1)(2) ~is 42\n'
    code += 'check Outer.Inner.Deeper.compare(3)(4) ~is 42\n'
    code += 'check Outer.sum_prime(20, 22) ~is 42\n'
    code += 'check Outer.total ~is 42\n'
    code += 'check Outer.Inner.identity(42) ~is 42\n'
    code += 'check Outer.Copy.identity(42) ~is 42\n'
    code += 'check Outer.Copy.Deeper.compare(3)(4) ~is 42\n'
    path = Path(__file__).with_name('scope_cases.rhm')
    path.write_text(code)
    try:
        result = subprocess.run(['racket', str(path)], capture_output=True, text=True, timeout=60)
        if result.returncode:
            raise RuntimeError(result.stderr)
        print('Translation regressions: 7 checks passed')
    finally:
        path.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
