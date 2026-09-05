#!/usr/bin/env python3
"""Turn an idris2 --cg racket executable output into a requireable module.

idris2 --cg racket emits a single #lang racket/base file that wraps every
top-level definition in one big anonymous (let () ...) and then, at the very
end, forces the compiled `main` as a side effect
(`(void (PrimIO-unsafePerformIO Main-main))`) followed by `(collect-garbage)`.
That shape runs fine as a script but exports nothing -- `require` on it sees
an empty module.

This script unwraps the (let () ...) so every definition becomes a top-level
module definition, adds `(provide (all-defined-out))`, and drops the
`Main-main`-forcing line so requiring the module has no side effect. The
result is an ordinary #lang racket/base module whose Idris-level top-level
names (Kernel-reflR, Term-mkVar, HType-boolTy, ...) are just Racket
identifiers, callable directly -- no serialization, no subprocess boundary.

Usage: libify.py <generated-kernel.rkt> <output-lib.rkt>
"""
import re
import sys


def libify(src_path: str, dst_path: str) -> None:
    lines = open(src_path).read().split("\n")
    try:
        idx = next(i for i, l in enumerate(lines) if l.strip() == "(let ()")
    except StopIteration:
        raise SystemExit(f"{src_path}: no top-level '(let () ...)' wrapper found "
                          "-- idris2's Racket codegen output shape may have changed")
    if lines[-1].strip() != "(collect-garbage)":
        raise SystemExit(f"{src_path}: expected trailing '(collect-garbage)', "
                          "codegen output shape may have changed")
    body = lines[:idx] + ["(provide (all-defined-out))"] + lines[idx + 1:-2]
    # Drop the line that forces Main's IO action as a side effect of loading
    # the module -- a library has no business running a smoke test on require.
    body = [l for l in body
            if not re.search(r"\(void \(PrimIO-unsafePerformIO Main-main\)\)", l)]
    # `(ffi-lib "libidris2_support")` resolves via the OS's library search
    # path (LD_LIBRARY_PATH etc.), which the executable's shell wrapper sets
    # but a `require`ing caller (raco make, in particular) has no reason to.
    # Resolve it relative to this module's own file instead, via
    # racket/runtime-path, so it works regardless of caller or cwd.
    #
    # This dependency is best avoided entirely rather than patched around --
    # it exists only because idris2's own `putStrLn` (Racket backend) routes
    # through this shared library, so a Main.idr with no IO calling through
    # it (see that file's module comment) produces a kernel.rkt with no
    # `ffi-lib` call at all, and this whole patch is then a no-op.
    ffi_lib_re = re.compile(r'\(ffi-lib "libidris2_support"\s*\)')
    patched = False
    for i, l in enumerate(body):
        if ffi_lib_re.search(l):
            body[i] = ffi_lib_re.sub("(ffi-lib idris2-support-so-path)", l)
            patched = True
    if patched:
        lang_idx = next(i for i, l in enumerate(body) if l.startswith("#lang "))
        body[lang_idx + 1:lang_idx + 1] = [
            "(require racket/runtime-path)",
            '(define-runtime-path idris2-support-so-path "libidris2_support.so")',
        ]
    open(dst_path, "w").write("\n".join(body) + "\n")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    libify(sys.argv[1], sys.argv[2])
