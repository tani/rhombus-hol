# idris-kernel

An Idris2 port of the LCF kernel's term algebra
(`rhombus-hol-lib/rhombus/hol/private/{htype,term,kernel}.rhm`), compiled
through Idris2's Racket backend, that **coexists with, but does not replace,**
the native Rhombus kernel.

## Current design: verification tool, not a runtime dependency

`rhombus-hol-lib/rhombus/hol/private/kernel.rhm` is 100% native Rhombus --
the trust boundary Rhombus/HOL actually runs on. This directory is not
`require`d by it, does not participate in `raco make` / `raco test`, and
adds no runtime dependency to the Rhombus packages.

This directory's job instead is to **state and check properties of the same
kernel logic in Idris2's dependent type system**, on its own schedule
(`idris2 --build kernel.ipkg`, whenever someone chooses to run it -- a CI
job, a pre-release check, or by hand), decoupled from the Rhombus build
entirely. `src/Kernel.idr`'s "soundness proofs: lineage" section is the
first of these: a machine-checked proof of the lineage argument that
`kernel.rhm`'s own module comment states in prose (see below).

This directory previously went further and actually routed all ten
`kernel.rhm` primitive rules through this Idris code at runtime (via a
generated Racket module `require`d from `kernel.rhm`). That was reverted:
it worked and all tests passed, but the design didn't hold up as the right
one to keep --the runtime cost (see "History" below) versus the value of
*executing* the same logic twice in different languages was worse than the
value of *proving properties about* one authoritative implementation and
keeping the other as the single thing that actually runs.

## What is proved so far

`combineStampsSound`, in `src/Kernel.idr`: whichever `Stamp` `combineStamps`
picks when merging two theorems' provenance, that stamp is reachable
(`descends`) from *both* inputs -- given each input is itself
self-reachable, which `descendsSelfFresh`/`descendsSelfNext` show holds for
every `Stamp` this kernel's own constructors (`freshStamp`/`nextStamp`) can
produce. This is the formal version of the argument `kernel.rhm`'s "-- Two
theorems may be combined only when their theories lie on one line of
extension. The result belongs to the later of the two." comment makes in
prose: it says the *chosen* stamp is never a regression for either side,
which is what makes "later of the two, or reject" a sound merge strategy
and not merely a deterministic one.

One assumption is made explicit rather than derived: `stringEqRefl` asserts
`s == s = True` for an abstract `String`, because Idris cannot derive that
by computation for a primitive/opaque backend operation. It is stated as an
axiom, not hidden inside a `believe_me` with no comment -- see its doc
comment in `src/Kernel.idr`.

This is one property, not an exhaustive verification of the kernel --
term/type safety (e.g. "`checkTerm` succeeding implies `typeOf` always
succeeds", the usual subject-reduction-shaped claim) is not proved here yet.
The lineage property was chosen first because it is exactly the one
`kernel.rhm`'s own comments call out as the subtle, easy-to-get-wrong part
(the fork/sibling-theories argument), and because it does not require
re-architecting `Term`/`HType` as intrinsically-typed to state.

## Layout

- `src/HType.idr` — HOL types (`htype.rhm`).
- `src/Term.idr` — locally-nameless terms (`term.rhm`).
- `src/Kernel.idr` — the ten primitive inference rules and theory extension
  (`kernel.rhm`), returning `Either String a` rather than raising, plus the
  lineage soundness proof described above.
- `src/Main.idr` — a smoke test exercising every one of the ten primitive
  rules plus theory extension (idris2's codegen only emits functions
  *reachable from `main`*, so this also keeps everything buildable even
  though nothing outside this directory calls it any more). Its `IO` calls
  go through a hand-rolled `myPutStrLn` (`%foreign "scheme,racket:display"`,
  straight into Racket's own `display`) rather than idris2's own
  `putStrLn`, which otherwise pulls in a runtime shared library
  (`libidris2_support.so`) purely for that -- see its doc comment.
- `scripts/libify.py` — turns `idris2 --cg racket`'s executable output into
  a `require`-able Racket module. Not currently used by anything (nothing
  requires the generated module any more), kept because re-wiring this
  directory into the runtime -- if a future property proved here, or a
  performance fix, changes the calculus -- would need it again; see
  `SPIKE.md` for why it's needed and how it works.

## Building / checking the proofs

```sh
cd idris-kernel
idris2 --cg racket --build kernel.ipkg   # typechecks everything, including
                                          # the proofs in Kernel.idr, and
                                          # builds the smoke-test executable
racket build/exec/kernel_app/kernel.rkt  # or just: build/exec/kernel
```

A failing proof is a compile error from this command, same as any other
type error -- there is no separate "run the proofs" step.

## History: why this isn't wired into `kernel.rhm`

An earlier iteration of this directory routed all ten primitive rules
through Idris at runtime (Rhombus `kernel.rhm` calling into a generated
Racket module via a hand-written term/type codec, with all lineage/stamp
bookkeeping kept native in Rhombus regardless -- Idris only validated and
computed the resulting term). It worked -- all 872 tests in
`rhombus-hol/rhombus/hol/tests` passed, including the white-box
`kernel.rhm` soundness-regression suite -- but:

- Clean `raco make` + `raco test` went from 3m52s (native) to ~5m
  (Idris-backed), a real ~30% regression, confirmed apples-to-apples on one
  machine.
- The regression turned out to be dominated by a **fixed per-process cost**
  of loading/instantiating the generated Racket module (not a cost that
  scaled with how many rules were migrated, nor mainly the
  `libidris2_support.so` FFI setup -- removing that dependency entirely,
  by having `Main.idr` avoid idris2's own `putStrLn`, did not measurably
  help). The bulk is simply the size and Racket-module-instantiation cost
  of what idris2's Racket backend emits.

Given that fixed cost doesn't buy back much (the same logic, running
twice, in two languages, at every compile of every HOL-using module) versus
what proving a property once, checked on its own schedule, buys (a
genuine independent check of the kernel's reasoning, paid for zero
runtime cost), the design changed to the one described above.

## Known gaps

- `Thm`/`Theory` are ordinary exported records here, not given the
  construction-proof boundary the Rhombus kernel has (`authentic`,
  `constructor ~none`, an unexported `internal` constructor) -- moot for
  verification purposes (nothing here needs to forge a `Thm`), but would
  matter again if this were ever wired back into the runtime.
- `new_basic_type_definition`'s soundness comment and `dest_abs`'s
  human-readable variable naming (`x, y, z, u, v, w, ...`) are ported as
  logic but not re-explained here; read the `.rhm` originals for the "why".
- Beyond `combineStampsSound`, no proofs of totality/soundness beyond what
  Idris2's (non-`%default total`) checker gives for free -- `%default
  covering` is used throughout, and list recursion into `HType`/`Term` is
  hand-written in `mutual` blocks because Idris2 0.8.0's termination
  checker does not see through `Eq`/`Show`'s default methods or
  higher-order list combinators (`map`, `foldl`, `any`) applied to a type
  mutually recursive with `List`.
