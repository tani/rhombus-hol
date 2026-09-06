# idris-hol-kernel

An Idris2 port of the LCF kernel's term algebra
(`rhombus-hol-lib/rhombus/hol/private/{htype,term,kernel}.rhm`), compiled
through Idris2's Racket backend, that **coexists with, but does not replace,**
the native Rhombus kernel.

## Current design: verification tool, not a runtime dependency

`rhombus-hol-kernel/rhombus/hol/private/kernel.rhm` is 100% native Rhombus --
the trust boundary Rhombus/HOL actually runs on. This directory is not
`require`d by it, does not participate in `raco make`, and adds no runtime
dependency to the Rhombus packages.

**Which side is normative: this one.** The Idris kernel is machine-checked
— `%default total`, no `believe_me`, no holes, all ten rules proved to
produce well-formed theorems — so when the two disagree, the bug is far
more likely to be in `kernel.rhm`, and the fix belongs there. Revising the
Idris kernel to match Rhombus would throw away the only independently
verified artifact in the project. The exception is a discrepancy showing
that the Idris *statement* is the wrong specification (a rule HOL does not
have, say); that is worth fixing here, and worth saying so explicitly.

Two tests in the Rhombus test package connect the two, using a generated
Racket module checked in there (not in the library, so it stays out of
`rhombus/hol.rkt`'s dependency graph):

- `tests/idris_differential.rhm` runs both kernels side by side over a
  deterministic corpus — all ten rules, theory extension, and the lineage
  cases — and compares every decision and every resulting sequent.
- `tests/idris_replay.rhm` records the primitive steps of a derivation the
  library actually performs (`bool.rhm`'s base theory: every logical
  constant plus the three axioms, followed by one application of each of
  the ten rules) and has the Idris kernel re-derive the whole thing from
  its own `initialTheory`.

The replay is the shape of integration these proofs actually support. They
say the ten rules, *as this kernel implements them*, produce well-formed
theorems from theorems this kernel built. A wiring that hands it a theorem
manufactured elsewhere gets nothing from them — which is exactly what the
reverted integration did (see History). In replay the Idris kernel is
handed no theorems at all, only a script of rule applications, so it is in
the situation the proofs are about; and it runs once, in a test, rather
than on `kernel.rhm`'s phase-1 hot path.

Recording the steps needs a hook in `kernel.rhm`, off by default, costing
one box read and a branch per rule. Measured A/B on one machine, clean
build plus full suite: 4m02.8s for 892 tests without it, 4m07.6s for 899
tests with it and the replay test — **+4.8s (+2.0%)**, of which the replay
test is about 1.9s. The reverted runtime integration cost about 30%.

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

## Could `kernel.rhm` become glue over this kernel?

Measured, not guessed — `rhombus-hol/rhombus/hol/tests/idris_bench.rhm`
(µs/call, one machine):

| | native Rhombus | via Idris |
|---|---|---|
| `REFL`, 10-deep term, codec on every call | 2.99 | 10.92 |
| `MK_COMB`, theorems already Idris-side | 0.53 | **0.15** |
| `INST`, theorem already Idris-side | 0.77 | **0.27** |

The first row is why the earlier integration regressed ~30%, and it is not
what the original post-mortem blamed. The rules themselves are not slow:
**with no codec in the way the Idris kernel is 2–3.5× faster than the
native one.** All the cost is the boundary — for a 10-deep term, encode
1.9µs plus decode 3.7µs against a 1.5µs call.

And the boundary is nearly free once it is memoised. Rewriting rebuilds
spines but shares subterms, so a cache keyed on term identity makes the
cost proportional to the *new* nodes:

| | cold | memoised |
|---|---|---|
| encode, one new node on a cached spine | 2.07 | **0.021** |
| decode | 3.74 | **0.023** |

A full `REFL` round trip with a memoised codec measures 2.70µs against the
native 2.95µs — cost-neutral, with the rule itself still 2× faster.

So the answer is yes in principle, and the remaining work is not
performance:

- **Memo tables.** Two identity-keyed caches. They must be ephemeron
  tables (`make-ephemeron-hasheq`), not plain weak ones: encode maps term →
  vector and decode maps vector → term, and a plain weak hash holds its
  values strongly, so the pair would keep each other alive forever.
- **Identity.** Stamps become caller-supplied `Nat` tokens from a counter,
  and names go through a `Symbol`-to-`Nat` intern table. Both are global
  mutable state, but of the kind `initial_theory`'s comment permits:
  nothing *decides* anything by comparing them except for equality and set
  membership, so a different allocation order gives different tokens and
  the same answers — which is already true of today's uninterned symbols.
- **The trust boundary grows.** The 92KB generated module joins it, along
  with `idris_kernel.rkt`'s transform, the codec and the intern table. That
  is the real price: `kernel.rhm` today is readable Rhombus that a person
  can audit.
- **Error messages.** This kernel returns terse `Left` strings where
  `kernel.rhm` raises with labelled values; the white-box tests match on
  message text.
- **Hypothesis order** becomes this kernel's (see the divergence above).

### The generated file is never edited

There is no post-processing step and no `libify.py` any more.
`idris_kernel_gen.rkt` is byte-for-byte what `idris2 --cg racket` emits,
and `rhombus-hol/rhombus/hol/tests/idris_kernel.rkt` turns it into a
library at *expansion time*: it reads the file with Racket's own reader and
splices the transformed body into itself, so `raco make` byte-compiles the
result and nothing is paid at load time.

That removes the objection that used to sit here. Rewriting generated
source with a regex is a bad trade — it cannot tell an application of
`vector` from the same characters inside a string literal, and it cannot
fail loudly when the shape it assumed is gone. Doing the same work on the
s-expressions the reader produces is neither of those things, and every
assumption is checked with a `raise-syntax-error` that names what it
expected:

1. exactly one top-level `(let () ...)` holds the whole body,
2. nothing outside it but `require`s and a trailing `(collect-garbage)`,
3. the `let` ends by forcing `Main-main`, which is dropped,
4. **every vector is born from a `(vector ...)` application and none is
   ever mutated.**

(4) is what licenses the one semantic change: applications of `vector`
become `vector-immutable`, in head position only. It is checked as an
allowlist rather than a blocklist of mutators, which matters: a blocklist
would wave through `list->vector`, whose result is mutable and would then
never be `==` to anything — silently, which is the failure mode worth
engineering against. So any symbol naming a vector operation must be one of
the four readers the module actually uses (`vector-ref`, `vector-length`,
`vector?`, `vector->list`, plus the `blodwen-vector-*` wrappers around
them), and bare `vector` must appear only in head position.

Verified by injection, not by inspection: adding `(list->vector '(1 2))`,
`(vector-set! v 0 1)` or `(apply vector xs)` to the generated file each
fails the build with a message naming the problem. And past that, the
runtime failure would still be loud — `vector-set!` on an immutable vector
raises.

For the record, on the current output: 183 `(vector ...)` applications, all
in head position, all rewritten; the only other vector operations are
`vector-ref`, `vector-length`, `vector?` and one `vector->list`, all
readers; `blodwen-vector-ref`/`-length`/`-list`/`blodwen-is-vector` are
thin wrappers around those and create nothing.

`register-external-file` makes `raco make` rebuild when the generated file
changes, so a fresh `idris2` build is not silently ignored.

### The variant that skips the codec: a Rhombus *view*

Rather than keeping its own `Term`/`HType` classes and encoding, the Rhombus
side can work on the Idris representation directly, with a view over it.
Spiked in `rhombus-hol/rhombus/hol/tests/idris_view_spike.rhm`, which is
kept running so a Rhombus upgrade that breaks one of these facilities is
caught early. **It works**, with one hazard that had to be found first.

One name in three spaces gives back the existing syntax — a function for
construction, a `bind.macro` for patterns, an `annot.macro` carrying a dot
provider for `.ty`:

```rhombus
fun Comb(f, x): rb.#{vector-immutable}(3, f, x)
bind.macro 'Comb($f, $x)': 'Array(3, $f, $x)'
```

Because the binding macro expands to another *pattern* rather than to a
predicate, nesting composes: `Comb(Abs(_, body), arg)` — `BETA`'s exact
shape — matches. Verified along with `.ty` through the dot provider,
`is_a Term`, and `===` for `term.rhm`'s unchanged-subterm short-circuit.

There is only one representation in play, which is worth being explicit
about: Idris's generated code builds ordinary Racket vectors, and `Array`
is Rhombus's name for exactly those. Both mutable and immutable vectors are
`is_a Array` and match the same patterns. The change below is one rewrite in
`idris_kernel.rkt` — emit `vector-immutable` instead of `vector` — not a
second data type.

**The hazard.** Rhombus `==` on a *mutable* `Array` is identity, not
structure. Terms are locally nameless, so `==` **is** alpha-equivalence, and
it is relied on in `TRANS`'s middle-term check, `EQ_MP`'s antecedent match,
hypothesis dedup, and as a `Map` key. Silently getting identity there would
be an unsoundness, not a bug. Immutable vectors compare structurally and
work as `Map` keys, and the generated module never mutates a vector — no
`vector-set!`, `make-vector` or `vector-fill!` occurs in it (the three
`vector-copy!` greps are `bytevector-copy!` in the string runtime) — so
`idris_kernel.rkt` rewrites them to `vector-immutable` as it splices the
body in. With that in place the differential and replay tests still pass,
31/31.

The corollary is that the representation has to be immutable
*consistently*. A mutable and an immutable vector are never `==` however
equal their contents, and Rhombus's own `Array(...)` constructor makes a
mutable one — so every term must be built through `vector-immutable` and
none through the `Array(...)` literal. Mixing them makes `==` quietly
answer false, which for alpha-equivalence is the unsound direction. Having
the `Term` annotation test `immutable?`, as the spike does, turns that into
a failed annotation at the boundary instead.

**Cost, measured** (µs, depth-10 term, 200k iterations):

| | Rhombus class | view |
|---|---|---|
| construction | 0.039 | 0.045 |
| pattern-match traversal | 0.026 | 0.041 |
| structural equality | 1.09 | **0.28** |

Traversal is ~1.6× slower; equality is ~3.8× *faster*, because a class's
`Equatable` goes through a recursive protocol while `equal-always?` on an
immutable vector is a primitive. Term equality is pervasive in HOL, so this
is not a small line.

**What stays a Rhombus class: `Thm` and `Theory`.** A bare vector is
forgeable by anyone who can write `vector-immutable`, which would destroy
the LCF boundary. They keep `authentic` / `constructor ~none` / an
unexported `internal` constructor and wrap the Idris value — one allocation
per theorem, negligible against a 0.15µs rule. Terms need no such
protection: they carry no authority.

**What the migration would still cost.** The 121 constructor and pattern
sites across 18 files need *no* change — that is the point of the view. The
124 field accesses need their values statically annotated for the dot
provider to fire; where they are not, it is a compile-time error, so
nothing breaks silently. Everything in the previous section that is not
about the codec still applies: identity tokens, the intern table, the trust
boundary growing to include the generated module and the transform, error
messages, and hypothesis order.

## What is proved

**Every one of the kernel's ten primitive rules is proved to produce a
well-formed theorem.** Everything below is machine-checked by
`idris2 --cg racket --build kernel.ipkg` -- with **no `?hole`s anywhere**
(verified with `:metavars` after loading `Main`, which reaches every proof
transitively) and **no axioms**: `grep believe_me src/*.idr` comes back
empty. Every fact below is an ordinary structural induction.

### Why there are no axioms: `Name` instead of `String`

An earlier version of this development assumed two axioms about `String`
equality (`s == s = True`, and `a == b = True -> a = b`). They were not
avoidable while names were `String`s: `String` is a *primitive* -- it has
no constructors -- so for abstract `x` and `y` a proof of `x = y` cannot be
built by matching on anything, only coerced into being with `believe_me`.
Base's own `DecEq String` instance is implemented exactly that way, so
switching to it would have relocated the assumption into the standard
library rather than removed it.

`src/Name.idr` makes the name type inductive instead:

```idris
data Name = NFun | NBool | NEq | NAlpha | NRepVar | NUser Nat
```

The five fixed constructors are the names `kernel.rhm` writes *literally*
rather than receiving from a caller: `fun`, `bool`, `eq`, the type variable
in `eq`'s generic type, and the representation variable
`newBasicTypeDefinition` introduces. `Name` carries no text, so each of
those needs its own constructor. They are not privileged — a user may
declare `a` or `r` too, and the bridge maps those to the same place, which
is what keeps it injective. They mirror
`rhombus-hol-kernel/rhombus/hol/private/names.rhm`, which fixes the same names
on the Rhombus side. Everything a user declares is `NUser`, carrying
a `Nat` rather than text -- which is what Rhombus `Symbol` equality
actually *is*: interned identity, not a character-by-character comparison.
`nameEqRefl` and `nameEqSound` are then plain inductions, and so is
`natEqSound` (`Nat` is inductive too), and everything downstream
-- `htypeEqSound`, `htypeEqRefl`, `termEqSound` -- follows from those.

`Stamp`'s identity token became a `Nat` for the same reason: it is a fresh
identity supplied by the caller, never text.

A future re-wiring to Rhombus would intern names at the boundary (a
`Symbol`-to-`Nat` map on the Racket side), which is the same thing Racket
already does for symbols internally.

### Lineage: `combineStampsSound`

Whichever `Stamp` `combineStamps` picks when merging two theorems'
provenance is reachable (`descends`) from *both* inputs, given each is
itself self-reachable -- which `descendsSelfFresh`/`descendsSelfNext` show
holds for every `Stamp` the kernel's own constructors can produce. This is
the formal version of the "the result belongs to the later of the two"
argument `kernel.rhm`'s comment makes in prose: the chosen stamp is never
a regression for either side, which is what makes "later of the two, or
reject" sound rather than merely deterministic.

`siblingsIncomparable` and `rootsIncomparable` state the property the
ancestor *set* exists for, and the one the section's prose asserted but
nothing proved: two sibling extensions of one base theory (and two
independently rooted theories) never descend from one another, in either
direction. Without it, a theorem proved in one sibling could be handed to
a rule checking membership in the other. A plain generation counter cannot
support this — both siblings would get the same number — which is the
formal reason the kernel carries sets rather than a depth.

Token freshness is a genuine precondition of both, not an oversight: Idris
cannot mint identities, so distinctness is what the caller supplies and
what the Racket host's `gensym` provides. Making that a typed hypothesis
rather than a comment is the point.

### The construction boundary

`Stamp`, `Thm` and `Theory` are `export`, not `public export`, so their
constructors are private to `Kernel.idr`. Outside it they can only be
built by the ten rules and the extension principles, and only read through
the accessors — the same boundary `kernel.rhm` draws with `authentic`,
`constructor ~none` and an unexported `internal` constructor. Costing
nothing in proofs (every proof lives in `Kernel.idr` and still sees the
constructors), it removes the possibility of an Idris-level client
fabricating a theorem.

The guarantee is Idris-level and **does not survive compilation**: the
Racket backend represents these values as bare tagged vectors, so a Racket
caller can fabricate one. This is not a fixable gap in the port — it is a
property of the FFI boundary — and it is the concrete reason a wiring that
*hands* this kernel caller-built theorems gains nothing from the proofs
here. What does gain from them is a wiring in which this kernel constructs
every theorem itself.

### Type safety: `checkTermTypeOfSound`, `typeOfWellFormed`

`checkOpenTerm thy t env = Right () -> (ty ** typeOf t = Right ty)`: a term
the kernel accepts always has a type, so `typeOf` never fails downstream on
something `checkTerm` already passed. And `typeOfWellFormed`: that type is
itself well-formed in the theory (needs `WellFormedTheory`, below, for the
`Abs` case, which builds a `fun` type).

### Beta reduction: the full subject-reduction story

`BETA` rewrites `Comb (Abs ty body) arg` to `substBvar arg body` and never
re-checks the result, so it owes three things, all now proved:

| | theorem | what it gives |
|---|---|---|
| type | `betaTypeSound` | the reduct has the same type as the redex |
| scope | `betaClosedSound` | the reduct has no dangling de Bruijn index |
| form | `betaCheckSound` | the reduct still passes `checkTerm` |

Each rests on a general substitution lemma proved by induction under
binders, with the de Bruijn depth and the environment growing together:
`substAtTypeSound` (typing), `substShiftClosed` (local closure, in
`Term.idr`), and `substAtCheckSound` (well-formedness), the last of which
also needs `checkWeakenRight` (weakening: entering more binders never
invalidates a term) and `checkClosed` (anything well-formed in an
environment has no index escaping it).

`shiftPreservesType` and `shiftClosedId` are the load-bearing small lemmas:
`shift` only rewrites `BVar` *indices*, so it cannot change a type, and on
a term already closed at the cutoff it is the identity. The second is what
keeps `shift`'s `Integer` index arithmetic out of every proof here -- no
reasoning about `integerToNat (natToInteger i + d)`, which would need
further axioms about primitive `Integer` operations, appears anywhere.

### Theory extension: `newTypeMonotone`, `newConstantMonotone`

Declaring a new type constructor or constant never un-declares an existing
one. This is what makes `in_theory`/`descends` meaningful: a theorem proved
against an ancestor theory is safe to reuse in an extension *because* the
extension still recognizes everything the ancestor did.

### Well-formed theories and equation building

`WellFormedTheory` pins down what the kernel assumes about a theory: `fun`
has arity 2, `bool` arity 0, and `eq` is declared at `'a -> 'a -> bool`.
`initialTheoryWellFormed` proves `initialTheory` satisfies it (the
monotonicity results above are what carry it through extension).

On top of that, `mkEqCheckSound`: an equation `mkEq` builds from two
checked terms of one type is itself a checked term. Its core,
`eqConstCheck`, is where `typeMatch` has to actually succeed -- matching
`'a -> 'a -> bool` against `ty -> ty -> bool` binds `'a` to `ty`, then
meets `'a` again and compares `ty` with itself, which is what
`htypeEqRefl` is for.

### The rules' outputs: all ten of them

A `Thm` is well-formed when every hypothesis and its conclusion are terms
the theory accepts (`WellFormedThm`). Nothing in the kernel re-checks a
theorem it built, so each rule owes exactly that -- and **all ten now
discharge it**:

| rule | theorem | what the proof turns on |
|---|---|---|
| `REFL` | `reflWellFormed` | `mkEqCheckSound` on the term it was handed |
| `ASSUME` | `assumeWellFormed` | its conclusion *is* the checked term |
| `BETA` | `betaWellFormed` | the whole beta development above |
| `TRANS` | `transWellFormed` | operands of a well-formed equation are well-formed |
| `EQ_MP` | `eqMpWellFormed` | its conclusion is the equation's right-hand side |
| `DEDUCT_ANTISYM_RULE` | `deductAntisymWellFormed` | operands are the inputs' own conclusions |
| `MK_COMB` | `mkCombWellFormed` | `eqOperandTypes` -- see below |
| `ABS` | `absWellFormed` | `abstractAtCheck`, substitution run backwards |
| `INST` | `instWellFormed` | `instFvarGoCheck`, substitution driven by a list |
| `INST_TYPE` | `instTypeWellFormed` | `instTypeGoCheck` + `typeMatchSubst` |

Three of these needed machinery of their own:

- **`MK_COMB`** equates applications it *builds*, so it has to know the two
  theorems it was given equate same-typed terms. `eqOperandTypes` recovers
  that from nothing but the fact that the equation type-checked, by
  inverting `typeMatch` (`typeMatchEqInv`): `eq`'s generic type
  `'a -> 'a -> bool` meets `'a` twice, so any instance of it pins both
  sides to one type. The other equation rules get their types more cheaply
  -- `mkEq` refuses to build an equation whose sides disagree, so a
  successful `mkEq` is already that proof (`mkEqTypes`).
- **`ABS`** closes a free variable: substitution run backwards, replacing
  an `FVar` by a `BVar` and *appending* the variable's type to the
  environment rather than consuming it (`abstractAtCheck`).
- **`INST_TYPE`** rewrites the types inside a theorem, so the environment
  moves with the term (`map (typeSubst' tyin) env`). Its delicate case is
  `Const`, whose check asks whether the use type is still an instance of
  the declared generic type: `typeMatchSubst` shows instantiating an
  instance leaves it an instance, with the matcher's bindings substituted
  the same way.

Hypothesis-list bookkeeping is covered too (`hypInsertChecked`,
`hypUnionChecked`, `hypRemoveChecked`, `rehashChecked`): every rule that
merges or drops hypotheses only moves existing ones around.

## What is not proved

The kernel's *syntactic* obligations are discharged: every primitive rule
produces a well-formed theorem, beta reduction preserves typing and scope,
theory extension is monotonic, and the lineage discipline is sound.

What is not here, and would not be:

- **Semantic consistency** -- that the axioms and rules cannot derive
  falsity. That is a claim about a model of the logic, not about the syntax
  this port describes; no amount of work in this directory would state it.
- **The theory-extension principles' own soundness** (`new_axiom`,
  `new_basic_definition`, `new_basic_type_definition` being conservative).
  Conservativity is again a semantic property; what *is* proved here is the
  syntactic half that the kernel relies on -- `newTypeMonotone` /
  `newConstantMonotone`.
(Termination is *not* on this list any more: every module is
`%default total`, so the proofs are of total correctness. See below.)

## Termination

Every module carries `%default total`, so Idris2 checks each function for
coverage *and* termination, and a `total` function may only call other
`total` functions — the property is closed downwards through the whole
development, base library included. Consequently the well-formedness
theorems are statements of total correctness: `reflWellFormed` and friends
say the rule *returns* a well-formed `Thm`, not merely that it does so if
it returns at all.

This was not hard, because nothing in an LCF kernel actually needs
non-structural recursion: `typeOf`, `checkOpenTerm`, `checkType`, `shift`,
`substAt`, `abstractAt`, `instFvarGo`, `instTypeGo`, `typeMatch`,
`htypeEq`, `nthEnv` and `hypInsert` all recurse into a strict subterm of
their argument. The kernel has no fixpoint iteration and no fresh-name
search loop (`term.rhm`'s `variant`, whose termination *would* need a real
argument — that a finite avoid-set leaves some suffix unused — is not part
of this port; the locally-nameless representation is exactly what removes
the need for it).

The one function Idris2's size-change analysis could not see through was
`termOrd`, and not for a deep reason: it dispatched on the *pair*
`case (a, b) of ...`, which hides the structural descent from the checker
because the recursive calls are on components of a freshly built tuple
rather than on subterms of the matched arguments. Pattern-matching the two
arguments directly instead makes the descent visible and it is accepted.
The earlier hand-written `mutual` blocks for `HType`/`Term`'s `Eq`/`Show`
(written to dodge the checker's blind spot around interface default
methods and higher-order list combinators over a type mutually recursive
with `List`) turned out to be exactly what totality needed as well, so
they carried over unchanged.

## Layout

- `src/Name.idr` — the inductive name type, and the equality
  soundness/reflexivity for it and for `Nat` that everything else rests on.
- `src/HType.idr` — HOL types (`htype.rhm`), plus `HType` equality
  soundness and reflexivity.
- `src/Term.idr` — locally-nameless terms (`term.rhm`), plus
  `shiftPreservesType` and the local-closedness lemmas
  (`shiftClosedId`, `substShiftClosed`, `substBvarClosed`).
- `src/Kernel.idr` — the ten primitive inference rules and theory extension
  (`kernel.rhm`), returning `Either String a` rather than raising, plus
  every other proof described above.
- `src/Main.idr` — a smoke test exercising every one of the ten primitive
  rules plus theory extension (idris2's codegen only emits functions
  *reachable from `main`*, so this also keeps everything buildable even
  though nothing outside this directory calls it any more). Its `IO` calls
  go through a hand-rolled `myPutStrLn` (`%foreign "scheme,racket:display"`,
  straight into Racket's own `display`) rather than idris2's own
  `putStrLn`, which otherwise pulls in a runtime shared library
  (`libidris2_support.so`) purely for that -- see its doc comment.
- (`scripts/libify.py` is gone. The generated file used to be
  post-processed into a `require`-able module by that script; it is now
  transformed at expansion time by
  `rhombus-hol/rhombus/hol/tests/idris_kernel.rkt` instead, so the checked-in
  generated file is byte-for-byte idris2's output.)
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

## Known divergences from `kernel.rhm`

Found by reading the two implementations side by side rather than by
testing; the ten rules, the extension principles, `check_type` /
`check_open_term`, `type_of`, `type_match`, `type_subst`, `inst_fvar`,
`inst_type`, `abstract_at`, `subst_at`, the hypothesis-set operations and
`term_ord`'s rank table all agree exactly. Two remain.

A third was fixed rather than documented: `new_basic_type_definition` used
to write `mkVar (NUser 0) rty` for its representation variable, a hardcoded
*user* id, where `kernel.rhm` writes `mk_var(#'r, rty)`. Both theorems were
correct — the variable is arbitrary and `pred` is checked closed, so
nothing can capture — but they were not the *same* theorem, and through the
bridge `NUser 0` decoded to whichever symbol was interned first. `Name` now
has an `NRepVar` alongside `NAlpha`, and `names.rhm` gained `v_alpha` and
`v_rep` so the Rhombus side names them in one place too.

1. **Hypothesis order.** Both kernels keep hypothesis lists sorted and
   deduplicated, but by different orders. `kernel.rhm` sorts names
   lexicographically (`sym_ord` on `Symbol`); `Name` here has no text to
   sort by — that is exactly what dropping `String` bought — so `Ord Name`
   ranks the reserved constructors and orders `NUser` by its id. They
   disagree on, e.g., `zz` versus `bb`. This cannot be reconciled without
   giving `Name` its text back. It is not a soundness issue: the order is
   an internal canonicalisation, nothing in the derived layer indexes
   hypotheses positionally, and each kernel is self-consistent. The shared
   contract is the hypothesis *set*, which is what the tests now compare.

2. **`shift` on a negative result.** `kernel.rhm` raises "shift would
   produce a negative index"; here `integerToNat` clamps it to `0`
   silently. Unreachable through the kernel's own checked paths — the only
   negative shift is `substBvar`'s `shift (-1)`, and `BETA` calls
   `checkTerm` first, which is what `shiftClosedId` and `substBvarClosed`
   above prove — but the two differ on malformed input reaching `substBvar`
   directly.

## Known gaps

- The construction boundary is drawn at the Idris level only (see "The
  construction boundary" above); it does not survive compilation, since the
  Racket backend emits bare tagged vectors.
- `new_basic_type_definition`'s soundness comment and `dest_abs`'s
  human-readable variable naming (`x, y, z, u, v, w, ...`) are ported as
  logic but not re-explained here; read the `.rhm` originals for the "why".
- See "What is not proved" above.
- Many definitions had to change from `export` to `public export` for the proofs above to see
  through their definitions at all (Idris2's `export` hides a function's
  *body* outside its own module, keeping only its type visible -- `public
  export` keeps the body transparent for reduction elsewhere, which a
  proof needs). This is a visibility widening only; it changes nothing
  about what other modules can construct or observe. `checkOpenTerm` also
  gained plain `export` (it was module-private before) so `Main.idr` and
  any future caller can reach it -- the proofs about it live in the same
  module (`Kernel.idr`) and never needed that widening themselves.
- Several definitions were restructured so that proofs can unfold them,
  with behaviour unchanged in every case: `checkOpenTerm`'s `Const`,
  `BVar` and `Comb` clauses now call `checkConstUse`/`checkBVarUse`/
  `checkCombUse` instead of inlining a `do` block (Idris's unifier
  compares two `checkOpenTerm` applications argument-wise and never
  unfolds a multi-statement clause body); `checkType` walks its arguments
  with an explicit `checkTypeList` rather than `traverse_`, and
  `instTypeR` likewise; `nthEnv` puts its empty-list clause first;
  `destFun`, `isFun` and `destEq` test the constructor name with `==`
  rather than matching a string literal (a literal pattern leaves them
  stuck on an abstract name, since Idris's evaluator does not carry "n is
  not \"fun\"" into the default branch); `instFvar`'s and `instType`'s
  workers, and `instR`'s `checkTheta`, are top-level rather than
  `where`-local; and both `typeMatch`'s accumulator and `typeSubst`'s
  substitution are association lists rather than `SortedMap`s, whose
  operations are `export`-only in base and therefore will not reduce
  during typechecking at all.
