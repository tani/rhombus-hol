# idris-hol-kernel

An Idris2 port of the LCF kernel's term algebra
(`rhombus-hol-lib/rhombus/hol/{htype,term,kernel}.rhm`), compiled
through Idris2's Racket backend. It is an independent, machine-checked
verification tool, not a runtime dependency: `rhombus-hol-kernel`'s own
`kernel.rhm` is 100% native Rhombus and is the trust boundary Rhombus/HOL
actually runs on. This directory is not `require`d by it, does not
participate in `raco make`, and adds no runtime dependency to the Rhombus
packages.

A runtime integration was tried once — all ten primitive rules routed
through this Idris code at runtime via a generated Racket module. A demo
showed it worked, but it cost about a 30% performance regression and, in the
form that avoided that cost, no longer exercised the kernel logic the proofs
below are actually about (see "Testing", below). It was reverted; this
directory now exists purely to state and check properties of the kernel
logic on its own schedule, decoupled from the Rhombus build entirely.

## Which side is normative

**This one.** The Idris kernel is machine-checked — `%default total`, no
`believe_me`, no holes, all ten primitive rules proved to produce
well-formed theorems — so when the two disagree, the bug is far more likely
to be in `kernel.rhm`, and the fix belongs there. Revising the Idris kernel
to match Rhombus would throw away the only independently verified artifact
in the project. The exception is a discrepancy showing that the Idris
*statement* is the wrong specification (a rule HOL does not have, say);
that is worth fixing here, and worth saying so explicitly.

## What is proved

**Every one of the kernel's ten primitive rules is proved to produce a
well-formed theorem.** Everything below is machine-checked by
`idris2 --cg racket --build kernel.ipkg` — with **no `?hole`s anywhere**
(verified with `:metavars` after loading `Main`, which reaches every proof
transitively) and **no axioms**: `grep believe_me src/*.idr` comes back
empty. Every fact below is an ordinary structural induction, and every
module carries `%default total`, so each is a statement of *total*
correctness — a rule provably *returns* a well-formed `Thm`, not merely
does so if it returns at all.

| rule | theorem | what the proof turns on |
|---|---|---|
| `REFL` | `reflWellFormed` | `mkEqCheckSound` on the term it was handed |
| `ASSUME` | `assumeWellFormed` | its conclusion *is* the checked term |
| `BETA` | `betaWellFormed` | type, scope and form of substitution (below) |
| `TRANS` | `transWellFormed` | operands of a well-formed equation are well-formed |
| `EQ_MP` | `eqMpWellFormed` | its conclusion is the equation's right-hand side |
| `DEDUCT_ANTISYM_RULE` | `deductAntisymWellFormed` | operands are the inputs' own conclusions |
| `MK_COMB` | `mkCombWellFormed` | `eqOperandTypes` inverts `typeMatch` to recover both sides' type |
| `ABS` | `absWellFormed` | `abstractAtCheck`, substitution run backwards |
| `INST` | `instWellFormed` | `instFvarGoCheck`, substitution driven by a list |
| `INST_TYPE` | `instTypeWellFormed` | `instTypeGoCheck` + `typeMatchSubst` |

Supporting results: `BETA` needs the full subject-reduction story
(`betaTypeSound`, `betaClosedSound`, `betaCheckSound`, resting on general
substitution/weakening/closedness lemmas over de Bruijn indices);
`newTypeMonotone`/`newConstantMonotone` show theory extension never
un-declares anything (so a theorem proved against an ancestor theory stays
valid in an extension); `WellFormedTheory` plus `initialTheoryWellFormed`
and `mkEqCheckSound` pin down what the kernel assumes about a theory and
that equation-building respects it; and hypothesis-list bookkeeping
(`hypInsertChecked`, `hypUnionChecked`, `hypRemoveChecked`, `rehashChecked`)
is covered so that no rule silently drops or duplicates a hypothesis.

`Stamp`, `Thm` and `Theory` are `export`, not `public export`: their
constructors are private to `Kernel.idr`, so outside it a theorem can only
be built by the ten rules and read through the accessors — mirroring the
`authentic`/`constructor ~none` boundary `kernel.rhm` draws. This guarantee
is Idris-level only and does not survive compilation to Racket, where these
values are bare tagged vectors; a Racket caller could fabricate one. That is
the concrete reason a wiring that *hands* this kernel caller-built theorems
would gain nothing from these proofs — only a wiring in which this kernel
constructs every theorem itself would.

### Lineage: `combineStampsSound`

Whichever `Stamp` `combineStamps` picks when merging two theorems'
provenance is reachable (`descends`) from *both* inputs — the formal version
of the "result belongs to the later of the two" argument `kernel.rhm`'s
comment makes in prose. `siblingsIncomparable`/`rootsIncomparable` further
show that two sibling extensions of one theory (or two independently rooted
theories) never descend from one another, which is the formal reason the
kernel tracks ancestor *sets* rather than a generation counter (a counter
alone cannot distinguish siblings). Token freshness is a typed precondition
of both: Idris cannot mint identities, so distinctness is exactly what the
caller (the Racket host's `gensym`) must supply.

### Why there are no axioms: `Name` instead of `String`

An earlier version of this development assumed two axioms about `String`
equality, because `String` is a primitive type with no constructors — a
proof of `x = y` for abstract strings `x, y` cannot be built by matching on
anything, only coerced into being with `believe_me`. `src/Name.idr` avoids
this by making names an inductive type instead:

```idris
data Name = NFun | NBool | NEq | NAlpha | NRepVar | NUser Nat
```

The five fixed constructors are the names `kernel.rhm` writes literally
(`fun`, `bool`, `eq`, the type variable in `eq`'s generic type, and the
representation variable `new_basic_type_definition` introduces); everything
a user declares is `NUser`, carrying a `Nat` — which is what Rhombus
`Symbol` equality actually *is* (interned identity, not character
comparison), so nothing is lost by dropping text. With names inductive,
`nameEqRefl`/`nameEqSound` (and everything downstream: `htypeEqSound`,
`termEqSound`, ...) are plain structural inductions, needing no axiom.
`Stamp`'s identity token is a `Nat` for the same reason.

### What is not proved

- **Semantic consistency** — that the axioms and rules cannot derive
  falsity. This is a claim about a model of the logic, not about syntax;
  nothing in this port speaks to it.
- **The theory-extension principles' own soundness** (`new_axiom`,
  `new_basic_definition`, `new_basic_type_definition` being conservative).
  Conservativity is a semantic property; what *is* proved is the syntactic
  half the kernel relies on — `newTypeMonotone`/`newConstantMonotone`.

### Termination

Nothing in an LCF kernel needs non-structural recursion: every recursive
function here (`typeOf`, `checkOpenTerm`, `substAt`, `typeMatch`, `htypeEq`,
...) recurses into a strict subterm of its argument, so `%default total`
holds throughout with one wrinkle. `termOrd` originally dispatched on the
*pair* `case (a, b) of ...`, which hid the structural descent from Idris's
termination checker because the recursive calls were on components of a
freshly built tuple rather than on subterms of the matched arguments.
Pattern-matching the two arguments directly instead makes the descent
visible and total.

## Testing: `idris_differential.rhm` / `idris_replay.rhm`

Two tests in the Rhombus test package connect the two kernels, using a
generated Racket module checked in there (not in the library, so it stays
out of `rhombus/hol.rkt`'s dependency graph):

- `tests/idris_differential.rhm` runs both kernels side by side over a
  deterministic corpus — all ten rules, theory extension, and the lineage
  cases — and compares every decision and every resulting sequent.
- `tests/idris_replay.rhm` records the primitive steps of a derivation the
  library actually performs (`bool.rhm`'s base theory, then one application
  of each of the ten rules) and has the Idris kernel re-derive the whole
  thing from its own `initialTheory`.

The replay is the shape of integration the proofs above actually support:
they say the ten rules, *as this kernel implements them*, produce
well-formed theorems from theorems this kernel itself built. A wiring that
hands the Idris kernel a theorem manufactured elsewhere gains nothing from
them — which is exactly what the reverted runtime integration did. In
replay the Idris kernel is handed no theorems at all, only a script of rule
applications, so it is in the situation the proofs are about, and it runs
once, in a test, off the hot path.

## Known divergences from `kernel.rhm`

Found by reading the two implementations side by side; besides these three,
the ten rules, the extension principles, `check_type`/`check_open_term`,
`type_of`, `type_match`, `type_subst`, `inst_fvar`, `inst_type`,
`abstract_at`, `subst_at`, the hypothesis-set operations and `term_ord`'s
rank table all agree exactly.

1. **Hypothesis order.** Both kernels keep hypothesis lists sorted and
   deduplicated, but by different orders: `kernel.rhm` sorts names
   lexicographically (`sym_ord` on `Symbol`); `Name` here has no text to
   sort by, so `Ord Name` ranks the reserved constructors and orders
   `NUser` by its id. Not a soundness issue — the order is an internal
   canonicalisation that nothing indexes positionally — but it means the
   tests compare the hypothesis *set*, not the list, between kernels.
2. **`new_basic_type_definition`'s representation variable.** `kernel.rhm`
   writes `mk_var(#'r, rty)`; the Idris side uses a dedicated `NRepVar`
   constructor (alongside `NAlpha` for the alpha-conversion variable) rather
   than a `NUser` id, so both sides name it in one place rather than
   relying on interning order to make the two theorems the same.
3. **`shift` on a negative result.** `kernel.rhm` raises "shift would
   produce a negative index"; here `integerToNat` clamps it to `0`
   silently. Unreachable through the kernel's own checked paths (`BETA`
   calls `checkTerm` first, which is what rules out the only negative
   shift), but the two differ on malformed input reaching `substBvar`
   directly.

## Reproducing

```sh
cd idris-hol-kernel
idris2 --cg racket --build kernel.ipkg
```

This builds `src/Main.idr`, a smoke test exercising all ten primitive rules
plus theory extension, and type-checks (hence proof-checks) everything else
transitively. To confirm there are no open proof obligations, load `Main`
in the REPL and run `:metavars`; it should report none.

## Layout

- `src/Name.idr` — the inductive name type, plus the equality
  soundness/reflexivity for it and for `Nat` that everything else rests on.
- `src/HType.idr` — HOL types (`htype.rhm`), plus `HType` equality
  soundness and reflexivity.
- `src/Term.idr` — locally-nameless terms (`term.rhm`), plus
  `shiftPreservesType` and the local-closedness lemmas.
- `src/Kernel.idr` — the ten primitive inference rules and theory extension
  (`kernel.rhm`), returning `Either String a` rather than raising, plus
  every proof described above.
- `src/Main.idr` — the smoke test described above (idris2's codegen only
  emits functions *reachable from `main`*, so this also keeps everything
  buildable even though nothing outside this directory calls it). Its `IO`
  calls go through a hand-rolled `myPutStrLn`
  (`%foreign "scheme,racket:display"`) rather than idris2's own `putStrLn`,
  to avoid pulling in a runtime shared library purely for that.

`rhombus-hol/rhombus/hol/tests/idris_kernel.rkt` turns idris2's raw Racket
output into a library at expansion time: it reads the generated file
(checked in verbatim, byte-for-byte what `idris2 --cg racket` emits) with
Racket's own reader and splices the transformed body into itself, so
`raco make` byte-compiles the result and nothing is paid at load time. Every
transform it makes is checked against an allowlist of assumptions about the
generated file's shape and fails loudly (via `raise-syntax-error`) if a
future idris2 version violates one.
