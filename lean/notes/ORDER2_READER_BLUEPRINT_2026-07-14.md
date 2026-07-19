# Order-≥2 genuine reader — subsystem blueprint (2026-07-14)

Scope: this note precisely characterizes the residue-field-EXTENSION reader subsystem that the
`lean_urat` genuine classifier needs to be faithful at OM order `≥ 2`. It is a design document,
not a formalization: nothing here is built. The single additive artifact that accompanies it is the
interface-stub leaf `LeanUrat/OM/OrderTwoContext.lean` (`fChildCtxExt`, `card_Fr_fChildCtxExt`),
which surfaces only that the extension-field context TYPE is constructible as an `M5.OMType` — it
reads nothing from `f` and is NOT part of any reader.

## 0. Why order ≥ 2 is a new subsystem, not a slice

The current genuine reader (`Classifier.classifyGenuine` / `classifyGenuineAux`, DE-STUB A1,
2026-07-13) develops the ORIGINAL `f` against `liftKey ψ` at every depth, with the OM residue field
pinned to `ZMod p`:

- `Classifier.childResidual p N f ψ μ : (ZMod p)[X]` reads the `ZMod p` unit residue of the
  constant term of each φ-adic digit `Development.develop (liftKey p N ψ) μ f.1 t`.
- `Classifier.fChildCtx` sets `F0 = Fr := ZMod p`, `δ := 1`, `Rr := childResidual …`.
- `classifyGenuineAux` takes `ψ : (ZMod p)[X]` and recurses with `ch.P : (fChildCtx …).Fr[X]`,
  which is `(ZMod p)[X]` **definitionally** — no type transport, because `Fr := ZMod p` is fixed.

This is faithful only at order `≤ 1`: the reader lives in the single-slope tame tower `Fr = ZMod p`
(where P2 drainage lives). At order `≥ 2` the Montes descent enters a residue-field EXTENSION: the
repeated residual factor `ψ` over `F_r` may have `deg ψ > 1`, so the next residue field is
`F_{r+1} = F_r[Y]/(ψ)`, a genuine extension of `ZMod p` of degree `[F_{r+1} : F_p] = deg ψ · [F_r : F_p]`.
The reader at that level must:

1. develop over the unramified base ring `O″ = (ZMod p^N)[X]/(g)` (`UnramifiedBase.Oring`) whose
   residue field is `resField = F_{p^{deg g}}`, not over `(ZMod p^N)[X]`; and
2. read the residual off the digits into `resField[X]`, not `(ZMod p)[X]`.

Neither the ring `O″[X]` development nor a `resField`-valued residual reader exists. That is the
subsystem below.

## 1. The extension reader `childResidualExt` (signature)

Replacement for `Classifier.childResidual`. Fix `p N`, `[Fact p.Prime]`, `hN : 0 < N`, the
unramified key `g : (ZMod p^N)[X]` with `hgm : g.Monic` and `hgirr : Irreducible (gbar p N g hN)`.
Write `O := UnramifiedBase.Oring p N g` (the level-N unramified base ring) and
`Fr := UnramifiedBase.resField p N g hN` (a genuine `Field`, card `p^{deg g}`).

Proposed signature (`O″`-valued box, `resField[X]`-valued residual):

```
noncomputable def childResidualExt
    (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N)
    (g : (ZMod (p ^ N))[X]) (hgm : g.Monic) (hgirr : Irreducible (gbar p N g hN))
    (f : O″Box p N g n)                 -- an f living over O = Oring p N g (see §1a)
    (Ψ : (resField p N g hN)[X])        -- a repeated residual factor over the EXTENSION field
    (μ : ℕ) : (resField p N g hN)[X] :=
  ∑ t : Fin μ, Polynomial.C
    (resUnitResidue p N g hN                     -- §2b: residue reader O → resField
      ((Development.develop (liftKeyExt p N g Ψ) μ f.1 t).coeff 0))
    * Polynomial.X ^ (t : ℕ)
```

Three genuinely new pieces vs `childResidual`:

- `O″Box p N g n` (§1a): the `Development.develop`-able box object over `O = Oring p N g` — an
  `O[X]`-truncation analogous to `QuotientBox.monicBox p N n` but with coefficient ring `O` instead
  of `ZMod (p^N)`. Its `.1` is an `O[X]`.
- `liftKeyExt p N g Ψ : O[X]` (§2a): a monic lift of `Ψ ∈ resField[X]` to the base ring `O` — the
  Teichmüller/Hensel lift. This is the FIRST missing lemma.
- `resUnitResidue p N g hN : O → resField` (§2b): the residue reader `O → O/(p) = resField`, the
  extension analogue of `PadicLift.zmodUnitResidue`. Available in spirit already:
  `UnramifiedBase.resHom p N g hgm hN : Oring → resField` is exactly the reduction `O → O/(p)`, and
  `pval_Oring` gives the valuation; the "unit residue" wrapper (divide out `p^{val}` then reduce) is
  a modest composition, NOT one of the two hard lemmas.

### 1a. The box object over `O = Oring`

`QuotientBox.monicBox p N n` truncates monic degree-`n` polynomials over `ZMod (p^N)`. The extension
reader needs the same over `O`: `O″Box p N g n := { f : O[X] // f.Monic ∧ f.natDegree = n }` (or the
project's exact `monicBox` shape re-based on `O`). Since `O` is a finite commutative local ring
(`UnramifiedBase.isLocalRing`, `finite_Oring`), all the finiteness/valuation infrastructure that
`monicBox` relies on transports; this is engineering, not new math. The genuine `f` at an order-≥2
node is obtained by base-change of the original `f` along `ZMod (p^N) → O` composed with the
running key change — the bookkeeping the SEPARATE recursion (§3) must thread.

## 2. The two missing new-math lemmas

### Lemma A — Teichmüller/Hensel lift `liftKeyExt` (the key lift into the extension base)

Statement (proposed):

```
noncomputable def liftKeyExt
    (p N : ℕ) [Fact p.Prime] (hN : 0 < N) (g : (ZMod (p^N))[X])
    (hgm : g.Monic) (hgirr : Irreducible (gbar p N g hN))
    (Ψ : (resField p N g hN)[X]) : (Oring p N g)[X]

theorem liftKeyExt_monic … : (liftKeyExt … Ψ).Monic
theorem liftKeyExt_natDegree … : (liftKeyExt … Ψ).natDegree = Ψ.natDegree
theorem liftKeyExt_reduces … :        -- ḡ-analogue of Classifier.liftKey_map / resHom naturality
    (liftKeyExt … Ψ).map (resHom p N g hgm hN) = Ψ
```

Why it is hard. `Classifier.liftKey` lifts `ψ ∈ (ZMod p)[X]` coefficientwise by the trivial
set-section `ZMod p → ZMod (p^N)`, `c ↦ (c.val : ZMod (p^N))` (`liftCoeff`) — a pure
representative-choice, no algebra, and `liftKey_map` is just `map_natCast`. Here the coefficients of
`Ψ` live in the residue field `resField = O/(p)`, and we must lift each `resField`-coefficient to an
element of `O` that reduces back to it AND makes the lifted polynomial's reduction equal `Ψ`. Two
routes, both non-trivial:

- **Teichmüller route.** `O` is a finite unramified local ring with residue field `resField`; the
  multiplicative Teichmüller section `resField → O` (the unique multiplicative set-section
  `τ : resFieldˣ ∪ {0} → O` with `resHom ∘ τ = id`) exists because `O` is `p`-adically complete at
  level `N` (finite length). Mathlib has Teichmüller/Witt-vector machinery
  (`WittVector.teichmuller`) but NOT, off the shelf, "the finite-length truncation `O = W(k)/p^N` has
  a Teichmüller section landing in `O`" in the `AdjoinRoot g` presentation used here. Bridging the
  `AdjoinRoot`-presentation of `O` (a quotient of `(ZMod p^N)[X]`) to the Witt-vector presentation
  (needed for `teichmuller`) is a real identification (`Oring ≃+* W(resField)/p^N`), NOT currently in
  the repo (`UnramifiedBase` deliberately banks only the card and local structure, not the Witt iso;
  see its §"card `p^m` suffices / GaloisField note").
- **Hensel route.** Alternatively lift each coefficient by any set-section `resField → O` (e.g. via
  `resHom` surjectivity + `Function.surjInv`, which `UnramifiedBase.resHom_surjective` supplies) and
  accept a non-multiplicative lift; then `liftKeyExt_reduces` holds by construction but monicity and
  the DEGREE tie need the leading coefficient lifted to a genuine UNIT of `O` (so
  `liftKeyExt_monic`). `UnramifiedBase.isUnit_iff_notMem` characterizes units, so a monic
  `Ψ` (leading coeff `1`) lifts to leading coeff `1 ∈ O`ˣ cleanly — this makes the Hensel/surjInv
  route the LIKELY cheaper path, its only cost being that `liftKeyExt_reduces` must be proved
  coefficientwise from `resHom (surjInv …) = id` rather than for free.

Estimated difficulty: MEDIUM-HARD. The surjInv route is probably ~150–250 lines (the coefficientwise
reduction lemma is the bulk, mirroring `liftKey_map` but over `resHom` not `map_natCast`). The
Teichmüller route needs the Witt iso first and is HARD (500+ lines) — avoid unless multiplicativity
is later required.

### Lemma B — `O″`-development residue naturality (the `develop_map` analogue)

Statement (proposed): the extension analogue of `Development.develop_map`, transporting a φ-adic
development along the residue hom `resHom : O → resField` (and along the level-reduction
`O_{N+1} → O_N`, for the reduction-stability the CERTLEVEL layer will eventually need):

```
theorem developExt_resHom_natural
    (p N : ℕ) [Fact p.Prime] (hN : 0 < N) (g …) (hgm …) (hgirr …)
    {Φ : (Oring p N g)[X]} (hΦ : Φ.Monic) (k : ℕ) (h : (Oring p N g)[X]) (j : Fin k) :
    (Development.develop Φ k h j).map (resHom p N g hgm hN)
      = Development.develop (Φ.map (resHom p N g hgm hN)) k (h.map (resHom p N g hgm hN)) j
```

Why it is hard. `Development.develop_map` is a general theorem over ANY ring hom `f : R →+* S` and
holds because `%ₘ` / `/ₘ` by a monic commute with `Polynomial.map` (`map_modByMonic`,
`map_divByMonic`). So the STATEMENT above is, on its face, a direct instance of `develop_map` with
`f := resHom` — IF the only thing needed were digit transport.

The genuine difficulty is not this instance; it is the SEMANTIC content the extension reader needs on
TOP of it, which `develop_map` does NOT give:

1. **Digit-constant-term ↦ residual coefficient faithfulness.** `childResidualExt` reads
   `resUnitResidue (digit.coeff 0)`. To know this reads the GENUINE order-r residual (the Montes
   residual polynomial `R_r ∈ resField[X]`), one needs that the φ-adic digits of `f` over `O`, reduced
   mod `p`, ARE the residual — i.e. the O″-development computes the same object as the
   abstract-Montes residual `M4/ResidualPolynomial` over the extension. `develop_map` transports
   digits but says NOTHING about them being the residual; that identification is the actual math (it
   is the extension analogue of the order-0/order-1 residual-correctness that the project currently
   asserts via the `boxCoeffData`/`residualPoly` construction at `Fr = ZMod p`, and which has NO
   proof for the extension `Fr`). This is where "reads `f` faithfully at order 2" would have to be
   discharged, and it is genuinely open in the repo.
2. **Valuation/gap bookkeeping over the UNGAPPED filtration.** `zmodUnitResidue` divides out the
   `p`-adic valuation; over `O` the filtration is unramified/UNGAPPED
   (`UnramifiedBase.card_map_span_p_pow`: successive quotients all `p^{deg g}`), so
   `resUnitResidue` = "reduce `pval`-normalized element mod `p`" is well-defined, but the
   reduction-STABILITY analogue of `childResidual_reduce_stable` (needed for CERTLEVEL) must be
   re-proved with the `O`-valuation `pval_Oring` in place of `PadicLift.zmodValuation`, including the
   per-digit cutoff hypothesis restated over `O`.

Estimated difficulty: the bare `develop_map` instance is EASY (~10 lines). The residual-faithfulness
identification (2b.1) is HARD and is the true order-2 content — this is the lemma that makes the
reader a READER; without it `childResidualExt` computes a `resField[X]` that is not certified to be
`f`'s residual. Budget the faithfulness proof at 300+ lines and treat it as the gating research
result, not the transport lemma.

## 3. Wiring: a SEPARATE `classifyGenuineExtAux` recursion (do NOT repoint the current one)

Hard constraint. `Classifier.classifyGenuineAux` recurses with `ch.P : (fChildCtx …).Fr[X]`, and its
well-foundedness/`Nat.strongRecOn` closure relies on `(fChildCtx …).Fr = ZMod p` **definitionally**:
the recursive call `ih ch.childSize hlt (T.order + 1) ch.P ch.μ` typechecks only because `ch.P`'s
type `(fChildCtx …).Fr[X]` is DEFEQ to the `(ψ : (ZMod p)[X])` argument slot, with no `eqRec`/`▸`
transport on the residual. (The docstring at `classifyGenuineAux` states this explicitly: "all
`Fr := ZMod p` DEFINITIONALLY … NO type transport".) Repointing this recursion at an extension `Fr`
would make `ch.P : Fr[X]` with `Fr` a NON-definitional extension field, forcing an `eqRec_heq`
transport across the residue field into the strong-recursion motive — which does NOT reduce, breaking
the definitional closure the current proof depends on.

Therefore the extension reader must be a SEPARATE recursion, parameterized by the running extension
field as DATA:

```
noncomputable def classifyGenuineExtAux
    (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ) (hN : 0 < N) :
    (budget : ℕ) →
    (g : (ZMod (p^N))[X]) → (hgm : g.Monic) → (hgirr : Irreducible (gbar p N g hN)) →
    (f : O″Box p N g n) →           -- f re-based over O = Oring p N g
    (r : ℕ) → (Ψ : (resField p N g hN)[X]) → (μ : ℕ) → ClusterShape
```

Design points:

- The residue field `resField p N g hN` travels as a FUNCTION of the running key `g`, which is
  itself data threaded through the recursion — so each level has its OWN `Fr`, carried explicitly,
  never fixed to `ZMod p`. There is no single ambient `Fr`, hence no definitional-`Fr` closure to
  preserve and no `eqRec` on the motive.
- At each descent, the child's repeated residual factor `ch.P : (fChildCtxExt …).Fr[X] = resField[X]`
  becomes the next level's `Ψ`, and the next key `g'` is `liftKeyExt … ch.P` composed with the tower
  step (the new base is `O′ = Oring p N g'` — a TOWER of unramified/Eisenstein extensions; the
  Eisenstein child over `O` is `UnramifiedBase`'s named-but-unbuilt `RphiExt`, W6b-f2-proper).
  Threading `g ↦ g'` and re-basing `f` is the recursion's real bookkeeping.
- Well-foundedness is STILL by `Nat.strongRecOn` on `budget`, exactly as `classifyGenuineAux` — the
  cluster-size descent `ch.hChildSizeLt` is field-agnostic. Only the residual-carrying argument
  changes type per level, which is fine because it is data, not a fixed motive parameter.
- The stub `OrderTwoContext.fChildCtxExt` is the TYPE the child context would take at a level (its
  `Fr = resField`, card `p^{deg g}`, `hResidueDeg` discharged). The genuine version replaces its
  `Rr := 0` with `Rr := childResidualExt …` once Lemmas A and B exist.
- `classify`/`classifyAux`/`classifyGenuineAux` are LEFT UNTOUCHED (they stay in the tame
  `Fr = ZMod p` order-≤1 tower). The extension recursion is additive, built ALONGSIDE, and only a
  final (CERTLEVEL-breaking) swap phase — well beyond this subsystem — would ever repoint the master
  classifier at it.

## 4. Honest size estimate

Component-by-component (net-new Lean, off the existing `UnramifiedBase`/`Development`/`OMType`
infrastructure):

| Component | New math? | Est. lines |
|---|---|---|
| `O″Box` over `Oring` (finite local ring box, valuation infra transport) | engineering | 200–400 |
| `resUnitResidue` (residue reader `O → resField`, `pval`-normalized) | modest (compose `resHom`+`pval_Oring`) | 80–150 |
| Lemma A `liftKeyExt` (surjInv/Hensel route) + monic/degree/reduces | MEDIUM-HARD | 150–250 |
| Lemma A (Teichmüller route, needs `Oring ≃ W(k)/p^N` iso) | HARD — avoid | 500+ |
| Lemma B — bare `develop`/`resHom` transport | EASY | ~10–30 |
| Lemma B — residual-faithfulness identification (the true order-2 content) | HARD, gating | 300+ |
| Lemma B — reduction-stability over `pval_Oring` (CERTLEVEL analogue) | MEDIUM-HARD | 150–300 |
| `childResidualExt` + non-vacuity witness | small once A,B land | 60–120 |
| `classifyGenuineExtAux` + `_unfold` (separate strong-recursion) | MEDIUM (tower bookkeeping) | 200–350 |
| Tower step `RphiExt` over `O` (Eisenstein child, W6b-f2-proper) | LARGE separate wave | (out of scope) |

Total for a faithful order-2 reader (surjInv route, single unramified level, NOT the full tower):
roughly **1200–1900 lines**, of which the two genuinely-open results are the residual-faithfulness
identification (Lemma B, ~300+ lines and the gating research risk) and, secondarily, `liftKeyExt`
(Lemma A). The full multi-level tower (Eisenstein `RphiExt` children, general OM order) is a further
LARGE wave (W6b-f2-proper, explicitly out of scope of `UnramifiedBase`) and multiplies this.

Bottom line: order-≥2 faithfulness is a subsystem on the scale of the entire existing DE-STUB genuine
reader, gated on one genuinely-open faithfulness lemma. The interface stub `fChildCtxExt` establishes
ONLY that the extension-field context TYPE is constructible — it is not progress on any of the above.
