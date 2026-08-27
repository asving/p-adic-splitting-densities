# Unit verdict MI1 — INTERFACE I1 (resPoly/scalar-digit identification)

Charge: `docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md`'s `[MRFIX 2026-08-27]` INTERFACE I1
section — the four numbered obligations that discharge the open bridge between B.29's `resPoly`
(read in `resField X`) and the scalar digit polynomial `ψ` the ramified-exactness document's
SPREAD 3–4 argument manipulates. Sources read in full before proving: the I1 section itself,
`runs/wave-b/verdict_MRFIX.md` finding 3, `runs/wave-b/verdict_VRAMX.md` finding 3 (the original
diagnosis), and the cited files at the cited lines (`C01.lean:80-100`, `C27.lean:164-171`,
`B29.lean:91-94`, `B35c.lean:84-105`, `B59a.lean` in full, `B15.lean`, `B20.lean`, `B34.lean`).

## Filename deviation (flagged)

The charge asked for `leanfinal/Uniformity/ChapB/B59b.lean`. That name is **already the landed
B.59 contract** (`irreducible_map_iff_irreducible_resPoly`, committed `6a7753d9`, consumed by
`B60.lean` and imported by `Uniformity/ChapB.lean`). Overwriting it would destroy an unrelated,
already-proved node and break the build. The work lands instead at
**`leanfinal/Uniformity/ChapB/B59c.lean`** — the next free slot in the same `φ = X`
residual-to-reduction family (`B59a` = digit identity at integral slope; `B59b` = its
irreducibility contract; `B59c` = this unit, both at the *fractional* slope `h/e₁` a `KeyFrame`
actually carries). No roll-up file (`Uniformity/ChapB.lean`, `leanspec/*`) was touched, per
charge; `B59c` is not wired into any import graph and must be added by a human/owner pass if it
is to be consumed downstream.

## Disposition: all four obligations PROVED, none blocked

1. **Side geometry** (`frameKey_sideGeometry`): `sideMin = 0`, `sideMax = Φ'.natDegree`,
   `sideDeg = f₁`, from `hpure : IsPure X Φ' h e₁` unfolded at both `IsPure` endpoints (`0` and
   `Φ'.natDegree`, since `X.natDegree = 1`) plus `hdeg : Φ'.natDegree = e₁*f₁`. No corpus lemma
   existed for this at general `ℓ = e₁` (B.59a's `sideData_X_of_isPure` is `ℓ = 1`-only); proved
   directly by the same `Finset.min'/max'` membership argument B.20/B.59a use.
2. **The non-`rfl` pin** (`frameKey_hpin`): `npHgt X Φ' (sideMin ...) = ((h*f₁:ℕ):ℕ∞)`, from
   obligation 1's `sideMin = 0`, B.15's `npHgt_X`, and P2
   (`Uniformity.ChapC.C27.isPure_addVal_coeff_zero` applied to `hpure`, giving
   `e₁ • addVal O (Φ'.coeff 0) = ↑(h*Φ'.natDegree)`), then a hand-proved `ℕ∞` cancellation
   lemma (`eq_of_nsmul_eq_cast_mul`: `n•x = ↑(n*c) ∧ n>0 → x = ↑c`, via `ENat.ne_top_iff_exists`
   + `Nat.eq_of_mul_eq_mul_left`) dividing the purity equation by `e₁`.
3. **Coefficientwise identification** (`frameKey_resPoly_eq_map`): `resPoly π X Φ' h e₁ hne
   (h*f₁) = (frameResidualPoly π Φ' h e₁ f₁).map (resFieldXEquiv O)`, where
   `frameResidualPoly` is the literal SPREAD-4 polynomial `Σ_{b≤f₁} C(digAt π (h*(f₁-b))
   (Φ'.coeff (e₁*b))) * X^b`. Proved coefficientwise, unconditionally in `b` (no `b ≤ f₁` guard
   needed: B35c's `resPoly_coeff_of_pure` already gives the formula at every `k`, and
   `Nat.mul_sub` turns `h*f₁ - h*b` into `h*(f₁-b)` without a truncation case split), via B.15's
   `dev_X`, B.59a's `digPoly_C`/`AdjoinRoot.mk_C`/`resFieldXEquiv_coe`. The `b > f₁` branch
   (where `frameResidualPoly`'s sum is literally `0`) closes using a new corollary of B.30's
   `natDegree_resPoly`, `frameKey_natDegree_resPoly : (resPoly ... (h*f₁)).natDegree = f₁`
   (needs `X` to be `IsKey`, reproduced inline exactly as `B63.lean:337` already does it, and
   `suppVal ≠ ⊤`, proved from the finite pin via `Finset.inf_le` at index `0`).
4. **Transport** (`frameKey_scalarResidual_irreducible`): given a hypothesis of *exactly*
   `KeyFrame.hresirr`'s shape (`C01.lean:98-100`, universally quantified over `H₀` and its pin),
   specialise at `H₀ := h*f₁` via obligation 2's pin, rewrite along obligation 3's identity, and
   transport `Irreducible`/`natDegree = f₁` along `Polynomial.mapEquiv (resFieldXEquiv O)` using
   `MulEquiv.irreducible_iff` and `Polynomial.natDegree_map_eq_of_injective` — the same idiom
   `B59b.lean`'s landed `irreducible_map_iff_irreducible_resPoly` already uses for its own
   (integral-slope) transport. The result is stated purely in terms of the raw hypotheses a
   `KeyFrame` packages (`he₁ hf₁ hcop hmonic hdeg hpure hne hresirr`), so a future `ChapC`
   consumer instantiates it by passing `F.he₁ F.hf₁ F.hcop F.hmonic F.hdeg F.hpure F.hne
   F.hresirr` literally — no `KeyFrame` import needed in `ChapB`.

No obligation needed an unstated fact; nothing is `BLOCKED`.

## Reverse-dependency note (flagged for review, not a defect)

`B59c.lean` imports `Uniformity.ChapC.C27` for P2 (`isPure_addVal_coeff_zero`), which is stated
generically for any monic `g` and `IsPure X g h e` — it does not use `KeyFrame` — but happens to
be filed in a chapter-C module. No `ChapC` file imports `B59c`, so this creates no import cycle,
but it is the first `ChapB → ChapC` edge in the corpus and is called out for an owner decision
(leave as is, or have someone move/re-cite P2 into chapter B where its statement actually
belongs).

## Verification

```
cd leanfinal && lake env lean Uniformity/ChapB/B59c.lean
```
Zero errors, zero warnings, zero `sorry`. AxChk footer (from the file's own `#print axioms`
section, all four signed declarations):

```
'Uniformity.Density.Leaf.frameKey_sideGeometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Leaf.frameKey_hpin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Leaf.frameKey_resPoly_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Leaf.frameKey_scalarResidual_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only — no new axioms, matching the repo's axiom policy.

## What this does and does not close

This discharges INTERFACE I1 as a **standalone, reusable chapter-B fact**. It does *not* by
itself flip `docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md`'s T1 from PARTIAL to PROVED:
that document's `ψ` (SPREAD 3–4) is exactly `frameResidualPoly` here, and
`frameKey_scalarResidual_irreducible` is exactly the missing link the doc names, but wiring it
into the document's own Lean transcription (X1–X3/X9, per `verdict_MRFIX.md`'s disposition) and
into `docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md`'s own I1 status line is separate,
unstarted work, left to whoever picks up the ramified T1 chain next.
