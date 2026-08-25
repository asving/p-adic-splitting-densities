# Verdict — unit RB3 (Chapter C, READY batch 3 from `verdict_CCUR.md`)

Deliverable: `leanfinal/Uniformity/ChapC/C150rb3.lean` (only new file written by this unit).

Batch-3 assignment (`runs/wave-b/verdict_CCUR.md`, "Ranked READY batches" §, batch 3 — "the
now-composedKey-unblocked §7-tail/§8 family"): `refine_invariants` (C.56),
`side_degree_conservation` (C.70), `shadow_persistence` (C.74 family), `window_band1` (C.58).
Input inventory per the table: `C43.lean` (`composedKey`), `C38a.lean`/`C56a.lean`
(`dv2SideSet`, `k2DigitLift`), `C13.lean` (`IsTestKey`), `C34.lean`/`C35b.lean`
(`dvSideLen`/`IsDvPure`), `C131y.lean` (`dv2Hgt_add_eq_left_of_lt`, `dv2Res_add_deep`).

**Two land** (`side_degree_conservation`, `window_band1`); **two are genuinely BLOCKED**
(`refine_invariants`, `shadow_persistence`) — real proof-content gaps found during the attempt,
not naming/wiring nits, per the batch's own "moderate-confidence" framing. No `sorry`, no new
axiom, no weakened restatement anywhere in this unit's file.

## `side_degree_conservation` (C.70) — **LANDED**

`(F) (hπ) [IsAdicComplete …] {H₀} (hpin : F.Pin H₀) {f} {u ℓ} (hℓ) (hcop) (hf : f.Monic)
(hpure : IsDvPure F f u ℓ) (hne) {M₀} (hp) : dvSideLen F f u ℓ hne = ℓ *
(dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree`. A direct two-lemma composition: C.26's
`natDegree_dvResPoly` (`(dvResPoly …).natDegree = dvSideDeg …`, its first conjunct) rewritten
into C.08's `dvSideLen_eq` (`dvSideLen = ℓ · dvSideDeg`). One line: `rw [dvSideLen_eq F hℓ hcop
hne, (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1]`. `hf`/`hpure` are carried,
unused (the identity is floor-level and never touches monicity or purity — exactly the
"structurally immune" reading `HX_SWEEP_2026-08-20.md` §6.2 flagged). Signature verified
byte-identical to `leanspec/Leanspec/ChapC.lean:2402-2408`.

## `window_band1` (C.58) — **LANDED**

`(T) (hπ) (hh) […] {μ₂ N} {a a'} (hc : proj O (μ₂*T.D₂) N a = proj O (μ₂*T.D₂) N a') (ha :
monicPoly a ∈ towerLocus T μ₂) {j m} (hj) (hm : dv2Pin (T.levelDatum hπ) (composedKey T)
(monicPoly a) j = m) (hband : m < F.e₁ * T.e₂ * N) : dv2Pin … (monicPoly a') j = m ∧ dv2Res …
(dev (composedKey T) (monicPoly a') j) = dv2Res … (dev (composedKey T) (monicPoly a) j)`.

Landed as a direct assembly of the A-C.7 congruence-stability toolkit (`C118a.lean`/
`C118b.lean`, the exact repair units the CCUR table's own "same genre as `C131y`'s
congruence-stability lemmas" pointer was gesturing at, one layer over):

1. `C118a.monicPoly_coeff_congr hπ hc : ∀ i, π^N ∣ (monicPoly a - monicPoly a').coeff i` turns
   the `proj`-congruence into a coefficientwise valuation bound.
2. `C118a.dev_blocks_congr` pushes that through the `composedKey T`-development at slot `j`:
   `∀ i, π^N ∣ (dev Φ₂ (monicPoly a) j - dev Φ₂ (monicPoly a') j).coeff i`.
3. Clause (a): `dv2_read_congr_min (T.levelDatum hπ) hπ hc j` gives the capped law
   `min (dv2Pin … a j) W = min (dv2Pin … a' j) W` at `W = (F.e₁·T.e₂)·N`; since `hm`+`hband`
   place `dv2Pin … a j = m < W`, `C118b.eq_of_min_eq_of_lt` strips the cap and returns
   `dv2Pin … a' j = m`.
4. Clause (b): `dv2Pin … a j < W` unfolds (two `def`s: `dv2Pin`, `dv2Hgt`) to exactly the
   hypothesis `C118b.dv2Res_congr_of_lt` wants (`dvSupp F (dev Φ₂ a j) L.u L.ℓ < W`); fed the
   coefficientwise bound from step 2, it gives `dv2Res … (dev Φ₂ a j) = dv2Res … (dev Φ₂ a' j)`
   directly, `.symm`'d into the signed orientation.

`(T.levelDatum hπ).ℓ = T.e₂` and `(T.levelDatum hπ).u = T.u₂` by `rfl` (`C44.lean`'s
`TowerDatum.levelDatum` literal field assignment), used via `show`/defeq rather than an
explicit rewrite lemma. `ha` is carried, unused — the congruence machinery needs no
`towerLocus` membership, only the raw `proj` congruence and the pin bound. Signature verified
byte-identical to `leanspec/Leanspec/ChapC.lean:2203-2213`.

## `refine_invariants` (C.56) — **BLOCKED** (genuine gap, not a naming nit)

`RESCHEDULE_C56_2026-08-16.md` correctly named `composedKey` (C.43) as the sole recorded
blocker for THIS clause, and it is now landed — but clearing it exposes the actual
mathematical content, which is unlanded elsewhere: GENTOW-2(i)+(ii), a one-step
Newton–Hensel refinement of `composedKey T` itself. Two independent gaps:

1. The hypotheses `hne`/`hres` are stated about a WITNESS `f ∈ towerLocus T μ₂`'s dv2-residual
   at slope `(lam, 1)` — `dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne = (X - C
   s)^μ₂` — while the CONCLUSION is entirely about `composedKey T - k2DigitLift T s lam` (no
   `f`). No landed lemma transports `f`'s residual pattern to `composedKey T`'s own residual at
   that slope; the closest landed material (`dv2Res_add_deep`/`dv2ResPoly_add_deep`, C.131y)
   handles a single coefficient's OR a single side's residual under a "strictly deeper
   perturbation", not a member-to-generator transfer of a full `μ₂`-th-power factorization
   pattern.
2. Even granting `composedKey T`'s own residual is `(X-Cs)^μ₂` at `(lam,1)`, no landed lemma
   proves the actual refinement step: "subtract `k2DigitLift T s lam` and the corrected key is
   still `Monic`, still `natDegree = D₂`, and still `IsTestKey`" — a genuine one-step Hensel
   lift comparable in scale to C.47's `composedKey_isTestKey` (which only establishes these
   three facts for `composedKey T` ITSELF, unperturbed) or C.131w's 900-line `shadow_floor`
   development, not a wrap of existing material.

No proof attempted beyond this diagnosis (attempting one without the missing mechanism above
would risk an unsound shortcut); no declaration under the exact name `refine_invariants` is
in the delivered file.

## `shadow_persistence` (C.74 family) — **BLOCKED** (genuine gap, not a naming nit)

CCUR's own hedge ("the `hbudget` hypothesis's exact fit is unverified... not a guaranteed
one-liner") is borne out. The statement needs, and the corpus lacks:

1. An **upward** bridge from the coefficientwise `hbudget` floor (on
   `(dev F.key (dev (composedKey T) g j') b).coeff a`, an `addVal` bound) to a `dv2Hgt`/
   `dv2Pin`-level lower bound on `shadowDev T g j - dev (composedKey T) g j`. The only landed
   machinery in this direction is C.131w's `dv2Hgt_dev_floor`/`dev_coeff_paid_floor`, and both
   go the OPPOSITE way (an overall `dv2Hgt` floor descends to per-digit/per-coefficient floors,
   at the bespoke `wtCoeff`/`θ`/margin grid calculus built for `shadow_floor`'s specific proof)
   — not reusable as stated for the reverse direction `shadow_persistence` needs.
2. Additivity of `biRead`/`shadowDev` in the polynomial argument (a `biRead_add` lemma) plus
   monicity of `biRead F (composedKey T)`, needed to decompose `(composedKey T)^μ₂ + g`'s
   shadow discrepancy into the two summands' separately-established discrepancies via the
   C.131y `dv2Hgt_add_eq_left_of_lt`/`dv2Res_add_deep` "strictly deeper perturbation leaves the
   shallower read unchanged" pattern (exactly `shadow_faithful_band`'s own proof shape, one
   level up). Checked and confirmed absent: `grep -rn "biRead_add\|biRead.*Monic"
   Uniformity/ChapC/*.lean` returns nothing; `biRead`'s only landed properties are
   `biRead_coeff`/`biRead_eval_eq_map` (`C127.lean`), neither of which is additivity or
   monicity.

Both gaps are genuine new-mathematics items (each plausibly its own multi-hundred-line unit,
by the scale of the nearest landed analogues), not assembly. No declaration under the exact
name `shadow_persistence` is in the delivered file.

## Verification

```sh
cd leanfinal
lake env lean Uniformity/ChapC/C150rb3.lean
# 0 errors, 0 sorry; 5 harmless unused-variable linter warnings (hf, hpure, hh, ha, hj — all
# part of the frozen signed signatures, genuinely unused given the routes above); exit 0.
```

`#print axioms` footprint (AxCheck footer, also run inline by `lake env lean`):

```
Uniformity.Density.Tower.side_degree_conservation : [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.window_band1             : [propext, Classical.choice, Quot.sound]
```

Lean core only for both (`Classical.choice` only from the corpus's standard `ℕ∞`/`Finset`
machinery, same as every other landed node in this chapter — not a cite of any kind).

No file other than `leanfinal/Uniformity/ChapC/C150rb3.lean` and this verdict was created or
modified by this unit. `leanspec/`, roll-ups, and other units' files untouched. No commit made.
