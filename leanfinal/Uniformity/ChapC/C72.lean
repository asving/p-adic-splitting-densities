/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C73
import Uniformity.ChapC.C38a
import Uniformity.ChapC.C27

/-!
# Uniformity.ChapC.C72 — GENTOW-3(i)+(ii): the floor and the faithful band — **PARTIAL: BLOCKED**

**Chapter C, NODE C.72** [theorem] [fresh] [signed: A-C.1 — two public names as planned]
(`blueprint/CHAP-C_tower_grammar.md` §8, NODE C.72; twin `leanspec/Leanspec/ChapC.lean`, the
`### NODE C.72` block).  **ENV-C1**.

## ⚠ DISPOSITION — READ THIS FIRST

**NEITHER signed statement is landed.**  `shadow_floor` and `shadow_faithful_band` are **OPEN**.
This file lands, honestly and with nothing claimed beyond it:

1. the two signed statements as **statement carriers** (`def … : Prop`) — the A-C.8.5 discipline
   (*"the signing unit must use statement carriers, never temporary axioms"*), so downstream
   consumers can NAME the obligation without any declaration asserting it;
2. the **x-free stratum, PROVED** — `shadow_floor_of_xfree` and `shadow_faithful_band_of_xfree`,
   the two clauses at every datum satisfying C.73's `IsXFree`.  There the discrepancy is
   identically zero (C.73's `shadow_exact_of_xfree`), so the floor is `⊤ ≥ Θ_j` and the band
   clause is a triviality.  This is a genuine but NARROW stratum: it is precisely the stratum on
   which the node has no content, since C.72's whole purpose is the non-x-free case;
3. the reusable reduction the above rides on: the level-2 height of `0` is `⊤` — `dv2Hgt_zero`,
   imported from `C27.lean` (the hypothesis-free form; this file's original copy carried a
   redundant `0 < L.ℓ` binder already available as the `LevelDatum.hℓ` field, and was removed
   when wiring C27 exposed the name collision, 2026-08-20);
4. the **BLOCKED record** below, with the exact mechanism.

**No consumer may read this file as supplying GENTOW-3(i) or (ii).**

## Why it is blocked — the exact mechanism, not a difficulty report

The route the blueprint assigns is `EFF.GENTOW3.22`–`.24`'s Steps 0–2, and it is a **weight-ledger
argument on two-variable monomials**:

* **Step 0** (`.22`) prices the reduction moves in `wt(π^v x^{a'} Y^{b'}) = e₁e₂·v + a'·e₂h +
  b'·u₂`, and turns on the audited claim that the x-carry `x^{D′} = Φ′ + tail` splits with the
  `Φ′`-branch landing at *parent* `+ δ` **EXACTLY** (`δ = u₂ − e₂D′h`, C.71's `margin`) — the
  source calls this "the whole engine of the note";
* **Step 1** (`.23`) is a weight-monotone induction down the `Y`-degree giving the ledger
  `wt(Ĝ_j) ≥ (μ₂−j)E₂`, and it consumes the FULL-SIDE hypothesis exactly once, through
  `μ₁u₂ = μ₂E₂`;
* **Step 2** (`.24`) is a three-branch census (x-overflow, `Φ′`-exponent reaching `e₂f₂` and
  recarrying into coordinate `j+1`, and forward-fed reduction discrepancies) with per-branch
  pricing, closed by **GENHN-2′**'s weight-to-height conversion ("each slot digit's `dv₂`-value is
  the slot-min exactly and heights separate classes").

**Nothing in the landed corpus carries a weight grading of this kind.**  This is not an inference
of mine: C.127's own module docstring records exactly this gap for its own §2/§3 —
*"Nothing landed carries a weight grading of this kind"* — and names the two nearest candidates as
inapplicable (`shadowDev_of_ingrid` explicitly does NOT apply to the over-grid case, which is the
whole content of the law; `binomKey_mod_monomial` is stated at the binomial key `X^D − C w` and
cannot be reused at the one-sided non-binomial `Φ′`).  Concretely, the four missing objects are:

* the two-variable weight function `wt` itself, and its monotonicity under monic `Y`-division;
* the `+δ` EXACTNESS of the x-carry's `Φ′`-branch (Step 0's engine);
* the recarry bookkeeping `(μ₂−j′)E₂ + kδ − (j−j′)E₂ ≥ (μ₂−j)E₂ + δ`, which needs the
  "recarry moves content only UPWARD in `j`" division-uniqueness lemma;
* GENHN-2′'s weight-to-height conversion, the step that turns "difference supported at weights
  `≥ Θ_j`" into "every disagreeing HEIGHT is `≥ Θ_j`".

Each is a node's worth of work; three of the four are *chapter*-level supply (the weight calculus
is C.84's `towerWeight` at level 2 plus a division-monotonicity theory that does not exist, and
GENHN-2′ is an accepted ANNEX, not a landed Lean object).  So the block is a **missing-supply**
block, not a proof-search failure, and the honest disposition is BLOCKED rather than a weakened
statement that compiles.

### The verbatim goal that remains

With every hypothesis introduced, `shadow_floor`'s goal is its own statement — no reduction is
available in the non-x-free case, which is exactly the point:

```text
O : Type u_1
inst✝³ : CommRing O
inst✝² : IsDomain O
inst✝¹ : IsDiscreteValuationRing O
π : O
F : KeyFrame O π
H₀ : ℕ
hpin : F.Pin H₀
T : TowerDatum F H₀ hpin
hπ : Irreducible π
hh : 1 ≤ F.h
inst✝ : Finite (IsLocalRing.ResidueField O)
μ₂ : ℕ
f : Polynomial O
hf : f ∈ towerLocus T μ₂
j : ℕ
hj : j < μ₂
⊢ ↑(T.theta μ₂ j) ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)
```

The single available reduction is `dv2Hgt_zero` (C27): if the difference is `0` the goal closes
by `le_top`.  That is the x-free stratum, and it is landed.  Off it, the goal above is untouched:
`dv2Hgt` is a `Finset.inf` of `dvSupp` over the `Φ′`-digits of a DIFFERENCE of two division
towers, and there is no landed lemma that lower-bounds such a thing.

## MANDATORY A-C.7 FIVE-INSTANCE BINDER-VACUITY AUDIT — verdict: **PASS with one disclosure**

Performed before any proving, on both signed statements, against the A-C.7 registry's four prior
A-C.1 failures plus the A-C.8.4 additional row.  Hypotheses under audit — `shadow_floor`: `T`,
`hπ`, `hh`, `[Finite (ResidueField O)]`, `hf : f ∈ towerLocus T μ₂`, `hj : j < μ₂`;
`shadow_faithful_band`: those plus `hm : m < T.theta μ₂ j` and
`hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)`.

**Pattern 1 — C.111 `hnode`, an unpinned carrier field.**  No analogue.  Every object in both
conclusions (`T.theta`, `shadowDev`, `dev (composedKey T)`, `dv2Hgt`, `dv2Res`) is a `def` applied
to `T`, `f`, `j` and the level datum `T.levelDatum hπ`; no carrier is quantified free.

**Pattern 2 — C.94, a self-loop trivializing an infinite relation.**  No relation, history, or
reachability predicate; both statements are single comparisons at a fixed coordinate `j`.

**Pattern 3 — C.113 `hne`, a `Nonempty` hypothesis with no intended content.**  No `Nonempty` and
no dependent side witness appears in either signature.  ⚠ NOTE the near-miss: `dv2Res`'s BODY
contains a `dif` on exactly such an existential (C.38a: "junk `0` off the pinned locus"), so the
band clause's second conjunct is an equation between two possibly-junk reads.  That is not a
vacuity defect — the clause is still a genuine constraint, and it is the SIGNED form — but it does
mean the conjunct is weaker than "both reads are pinned and agree".  Recorded, not repaired: the
statement is frozen.

**Pattern 4 — C.118 `Visible₂`, an implication guard leaving the `⊤` stratum unguarded.**  ⚠
**THIS ONE BITES, and unlike C.73's it is NOT closable here.**  `shadow_faithful_band`'s
`hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)` is a FINITENESS guard in
disguise: it presupposes the honest read's level-2 height is the finite `m`, so the stratum where
that height is `⊤` — i.e. where the honest digit `dev Φ₂ f j` is the ZERO block, the DRAIN case —
is entirely outside the clause.  This is the same shape as the machine-refuted C.118 clause 1,
where a `⊤` pin escaped an unguarded implication.  Here it is **benign but load-bearing**: it does
not make the statement vacuous (finite-height instances are the generic case), and the excluded
stratum is exactly the one C.74's `shadow_attained_of_certificate` is about (`C_j = 0` with the
shadow carrying a digit at `Θ_j`) — so the guard is what keeps (ii) consistent with (iv) rather
than an oversight.  **But it means (ii) as signed says NOTHING about drain coordinates**, and any
consumer that reads it as "the two reads agree below `Θ_j`, full stop" is over-reading it.  Filed
here because that over-reading is the natural one and the frozen text invites it.

**Pattern 5 — C.66's low-degree purity collapse.**  `towerLocus` carries `IsDvPure F f T.u₂
T.e₂`, so the C.66 shape is present in the hypothesis set.  It cannot collapse the conclusion: the
locus also pins `f.natDegree = μ₂ * T.D₂` with `2 ≤ e₂f₂` (`T.hcomp`), so `deg f ≥ D′·2·μ₂`, well
clear of the `0 < deg g < D′` window in which `IsDvPure` degenerates.

**Is the hypothesis set satisfiable?**  The binding constraint is `hf : f ∈ towerLocus T μ₂`
together with `hj : j < μ₂` (so `μ₂ ≥ 1`).  Mathematically yes — `f = Φ₂^{μ₂}` is the intended
member, and it is the member C.74's certificate is stated at.  **DISCLOSURE, twofold and the same
one C.73 carries:** (a) the corpus lands NO `TowerDatum` value at all, so no instance of these
binders is a Lean object; (b) `Φ₂^{μ₂} ∈ towerLocus T μ₂` is itself an UNLANDED lemma — C.52's
docstring names it `composedKey_pow_mem_towerLocus` as a planned step and C.52 landed only
`budgetFloor`, `budgetFloor_le_iff` and `dev_pow_self`.  So locus inhabitation is argued, not
machine-checked.  This is a chapter-wide gap; it is recorded here because it is the one thing that
could make these two statements vacuous, and a reader is entitled to know it is open.

**Verdict.** No fifth instance of the A-C.7 pattern in the SIGNED types.  Two disclosures stand
and are deliberately not smoothed over: the pattern-4 `hval` finiteness guard silently exempts the
drain stratum (benign, load-bearing, easy to over-read), and locus inhabitation is unlanded.
*Self-refutation attempt:* the tempting repair of DROPPING `hval` and stating (ii) as an
unconditional agreement below `Θ_j` is **REFUTED** by C.74's own certificate clause — at a
`TouchCert` datum the honest digit is `0` (height `⊤`) while the shadow digit sits at exactly
`Θ_j`, so the two heights differ on the drain stratum and an unguarded (ii) would be FALSE.  The
signed `hval` is therefore correct as frozen, and this is why.

**DEPENDS.** C.11 (`dv2Hgt`) · C.38a (`dv2Res`) · C.50 · C.52 (Step 0's carry pricing — the
missing supply) · C.71 (`shadowDev`, `TowerDatum.theta`, `margin`) · C.73 (`IsXFree`,
`shadow_exact_of_xfree` — the x-free stratum) · C.127 (`KeyFrame.stageHeight_zero`) — imported.

**PROOF (route).** See the BLOCKED record above.

**SIZE.** 40 lines (blueprint estimate).  **Split candidate:** (i)'s ledger / (ii)'s restatement.

**SOURCE.** `EFF.GENTOW3.18`/`.19` (the two clauses, verbatim); `.22` (Step 0 with the
`+δ EXACTLY` audit); `.23`/`.24` (Steps 1–2); `.25` ("(ii) is (i) restated").

**TEETH.** P-1 FLOOR 274 checks (census corrected to 137 `member_check` calls — CHAIN-CENSUS
TERMINAL `.49`) and P-6 LABEL 6 + A7-BAND rows remain OWED: they guard the general clauses, which
are not landed.  No tooth is discharged by this file.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only) — but **the two signed statements are OPEN**, carried
here only as `Prop`-valued statement carriers.  Landed as theorems: the x-free stratum of both
clauses, and `dv2Hgt_zero`.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## The reduction the x-free stratum rides on -/

/-- `n • ⊤ = ⊤` in `ℕ∞` for positive `n` (C.127 carries a private copy; `private` does not
export). -/
private theorem nsmul_top_pos {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  subst hk
  clear hn
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, top_add]

/- `dv2Hgt_zero` — the level-2 height of `0` is `⊤` — is imported from `C27.lean` (the
hypothesis-free form).  It is the reduction that makes "the two reads agree" imply "the floor
holds": a vanishing discrepancy has height `⊤`, which dominates every threshold. -/

/-! ## The two signed statements, as STATEMENT CARRIERS (nothing is asserted)

Per the A-C.8.5 discipline: a unit that cannot discharge a signed statement records it as a
`Prop`-valued carrier, never as a temporary axiom.  These two `def`s let downstream nodes NAME
GENTOW-3(i)/(ii) — and let a future unit state "`ShadowFloorStatement` → …" — while nothing in the
corpus asserts either.  The binder lists are byte-frozen from the leanspec twin. -/

/-- **NODE C.72(i) — GENTOW-3 FLOOR, the statement (OPEN).**  Every `dv₂`-height at which the
shadow and composed reads carry different slot digits is `≥ Θ_j`: the first disagreeing height of
the difference clears the threshold.  **Not proved.**  See the module docstring's BLOCKED record;
the x-free stratum is `shadow_floor_of_xfree` below. -/
def ShadowFloorStatement {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ : ℕ) (f : Polynomial O) (j : ℕ) : Prop :=
  (T.theta μ₂ j : ℕ∞)
    ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)

/-- **NODE C.72(ii) — GENTOW-3 FAITHFUL BAND, the statement (OPEN).**  At a height `m < Θ_j` at
which the composed read is pinned, the shadow read is pinned at the same height with the same
`K₂`-residue.  **Not proved.**  Note the `hval` guard: it exempts the DRAIN stratum (honest height
`⊤`), and must — see the module docstring's pattern-4 row, where dropping it is refuted by C.74's
certificate. -/
def ShadowFaithfulBandStatement {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (f : Polynomial O) (j m : ℕ) : Prop :=
  dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞) →
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
      dv2Res (T.levelDatum hπ) (shadowDev T f j)
        = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j)

/-! ## The x-free stratum, PROVED

Both clauses hold at every datum satisfying C.73's `IsXFree`, for the degenerate reason that the
discrepancy vanishes identically there (`shadow_exact_of_xfree`).  This is a real theorem and a
narrow one: it is exactly the stratum on which C.72 has no content, since the node exists for the
non-x-free case.  It is landed because it is the only part of (i)/(ii) that the corpus can
currently support, and because it pins the x-free/non-x-free boundary that C.74's attainment
clause sits on. -/

-- Binders byte-frozen from the leanspec twin, plus `hx : IsXFree T`.  Unconsumed signed binders
-- (`hh`, `[Finite …]`, `hj`) are kept: the statement is frozen and the x-free specialization must
-- not silently drop them.
set_option linter.unusedVariables false in
/-- **C.72(i) at an x-free datum.**  The floor holds, because the discrepancy is identically zero
(C.73's `shadow_exact_of_xfree`) and `dv2Hgt` of `0` is `⊤` (`dv2Hgt_zero`), which dominates
`Θ_j`.  This does NOT prove `shadow_floor`: off the x-free stratum the discrepancy is genuinely
nonzero and its height is what Steps 0–2 must bound. -/
theorem shadow_floor_of_xfree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (IsLocalRing.ResidueField O)] (hx : IsXFree T)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂) :
    (T.theta μ₂ j : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j) := by
  rw [shadow_exact_of_xfree T hπ hh hx hf j, sub_self,
    dv2Hgt_zero (T.levelDatum hπ)]
  exact le_top

set_option linter.unusedVariables false in
/-- **C.72(ii) at an x-free datum.**  Both conjuncts are immediate: the two reads are the same
polynomial, so their heights and their `K₂`-residues are equal on the nose — no band, no
threshold, and in particular no use of `hm : m < T.theta μ₂ j`. -/
theorem shadow_faithful_band_of_xfree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (IsLocalRing.ResidueField O)] (hx : IsXFree T)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂)
    {m : ℕ} (hm : m < T.theta μ₂ j)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
      dv2Res (T.levelDatum hπ) (shadowDev T f j)
        = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j) := by
  rw [shadow_exact_of_xfree T hπ hh hx hf j]
  exact ⟨hval, rfl⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dv2Hgt_zero
#print axioms Uniformity.Density.Tower.ShadowFloorStatement
#print axioms Uniformity.Density.Tower.ShadowFaithfulBandStatement
#print axioms Uniformity.Density.Tower.shadow_floor_of_xfree
#print axioms Uniformity.Density.Tower.shadow_faithful_band_of_xfree

end AxCheck
