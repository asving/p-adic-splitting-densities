# UNIT CN01 — VERDICT: CN0 PROVED IN FULL, CN1 PROVED IN ITS CLASS-STABLE REGION (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG22.lean` (562 lines, ZERO sorries; all 13
AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`; the C.33
cite does not occur; no landed file touched except the sanctioned one-line aggregator
import in `Uniformity/ChapI.lean`; `I10TauSupply.lean` untouched; no git ops).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG22.lean`
(final run: zero errors, zero warnings), targeted `lake build Uniformity.ChapI.IFCG22`
green (8919 jobs), `lake env lean Uniformity/ChapI.lean` (aggregator) green.

## ★★ CN0 — TRANSLATION SYMMETRY, PROVED IN FULL

    theorem coneCellCount_translation (hπ : Irreducible π) (hm : 1 ≤ m)
        (σ) (M) (γ γ' : ResidueField O) :
      coneCellCount O π m σ M γ = coneCellCount O π m σ M γ'

    def ZeroConeLaw : Prop            -- CenteredConeLaw with the centre pinned to 0
    theorem centeredConeLaw_iff_zeroCone : CenteredConeLaw ↔ ZeroConeLaw   -- ★★ payoff

The fractional-cell obligation of `decidedSliceAt_all_of_cones` is now the SINGLE centred
cone at `0`; centre-uniformity is DERIVED (as ECONE's fence promised it could be), never
assumed.

**The mechanism (simpler than the blueprint anticipated).**  The class recentring is
H.123a's `recentreClass` at the canonical shift `w := resSect O γ' − resSect O γ`.  The
three constituents of `coneCellCount` transport:

1. decidedness — landed `decidedAt_recentreClass` verbatim;
2. stratum — `recentreClass_mem_stratum`: the recentred lift reduces to
   `((X+Cγ)^m).comp (X + C(γ'−γ)) = (X+Cγ')^m` (one `C_add`/`sub_add_cancel` line);
3. the full-recentring range — `recentreClass_fullLoopClassN`:
   `recentreClass w (fullLoopClassN π (γ, d)) = fullLoopClassN π (γ', d)` **with the SAME
   box `d`**.  The blueprint's anticipated "triangular unit-diagonal action on mixed
   boxes" COLLAPSES TO THE IDENTITY: `loopMapN γ π d = shiftVecN (loopVecN π d)
   (resSect γ)` and the canonical lifts compose on the nose
   (`resSect γ + w = resSect γ'`, `shiftVecN_add`).  No box bijection, no
   `mkBoxN/shiftVecN(resOut∘d)` machinery was needed.

Count equality is two `Nat.card_le_card_of_injective` injections (`recentreClass_injective`),
one per direction, with the sdiff leg closed by the involution
(`recentreClass_recentreClass` + `neg_sub` + leg 3 at `(γ', γ)`).

## ★★ CN1 — CLASS-LEVEL NEWTON DATA, PROVED EXACTLY ON THE CLASS-STABLE PART

**Design (the unit's main economy):** no new valuation was built.  `classCoeffVal c i :=
resOrd (c i)` — H.107's LANDED windowed valuation, coordinatewise; and the "lift NP at
window `K`" IS the class NP of `proj O m K a`, so lift-stability is a REFINEMENT statement
along the landed `resFactor`.  Engine: the min-law

    theorem resOrd_resFactor (hNK : N ≤ K) (x : Res O K) :
      resOrd (resFactor hNK x) = min N (resOrd x)

The polygon is encoded by its integer support function (Legendre/support encoding of the
lower hull — convexity-free, faithful; `(h, e')` represents the rational slope `h/e'`):

    def classCoeffVal (c : Coeff O m N) (i : Fin m) : ℕ := resOrd (c i)
    def npHeight c i          -- heights with the monic point (m, 0) appended
    def classNPSupport c h e' -- min over range (m+1) of e'·v_i + h·i
    def NPAttains c h e' i    -- i ≤ m ∧ the min is attained at i
    def ClassNPFace c h e'    -- ∃ i < j both attaining  (segment of slope −h/e' on the hull)
    def NPVisibleAt c h e'    -- classNPSupport c h e' < e'·N   (THE FRAME FLOOR, strict)

Lift semantics of the valuation (uniform in q, e', degree, window):
`le_classCoeffVal_iff_dvd` (`k ≤ classCoeffVal c i ↔ π^k ∣ a i`, any lift, `k ≤ N`),
`classCoeffVal_exact` (visible ⇒ exact valuation of every lift), `classCoeffVal_eq_iff`
(`= N ↔ c i = 0`, invisibility — H.107 clause ii), `resOrd_mk_eq` (computation rule).

**The stability theorems** (all with the strict floor `NPVisibleAt` as the ONLY extra
hypothesis; `K ≥ N` arbitrary):

    classNPSupport_le_refine   : refinement can only raise the support (unconditional)
    classNPSupport_refine_eq   : below the floor, refinement support = class support
    npAttains_refine_iff       : below the floor, the ATTAINMENT SETS are equal
    classNPFace_refine_iff     : below the floor, the FACES are equal
    classNP_lift_eq            : classNPSupport (proj O m K a) h e' = classNPSupport c h e'   -- ★★
    classNPFace_lift_iff       : ClassNPFace (proj O m K a) h e' ↔ ClassNPFace c h e'         -- ★★

Cone glue: `one_le_classCoeffVal_of_mem_stratum` — classes of the stratum of `X^m` have
all heights `≥ 1` (the CN2 input shape; centres `≠ 0` reduce to it through CN0).

**Why the floor is the honest boundary (the proved mechanism):** an invisible coordinate
(`v_i = N`) contributes `≥ e'·N`; so a support `< e'·N` forces EVERY attaining marked
point visible (or the monic point), where the min-law pins every refinement.  At the
floor this breaks, PROVABLY:

    theorem npSupport_not_stable_at_floor (hπ : Irreducible π) :
      ∃ a a', proj O 2 1 a = proj O 2 1 a' ∧
        classNPSupport (proj O 2 1 a) 1 1 = 1 * 1 ∧          -- support = e'·N exactly
        classNPSupport (proj O 2 3 a) 1 1 ≠ classNPSupport (proj O 2 3 a') 1 1  -- 1 ≠ 2

(witness `(π,π)` vs `(π³,π³)` over the zero class — uniform over every DVR; doubles as
the nonvacuity instrument).  The at-or-above-floor region — the classes whose visible
polygon still touches the precision ceiling — is exactly the deep/undecided boundary that
CN2's decidedness criterion must dissect.  NOT leaked into: this file decides no type,
counts no stratum; both cone laws remain OPEN.

## SIGNATURE DELTAS vs the ECONE blueprint (charge item)

1. `coneCellCount_translation (γ γ')` gained `(hπ : Irreducible π)` (the recentring
   machinery is π-pinned via `proj_recentreVec`) and `(hm : 1 ≤ m)` (the stratum ∃-iff
   needs level ≥ 1).  Both forced and harmless: every consumer has `4 ≤ m` and a pinned
   irreducible.
2. Blueprint's `def classNP` realized as the SUPPORT-FUNCTION encoding `classNPSupport`
   (+ `NPAttains`, `ClassNPFace`) rather than a hull object — standard faithful encoding,
   chosen because CN2 consumes faces/slopes, not hull vertices, and it keeps everything
   in ℕ (no ℚ, no convexity library).
3. `classNP_lift_eq`'s "when visible" made precise as the STRICT floor criterion
   `NPVisibleAt` (`< e'·N`), and PROVED SHARP (`npSupport_not_stable_at_floor`) — the
   non-strict version is false.
4. `classCoeffVal` takes NO `π` argument (H.107's `resOrd` is ideal-theoretic; uniformizer
   independence is free).  The lift lemmas quantify over any lift, any window `K ≥ N`.
5. CN1's section carries `[Finite (ResidueField O)]` — NOT mathematically needed, but the
   landed `resFactor` auto-includes it (the same section-variable quirk H.107's docstring
   documents for `mem_maximalIdeal_pow_iff_dvd`).  Dropping it would mean re-declaring
   `resFactor`; not worth a parallel def.  All consumers carry the instance.

## What this unit did NOT do (honest fence)

No cone COUNT, no decidedness criterion, no residual polynomial: `PointConeLaw` and
`ZeroConeLaw` (= `CenteredConeLaw`) are open.  CN2's heart — "visible fractional face ⇒
ramified factor" — is untouched, by charge.  The CN1 face data is exactly the input CN2's
`typeOf_ram_of_fracFace` should consume: `ClassNPFace c h e'` with `NPVisibleAt` and
`gcd(h,e') = 1, e' ≥ 2` is now a well-defined, lift-independent hypothesis over `Coeff`.

## File map

`leanfinal/Uniformity/ChapI/IFCG22.lean`: §1 CN0 (`residue_resSect_sub`,
`recentreClass_mem_stratum`, `recentreClass_fullLoopClassN`, `recentreClass_mem_coneSet`,
★ `coneCellCount_translation`, `ZeroConeLaw`, ★★ `centeredConeLaw_iff_zeroCone`) ·
§2 CN1 (`classCoeffVal` + lift semantics, `resOrd_resFactor`, `resOrd_mk_eq`,
`npHeight`/`classNPSupport`/`NPAttains`/`ClassNPFace`/`NPVisibleAt` + support API,
`npHeight_refine`, the four stability theorems, ★★ `classNP_lift_eq` +
`classNPFace_lift_iff`, `one_le_classCoeffVal_of_mem_stratum`,
⚠ `npSupport_not_stable_at_floor`) · AxCheck footer (13 lines, all Lean core).
Aggregator: one import line in `Uniformity/ChapI.lean`.

## Repair log (4 error rounds, all trivial; CN0's five substantive proofs landed FIRST TRY)

1. `Finset.nonempty_range_succ` absent at this pin → `Finset.nonempty_range_iff.mpr`.
2. `resFactor` carries an auto-included `[Finite (ResidueField O)]` → added the instance
   to CN1's section (delta 5 above).
3. Witness lemma: `resOrd_ge_iff`'s implicit window left a metavariable in a `by omega`
   argument → pin `(N := K)`; `rw [ht]` rewrote `π` on BOTH sides of the unit equation →
   `calc`.  Missing `decide` after the first support rewrite.
4. Naming churn: `Irreducible.not_unit` → `.not_isUnit`; `isUnit_of_mul_eq_one` gone and
   `IsUnit.of_mul_eq_one` concludes `IsUnit` of the SECOND factor → constructed the unit
   `⟨⟨π, t, _, _⟩, rfl⟩` directly.
