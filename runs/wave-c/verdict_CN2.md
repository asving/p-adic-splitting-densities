# UNIT CN2 — VERDICT: THE CRITERION PROVED (pure fractional face), THE FLOOR PROVED SHARP FOR DECIDEDNESS (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG23.lean` (670 lines, ZERO sorries; all 15
AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`; the C.33
cite does not occur — no ChapC import at all; no landed file touched except the sanctioned
one-line aggregator import in `Uniformity/ChapI.lean`; `I10SiteCalc.lean` untouched; no git
ops). Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG23.lean`
(final run: zero errors, zero warnings), targeted `lake build Uniformity.ChapI.IFCG23` green
(8929 jobs), `lake env lean Uniformity/ChapI.lean` (aggregator) green.

## ★★★ THE RESULT — class-level NP fractional-face decidedness, PROVED at the pure face

    theorem ramIndexOf_dvd_of_visible_face :          -- ★ the C61 ℓ-half at class level (pure case)
      0 < m → 0 < e' → Nat.Coprime h e' →
      NPAttains c h e' 0 → NPAttains c h e' m → NPVisibleAt c h e' →
      proj O m N a = c → ∀ g' ∈ monicFactors (monicPoly a), e' ∣ ramIndexOf g'

    theorem decidedAt_of_eisenstein_face :            -- ★★ THE DECIDEDNESS CRITERION (e' = m)
      0 < m → Nat.Coprime h m →
      NPAttains c h m 0 → NPAttains c h m m → NPVisibleAt c h m →
      DecidedAt O m ⟨{(m, 1)}⟩ N c                    -- uniform in (q, m, h, N)

(over every complete DVR with finite residue field; `c : Coeff O m N` a coefficient CLASS.)
A class-visible pure face of slope `h/e'`, `gcd(h,e') = 1`, attained at both endpoints and
STRICTLY below the frame floor, forces `e' ∣ ramIndexOf` on every monic irreducible factor
of EVERY lift; at denominator `= degree` it pins the full type: the class is DECIDED totally
ramified. This is the first general class-level decidedness theorem of the census beyond
IFCG19's irreducible-residual monomial — the fractional half the whole cone architecture was
built around.

## THE RESOLUTION of the CN1-floor tension (charge item 1 — written to this stub BEFORE proving, now machine-checked)

CN1 proved the class NP is NOT lift-stable at support `= e'·N`; CN2 needs face-decidedness to
be a class property. Resolution, each clause now a checked artifact:

**(R1) Decidedness is class-level BY DEFINITION.** `DecidedAt O n σ N c := ∀ a, proj a = c →
typeOf (monicPoly a) = σ` quantifies over all lifts — the floor threatens only polygon-based
CRITERIA, which may consume only the lift-stable (strictly visible) data. No well-definedness
problem exists.

**(R2) Strictly below the floor the face DECIDES** — the two theorems above. The mechanism is
C61's CLOSED `e₁`-leg, not its open `ℓ`-half: CN1's exactness (`classCoeffVal_exact`) pins
the true `addVal` of every lift's coefficients below the window (`npHgt_monicPoly_eq`, via
B.15's `npHgt_X`), so the class face makes every lift x-pure in ChapB's sense
(★ `isPure_monicPoly_of_face`), and the landed level-1 supply (B.18 `sideSet_nonempty`, B.57
`isPure_of_monic_factor`, B.35b `sideDeg_of_pure`, B.54 `inertiaDegOf_dvd_key_mul_resDeg`)
delivers the ramification leg (`dvd_ramIndexOf_of_isPure` — C61 §3b restated with the
`KeyFrame` fields as plain coprime data; no frame object constructed). B.56's
`factorizationType_eq_of_dvd` collapses the type at `e' = m`.

**(R3) AT the floor the criterion's CONCLUSION fails, not merely its proof** —
⚠ `eisenstein_face_floor_sharp`: at `m = 2`, odd `N`, the zero class carries the criterion's
FULL hypothesis vector (face attained at `0` and `2`, `Nat.Coprime N 2`, support `= 2N`)
except strict visibility (support `= e'·N` exactly), and it is `σ`-undecided for EVERY `σ`.
So `NPVisibleAt` cannot be relaxed to `≤`: CN1's polygon instability at the floor is REAL
undecidedness. Consistency with CN1's sharp pair: `(π,π)` and `(π³,π³)` both happen to have
type `{(2,1)}` — the class's undecidedness is witnessed by OTHER lifts (`X²`, type
`{(1,1),(1,1)}` via `typeOf_X_pow`, against the Eisenstein witness
`typeOf_eisenstein_witness`, type `{(m,1)}` — itself an instance of the criterion at window
`v+1`).

Bonus uniform floor statement: ⚠ `not_decidedAt_zero_class` — the zero class (the deep
boundary) is `σ`-undecided for EVERY `σ`, every `m ≥ 2`, EVERY window `N`, every DVR. The
deep boundary contributes ZERO to every decided count at every level — exactly what the
census's squeeze needs to know about the floor stratum.

## THE e = 2 INSTRUMENT (charge item 2) — run concretely, mechanism read off

    theorem decidedAt_quad_ram :        -- the depth-j ramified cone class, decided
      classCoeffVal c 0 = 2j+1 → 2j+1 < N → j+1 ≤ classCoeffVal c 1 →
      DecidedAt O 2 ⟨{(2,1)}⟩ N c
    theorem decidedAt_of_stratum_vzero_one :   -- the depth-0 cone slice, FULLY decided
      2 ≤ N → c ∈ levelZeroStratum O 2 N (X²) → classCoeffVal c 0 = 1 →
      DecidedAt O 2 ⟨{(2,1)}⟩ N c

**Which classes of the quadratic-ramified cone are decided at the frame floor: exactly the
strictly-visible odd-face classes** (`v₀ = 2j+1 < N`, `v₁ ≥ j+1`); the floor-touching
classes are provably undecided (§6). The depth-0 slice `v₀ = 1` is decided WITHOUT any side
condition beyond the stratum — its class count is the `(q−1)q^(2N−3)` monomial (counting is
CN4's job, not performed here).

**Mechanism verdict (confirmed by the proofs, not just the scan):** the deciding engine is
the LEVEL-1 x-frame purity machine fed through CN1's lift-exactness —
NOT the dv-graded Hensel engine (C133mh* lives at ChapC's `dvResPoly` carrier; needed only
when a face carries a nontrivial residual, `e' < m`, or for multi-face dissection),
NOT the s2Mu4/s2Mu5 refinement calculi (in-tower slope refinement at the S2 witness; the
cone's first face needs no refinement),
NOT a fresh recentring/ehat extension (that is CN5's base-change territory, δ ≥ 2).

## THE REDUCTION of the at-floor cone count (charge item 3)

    theorem quad_stratum_reduction :   -- ★ the dissection of the level-N quadratic stratum
      c ∈ levelZeroStratum O 2 N (X²) →
      DecidedAt O 2 ⟨{(2,1)}⟩ N c ∨ 2 ≤ classCoeffVal c 0 ∨ N ≤ 1

Every stratum class is criterion-decided (depth-0 face), or deep (`v₀ ≥ 2` — IFCG20's
recentring territory: the loop classes and the deeper faces, which recurse through the
smaller value laws per CN3), or the window is trivial (`N ≤ 1`: the stratum IS the floor,
provably all-undecided). So the `⟨{(2,1)}⟩`-decided cone count = Σ_j (criterion classes at
depth j: exact geometric monomials `(q−1)q^(2N−3(j+1))` — CN4 counts them) + the recentred
copy (CN3/IFCG20), with the floor contributing zero.

**Correction to ECONE's first-blood target, recorded:** `stratDecCount O 2 ⟨{(2,1)}⟩ N (X²)`
is NOT exactly `Σ_j (q−1)q^(2N−3(j+1))` — the UNSUBTRACTED stratum also contains deep
recentred ramified classes (`v₀ = 2j` even, unit-frame discriminant of odd valuation), which
are `{(2,1)}`-decided but not visible-odd-face. The geometric sum is the count for the
CONE-PROPER (loop-subtracted) object `coneCellCount` — exactly why the architecture removes
the recentred part. CN4 should target the cone, not the raw stratum.

## THE EXACT NAMED REMAINDER (honest fence — what CN2 did NOT close)

1. **General-position faces**: `FracFaceForcesRamStatement` (declared as a Prop, OPEN) — a
   visible fractional face ANYWHERE on the class polygon (`ClassNPFace c h e'`, `e' ≥ 2`,
   coprime, visible) forces a factor with `e' ∣ ramIndexOf` in every lift. Its pure instance
   is PROVED (`fracFaceForcesRam_pure`). The general position needs the Newton-polygon FACE
   FACTORIZATION over a complete DVR (a Hensel-grade input: either hoist ChapB's machinery
   past single-sidedness, or bridge C133mh's dissection to `Coeff` — FP1's GC0 by another
   name). This is the honest residue of C61's open `ℓ`-half at class level.
2. **Pure faces with `e' < m`** (`k = m/e' ≥ 2`): the criterion gives `e' ∣ ram` on every
   factor (PROVED) but the type is not pinned — the face's residual polynomial (degree `k`)
   dissects further. That refinement is where C.33/C133mh genuinely enter the census.
3. **Counting**: no cardinality was computed (CN4's charge). The criterion families are
   exact resOrd-fibre products; their counts are the RW1-row monomials.
4. **δ ≥ 2** (nonlinear centres/points): CN5's unramified base change, untouched.
5. `decidedAt_quad_ram` PLUS a split/inert criterion would close the full m = 2 census — the
   split (integer-slope) analogue is a DIFFERENT mechanism (needs completeness/Hensel for
   the reducibility direction) and was not attempted (not CN2's face).

## File map (`leanfinal/Uniformity/ChapI/IFCG23.lean`, 670 lines)

§1 valuation bridge (`addVal_eq_of_pow_dvd_not_dvd`, `not_pow_succ_dvd`; engine:
`Uniformity.Hensel.pow_dvd_iff_le_addVal`) · §2 purity bridge (`le_npHgt_monicPoly`,
`npHgt_monicPoly_eq`, `npHgt_monicPoly_top`, `classNPSupport_eq_of_attains_top`,
`suppVal_monicPoly_of_attains`, ★ `isPure_monicPoly_of_face`) · §3 the frame-free `e'`-leg
(`isKey_X` private, `dvd_ramIndexOf_of_isPure`) · §4 ★ `ramIndexOf_dvd_of_visible_face` +
★★ `decidedAt_of_eisenstein_face` · §5 `decidedAt_quad_ram`,
`decidedAt_of_stratum_vzero_one`, ★ `quad_stratum_reduction` · §6 `monicPoly_zero`,
`monicFactors_X_pow`, `typeOf_X_pow`, `typeOf_eisenstein_witness`,
⚠ `not_decidedAt_zero_class`, ⚠ `eisenstein_face_floor_sharp` · §7
`FracFaceForcesRamStatement` (open Prop) + `fracFaceForcesRam_pure` · AxCheck footer
(15 lines, all Lean core). Aggregator: one import line in `Uniformity/ChapI.lean`.

## Repair log (5 error rounds, all trivial; the §3 transcription and BOTH §4 criterion theorems landed FIRST TRY)

1. Helper lemma inserted between a docstring and its theorem (parse); `add_le_add_right`
   orientation → `gcongr`.
2. One leftover cast goal `↑(h*m) = ↑h*↑m` — explicit `Nat.cast_mul` chain instead of
   `push_cast`.
3. Fin-coercion defeq: `rw [ha']` leaves beta-redexes on `set`-bound vectors — use
   `rfl`/`show` (set-fvars are let-bound, defeq unfolding applies); `omega` cannot see
   through `(⟨j,hj⟩ : Fin m).val`.
4. `Nat.dvd_sub'` → `Nat.dvd_sub` at this pin; `Nat.add_sub_cancel_left` as a term didn't
   unify → `simp`.
5. `le_or_lt` unknown at this pin → `Nat.lt_or_ge`. Also: all support arithmetic with TWO
   symbolic factors (`v*m` vs `m*(v+1)`) is nonlinear — omega rejects it; manual
   `Nat.mul_comm`/`Nat.le_add_right`/`ring` calc chains (recorded for CN4, whose sums will
   hit the same wall).
