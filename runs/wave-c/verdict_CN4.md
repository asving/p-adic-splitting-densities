# UNIT CN4 — VERDICT: THE CONE COUNTED — e = 2 CLOSED FOR EVERY TYPE, THE PURE-FACE SECTOR CLOSED AT EVERY m, THE REMAINDER NAMED (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG24.lean` (1262 lines, ZERO sorries; all
14 AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`; the
C.33 cite does not occur — no ChapC import at all, the only "C133" text is docstring
prose naming the remainder's discharge territory; no landed file touched except the
sanctioned one-line aggregator import in `Uniformity/ChapI.lean`; no git ops).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG24.lean`
(final run: zero errors, zero warnings), targeted `lake build Uniformity.ChapI.IFCG24`
green (8930 jobs), `lake env lean Uniformity/ChapI.lean` (aggregator) green.

## ★★★ THE STRUCTURAL THEOREM (uniform in m): the zero-centre recentring range IS the deep box

    theorem range_fullLoopClassN_zero :          -- ★ the zero-range theorem
      Irreducible π → 0 < m →
      Set.range (fun d : MBoxN O m M => fullLoopClassN π (0, d))
        = {c : Coeff O m (M+m) | ∀ i : Fin m, m - i ≤ resOrd (c i)}   -- =: deepBox

⊆ is the binomial law: `loopMapN 0 π d = shiftVecN (loopVecN π d) w` with
`w = resSect O 0 ∈ 𝔪`, and coordinate `i` of the shift carries `π^(m−j)·w^(j−i)` per
term (IFCG1's `shiftVecN_apply`; the `j < i` terms die on `Nat.choose_eq_zero_of_lt`).
Equality is by COUNTING: both sides have exactly `q^(mM + κ_m)` elements
(`card_MBoxN_kappaLoop` = the new `card_deepBox`), and `fullLoopClassN` is injective
(landed).  Hence (`coneCellCount_zero_eq`, uniform in m and σ):

    coneCellCount O π m σ M 0 = #(decidedSet σ ∩ stratum(X^m) ∩ SHALLOW)
      where SHALLOW = {c | ∃ i, resOrd (c i) < m − i}

**The cone is the immediate-face part and nothing else: the loop subtraction removes the
ENTIRE deep box** — the recentred copy exactly, no orphans, no leakage.  This also shows
`coneCellCount · 0` is π-independent (the carrier is π-free).

## ★★ FIRST BLOOD — the e = 2 cone count, EXACT at every finite level

    theorem coneCellCount_two_ram :   -- σ = ⟨{(2,1)}⟩ (totally ramified)
      coneCellCount O π 2 ⟨{(2,1)}⟩ M 0 = (q − 1) · q^(2M+1)
    theorem coneCellCount_two_ne  :   -- every other σ
      σ ≠ ⟨{(2,1)}⟩ → coneCellCount O π 2 σ M 0 = 0

Mechanism: shallow ∩ stratum at m = 2 is exactly `{v₀ = 1, v₁ ≥ 1}`
(`coneSet_two_ram`, via the new two-sided `mem_stratum_X_pow_iff`); every such class is
decided ramified (CN2's `decidedAt_of_stratum_vzero_one`), so the ramified cone is the
FULL box — ECONE's depth-0 monomial `(q−1)q^(2N−3)` at `N = M+2`, EXACTLY; and by
`decidedAt_unique` no other type touches the shallow classes — the split/inert/unramified
quadratic content lives entirely in the recentred copy.

    theorem zeroConeClause_two (σ) : ZeroConeClause 2 σ    -- ★★ the e=2 clause FIRES
      -- ZeroConeClause m σ := ZcURLim (coneFamily m σ): ZeroConeLaw's clause body
      -- verbatim, one (m, σ) at a time.  Pairs: (X − 1, X³) at ⟨{(2,1)}⟩ (value
      -- (q−1)/q³, a CONSTANT sequence); (0, 1) otherwise.  UNCONDITIONAL (m = 2 sits
      -- below the law's m ≥ 4 quantifier; no smaller-law premises consumed).

## ⚠ THE CORRECTION TO CN2's CORRECTION — machine-checked, not prose

CN2's verdict recorded (correcting ECONE) that the geometric sum
`Σ_j (q−1)q^(2N−3(j+1))` counts the loop-subtracted cone.  The truth is one step MORE
drastic, and is now a theorem: the loop subtraction removes EVERY depth-`j ≥ 1` slice
too —

    theorem quadDepthSlice_subset_range : 1 ≤ j →
      {v₀ = 2j+1, v₁ ≥ j+1} ⊆ Set.range (fun d => fullLoopClassN π (0, d))

(immediate from the zero-range theorem: `2j+1 ≥ 2`, `j+1 ≥ 1`).  So the cone keeps ONLY
depth 0 — one monomial, constant normalized value `(q−1)/q³`, NOT a series.  The series
is the FULL decided density, resummed by the architecture's fixed-point recursion at
ratio `q^(−T₂) = q^(−3)` (IFCG14's engine — already landed, not re-proved here):

    theorem card_quadDepthSlice : 2j+1 < K →
      #{v₀ = 2j+1, v₁ ≥ j+1 at level K} = (q−1)·q^(2K−3(j+1))   -- the RW1 monomials
    theorem quad_cone_geometric_regression : 2 ≤ q →
      HasSum (fun j => (q−1)/q^(3(j+1))) (1/(q²+q+1))            -- ECONE's instrument
                                                                  -- value RECOVERED ✓

The regression closes: cone monomial × recursion multiplier = 1/(q²+q+1), exactly as
the instrument demanded — with the loop-subtracted correction applied at its true depth.

## ★★ GENERAL e — the pure-face monomial bank and the exact partition

    def faceBox O m K h := {c | npHeight c 0 = h ∧ ∀ i, h(m−i) ≤ m·resOrd(c i)}
    theorem faceBox_subset_decided : 0 < m → gcd(h,m)=1 → h < K →
      faceBox O m K h ⊆ decidedSet O m ⟨{(m,1)}⟩ K        -- CN2's criterion consumed
    theorem card_faceBox : #faceBox = (q−1)·q^(mK − wFace m h)  -- EXACT, every level
      -- wFace m h = 1 + h + Σ_{0<i<m} ⌈h(m−i)/m⌉ : the K-INDEPENDENT weight (RW1 row)
    theorem coneCellCount_partition_ram :                   -- ★ the finite-level count
      coneCellCount O π m ⟨{(m,1)}⟩ M 0
        = Σ_{h ∈ faceH m} (q−1)·q^(m(M+m) − wFace m h) + coneRemainderCount O m ⟨{(m,1)}⟩ M
    theorem coneCellCount_eq_remainder_of_ne : σ ≠ ⟨{(m,1)}⟩ →
      coneCellCount O π m σ M 0 = coneRemainderCount O m σ M
    theorem coneRemainder_two_ram_eq_zero :                 -- consistency: m = 2 closes
      coneRemainderCount O 2 ⟨{(2,1)}⟩ M = 0

`faceH m = {h | 1 ≤ h < m, gcd(h,m) = 1}`; each admissible box is decided-{(m,1)}
(endpoint-spanning Eisenstein face, `decidedAt_of_eisenstein_face`), inside stratum and
shallow cone, pairwise disjoint (pinned by `v₀ = h`); the boxes with `h ≥ m` are deep
(recentred copy) and correctly excluded by the zero-range theorem.  All uniform in
`(q, m, h)`.

## ★★★ THE WIRING — what is discharged, what the front now rests on

    def ConeRemainderLaw (m σ) : Prop    -- THE NAMED REMAINDER (the input Prop):
      -- one rational pair for the normalized count of the decided shallow classes
      -- OUTSIDE every pure-face box.  π-free carrier.  Discharge territory (CN2 §7
      -- verbatim): general-position fractional faces (needs the NP face factorization
      -- = C61's open ℓ-half / FP1's GC0) and pure faces with e' < m (residual
      -- refinement — where C.33/C133mh genuinely enter).
    theorem zeroConeClause_of_remainderLaw : 0 < m → ConeRemainderLaw m σ → ZeroConeClause m σ
    theorem zeroConeLaw_of_remainderLaws :
      (∀ m ≥ 4, (smaller value laws < m) → ∀ σ deg-m Witnessed, ConeRemainderLaw m σ)
        → ZeroConeLaw
    theorem centeredConeLaw_of_remainderLaws : (same) → CenteredConeLaw
    theorem decidedSliceAt_all_of_pointCone_remainder :     -- ★★★ the census front
      PointConeLaw → (remainder laws) → ∀ n, DecidedSliceAt n

**Honest status.** `CenteredConeLaw`/`ZeroConeLaw` are NOT discharged — they are
REDUCED: the pure-face (endpoint-spanning) sector is closed UNCONDITIONALLY at every
`(m, σ)` (an exact monomial bank at every finite level, absorbed by the new ZcURLim
pair calculus §1 — the uniformizer-parametrized mirror of IFCG21's `PtURLim`), and the
exact open residue is `ConeRemainderLaw` at each `(m ≥ 4, σ)` — with the same
conditional supply the law itself carries.  `PointConeLaw` is untouched (CN3's
linear-centre conversion + CN5's unramified base change).  At `m = 2` the remainder is
PROVED EMPTY — that is how the first blood closes.  Nothing was weakened; `m = 2`
values are regression instruments, per directive.

## What CN4 did NOT close (exact fence)

1. `ConeRemainderLaw m σ` for `m ≥ 4` — the named remainder (above).  At `m = 3` (not a
   law clause, but the next instrument) the remainder is nonempty: e.g. `v₀ = 2, v₁ = 1`
   has hull faces of slopes 1 and 1/2 — a general-position dissection, type
   `{(1,1),(2,1)}`-shaped, beyond the pure criterion.
2. `PointConeLaw` (δ ≥ 1 point cones) — open, CN3/CN5.
3. The full-density resummation (cone → 1/(q²+q+1) via the fixed point) is checked as
   the ℝ-identity `quad_cone_geometric_regression`; the DecidedValueLaw-level tie at
   m = 2 is the landed IFCG14/IFCG20 machinery's business, not re-derived here.

## File map (`leanfinal/Uniformity/ChapI/IFCG24.lean`, 1262 lines)

§1 `ZcURLim` calculus (congr/add/zero/sum/★ `ZcURLim_qmonomial`) · §2 toolkit
(`resFactor_eq_zero_iff`, `card_setOf_le_resOrd` = q^(K−k) via the resFactor-kernel
count, `card_setOf_resOrd_eq` = (q−1)q^(K−k−1), `card_pi_set`, private fibre helpers) ·
§3 `deepBox`/`shallowSet`, `dvd_resSect_zero`, `dvd_loopMapN_zero` (the binomial heart),
`range_zero_subset_deepBox`, `card_deepBox`, ★ `range_fullLoopClassN_zero` ·
§4 `mem_stratum_X_pow_iff`, ★ `coneCellCount_zero_eq` · §5 `coneSet_two_ram`,
★★ `coneCellCount_two_ram`, `coneCellCount_two_ne` · §6 `coneFamily`, `ZeroConeClause`,
★★ `zeroConeClause_two(_ram/_ne)` · §7 `card_quadDepthSlice`,
⚠ `quadDepthSlice_subset_range`, `quad_cone_geometric_regression` · §8 `tF`/`tF_le_iff`,
`npHeight_coe`, `faceBox` + stratum/shallow/★ decided legs, `wFace`/`wFace_le`,
★ `card_faceBox` · §9 `faceH`, `pureFaceSet`, `coneRemainderCount`,
★ `coneCellCount_partition_ram`, `coneCellCount_eq_remainder_of_ne`,
`coneRemainder_two_ram_eq_zero` · §10 `ConeRemainderLaw`,
★★ `zeroConeClause_of_remainderLaw`, ★★★ `zeroConeLaw_of_remainderLaws` +
`centeredConeLaw_of_remainderLaws` + `decidedSliceAt_all_of_pointCone_remainder` ·
AxCheck footer (14 lines, all Lean core).  Aggregator: one import line in
`Uniformity/ChapI.lean`.

## Repair log (7 error rounds, all mechanical; every theorem landed as designed — no mathematical failures)

1. Skeleton: `coneRemainderCount (O : Type)` vs `Type*` universe clash.
2. `rw` of `K−k = (K−k−1)+1` recursed into `K−k−1` → close with `Nat.add_sub_cancel`;
   `Set.mem_diff`/`Set.ncard_diff`/`push_neg` deprecations (→ `mem_sdiff`/`ncard_sdiff`/
   `push Not`).
3. `{c | ∀ i, c i ∈ S i}` with an `(i : ℕ)` coercion in the body makes the elaborator
   infer `i : ℕ` — bind `∀ i : Fin m` explicitly.  IFCG23's `monicPoly_zero` carries a
   baked `[IsAdicComplete]` section variable (linter.unusedSectionVars false) — reproved
   adic-free locally.
4. `fin_cases` leaves `⟨0,⋯⟩` mk-forms: omega sees DIFFERENT atoms from `c 0` — add
   `Fin.zero_eta`/`Fin.mk_one` to the simp.  The local `Classical.propDecidable`
   instance blocks the `reduceIte` simproc — use `if_pos`/`if_neg` with explicit proofs
   (instance-agnostic).
5. `rw [dif_pos]` does not auto-close across the `classCoeffVal` def — explicit `rfl`.
6. `hΣadd`: `Σ` is not a legal identifier character — parse error TRUNCATES the proof
   and reports as "unsolved goals" at the `by` line (trap recorded).
7. `nlinarith` misses `q³ ≥ 8` from `q ≥ 2` — supply `2³ ≤ q³` by `gcongr`, downgrade
   to `linarith`.  Twice, a closing tactic found "no goals" (field_simp/rw finished
   early via numeral defeq) — deleted.
