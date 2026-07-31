# LEANW6 — Lean units U-B + U-D + U-E executed (2026-08-01)

Dispatch: the SYNTH4 §4 unlocked Lean units (`lean/notes/SYNTHESIS_PASS4_2026-08-01.md`,
ACCEPTED per the ledger at dbccbc1), cross-read with `openmath/O3adj_adjudication.md`.
Discipline held: **new modules only; every existing statement byte-untouched; per-file
`lake env lean` gates + targeted `lake build` (8639 jobs, green); Lean-core axioms
only (`propext, Classical.choice, Quot.sound`) on every declaration; no `sorry`.**
None of the three units touches capstone-path code (leaf modules), so no
AxChk_baseline rerun was owed. One commit per unit.

## U-D — O5triple Theorem B's abstract counting core (commit c8b32e3)

File: `lean/LeanUrat/MovesU/O5CountingB.lean` (3 theorems).

* `surj_of_injOn_checksum` — an injection `φ : s → t` (Finsets) with all weights on
  `t` ≥ 1 and equal weighted totals `Σ_{a∈s} w(φ a) = Σ_{b∈t} w b` is ONTO `t`
  (the complement's total is 0 with all terms ≥ 1).  This is the verbatim arithmetic
  of O5triple Theorem B (`O5triple_phaseB_verifybrief_rev2.md` §6; V18/V23 no
  criticals): injectivity = (I-2), the two checksums = (I-3) + Theorem A(4).
* `bijOn_of_injOn_checksum` (`Set.BijOn` packaging), `card_eq_of_injOn_checksum`
  (|slots| = |leaves|).

CONSUMERS PARKED: instantiation at the engine/semantic carriers waits on the
(I-1)–(I-3) interface (K-RUN-C composition, O3adj §3.1 CU-7).  This gives the D-7b
"coverage consumes NO no-missing" mechanism its permanent Lean core.

## U-B — the O-12 pole-free theorem's Lean layer (commit 062a0bd)

File: `lean/LeanUrat/MovesU/O12PoleFree.lean` (16 checked declarations).
Source: the VERIFIED brief `openmath/O12_phaseB_verifybrief_rev4.md`.

* **𝒮 and L5**: `cycS` = the multiplicative set ⟨q, q^c−1 (c ≥ 1)⟩ ⊂ ℚ[q];
  `cycS_eval_pos` — every member strictly positive at every rational x ≥ 2.
* **ℛ = ℚ[q][𝒮⁻¹] (L7)**: `MemRcyc` + ring closure (add/mul/neg/sub, polynomials,
  𝒮-inverses); `MemRcyc.definedAt` = L7(i) (no pole at x ≥ 2, via
  `RatFunc.denom_div_dvd`); `MemRcyc.eval_ne_zero_of_inv` = L7(iii)'s consumption
  shape (ℛ-units evaluate nonzero); `MemRcyc.powSubst` = L7(ii) (closure under the
  (g5) base change q ↦ q^δ, `MovesS.powSubst`, via `cycS_expand`).
* **The grammar**: inductive `Gram` ((g1) poly, (g2)–(g4) as poly/𝒮-inverse
  composites, (g5) subst, (g6) add/mul/neg) + `Gram.memRcyc` — Theorem 2's
  absorption step.  ((g7)'s unit division is consumed at the theorem layer via
  `memRcyc_inv_cycS`, not a constructor.)
* **Corollary D margins, exact rationals**: `marginO1/O2/O3` (3/4, 7/8, 6/7 at
  x ≥ 2, E ≥ 3) + `eval_ratio` (polynomial-ratio evaluation) + the displayed
  booking determinants `detO1/detO2/detO3` with `detO*_unit` (nonzero ℛ-units,
  L7(iii)) and `detO*_margin` (the evaluated margins).
* **THE POLE-FREE THEOREM**: `AbsSolveTable` (per block a 1×1-kernel determinant
  Φ_e + finite entry list E(e)); `RegAt` = (r1)+(r2) at the corpus `DefinedAt`;
  `regAt_of_discipline` — ℛ-unit determinants + ℛ entries ⟹ (REG) at EVERY
  rational x ≥ 2; `regAt_primePow` — hence at every prime p, every depth δ ≥ 1
  (O12 Theorem 3's mechanism: the failing set is empty).

CONSUMERS PARKED (per the brief's own scope): the identification of the concrete
𝔅_n tables (bookings × composition data × allocation data) with an `AbsSolveTable`
satisfying `RcycDiscipline` is the instance-pin seam — D-11 + OL-O12-1/OL-O12-2,
expressly outside the O-12 claim.  Value correctness excluded (V7-F1 on record).
`RegP`/`RegData`/`RegPFinite` untouched.

## U-E — the WGEO/VTX degree-1 perimeter (commit 74ecc4b)

File: `lean/LeanUrat/HC2/UE_vtxUpper.lean` (4 theorems).
Source: O-1thr rev 3 §2.5 (`openmath/O1thr_phaseB_verifybrief_rev3.md`,
Corollary VTX); twins HK-11a/HK-52 per SYNTH4 §4.

* `UE.childW_ge_estar_mul_w` — **the new kernel**: at any `ReadFrame` with WEAK
  steepness e★·σ.h ≤ h★, the read functional dominates e★·σ.w on EVERY nonzero
  polynomial (not just key coefficients, where `hStretch` is equality).  This is
  the level-i development-identity consumption Corollary VTX displays as
  "e_i·w_i(C_μ) ≤ w_{i+1}(C_μ)".  Proof = `ReadFrame.hK1` (attained slot-min) +
  `Stage.hK1`/`hwΦ` (parent slot-min lower bound) + steepness on the slot term.
* `UE.regrade_ge_estar_mul_w` — the kernel at a recorded regrade
  (via `HK11a.regrade_w_eq_childW`).
* `UE.vtx_m6bi_n4upper` — **the packaged Corollary-VTX shape** at a coherent
  `ReadsOf` record, non-recentering read i: (a) `B μ ≠ 0` = **the (M6b)(i) row**;
  (b) `e★·σᵢ.w(B μ) ≤ gam − μ·e★·h★·g` = **the (N4)-UPPER with the shear slack
  displayed**; (c) `e★·σᵢ.w(B μ) ≤ gam`.  Supply = `HK11a.sigmaV_vertexLaw`
  (the vertex pin) + the kernel.
* `UE.vtx_htUpper_div` — the ℚ display `vhtx ≤ γ/e₀ = I` verbatim.

Carried hypotheses (same trio as HK-11a, named in the header): `StageCoreL σᵢ`
(tower provenance), STRICT read steepness (genuine at root/post-recentering reads,
HK-12 F5), non-recentering species.  **The e′-stretch seam does NOT enter**: all
conclusions live at the parent frame σᵢ/regrade σV, below the ν_{i+1}.e stretch
HK-52 compiled — which is exactly why the degree-1 (N4)-upper is unconditional in
e′, documenting WHY HK-11a's consumption shapes carry the e′ = 1 guard while this
band does not.

**Retirement status of the interface rows** (the SYNTH4 claim, stated honestly):
this unit SUPPLIES the (M6b)(i) and (N4)-upper content at the corpus carriers; the
rows themselves live in the O-1thr brief's interface vocabulary and in future
`GDInterface` fields (SYNTH4 U-A), not as standing Lean hypotheses today — so
"retire" = consumers that would have carried those rows now have a proved supplier
to key to.  The LOWER (N4) band and (M6b)(iii) AUX remain open with O-1thr's
residue, NOT claimed.  V9's four sorries are untouched (the HK-12 F4 ν_{i+1}.e
adjudication still gates them).

## Deferred / not attempted (honest scope)

* U-A (`GDInterface` design), U-C (Dfloor, waits on pass 2), U-F (waits on V8),
  U-G (waits on O-2a pass 2) — not in this dispatch.
* U-E's WGEO clauses (c)/(d) (full-polygon/beyond-window geometry) are NOT
  formalized here — the dispatch's retirement targets were exactly (M6b)(i) and
  (N4)-upper, both covered; the beyond-window strictness layer would ride a future
  window-hull carrier.
* U-B: the four bookings' SOLVE algebra (Theorem 1(3)) and Fact F/L6 cell
  combinatorics are instance-side, behind the parked pin.
