/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# HC1.CL11_posUniq — 𝔽_p[x] positional uniqueness (BP5 CL-11, REVISION-2 statement)

**Unit CL-11** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4;
REVISION 2 finding 1 — degeneracy hypotheses ADDED; risks R-1/R-2). **GATED on
CL-10's clean outcome** (countermodel-first: the NCL probe must complete before any
prover works this unit).

**Informal statement (over any field `K₀`, applied at `K₀ = 𝔽_p` by CL-12).** For a
NONEMPTY finite set of DISTINCT slot vectors `s : Fin (K+1) → ℕ`, bounded by
`slotBound` at inner levels and CONSTANT (`= b`) at the top, monic `Φ̄_r` with
`0 < deg Φ̄₀` and the exact key-degree ratio law
`deg Φ̄_{r+1} = slotBound r · deg Φ̄_r`, and nonzero digits `d̄_s` with
`deg d̄_s < deg Φ̄₀`:  `Σ_s d̄_s · ∏_r Φ̄_r^{s r} ≠ 0`.

**DEGENERACY RECORD (the REVISION-2 repair, verbatim from the blueprint).** As
previously sketched the EMPTY slot-vector set satisfied every hypothesis and gave
`Σ = 0` — the statement was FALSE. NONEMPTY is the load-bearing addition;
`0 < deg Φ̄₀` is then derivable (a nonzero digit with `deg d̄ < deg Φ̄₀` forces
`deg Φ̄₀ ≥ 1`) but is stated explicitly because the div/mod induction consumes it
directly — this writer keeps it as a hypothesis (the permitted downgrade to a
derived `have` is left to the prover, WITH a note; the nonemptiness may NEVER be
dropped). Both discharge for free at the CL-12 site: survivor set nonempty (`y ≠ 0`,
`l_min` attained) and `(T.stg 0).hdeg : 1 ≤ Φ.natDegree` + monic-map degree
preservation (CL-27(b) `red_monic_deg`).

**Proof sketch.** Strong induction on the highest inner level where the slot
vectors differ; Euclidean uniqueness of div/mod by `Φ̄_r^{(min slot at level r)}`
with the degree bound `Σ_{r'<r} slotBound·deg < deg Φ̄_r` (the mixed-radix carry
bound — T9(b)'s numeric kernel shape re-used, here in degree form:
`CL11a_prefix_degree_lt` below); base case: no inner level left, one term (the slot
vectors were distinct), `d̄ ≠ 0` times a monic power ≠ 0. The top slot is CONSTANT
`b`, so `Φ̄_K^b` factors out (monic over a field, ≠ 0) — the induction runs on inner
levels only.

**E-phase resolutions recorded.**
* "finite set of DISTINCT slot vectors ... digits d̄_s" is transcribed as a
  `Finset (Fin (K+1) → ℕ)` (distinctness = Finset elementhood) with a digit
  function `d` read on `S`; all hypotheses quantify over `s ∈ S`.
* Degree forms: `degree` (WithBot) for the digit bound — matching CL-27(b)'s
  `red_digLift_deg`, the discharging lemma — and `natDegree` for the ratio law and
  `0 < deg Φ̄₀`, matching `red_ratio_law`/`red_monic_deg`. **R-2 fence: the digit
  bound has NO lower-degree companion and must never gain one** (reduced digits may
  drop degree).
* SPLIT RULE (CL-11a/b, exercised): the div/mod DEGREE sublemma is emitted here as
  the standalone `CL11a_prefix_degree_lt` (the carry bound: any digit-cleared prefix
  stays strictly below the next place-value degree); the main statement is
  `CL11_posUniq`.

**Deps.** CL-10 (gate; must complete first). Tower-independent — imports Mathlib
only. difficulty: hard-fable. Size: ~150. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

/-- **CL-11a** (the div/mod degree sublemma — the mixed-radix carry bound in degree
form): a digit-cleared prefix `d · ∏_{r < n} Φ̄_r^{s r}` (digit degree below
`deg Φ̄₀`, inner slots below their bounds) has degree strictly below `deg Φ̄_n`.
Junk-true at `d = 0` (`degree ⊥`). Telescopes on the exact ratio law:
`deg Φ̄₀ + Σ_{r<n} (slotBound r − 1)·deg Φ̄_r = deg Φ̄_n`. -/
theorem CL11a_prefix_degree_lt {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀)
    (hmonic : ∀ r, (Φ r).Monic)
    (hdeg0 : 0 < (Φ 0).natDegree)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree)
    (s : Fin (K + 1) → ℕ) (n : Fin (K + 1))
    (hbound : ∀ r : Fin K, (r : ℕ) < (n : ℕ) → s r.castSucc < slotBound r)
    (d : Polynomial K₀) (hddeg : d.degree < (Φ 0).degree) :
    (d * ∏ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
        (Φ r) ^ (s r)).degree < (Φ n).degree := by
  sorry

/-- **CL-11 (REVISION-2 statement)**: positional uniqueness of the mixed-radix
Φ̄-development with bounded nonzero digits, over any field. NONEMPTY + `0 < deg Φ̄₀`
are the REVISION-2 degeneracy hypotheses (see the file header; nonemptiness may
never be dropped). Applied by CL-12 at `K₀ = 𝔽_p` with `Φ̄ = red ∘ Φ`,
`slotBound = T.slotBound`, `d̄ = red ∘ digLift`, hypotheses discharged by CL-27(b). -/
theorem CL11_posUniq {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀) (b : ℕ)
    (hmonic : ∀ r, (Φ r).Monic)
    (hdeg0 : 0 < (Φ 0).natDegree)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree)
    (S : Finset (Fin (K + 1) → ℕ)) (hSne : S.Nonempty)
    (hbound : ∀ s ∈ S, ∀ r : Fin K, s r.castSucc < slotBound r)
    (htop : ∀ s ∈ S, s (Fin.last K) = b)
    (d : (Fin (K + 1) → ℕ) → Polynomial K₀)
    (hd : ∀ s ∈ S, d s ≠ 0)
    (hddeg : ∀ s ∈ S, (d s).degree < (Φ 0).degree) :
    ∑ s ∈ S, d s * ∏ r, (Φ r) ^ (s r) ≠ 0 := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL11a_prefix_degree_lt
#print axioms LeanUrat.HC1.CL11_posUniq
