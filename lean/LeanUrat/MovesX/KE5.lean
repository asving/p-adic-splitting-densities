/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE5 — [ATTEMPT] X2TailsP: the tall-event tail from the D4R.2 pool bound

BRIDGE CAMPAIGN unit **KE5** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-iv) + §4 KE5, risk R8).
PROVED (2026-07-30, prover BP4-P8) — sorry-free, Lean-core axiom footprint.

THE KERNEL: `X2TailsP n X K` (MovesX/Defs.lean) —
`frac(TallEvent h*) ≤ C_T·p^{−c_T·h*}`. Blueprint sketch: price the FIRST
height-≥h* read via the D4R.2 pool bound `μ(P̂) ≤ M(P̂)·p^{W(P̂)−A(P̂)}` (`A`
grows with the tall read's height); union over prefixes with the per-depth
species-menu factor; CONVERGENCE OF THAT SERIES IS THE RISK (R8).

RECORDED RESOLUTIONS:
1. `TallExtEvent C H h*` (defined below) is the first-read event: some branch's
   history is `H ++ [ν]` with `h* ≤ ν.h`. The covering
   `TallEvent ⊆ ⋃_{d<cap} ⋃_{H realized, |H|=d} TallExtEvent ∪ (TallEvent ∩ DeepEvent cap)`
   holds by the earliest-tall-node ancestor (`parent_hist` prefixes; `termLast`
   converts length to `dTotal`); `realizedHists` is NOT restricted to tall-free
   prefixes (a superset union — sound and simpler).
2. INTERFACE-FORCED SHAPE: `XCtx.frac` has FINITE subadditivity
   (`frac_union_le`) and null countable unions ONLY — no countable
   subadditivity. The note's "sum over prefixes" is therefore transcribed as a
   FINITE depth window `depthCap h*` plus the deep remainder
   `frac(TallEvent ∩ DeepEvent (depthCap h*))`, both priced inside one field
   (`series_ok`). Any route must supply its own cutoff; this is recorded as an
   interface note, not a weakening (the target `X2TailsP` is verbatim).
3. ⚑ `TailsRoute` is the NAMED CARRIER (Q4 shape) bundling: the D4R.2 read
   price (`read_price`, depth-indexed), the species-menu count (`menu_card` on
   `realizedHists` — §M-SPECIES finite menus), and the R8 risk EXACTLY at
   `series_ok` (the summed window + remainder vs. `C_T·p^{−c_T·h*}`). If
   `series_ok` is uninhabitable, the divergent-series obstruction record is
   the deliverable.

deps: KE4 PHASE 1 (CM gate — candidate-stress + divergence detection runs
FIRST); MovesD mass laws (D4R.1/D4R.2 built) for the instance leg; ACCEPTANCE
GATED on KE4 phase 2 against the prover's actual constants (REV 2, F10).
Consumers: X.2's exponential envelope leg (CL-2/CL-3 tag set).

GATE RECORD (2026-07-30, prover BP4-P8): KE4 phase 1 PASSED 14/14 (exit 0,
pre-prover); `x2Tails_of_route` PROVED below (Lean-core footprint); KE4
PHASE 2 re-ran on the drafted pair (C_T, c_T) = (1200488, 1) — the D4R.2
composition's constants uniformized over p (max of the per-box sketch
values) — 2/2 PASS, exit 0. Acceptance gate CLEAR; the remaining owner-side
work is the per-prime `TailsRoute` instance leg (MovesD).
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- KE5 event vocabulary — the FIRST-tall-read extension event of a prefix `H`:
some branch of `f` has history exactly `H ++ [ν]` with a tall read `h* ≤ ν.h`. -/
def TallExtEvent {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (H : XHistory n)
    (hstar : ℕ) : Set (MonicBox n p) :=
  { f | ∃ b : C.Branch f, ∃ ν : XNode n, hstar ≤ ν.h ∧ C.hist b = H ++ [ν] }

/-- KE5 counting vocabulary — the depth-`d` REALIZED prefixes of a context: the
histories of length `d` realized by some branch of some box point (the union
index of the first-read decomposition; unrestricted per resolution 1). -/
def realizedHists {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (d : ℕ) :
    Set (XHistory n) :=
  { H | H.length = d ∧ ∃ f : MonicBox n p, ∃ b : C.Branch f, C.hist b = H }

/-- **KE5 named carrier (⚑ ratification)** — one context's tails route:
* `read_price` — the D4R.2 pool bound, packaged per prefix depth: the first-read
  event after any depth-`d` prefix has mass ≤ `price d h*`;
* `menu_finite`/`menu_card` — the per-depth species-menu factor: at most
  `menu^d` realized depth-`d` prefixes (§M-SPECIES finite menus);
* `series_ok` — THE R8 FIELD: the finite depth window `depthCap h*` of
  menu-weighted prices plus the deep remainder is dominated by the target
  envelope `CT·p^{−cT·h*}` (interface-forced finite shape, resolution 2). -/
structure TailsRoute (n p : ℕ) [Fact p.Prime] (C : XCtx n p) (CT cT : ℝ) where
  menu : ℕ
  price : ℕ → ℕ → ℝ
  depthCap : ℕ → ℕ
  price_nonneg : ∀ d hstar : ℕ, 0 ≤ price d hstar
  menu_finite : ∀ d : ℕ, (realizedHists C d).Finite
  menu_card : ∀ d : ℕ, (realizedHists C d).ncard ≤ menu ^ d
  read_price : ∀ (H : XHistory n) (hstar : ℕ),
    ((C.frac (TallExtEvent C H hstar) : ℚ) : ℝ) ≤ price H.length hstar
  series_ok : ∀ hstar : ℕ,
    (∑ d ∈ Finset.range (depthCap hstar), (menu : ℝ) ^ d * price d hstar)
        + ((C.frac (TallEvent C hstar ∩ DeepEvent C (depthCap hstar)) : ℚ) : ℝ)
      ≤ CT * (p : ℝ) ^ (-(cT * hstar))

/-- KE5 helper — finite subadditivity of the box content over a `Finset`-indexed
union with a remainder set: `frac((⋃ H ∈ s, A H) ∪ Rem) ≤ Σ frac(A H) + frac Rem`
(pure `frac_union_le` induction; the remainder slot avoids ever needing
`frac ∅ ≤ 0`, which the interface does not provide). -/
private lemma frac_biUnion_union_le {n p : ℕ} [Fact p.Prime] (C : XCtx n p)
    (s : Finset (XHistory n)) (A : XHistory n → Set (MonicBox n p))
    (Rem : Set (MonicBox n p)) :
    C.frac ((⋃ H ∈ s, A H) ∪ Rem) ≤ (∑ H ∈ s, C.frac (A H)) + C.frac Rem := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Set.union_assoc, Finset.sum_insert ha]
      calc C.frac (A a ∪ ((⋃ H ∈ s, A H) ∪ Rem))
          ≤ C.frac (A a) + C.frac ((⋃ H ∈ s, A H) ∪ Rem) := C.frac_union_le _ _
        _ ≤ C.frac (A a) + ((∑ H ∈ s, C.frac (A H)) + C.frac Rem) := by linarith
        _ = (C.frac (A a) + ∑ H ∈ s, C.frac (A H)) + C.frac Rem := by ring

/-- **KE5 [ATTEMPT]** — `X2TailsP` from a tails route at every prime: the
first-read covering (resolution 1) + finite subadditivity (`frac_union_le`,
`frac_mono`) bound `frac(TallEvent h*)` by the depth-window sum plus the deep
remainder; `menu_card` and `read_price` dominate each depth slice by
`menu^d·price d h*`; `series_ok` closes against `K.CT·p^{−K.cT·h*}`.
deps: KE4 phase 1 (gate — runs FIRST), `TailsRoute` (⚑); acceptance gated on
KE4 phase 2 (the prover's actual constants re-probed). Fallback: the
divergent-series obstruction record. -/
theorem x2Tails_of_route {n : ℕ} (X : XFamily n) (K : XConsts n)
    (hroute : ∀ (p : ℕ) [Fact p.Prime],
      Nonempty (TailsRoute n p (X.ctx p) K.CT K.cT)) :
    X2TailsP n X K := by
  unfold X2TailsP
  intro p _ hstar
  obtain ⟨R⟩ := hroute p
  haveI : DecidableEq (XHistory n) := Classical.decEq _
  -- (a) every `take` of a branch history is an ancestor's history
  --     (`parent_hist` prefixes along `reach`).
  have hprefix : ∀ (f : MonicBox n p) (b : (X.ctx p).Branch f) (i : ℕ),
      ∃ c : (X.ctx p).Branch f,
        (X.ctx p).hist c = ((X.ctx p).hist b).take i := by
    intro f b
    have hreach := (X.ctx p).reach b
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro i
        refine ⟨(X.ctx p).root f, ?_⟩
        rw [(X.ctx p).hist_root f]
        simp
    | @head a c hpar hrest ih =>
        intro i
        obtain ⟨ν, hν⟩ := (X.ctx p).parent_hist a c hpar
        by_cases hi : i ≤ ((X.ctx p).hist c).length
        · obtain ⟨d, hd⟩ := ih i
          refine ⟨d, ?_⟩
          rw [hν, List.take_append_of_le_length hi]
          exact hd
        · refine ⟨a, ?_⟩
          have hlen : ((X.ctx p).hist a).length ≤ i := by
            rw [hν, List.length_append, List.length_cons, List.length_nil]
            omega
          exact (List.take_of_length_le hlen).symm
  -- (b) a node at position `i` forces `dTotal ≥ i` (the first `i` nodes are
  --     continuing, by `termLast`; `length → dTotal` via the take/drop split).
  have hdeep : ∀ (f : MonicBox n p) (b : (X.ctx p).Branch f) (i : ℕ),
      i < ((X.ctx p).hist b).length → i ≤ dTotal ((X.ctx p).hist b) := by
    intro f b i hi
    have hcont : ∀ x ∈ ((X.ctx p).hist b).take i, x.continuing = true := by
      intro x hx
      obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
      have hjlen : j < i := by
        have hj' := hj
        rw [List.length_take] at hj'
        omega
      have hjl : j < ((X.ctx p).hist b).length := by omega
      have hterm := ((X.ctx p).wf b).termLast ⟨j, hjl⟩
        (by change j + 1 < ((X.ctx p).hist b).length; omega)
      rw [List.get_eq_getElem] at hterm
      rw [← hget, List.getElem_take]
      exact hterm
    have hfil : (((X.ctx p).hist b).take i).filter (·.continuing)
        = ((X.ctx p).hist b).take i :=
      List.filter_eq_self.mpr (fun a ha => hcont a ha)
    have hsplit : dTotal ((X.ctx p).hist b) =
        ((((X.ctx p).hist b).take i).filter (·.continuing)).length
          + ((((X.ctx p).hist b).drop i).filter (·.continuing)).length := by
      unfold dTotal
      conv_lhs => rw [← List.take_append_drop i ((X.ctx p).hist b)]
      rw [List.filter_append, List.length_append]
    rw [hfil, List.length_take] at hsplit
    omega
  -- (c) the first-read covering over the finite prefix window (resolution 1).
  set S : Finset (XHistory n) :=
    (Finset.range (R.depthCap hstar)).biUnion
      (fun d => (R.menu_finite d).toFinset) with hS
  have hcover : TallEvent (X.ctx p) hstar ⊆
      (⋃ H ∈ S, TallExtEvent (X.ctx p) H hstar)
        ∪ (TallEvent (X.ctx p) hstar
            ∩ DeepEvent (X.ctx p) (R.depthCap hstar)) := by
    intro f hf
    obtain ⟨b, ν, hmem, htall⟩ := hf
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    by_cases hiD : i < R.depthCap hstar
    · left
      obtain ⟨bi, hbi⟩ := hprefix f b i
      obtain ⟨bs, hbs⟩ := hprefix f b (i + 1)
      have htake : ((X.ctx p).hist b).take (i + 1)
          = ((X.ctx p).hist b).take i ++ [ν] := by
        rw [List.take_succ_eq_append_getElem hi, hget]
      have hHreal : ((X.ctx p).hist b).take i ∈ realizedHists (X.ctx p) i :=
        ⟨by rw [List.length_take]; omega, f, bi, hbi⟩
      have hHS : ((X.ctx p).hist b).take i ∈ S := by
        rw [hS]
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hiD,
          (R.menu_finite i).mem_toFinset.mpr hHreal⟩
      exact Set.mem_biUnion hHS ⟨bs, ν, htall, hbs.trans htake⟩
    · right
      exact ⟨⟨b, ν, hmem, htall⟩, b, by
        have := hdeep f b i hi
        omega⟩
  -- (d) finite subadditivity + the covering, in ℚ, then cast to ℝ.
  have hQ : (X.ctx p).frac (TallEvent (X.ctx p) hstar) ≤
      (∑ H ∈ S, (X.ctx p).frac (TallExtEvent (X.ctx p) H hstar))
        + (X.ctx p).frac (TallEvent (X.ctx p) hstar
            ∩ DeepEvent (X.ctx p) (R.depthCap hstar)) :=
    le_trans ((X.ctx p).frac_mono _ _ hcover)
      (frac_biUnion_union_le (X.ctx p) S _ _)
  have hQR : (((X.ctx p).frac (TallEvent (X.ctx p) hstar) : ℚ) : ℝ) ≤
      (∑ H ∈ S, (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ))
        + (((X.ctx p).frac (TallEvent (X.ctx p) hstar
            ∩ DeepEvent (X.ctx p) (R.depthCap hstar)) : ℚ) : ℝ) := by
    exact_mod_cast hQ
  -- (e) regroup the window sum per depth (`sum_biUnion`; the realized sets at
  --     distinct depths are disjoint — lengths differ).
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.range (R.depthCap hstar)) : Set ℕ)
      (fun d => (R.menu_finite d).toFinset) := by
    intro d1 _ d2 _ hne
    refine Finset.disjoint_left.mpr ?_
    intro H hH1 hH2
    have e1 : H.length = d1 := ((R.menu_finite d1).mem_toFinset.mp hH1).1
    have e2 : H.length = d2 := ((R.menu_finite d2).mem_toFinset.mp hH2).1
    exact hne (by omega)
  have hregroup : (∑ H ∈ S,
      (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ))
      = ∑ d ∈ Finset.range (R.depthCap hstar),
          ∑ H ∈ (R.menu_finite d).toFinset,
            (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ) := by
    rw [hS]
    exact Finset.sum_biUnion hdisj
  -- (f) dominate each depth slice by `menu^d · price d h*`
  --     (`read_price` + `menu_card`).
  have hinner : ∀ d ∈ Finset.range (R.depthCap hstar),
      (∑ H ∈ (R.menu_finite d).toFinset,
        (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ))
      ≤ (R.menu : ℝ) ^ d * R.price d hstar := by
    intro d _
    have hcard_le : (((R.menu_finite d).toFinset.card : ℕ) : ℝ)
        ≤ (R.menu : ℝ) ^ d := by
      have h1 : (realizedHists (X.ctx p) d).ncard ≤ R.menu ^ d := R.menu_card d
      have h2 : (realizedHists (X.ctx p) d).ncard
          = (R.menu_finite d).toFinset.card :=
        Set.ncard_eq_toFinset_card _ (R.menu_finite d)
      rw [h2] at h1
      exact_mod_cast h1
    have hterm : ∀ H ∈ (R.menu_finite d).toFinset,
        (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ)
          ≤ R.price d hstar := by
      intro H hH
      have hlen : H.length = d := ((R.menu_finite d).mem_toFinset.mp hH).1
      have hrp := R.read_price H hstar
      rwa [hlen] at hrp
    calc (∑ H ∈ (R.menu_finite d).toFinset,
          (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ))
        ≤ (R.menu_finite d).toFinset.card • R.price d hstar :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (((R.menu_finite d).toFinset.card : ℕ) : ℝ) * R.price d hstar :=
          nsmul_eq_mul _ _
      _ ≤ (R.menu : ℝ) ^ d * R.price d hstar :=
          mul_le_mul_of_nonneg_right hcard_le (R.price_nonneg d hstar)
  -- (g) close against the R8 field.
  calc (((X.ctx p).frac (TallEvent (X.ctx p) hstar) : ℚ) : ℝ)
      ≤ (∑ H ∈ S, (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ))
          + (((X.ctx p).frac (TallEvent (X.ctx p) hstar
              ∩ DeepEvent (X.ctx p) (R.depthCap hstar)) : ℚ) : ℝ) := hQR
    _ = (∑ d ∈ Finset.range (R.depthCap hstar),
          ∑ H ∈ (R.menu_finite d).toFinset,
            (((X.ctx p).frac (TallExtEvent (X.ctx p) H hstar) : ℚ) : ℝ))
          + (((X.ctx p).frac (TallEvent (X.ctx p) hstar
              ∩ DeepEvent (X.ctx p) (R.depthCap hstar)) : ℚ) : ℝ) := by
        rw [hregroup]
    _ ≤ (∑ d ∈ Finset.range (R.depthCap hstar),
          (R.menu : ℝ) ^ d * R.price d hstar)
          + (((X.ctx p).frac (TallEvent (X.ctx p) hstar
              ∩ DeepEvent (X.ctx p) (R.depthCap hstar)) : ℚ) : ℝ) :=
        add_le_add (Finset.sum_le_sum hinner) le_rfl
    _ ≤ K.CT * (p : ℝ) ^ (-(K.cT * hstar)) := R.series_ok hstar

end LeanUrat.MovesX
