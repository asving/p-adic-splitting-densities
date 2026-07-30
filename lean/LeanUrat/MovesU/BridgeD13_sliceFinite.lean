/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-!
# IB-D13 — thrSlice PLUMBING + THE R6 PIGEONHOLE PROBE (bridge campaign BP1;
front-runner probe unit)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†9) /
§4 group D (IB-D13) / §5 R6 (the pre-prover probe folded into this unit by the
blueprint: "attempt the pigeonhole proof … BEFORE wiring the row").

TWO HALVES:

(A) THE thrSlice PLUMBING (†9's Finset face, D14's supply): from a slice
    finiteness witness, `Set.Finite.toFinset` + its spec give
    `FiberSeries.thrSlice`/`mem_slice_iff`/`slice_exhausts`.  Stated GENERICALLY
    over any carrier-with-threshold (transcription resolution, recorded: IB-D3's
    `Tree σ` carrier is another cluster's unit; the generic form loses nothing —
    D14 instantiates it at the carrier).  All three PROVED here (one-liners).

(B) THE R6 PROBE (sealed prediction, recorded before proving): slice_finite may
    be PROVABLE OUTRIGHT — no kernel row needed.  Mechanism: realizable trees
    have nonempty fibers (`Realizes` is fiber-nonemptiness by definition), and
    fibers of DISTINCT trees are DISJOINT (`MovesT.vtree_eq_of_fiberAt`,
    F3_dictSum.lean:45, PROVED — a shared fiber point forces tree equality), so
    choosing one fiber point per realized tree injects the realized family into
    the FINITE box `MovesD.Box p m` — at most p^m = p^{n·N} realized trees per
    level (`realizes_finite`).  A thr-bounded self-realized family (the (†5)
    carrier shape: each tree realized at its own level lvl = max(thr, 1) ≤
    max(N, 1)) is then a finite union over levels of such families
    (`realizedSelf_slice_finite`).
    ON SUCCESS (report to orchestrator, per R6): `slice_finite` LEAVES
    `BridgeKernels` (IB-F2's row list shrinks) and the `slice_bound` row shrinks
    to the p-uniformity claim `(thrSlice σ N).card ≤ K7.Tbound N`.  ON FAILURE:
    the row stays as blueprinted; nothing downstream moves (upside-only probe,
    "worth one fable-day").
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-! ## (A) generic thrSlice plumbing -/

/-- The slice Finset of a threshold map from a finiteness witness (†9's
    `thrSlice` face, generic form — see header resolution note). -/
noncomputable def sliceFinset {α : Type*} (thr : α → ℕ) (N : ℕ)
    (hfin : {T : α | thr T ≤ N}.Finite) : Finset α :=
  hfin.toFinset

/-- `FiberSeries.mem_slice_iff`'s generic supply: the slice IS the thr ≤ N
    locus. -/
theorem mem_sliceFinset {α : Type*} (thr : α → ℕ) (N : ℕ)
    (hfin : {T : α | thr T ≤ N}.Finite) (T : α) :
    T ∈ sliceFinset thr N hfin ↔ thr T ≤ N :=
  hfin.mem_toFinset

/-- `FiberSeries.slice_exhausts`'s generic supply: every T sits in its own
    threshold's slice. -/
theorem sliceFinset_exhausts {α : Type*} (thr : α → ℕ)
    (hfin : ∀ N, {T : α | thr T ≤ N}.Finite) (T : α) :
    T ∈ sliceFinset thr (thr T) (hfin (thr T)) :=
  (mem_sliceFinset thr (thr T) (hfin (thr T)) T).mpr le_rfl

/-! ## (B) the R6 pigeonhole probe -/

/-- R6 PROBE, core: at ONE model/chart, the realized `VTree` family is FINITE.
    Pigeonhole route (header): pick a fiber point per realized tree; distinct
    trees have disjoint fibers (`MovesT.vtree_eq_of_fiberAt`), so the choice map
    into the finite box `MovesD.Box p m` is injective. -/
theorem realizes_finite {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tm : MovesD.TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    {V : MovesT.VTree p F | MovesT.Realizes Tm χ V}.Finite := sorry

/-- R6 PROBE, slice form (the (†5)-carrier shape, carrier-free statement): the
    thr ≤ N trees each realized at their OWN level lvl(V) = max(thr V, 1) form a
    finite family — a finite union over the levels L ≤ max(N, 1) of the per-level
    realized families of `realizes_finite`.  On success this IS `slice_finite`
    at the IB-D3 carrier (up to the subtype repackaging D14 performs), and the
    kernel row is DELETED — report per the header. -/
theorem realizedSelf_slice_finite {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N)) (N : ℕ) :
    {V : MovesT.VTree p (ZMod p) | V.thr n ≤ N ∧
      MovesT.Realizes (Tm (max (V.thr n) 1))
        (chart (max (V.thr n) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
        V}.Finite := sorry

end LeanUrat.MovesU
