/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.MovesU.DefsCarriers
import LeanUrat.MovesU.U0b_splitTypeFintype

/-!
# BridgeDict — the σ-vocabulary dictionary (bridge campaign BP1, cluster BP1-c2)

E-phase skeletons for units IB-A1 … IB-A7 of
`lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.1 (†1)/(†1c) + §4 group A,
under `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (BP1 Q1 Architecture B).

THE CONTENT: three σ-vocabularies coexist — MovesU's `SplittingType n`
(multiset of (e,f) pairs, entries ≥ 1, Σ e·f = n), the chain's σ-index
`Multiset C.T.VType` with membership `C.chain.Sigmas` (`sig_exact`:
Σ vdeg = n), and OM's `FactorizationType` (no positivity).  The load-bearing
new fact is (†1): `vmap C.T` is a BIJECTION from `SplittingType n` onto
`{s // s ∈ C.chain.Sigmas}`, with the sum-transport corollary (†1c) that
feeds the checksum unit IB-C4.  The OM dictionary (IB-A1) is isolated here so
OM-side enrichment units (IB-D19/IB-F7) never touch the capstone path.

FILE-SCOPE NOTE (cluster boundary): group A's remaining units IB-A8 … IB-A12
(the level-N box dictionary, †2/†3) belong to a SIBLING cluster and must land
in a NEW file — the E-phase no-edit rule forbids appending to this one.

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge):
* IB-A2/IB-A3 are stated over a bare `T : MovesS.TableShape n` (the blueprint
  displays them at `C.T`): `vmap` is T-level (`DefsCarriers.lean:35`), the
  chain plays no role in either statement, and `T := C.T` instantiates the
  blueprint's form verbatim.  IB-A4 … IB-A7 mention `C.chain.Sigmas`, so they
  carry `C : UCarriers n` as displayed.
* IB-A7's "CommMonoid-valued f" (†1c) is transcribed ADDITIVELY
  (`AddCommMonoid M`) — the `∑`/`Finset.sum` vocabulary the consumer IB-C4
  runs in; the multiplicative face is `to_additive`-trivial if ever needed.
* Defs carry their blueprint-specified DATA (the E-phase statement surface);
  only proof obligations are `sorry`d.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-! ## IB-A1 — the OM dictionary (`SplittingType` ↔ `FactorizationType`) -/

/-- IB-A1 (def half): `sigmaToFT σ := ⟨σ.1⟩` — a `SplittingType n` read as an OM
    `FactorizationType` (`Interface.lean:152`; the OM object carries NO positivity,
    so this direction is total).  Deps: none.  Needed only by the enrichment units
    (IB-D19/IB-F7); never on the capstone path. -/
def sigmaToFT {n : ℕ} (σ : SplittingType n) : FactorizationType :=
  ⟨σ.1⟩

/-- IB-A1 (degree law): the OM degree of `sigmaToFT σ` is n — `FactorizationType.degree`
    is literally `SplittingType`'s Σ e·f clause.  Sketch: `σ.2.2` up to unfolding
    `FactorizationType.degree` (`Multiset.map` congruence only). -/
theorem sigmaToFT_degree {n : ℕ} (σ : SplittingType n) :
    (sigmaToFT σ).degree = n :=
  σ.2.2

/-- IB-A1 (partial inverse): a `FactorizationType` with positive entries and degree n,
    read back as a `SplittingType n`.  The data is `ft.data`; positivity is the
    hypothesis; the degree clause is `hdeg` up to unfolding `FactorizationType.degree`. -/
def ftToSigma {n : ℕ} (ft : FactorizationType)
    (hpos : ∀ x ∈ ft.data, 1 ≤ x.1 ∧ 1 ≤ x.2) (hdeg : ft.degree = n) :
    SplittingType n :=
  ⟨ft.data, hpos, hdeg⟩

/-- IB-A1 (roundtrip, σ side): `ftToSigma ∘ sigmaToFT = id` — data-level `Subtype.ext`,
    both sides carry the multiset `σ.1`.  Sketch: `Subtype.ext rfl`. -/
theorem ftToSigma_sigmaToFT {n : ℕ} (σ : SplittingType n) :
    ftToSigma (sigmaToFT σ) σ.2.1 (sigmaToFT_degree σ) = σ :=
  Subtype.ext rfl

/-- IB-A1 (roundtrip, FT side): `sigmaToFT ∘ ftToSigma = id` on the positive degree-n
    locus.  Sketch: `FactorizationType` one-field eta (`rfl` or `cases ft; rfl`). -/
theorem sigmaToFT_ftToSigma {n : ℕ} (ft : FactorizationType)
    (hpos : ∀ x ∈ ft.data, 1 ≤ x.1 ∧ 1 ≤ x.2) (hdeg : ft.degree = n) :
    sigmaToFT (ftToSigma ft hpos hdeg) = ft :=
  rfl

/-! ## IB-A2 / IB-A3 — the vmap roundtrip and injectivity (†1, injective half) -/

/-- IB-A2: THE ROUNDTRIP — reading each verdict type of `vmap T σ` back through
    `T.vEquiv` as a bare (e,f) ∈ ℕ × ℕ pair recovers σ's multiset exactly.
    Deps: none.  Sketch: replay `vmap_deg_sum`'s hcongr/hattach pattern
    (`DefsCarriers.lean:51–69`) with the pair-valued reader in place of the degree
    reader: `Multiset.map_map`, then per-entry `Equiv.apply_symm_apply` collapses
    `vEquiv (vEquiv.symm ⟨(⟨x.1.1, _⟩, ⟨x.1.2, _⟩), _⟩)` to the pair itself
    (`Multiset.map_congr rfl`), then `Multiset.attach_map_val` kills the attach. -/
theorem vmap_roundtrip {n : ℕ} (T : MovesS.TableShape n) (σ : SplittingType n) :
    (vmap T σ).map (fun v => (((T.vEquiv v).1.1 : ℕ), ((T.vEquiv v).1.2 : ℕ)))
      = σ.1 := by
  unfold vmap
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl ?_).trans (Multiset.attach_map_val σ.1)
  intro x _
  simp only [Function.comp_apply]
  rw [Equiv.apply_symm_apply]
  rfl

/-- IB-A3: `vmap T` is injective (†1's injective half).  Deps: IB-A2.  Sketch:
    from `vmap T σ = vmap T σ'`, `congrArg (Multiset.map (pair reader))` + the
    roundtrip IB-A2 twice gives `σ.1 = σ'.1`; finish by `Subtype.ext`. -/
theorem vmap_injective {n : ℕ} (T : MovesS.TableShape n) :
    Function.Injective (vmap T) := by
  intro σ σ' h
  have h2 := congrArg
    (Multiset.map fun v => (((T.vEquiv v).1.1 : ℕ), ((T.vEquiv v).1.2 : ℕ))) h
  rw [vmap_roundtrip, vmap_roundtrip] at h2
  exact Subtype.ext h2

/-! ## IB-A4 / IB-A5 — the section of vmap over the chain's σ-index (†1, surjective half) -/

/-- IB-A4: `sigmaOfSigs` — a member of the chain's exact σ-index `C.chain.Sigmas`
    read back as a `SplittingType n`.  Data: `s.map` of the vEquiv pair reader
    (blueprint §3.1 display).  Deps: none.  Sketch for the two `sorry`d clauses:
    positivity is ℕ+-valuedness of `(vEquiv v).1` (`PNat.one_le`); the degree clause
    is `vdeg_spec` per entry + `sig_exact.mp hs` (`Multiset.map_map` collapse,
    same shape as `vmap_deg_sum`'s hcongr). -/
noncomputable def sigmaOfSigs {n : ℕ} (C : UCarriers n) (s : Multiset C.T.VType)
    (hs : s ∈ C.chain.Sigmas) : SplittingType n :=
  ⟨s.map (fun v => (((C.T.vEquiv v).1.1 : ℕ), ((C.T.vEquiv v).1.2 : ℕ))),
    by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx
      exact ⟨(C.T.vEquiv v).1.1.pos, (C.T.vEquiv v).1.2.pos⟩,
    by
      rw [Multiset.map_map]
      have hc : s.map ((fun x : ℕ × ℕ => x.1 * x.2) ∘ fun v =>
            (((C.T.vEquiv v).1.1 : ℕ), ((C.T.vEquiv v).1.2 : ℕ)))
          = s.map fun v => ((C.T.vdeg v : ℕ)) := by
        apply Multiset.map_congr rfl
        intro v _
        exact (C.T.vdeg_spec v).symm
      rw [hc]
      exact (C.chain.sig_exact s).mp hs⟩

/-- IB-A4 (data pin, definitional): the underlying multiset of `sigmaOfSigs`. -/
theorem sigmaOfSigs_val {n : ℕ} (C : UCarriers n) (s : Multiset C.T.VType)
    (hs : s ∈ C.chain.Sigmas) :
    (sigmaOfSigs C s hs).1
      = s.map (fun v => (((C.T.vEquiv v).1.1 : ℕ), ((C.T.vEquiv v).1.2 : ℕ))) :=
  rfl

/-- IB-A5: the reverse roundtrip `vmap C.T (sigmaOfSigs s hs) = s` (†1's surjective
    half).  Deps: IB-A4.  Sketch: unfold `vmap` at the mapped multiset — a map over
    the attach of a map, the area's one genuinely fiddly multiset computation;
    collapse by `Multiset.attach_map_val` + `Multiset.map_congr` (induction-free),
    with `Equiv.symm_apply_apply` per entry (the constructed ℕ+ pair is EXACTLY
    `(vEquiv v).1` by `PNat` ext, so `vEquiv.symm ⟨(vEquiv v).1, _⟩ = v` after
    `Subtype.ext` on the ≤ n component). -/
theorem vmap_sigmaOfSigs {n : ℕ} (C : UCarriers n) (s : Multiset C.T.VType)
    (hs : s ∈ C.chain.Sigmas) :
    vmap C.T (sigmaOfSigs C s hs) = s := by
  have hr : Function.Injective (fun v : C.T.VType =>
      (((C.T.vEquiv v).1.1 : ℕ), ((C.T.vEquiv v).1.2 : ℕ))) := by
    intro v w hvw
    apply C.T.vEquiv.injective
    apply Subtype.ext
    exact Prod.ext (PNat.coe_injective (congrArg Prod.fst hvw))
      (PNat.coe_injective (congrArg Prod.snd hvw))
  apply Multiset.map_injective hr
  rw [vmap_roundtrip]
  exact sigmaOfSigs_val C s hs

/-! ## IB-A6 — the dictionary equivalence (†1 assembled) -/

/-- IB-A6: (†1) — `vmap C.T` as an EQUIVALENCE onto the chain's exact σ-index.
    Forward: `vmap` + the membership `UCarriers.vmap_mem_Sigmas` (reused, per the
    blueprint); inverse: IB-A4's `sigmaOfSigs`.  Deps: IB-A3 (left_inv via
    injectivity, or directly), IB-A5 (right_inv).  Sketch: `left_inv` = IB-A3
    applied to IB-A5's equation at `s := vmap C.T σ`; `right_inv` = IB-A5 +
    `Subtype.ext`. -/
noncomputable def vmapEquiv {n : ℕ} (C : UCarriers n) :
    SplittingType n ≃ {s : Multiset C.T.VType // s ∈ C.chain.Sigmas} where
  toFun σ := ⟨vmap C.T σ, C.vmap_mem_Sigmas σ⟩
  invFun s := sigmaOfSigs C s.1 s.2
  left_inv := fun σ =>
    vmap_injective C.T (vmap_sigmaOfSigs C (vmap C.T σ) (C.vmap_mem_Sigmas σ))
  right_inv := fun s => Subtype.ext (vmap_sigmaOfSigs C s.1 s.2)

/-- IB-A6 (application pin, definitional): the forward map of `vmapEquiv` is `vmap`. -/
theorem vmapEquiv_apply_coe {n : ℕ} (C : UCarriers n) (σ : SplittingType n) :
    (vmapEquiv C σ).1 = vmap C.T σ :=
  rfl

/-! ## IB-A7 — sum transport (†1c) -/

/-- IB-A7: (†1c) SUM TRANSPORT — for any (additive-)commutative-monoid-valued f,
    the `Fintype` sum over splitting types of `f ∘ vmap` equals the `Finset` sum
    of f over the chain's σ-index `C.chain.Sigmas`.  THE consumer is IB-C4's
    checksum (`rs4_checksum_bridge`), step (i) of (†10b).  Deps: IB-A6 (and U0b's
    `Fintype (SplittingType n)` for the LHS).  Sketch: `Finset.sum_nbij'` from
    `univ` to `C.chain.Sigmas` along `vmapEquiv`/its inverse — membership by
    `vmap_mem_Sigmas`, inverses by IB-A6's two laws, value agreement by
    `vmapEquiv_apply_coe`. -/
theorem sum_vmap_eq_sum_Sigmas {n : ℕ} (C : UCarriers n) {M : Type*}
    [AddCommMonoid M] (f : Multiset C.T.VType → M) :
    ∑ σ : SplittingType n, f (vmap C.T σ) = ∑ s ∈ C.chain.Sigmas, f s := by
  rw [← Finset.sum_coe_sort C.chain.Sigmas f]
  exact Fintype.sum_equiv (vmapEquiv C) _ _ (fun σ => rfl)

end LeanUrat.MovesU
