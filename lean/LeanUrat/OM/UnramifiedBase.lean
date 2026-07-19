/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# O''-RING (Phase-B W6b-f2 infrastructure): the level-N UNRAMIFIED base ring
`Oring = ZMod (p^N)[X] ⧸ (g)`, `g` monic with `ḡ = g mod p` irreducible over `F_p`.

Blueprint: `uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §3 (the two-step `f ≥ 2`
descent: step 1 is the *unramified degree-f descent* to the ring `O''` with residue field
`GaloisField p (k·f) = F_{q^f}`), and §6 (the named follow-up wave **W6b-f2**).

This is the new ring object the `f ≥ 2` digit-restart needs — the level-N truncation of the
unramified degree-`m` extension of `ℤ_p` (the Witt/Teichmüller lift of `F_{p^m}` cut at level `N`).
It is the analogue of `LeanUrat.OM.RphiRing` (`Rphi = AdjoinRoot (X^e − c·p^h)` over `ZMod (p^N)`,
the *ramified* Eisenstein case) but for an **unramified** `g`: here `p` — NOT the root `t` — is the
uniformizer, so the `p`-adic filtration is **UNGAPPED** (each successive quotient has the SAME size
`p^m`), in contrast to the Eisenstein `RphiRing` where the gap is the ramification index.

## Set-up
`g : (ZMod (p^N))[X]` monic of degree `m`, with the hypothesis `hgirr` that its reduction
`ḡ := g.map (ZMod.castHom (p ∣ p^N) (ZMod p))` is IRREDUCIBLE over `ZMod p`. This is exactly the
data of a lift of an `F_p`-irreducible of degree `m`; irreducibility of `ḡ` is what makes `Oring`
unramified with residue field `F_{p^m}`. (Existence of such a `g` for every `m` is the standard
finite-field fact; here we take the polynomial + its irreducible reduction as a hypothesis, per the
task spec, so no existence theorem is invoked.)

## Deliverables (all gated in `/workspace-vast/asving/tmp/phaseb_oring/`, PASS 2026-07-06)
1. `Oring := AdjoinRoot g`, digit identification `digitEquiv`, and
   `card_Oring : Nat.card Oring = (p^N)^m = p^(N*m)`.
2. Local structure: `isNilpotent_natCast_p` (`p^N = 0`), `isUnit_iff_notMem` (`x` unit ↔ `x ∉ (p)`),
   `isLocalRing`, `maximalIdeal_eq` (`m = span {(p : Oring)}` — UNRAMIFIED: `p` generates it, unlike
   the Eisenstein `θ` case), and the residue field: `resField := AdjoinRoot ḡ` (a `Field`, since `ḡ`
   is irreducible), `card_resField : #resField = p^m`, and `card_residueField` (via `maximalIdeal`).
   (The `AlgEquiv resField ≃ₐ GaloisField p m` is OPTIONAL by finite-field uniqueness; the card
   `p^m` suffices and is what is banked — see the docstring note on `GaloisField`.)
3. The `p`-adic (unramified, UNGAPPED) filtration counts:
   `card_quotient_span_p_pow : #(Oring/(p^j)) = (p^m)^j = p^(m*j)`,
   `card_span_p_pow : #(span {(p^j : Oring)}) = (p^m)^(N-j) = p^(m*(N-j))` for `j ≤ N`,
   `card_map_span_p_pow : #((p^j)/(p^(j+1))) = p^m` (the CONSTANT successive-quotient size = the
   ungapped signature). `pval_Oring` is the `p`-adic valuation reader (largest `j ≤ N` with
   `x ∈ (p^j)`).

## §4 follow-up (NAMED, not built): `RphiExt` over `Oring` = W6b-f2-proper
The next wave builds the *Eisenstein tower over* `Oring`:
    `RphiExt := Oring[X] ⧸ (X^e − c·p^h)`   (`c ∈ Oringˣ`, the ramified child over `O''`),
and the `f ≥ 2` digit restart / `restartEquiv`-analogue over it (cf. `LeanUrat.OM.RestartEquiv` at
`f = 1`). That is **W6b-f2-proper** and is deliberately OUT OF SCOPE here — this module banks only
the unramified base `O''` and its structure.

Discipline: no `sorry`/`axiom`/`native_decide`; `Mathlib`-only imports.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.UnramifiedBase

open Polynomial

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

noncomputable section

/-! ## Base-ring helpers (mirror `RphiRing`) -/

theorem one_lt_pow_base (hN : 0 < N) : 1 < p ^ N :=
  one_lt_pow' hp.out.one_lt hN.ne'

theorem neZero_pow_base (hN : 0 < N) : NeZero (p ^ N) :=
  ⟨(Nat.zero_lt_of_lt (one_lt_pow_base p N hN)).ne'⟩

theorem nontrivial_base (hN : 0 < N) : Nontrivial (ZMod (p ^ N)) :=
  haveI : Fact (1 < p ^ N) := ⟨one_lt_pow_base p N hN⟩
  ZMod.nontrivial _

/-- The reduction hom `ZMod (p^N) →+* ZMod p` (`p ∣ p^N`). -/
def redHom (hN : 0 < N) : ZMod (p ^ N) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)

/-! ## The ring `Oring := AdjoinRoot g` -/

/-- The level-N unramified base ring `O'' = (ZMod (p^N))[X] ⧸ (g)`, spelled via `AdjoinRoot`. -/
abbrev Oring : Type _ := AdjoinRoot g

/-- `t`, the image of `X` (the adjoined root of `g`). Unlike the Eisenstein `θ`, `t` is a UNIT
(it reduces to a generator of the residue field). -/
def troot : Oring p N g := AdjoinRoot.root g

/-! ## Deliverable 1: digit identification and cardinality -/

/-- The `ZMod (p^N)`-power basis of `Oring` (dimension `m = g.natDegree`). -/
def pb (hgm : g.Monic) : PowerBasis (ZMod (p ^ N)) (Oring p N g) := AdjoinRoot.powerBasis' hgm

theorem pb_dim (hgm : g.Monic) : (pb p N g hgm).dim = g.natDegree := rfl

/-- The digit `ZMod (p^N)`-linear iso `Oring ≃ (Fin m → ZMod (p^N))` from the power basis. -/
def digitEquiv (hgm : g.Monic) (hN : 0 < N) :
    Oring p N g ≃ₗ[ZMod (p ^ N)] (Fin g.natDegree → ZMod (p ^ N)) :=
  (pb p N g hgm).basis.equivFun

theorem finite_Oring (hgm : g.Monic) (hN : 0 < N) : Finite (Oring p N g) := by
  haveI := neZero_pow_base p N hN
  exact Finite.of_equiv _ (digitEquiv p N g hgm hN).toEquiv.symm

/-- **Deliverable 1 (cardinality)**: `card Oring = (p^N)^m = p^(N·m)`. -/
theorem card_Oring (hgm : g.Monic) (hN : 0 < N) :
    Nat.card (Oring p N g) = (p ^ N) ^ g.natDegree := by
  haveI := neZero_pow_base p N hN
  calc Nat.card (Oring p N g)
      = Nat.card (Fin g.natDegree → ZMod (p ^ N)) :=
        Nat.card_congr (digitEquiv p N g hgm hN).toEquiv
    _ = (p ^ N) ^ g.natDegree := by
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_Oring_pow (hgm : g.Monic) (hN : 0 < N) :
    Nat.card (Oring p N g) = p ^ (N * g.natDegree) := by
  rw [card_Oring p N g hgm hN, ← pow_mul]

theorem nontrivial_Oring (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree) :
    Nontrivial (Oring p N g) := by
  have hcard := card_Oring_pow p N g hgm hN
  refine ⟨0, 1, fun h01 => ?_⟩
  haveI : Subsingleton (Oring p N g) := subsingleton_of_zero_eq_one h01
  have h1 : Nat.card (Oring p N g) = 1 := Nat.card_of_subsingleton 0
  rw [hcard] at h1
  have h2 : 1 < p ^ (N * g.natDegree) :=
    one_lt_pow' hp.out.one_lt (Nat.mul_ne_zero hN.ne' hm.ne')
  omega

/-! ## Deliverable 2 (part A): `p` is nilpotent, digit decomposition -/

/-- `(p : Oring)^N = 0` (image of `p^N = 0` in `ZMod (p^N)`). -/
theorem isNilpotent_natCast_p (hN : 0 < N) : ((p : ℕ) : Oring p N g) ^ N = 0 := by
  haveI := neZero_pow_base p N hN
  rw [← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (p ^ N)) (Oring p N g))]
  have : ((p ^ N : ℕ) : ZMod (p ^ N)) = 0 := by
    rw [ZMod.natCast_self]
  rw [this, map_zero]

/-! ## Deliverable 2 (part B): the residue field `resField = AdjoinRoot ḡ` -/

/-- The reduced key `ḡ = g mod p` over `ZMod p`. -/
def gbar (hN : 0 < N) : (ZMod p)[X] := g.map (redHom p N hN)

/-- `ḡ` is monic of degree `m`. -/
theorem monic_gbar (hgm : g.Monic) (hN : 0 < N) : (gbar p N g hN).Monic :=
  hgm.map _

theorem natDegree_gbar (hgm : g.Monic) (hN : 0 < N) :
    (gbar p N g hN).natDegree = g.natDegree := by
  rw [gbar]
  exact hgm.natDegree_map _

/-- The **residue field** `resField := AdjoinRoot ḡ` — the finite field `F_{p^m}` (residue field of
`Oring`). It is a genuine `Field` because `ḡ` is irreducible (`hgirr`). -/
abbrev resField (hN : 0 < N) : Type _ := AdjoinRoot (gbar p N g hN)

/-- The residue field is a field (needs `ḡ` irreducible): supply `Fact (Irreducible ḡ)` and the
mathlib instance `AdjoinRoot.instField` fires. -/
theorem isField_resField (hN : 0 < N) (hgirr : Irreducible (gbar p N g hN)) :
    IsField (resField p N g hN) := by
  haveI : Fact (Irreducible (gbar p N g hN)) := ⟨hgirr⟩
  exact Field.toIsField (resField p N g hN)

/-- **Deliverable 2 (residue-field card)**: `#resField = p^m`. Over the field `ZMod p`,
`AdjoinRoot ḡ` is free of rank `m = ḡ.natDegree = g.natDegree`, so it has `(#ZMod p)^m = p^m`
elements. -/
theorem card_resField (hgm : g.Monic) (hN : 0 < N) (hgirr : Irreducible (gbar p N g hN)) :
    Nat.card (resField p N g hN) = p ^ g.natDegree := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Fact (Irreducible (gbar p N g hN)) := ⟨hgirr⟩
  have hne : (gbar p N g hN) ≠ 0 := (monic_gbar p N g hgm hN).ne_zero
  have hbasis : Nat.card (resField p N g hN)
      = Nat.card (Fin (gbar p N g hN).natDegree → ZMod p) :=
    Nat.card_congr (AdjoinRoot.powerBasis hne).basis.equivFun.toEquiv
  rw [hbasis, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin,
    natDegree_gbar p N g hgm hN]

/-! ### The residue hom `Oring → resField` (`t ↦ root ḡ`, base reduced mod `p`). -/

theorem eval₂_g_root_gbar (hgm : g.Monic) (hN : 0 < N) :
    g.eval₂ ((AdjoinRoot.of (gbar p N g hN)).comp (redHom p N hN))
      (AdjoinRoot.root (gbar p N g hN)) = 0 := by
  rw [← AdjoinRoot.algebraMap_eq]
  have h1 : g.eval₂ ((algebraMap (ZMod p) (resField p N g hN)).comp (redHom p N hN))
      (AdjoinRoot.root (gbar p N g hN))
      = (g.map (redHom p N hN)).eval₂ (algebraMap (ZMod p) (resField p N g hN))
          (AdjoinRoot.root (gbar p N g hN)) := by
    rw [Polynomial.eval₂_map]
  rw [h1, AdjoinRoot.algebraMap_eq, ← gbar, AdjoinRoot.eval₂_root]

/-- The residue hom `Oring → resField`, `t ↦ root ḡ`, base `ZMod (p^N) → ZMod p`. -/
def resHom (hgm : g.Monic) (hN : 0 < N) : Oring p N g →+* resField p N g hN :=
  AdjoinRoot.lift ((AdjoinRoot.of (gbar p N g hN)).comp (redHom p N hN))
    (AdjoinRoot.root (gbar p N g hN)) (eval₂_g_root_gbar p N g hgm hN)

theorem resHom_troot (hgm : g.Monic) (hN : 0 < N) :
    resHom p N g hgm hN (troot p N g) = AdjoinRoot.root (gbar p N g hN) := by
  rw [resHom, troot, AdjoinRoot.lift_root]

theorem resHom_natCast_p (hgm : g.Monic) (hN : 0 < N) :
    resHom p N g hgm hN (((p : ℕ) : Oring p N g)) = 0 := by
  haveI := neZero_pow_base p N hN
  rw [resHom, ← map_natCast (algebraMap (ZMod (p ^ N)) (Oring p N g)) p,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, RingHom.comp_apply, map_natCast]
  simp only [ZMod.natCast_self, map_zero]

/-- `resHom (mk g q') = mk ḡ (q' mod p)` — `resHom` intertwines the two quotient maps along
coefficientwise reduction. -/
theorem resHom_mk (hgm : g.Monic) (hN : 0 < N) (q' : (ZMod (p ^ N))[X]) :
    resHom p N g hgm hN (AdjoinRoot.mk g q') = AdjoinRoot.mk (gbar p N g hN) (q'.map (redHom p N hN)) := by
  rw [resHom, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq,
    Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]

theorem resHom_surjective (hgm : g.Monic) (hN : 0 < N) :
    Function.Surjective (resHom p N g hgm hN) := by
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (redHom p N hN)
    (ZMod.castHom_surjective (dvd_pow_self p hN.ne')) q
  exact ⟨AdjoinRoot.mk g q', resHom_mk p N g hgm hN q'⟩

/-! ## Deliverable 2 (part C): the maximal ideal is `span {(p : Oring)}` (UNRAMIFIED) -/

/-- The reduction `redHom` kills exactly the multiples of `p`: `redHom a = 0 → (p : ...) ∣ a`. -/
theorem redHom_eq_zero_dvd (hN : 0 < N) {a : ZMod (p ^ N)} (ha : redHom p N hN a = 0) :
    (p : ZMod (p ^ N)) ∣ a := by
  haveI := neZero_pow_base p N hN
  -- `redHom a = (a.val : ZMod p) = 0`, so `p ∣ a.val`; then `a = a.val = p * (a.val / p)`.
  have hval : ((a.val : ℕ) : ZMod p) = 0 := by
    rw [← ha, redHom, ZMod.castHom_apply, ZMod.natCast_val]
  have hdvd : p ∣ a.val := (ZMod.natCast_eq_zero_iff _ _).mp hval
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨(b : ZMod (p ^ N)), ?_⟩
  have : ((a.val : ℕ) : ZMod (p ^ N)) = a := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← this, hb, Nat.cast_mul]

/-- The kernel of `resHom` is `span {(p : Oring)}` (both are the maximal ideal). -/
theorem ker_resHom_eq_span_p (hgm : g.Monic) (hN : 0 < N) :
    RingHom.ker (resHom p N g hgm hN) = Ideal.span {((p : ℕ) : Oring p N g)} := by
  apply le_antisymm
  · -- `ker ⊆ span{p}`: coefficientwise lift
    intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨q', rfl⟩ := AdjoinRoot.mk_surjective x
    rw [resHom_mk] at hx
    rw [AdjoinRoot.mk_eq_zero] at hx
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', rfl⟩ := Polynomial.map_surjective (redHom p N hN)
      (ZMod.castHom_surjective (dvd_pow_self p hN.ne')) s
    -- `q'.map red = ḡ * (s'.map red) = (g * s').map red`, so `(q' - g*s').map red = 0`
    have hr : (q' - g * s').map (redHom p N hN) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hs, gbar, sub_self]
    -- every coeff of `r := q' - g*s'` is a multiple of p, so `C p ∣ r`, so `mk g r ∈ span{p}`.
    set r := q' - g * s' with hrdef
    have hcoeff : ∀ i, (p : ZMod (p ^ N)) ∣ r.coeff i := by
      intro i
      apply redHom_eq_zero_dvd p N hN
      have := congrArg (fun q => Polynomial.coeff q i) hr
      simpa [Polynomial.coeff_map] using this
    obtain ⟨u, hu⟩ := (Polynomial.C_dvd_iff_dvd_coeff (p : ZMod (p ^ N)) r).mpr hcoeff
    have hmkC : AdjoinRoot.mk g (Polynomial.C (p : ZMod (p ^ N))) = ((p : ℕ) : Oring p N g) := by
      rw [AdjoinRoot.mk_C, ← map_natCast (algebraMap (ZMod (p ^ N)) (Oring p N g)) p,
        AdjoinRoot.algebraMap_eq, map_natCast]
    have hmem : AdjoinRoot.mk g r ∈ Ideal.span {((p : ℕ) : Oring p N g)} := by
      rw [hu, map_mul, hmkC, Ideal.mem_span_singleton]
      exact ⟨AdjoinRoot.mk g u, rfl⟩
    have hxeq : AdjoinRoot.mk g q' = AdjoinRoot.mk g r := by
      rw [AdjoinRoot.mk_eq_mk, hrdef]
      exact ⟨s', by ring⟩
    rw [hxeq]; exact hmem
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact resHom_natCast_p p N g hgm hN

/-- **Deliverable 2 (maximal ideal)**: `span {(p : Oring)}` is a maximal ideal (its residue is the
field `resField`; `p` — NOT the root `t` — generates it: the UNRAMIFIED signature). -/
theorem isMaximal_span_p (hgm : g.Monic) (hN : 0 < N) (hgirr : Irreducible (gbar p N g hN)) :
    (Ideal.span {((p : ℕ) : Oring p N g)}).IsMaximal := by
  haveI : Fact (Irreducible (gbar p N g hN)) := ⟨hgirr⟩
  rw [← ker_resHom_eq_span_p p N g hgm hN]
  exact RingHom.ker_isMaximal_of_surjective _ (resHom_surjective p N g hgm hN)

/-- `(p : Oring)^N = 0`, so `span {(p : Oring)}` is a nilpotent ideal. -/
theorem isNilpotent_span_p (hN : 0 < N) :
    IsNilpotent (Ideal.span {((p : ℕ) : Oring p N g)}) := by
  refine ⟨N, ?_⟩
  rw [Ideal.span_singleton_pow, isNilpotent_natCast_p p N g hN]
  exact Ideal.span_singleton_eq_bot.mpr rfl

/-- **Deliverable 2 (localness)**: `Oring` is a local ring — `span {(p : Oring)}` is its unique
maximal ideal (nilpotent + maximal). -/
theorem isLocalRing (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) : IsLocalRing (Oring p N g) := by
  haveI := nontrivial_Oring p N g hgm hN hm
  refine IsLocalRing.of_unique_max_ideal ⟨Ideal.span {((p : ℕ) : Oring p N g)},
    isMaximal_span_p p N g hgm hN hgirr, fun J hJ => ?_⟩
  -- any maximal `J` contains the nilradical, hence `span{p}` (nilpotent), so `J = span{p}`.
  have hle : Ideal.span {((p : ℕ) : Oring p N g)} ≤ J := by
    have hnil := isNilpotent_span_p p N g hN
    obtain ⟨k, hk⟩ := hnil
    have hpk : Ideal.span {((p : ℕ) : Oring p N g)} ^ k ≤ J := by rw [hk]; exact bot_le
    exact hJ.isPrime.le_of_pow_le hpk
  exact ((isMaximal_span_p p N g hgm hN hgirr).eq_of_le hJ.ne_top hle).symm

/-- **Deliverable 2 (maximal ideal, explicit)**: `m = span {(p : Oring)}`. -/
theorem maximalIdeal_eq (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) [IsLocalRing (Oring p N g)] :
    IsLocalRing.maximalIdeal (Oring p N g) = Ideal.span {((p : ℕ) : Oring p N g)} :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_span_p p N g hgm hN hgirr)).symm

/-- **Deliverable 2 (residue-field count via the maximal ideal)**: `#(Oring/m) = p^m`. -/
theorem card_quotient_span_p (hgm : g.Monic) (hN : 0 < N) (hgirr : Irreducible (gbar p N g hN)) :
    Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g)}) = p ^ g.natDegree := by
  rw [← ker_resHom_eq_span_p p N g hgm hN,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (resHom_surjective p N g hgm hN)).toEquiv]
  exact card_resField p N g hgm hN hgirr

/-- **Deliverable 2 (residue field via `IsLocalRing.maximalIdeal`)**: `#(Oring/m) = p^m`. -/
theorem card_residueField (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) [IsLocalRing (Oring p N g)] :
    Nat.card (Oring p N g ⧸ IsLocalRing.maximalIdeal (Oring p N g)) = p ^ g.natDegree := by
  rw [maximalIdeal_eq p N g hgm hN hm hgirr]
  exact card_quotient_span_p p N g hgm hN hgirr

/-- **Deliverable 2 (unit criterion)**: `x` is a unit iff `x ∉ span {(p : Oring)}` (`p` generates
the maximal ideal). Via the local structure: `span{p}` IS the maximal ideal `= nonunits`. -/
theorem isUnit_iff_notMem (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) [IsLocalRing (Oring p N g)] (x : Oring p N g) :
    IsUnit x ↔ x ∉ Ideal.span {((p : ℕ) : Oring p N g)} := by
  rw [← maximalIdeal_eq p N g hgm hN hm hgirr, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

/-! ## Deliverable 3: the `p`-adic filtration counts (UNRAMIFIED, UNGAPPED)

The `p`-adic filtration `{span {(p^j : Oring)}}_{j ≤ N}` has EQUAL successive-quotient sizes `p^m`
(the residue-field size), so `#(Oring/(p^j)) = (p^m)^j = p^{m·j}` and `#span{p^j} = p^{m(N−j)}`.
This is the **ungapped** signature that distinguishes the unramified `Oring` from the (gapped)
Eisenstein `RphiRing`, whose successive quotients are all `p` regardless of the residue degree. -/

/-- Arithmetic sandwich (mirrors `RphiRing.nat_sandwich`): a multiplicative chain with unit steps
`≤ P`, total `P^K`, is pinned to `P^j` at every level. -/
private theorem nat_sandwich {P K : ℕ} (hP : 0 < P) (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hK : a K = P ^ K) (hstep : ∀ j, j < K → ∃ k ≤ P, a (j + 1) = a j * k) :
    ∀ j, j ≤ K → a j = P ^ j := by
  have up : ∀ j, j ≤ K → a j ≤ P ^ j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hn1
      obtain ⟨k, hk, hak⟩ := hstep n (by omega)
      calc a (n + 1) = a n * k := hak
        _ ≤ P ^ n * P := Nat.mul_le_mul (ih (by omega)) hk
        _ = P ^ (n + 1) := (pow_succ P n).symm
  have down : ∀ d j, j + d = K → a K ≤ a j * P ^ d := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hjK : j = K := by omega
      subst hjK; simp
    | succ n ih =>
      intro j hj
      obtain ⟨k, hk, hak⟩ := hstep j (by omega)
      calc a K ≤ a (j + 1) * P ^ n := ih (j + 1) (by omega)
        _ = a j * k * P ^ n := by rw [hak]
        _ ≤ a j * P * P ^ n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
        _ = a j * P ^ (n + 1) := by rw [pow_succ]; ring
  intro j hj
  have hKe : P ^ K = P ^ j * P ^ (K - j) := by rw [← pow_add]; congr 1; omega
  have h1 : P ^ j * P ^ (K - j) ≤ a j * P ^ (K - j) := by
    rw [← hKe, ← hK]; exact down (K - j) j (by omega)
  exact le_antisymm (up j hj) (Nat.le_of_mul_le_mul_right h1 (pow_pos hP _))

omit hp in
theorem span_p_pow_succ_le (hN : 0 < N) (j : ℕ) :
    Ideal.span {((p : ℕ) : Oring p N g) ^ (j + 1)}
      ≤ Ideal.span {((p : ℕ) : Oring p N g) ^ j} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ j))

omit hp in
theorem span_p_pow_antitone {i j : ℕ} (hij : i ≤ j) :
    Ideal.span {((p : ℕ) : Oring p N g) ^ j} ≤ Ideal.span {((p : ℕ) : Oring p N g) ^ i} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hij)

omit hp in
theorem card_quotient_span_p_pow_zero :
    Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ 0}) = 1 := by
  have hsub : Subsingleton (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ 0}) := by
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  exact Nat.card_of_subsingleton 0

theorem card_quotient_span_p_pow_top (hgm : g.Monic) (hN : 0 < N) :
    Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ N})
      = p ^ (N * g.natDegree) := by
  have hbot : Ideal.span {((p : ℕ) : Oring p N g) ^ N} = (⊥ : Ideal (Oring p N g)) := by
    rw [isNilpotent_natCast_p p N g hN]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  rw [hbot, Nat.card_congr (Submodule.quotEquivOfEqBot (⊥ : Ideal (Oring p N g)) rfl).toEquiv]
  exact card_Oring_pow p N g hgm hN

/-- One filtration step: `#(Oring/(p^{j+1})) = #(Oring/(p^j)) · k` with `k ≤ p^m`. The factor `k`
is the size of the kernel of the connecting map, which is the image of `Oring/(p)` (`= F_{p^m}`)
under `x ↦ [p^j · x]` (`p·p^j = p^{j+1} ≡ 0`), hence `≤ p^m`. -/
theorem card_quotient_span_p_pow_succ (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (gbar p N g hN)) (j : ℕ) :
    ∃ k ≤ p ^ g.natDegree,
      Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ (j + 1)}) =
        Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ j}) * k := by
  haveI := finite_Oring p N g hgm hN
  set π := ((p : ℕ) : Oring p N g) with hπ
  have hIJ : Ideal.span {π ^ (j + 1)} ≤ Ideal.span {π ^ j} := span_p_pow_succ_le p N g hN j
  set I := Ideal.span {π ^ (j + 1)} with hIdef
  set J := Ideal.span {π ^ j} with hJdef
  have hsurj : Function.Surjective (Ideal.Quotient.factor hIJ) := fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I x, Ideal.Quotient.factor_mk hIJ x⟩
  have hlag := Submodule.card_eq_card_quotient_mul_card
    (RingHom.ker (Ideal.Quotient.factor hIJ))
  have hiso : ((Oring p N g ⧸ I) ⧸ RingHom.ker (Ideal.Quotient.factor hIJ)) ≃+*
      (Oring p N g ⧸ J) := RingHom.quotientKerEquivOfSurjective hsurj
  -- membership: `x·π^j ∈ J` for all `x` (since `π^j ∈ J`)
  have hmemK : ∀ x : Oring p N g,
      Ideal.Quotient.mk I (x * π ^ j) ∈ RingHom.ker (Ideal.Quotient.factor hIJ) := by
    intro x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, hJdef]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  refine ⟨Nat.card (RingHom.ker (Ideal.Quotient.factor hIJ)), ?_, ?_⟩
  · -- the kernel is the surjective image of `Oring/(π)` (card `p^m`) via `[x] ↦ [x·π^j]`
    haveI : Fact (Irreducible (gbar p N g hN)) := ⟨hgirr⟩
    -- the raw map `Oring → K`, `x ↦ [x·π^j]`, is surjective and constant on `(π)`-cosets
    have hraw : Function.Surjective
        (fun x : Oring p N g => (⟨Ideal.Quotient.mk I (x * π ^ j), hmemK x⟩ :
          RingHom.ker (Ideal.Quotient.factor hIJ))) := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, hJdef,
        Ideal.mem_span_singleton] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, Subtype.ext ?_⟩
      show Ideal.Quotient.mk I (z * π ^ j) = Ideal.Quotient.mk I (π ^ j * z)
      rw [mul_comm]
    -- it factors through `Oring/(π)`: `[(x - y)·π^j] = 0` when `x ≡ y (mod π)`, since `π^{j+1} ∈ I`
    have hrespect : ∀ x y : Oring p N g, x - y ∈ Ideal.span {π} →
        (⟨Ideal.Quotient.mk I (x * π ^ j), hmemK x⟩ : RingHom.ker (Ideal.Quotient.factor hIJ))
          = ⟨Ideal.Quotient.mk I (y * π ^ j), hmemK y⟩ := by
      intro x y hxy
      apply Subtype.ext
      rw [Ideal.mem_span_singleton] at hxy
      obtain ⟨w, hw⟩ := hxy
      show Ideal.Quotient.mk I (x * π ^ j) = Ideal.Quotient.mk I (y * π ^ j)
      rw [← sub_eq_zero, ← map_sub, ← sub_mul, hw, mul_comm π w, mul_assoc, ← pow_succ',
        Ideal.Quotient.eq_zero_iff_mem, hIdef]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    -- factor `hraw` through the quotient `Oring/(π)` (card `p^m`) via `Quotient.liftOn`
    set K := RingHom.ker (Ideal.Quotient.factor hIJ) with hKdef
    let ψ : (Oring p N g ⧸ Ideal.span {π}) → K := fun q =>
      Quotient.liftOn q (fun x => (⟨Ideal.Quotient.mk I (x * π ^ j), hmemK x⟩ : K))
        (fun a b hab => hrespect a b (by
          rw [← Ideal.Quotient.eq]; exact Quotient.sound hab))
    have hψsurj : Function.Surjective ψ := by
      intro y
      obtain ⟨x, rfl⟩ := hraw y
      exact ⟨Ideal.Quotient.mk (Ideal.span {π}) x, rfl⟩
    haveI : Finite (Oring p N g ⧸ Ideal.span {π}) := Quotient.finite _
    calc Nat.card K ≤ Nat.card (Oring p N g ⧸ Ideal.span {π}) :=
          Nat.card_le_card_of_surjective ψ hψsurj
      _ = p ^ g.natDegree := card_quotient_span_p p N g hgm hN hgirr
  · rw [hlag, Nat.card_congr hiso.toEquiv]; exact mul_comm _ _

/-- **Deliverable 3a (quotient counts)**: `#(Oring/(p^j)) = (p^m)^j = p^{m·j}` for `j ≤ N` — the
UNGAPPED (unramified) index law. -/
theorem card_quotient_span_p_pow (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) (j : ℕ) (hj : j ≤ N) :
    Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ j}) = (p ^ g.natDegree) ^ j :=
  nat_sandwich (pow_pos hp.out.pos g.natDegree)
    (fun i => Nat.card (Oring p N g ⧸ Ideal.span {((p : ℕ) : Oring p N g) ^ i}))
    (card_quotient_span_p_pow_zero p N g)
    (by rw [card_quotient_span_p_pow_top p N g hgm hN, ← pow_mul, Nat.mul_comm])
    (fun i _ => card_quotient_span_p_pow_succ p N g hgm hN hgirr i) j hj

/-- **Deliverable 3b (filtration counts)**: `#span{p^j} = (p^m)^(N−j) = p^{m(N−j)}` for `j ≤ N` —
the level-N unramified filtration size. -/
theorem card_span_p_pow (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) (j : ℕ) (hj : j ≤ N) :
    Nat.card (Ideal.span {((p : ℕ) : Oring p N g) ^ j}) = (p ^ g.natDegree) ^ (N - j) := by
  haveI := finite_Oring p N g hgm hN
  have hlag := Submodule.card_eq_card_quotient_mul_card
    (Ideal.span {((p : ℕ) : Oring p N g) ^ j})
  rw [card_Oring_pow p N g hgm hN, card_quotient_span_p_pow p N g hgm hN hm hgirr j hj] at hlag
  have hsplit : p ^ (N * g.natDegree) = (p ^ g.natDegree) ^ (N - j) * (p ^ g.natDegree) ^ j := by
    rw [← pow_add, ← pow_mul]
    have : N - j + j = N := by omega
    rw [this, Nat.mul_comm]
  have hpos : 0 < (p ^ g.natDegree) ^ j := pow_pos (pow_pos hp.out.pos _) j
  exact Nat.eq_of_mul_eq_mul_right hpos (hlag.symm.trans hsplit)

/-- **Deliverable 3c (successive quotients — the UNGAPPED signature)**: `#((p^j)/(p^{j+1})) = p^m`
for `j < N`, constant in `j` (contrast the Eisenstein `RphiRing`, where it is always `p`). Spelled
as the image ideal of `(p^j)` inside `Oring/(p^{j+1})`. -/
theorem card_map_span_p_pow (hgm : g.Monic) (hN : 0 < N) (hm : 0 < g.natDegree)
    (hgirr : Irreducible (gbar p N g hN)) (j : ℕ) (hj : j < N) :
    Nat.card (Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : Oring p N g) ^ (j + 1)}))
      (Ideal.span {((p : ℕ) : Oring p N g) ^ j})) = p ^ g.natDegree := by
  haveI := finite_Oring p N g hgm hN
  set π := ((p : ℕ) : Oring p N g) with hπ
  have hIJ : Ideal.span {π ^ (j + 1)} ≤ Ideal.span {π ^ j} := span_p_pow_succ_le p N g hN j
  have hlag := Submodule.card_eq_card_quotient_mul_card
    (Ideal.map (Ideal.Quotient.mk (Ideal.span {π ^ (j + 1)})) (Ideal.span {π ^ j}))
  have hq : Nat.card ((Oring p N g ⧸ Ideal.span {π ^ (j + 1)})
      ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {π ^ (j + 1)})) (Ideal.span {π ^ j}))
      = (p ^ g.natDegree) ^ j := by
    have hsup : Ideal.span {π ^ (j + 1)} ⊔ Ideal.span {π ^ j} = Ideal.span {π ^ j} :=
      sup_eq_right.mpr hIJ
    rw [Nat.card_congr (DoubleQuot.quotQuotEquivQuotSup
      (Ideal.span {π ^ (j + 1)}) (Ideal.span {π ^ j})).toEquiv, hsup]
    exact card_quotient_span_p_pow p N g hgm hN hm hgirr j (by omega)
  rw [card_quotient_span_p_pow p N g hgm hN hm hgirr (j + 1) (by omega), hq, pow_succ] at hlag
  have hpos : 0 < (p ^ g.natDegree) ^ j := pow_pos (pow_pos hp.out.pos _) j
  exact Nat.eq_of_mul_eq_mul_left hpos (by linarith [hlag])

/-! ## `pval_Oring`: the `p`-adic valuation reader on `Oring` (largest `j ≤ N` with `x ∈ (p^j)`) -/

open Classical in
/-- **`pval_Oring`**: `pval x` = the largest `j ≤ N` with `x ∈ (p^j)` (junk value `N` at `x = 0`).
Since `p` generates the maximal ideal, this is the honest `p`-adic valuation on the level-N ring
`Oring` (`vL = v_p`), with the ungapped filtration `{p^j}` counted by `card_span_p_pow`. -/
def pval_Oring (x : Oring p N g) : ℕ :=
  Nat.findGreatest (fun j => x ∈ Ideal.span {((p : ℕ) : Oring p N g) ^ j}) N

theorem pval_le (x : Oring p N g) : pval_Oring p N g x ≤ N := by
  classical
  unfold pval_Oring; exact Nat.findGreatest_le _

theorem mem_span_p_pow_pval (x : Oring p N g) :
    x ∈ Ideal.span {((p : ℕ) : Oring p N g) ^ (pval_Oring p N g x)} := by
  classical
  unfold pval_Oring
  refine Nat.findGreatest_spec
    (P := fun j => x ∈ Ideal.span {((p : ℕ) : Oring p N g) ^ j}) (m := 0) (Nat.zero_le _) ?_
  rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top

theorem le_pval_iff {x : Oring p N g} {j : ℕ} (hj : j ≤ N) :
    j ≤ pval_Oring p N g x ↔ x ∈ Ideal.span {((p : ℕ) : Oring p N g) ^ j} := by
  classical
  constructor
  · intro hle
    exact span_p_pow_antitone p N g hle (mem_span_p_pow_pval p N g x)
  · intro hmem; unfold pval_Oring; exact Nat.le_findGreatest hj hmem

theorem pval_zero : pval_Oring p N g 0 = N :=
  le_antisymm (pval_le p N g 0) ((le_pval_iff p N g le_rfl).mpr (Ideal.zero_mem _))

end

end LeanUrat.OM.UnramifiedBase
