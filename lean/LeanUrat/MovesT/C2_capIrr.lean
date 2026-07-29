/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D7_npid
import LeanUrat.MovesC.C0_unitriBij

/-! # T-C2 `tbcap_irr` — the (τ-irr) per-class cross-level cap law (MOVES 7161–7187):
the cap is N(η′,⊤) = `capIrrOf` = `jetTopLevel` (Defs §2.11); cross-level constancy
via T-D7 (NP-ID); the family law quantified over ALL presented N AND box sizes
(REV 4, Codex-3 #5). `capIrrOf` is DECLARED in Defs.lean (§2.5 order note (8)). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-! ### T-C2 helper kernel (2026-07-29 prover pass): foldr-union membership, the
unitriangular preimage-locality face, the SHZ digit-locality kernel, and the
coordOf–levelIdx bridge (the ≺-sorted chart is FORCED level-major). All proved. -/

/- `mem_foldr_union` MOVED to `D7_npid.lean` (round-3 repair; statement
byte-identical) — both units read `transportedLevels`' List-safe fold and C2
imports D7. -/

/-- **the ≺-unitriangular preimage-locality face** (§C.0.5): if two IMAGES of a
unitriangular move agree on a downward-closed coordinate set, so do the arguments —
by strong recursion on the coordinate index (the diagonal is the identity; the
correction reads strictly-earlier coordinates, which stay inside the downset). -/
lemma unitri_preimage_agree {m' q : ℕ} {Θ : (Fin m' → ZMod q) → (Fin m' → ZMod q)}
    (hΘ : IsUnitriangular Θ) {D : Fin m' → Prop}
    (hD : ∀ ⦃c' c : Fin m'⦄, c' ≤ c → D c → D c')
    {a b : Fin m' → ZMod q} (hab : ∀ c, D c → Θ a c = Θ b c) :
    ∀ c, D c → a c = b c := by
  choose C hC using hΘ
  have aux : ∀ K : ℕ, ∀ c : Fin m', (c : ℕ) < K → D c → a c = b c := by
    intro K
    induction K with
    | zero => intro c hc _; exact absurd hc (Nat.not_lt_zero _)
    | succ K ih =>
      intro c hcK hc
      have hcorr : (fun (j : Fin m') (_ : j < c) => a j) = (fun j _ => b j) := by
        funext j hj
        refine ih j ?_ (hD (le_of_lt hj) hc)
        have hjc := Fin.lt_def.mp hj
        omega
      have h3 := hab c hc
      rw [hC c a, hC c b, hcorr] at h3
      exact add_right_cancel h3
  intro c hc
  exact aux ((c : ℕ) + 1) c (Nat.lt_succ_self _) hc

/-- **T-C2's SHZ digit-locality kernel**: membership in the class locus `S(H,⊤)` reads
only the digits on a downward-closed coordinate set `D` containing every consumed
fresh-clause support. The presentation chain is unique over each box point (the moves
are ≺-unitriangular bijections, `C0_unitriBij`), agreement on a ≺-downset transports
down the chain (`unitri_preimage_agree`), and each clause reads only its support
(`LevelClause.dep`); `Z = ⊤` pins nothing. -/
lemma shz_top_local {H : History p F} (J : JetSetup H n N m)
    {D : Fin m → Prop} (hD : ∀ ⦃c' c : Fin m⦄, c' ≤ c → D c → D c')
    (hsupp : ∀ r, r < H.nodes.length → ∀ cl ∈ (J.fresh r).clauses,
      ∀ c ∈ cl.support, D c)
    {x x' : Box p m} (hagree : ∀ c, D c → x c = x' c) :
    x ∈ J.SHZ (topLocus p m) ↔ x' ∈ J.SHZ (topLocus p m) := by
  suffices h : ∀ u v : Box p m, (∀ c, D c → u c = v c) →
      u ∈ J.SHZ (topLocus p m) → v ∈ J.SHZ (topLocus p m) by
    exact ⟨h x x' hagree, h x' x (fun c hc => (hagree c hc).symm)⟩
  intro u v huv hu
  obtain ⟨y, hy0, hchain, hsat, -⟩ := hu
  -- the transported chain over v, through the move inverses
  let Th : ℕ → (Box p m ≃ Box p m) := fun r =>
    Equiv.ofBijective (J.Theta r) (C0_unitriBij (J.Theta_uni r))
  let y' : ℕ → Box p m := fun r =>
    Nat.rec (motive := fun _ => Box p m) v (fun r yr => (Th r).symm yr) r
  have hchain' : ∀ r, r < H.nodes.length → y' r = J.Theta r (y' (r + 1)) := by
    intro r _
    change y' r = J.Theta r ((Th r).symm (y' r))
    exact ((Th r).apply_symm_apply (y' r)).symm
  -- agreement on D rides down the chain
  have hag : ∀ r, r ≤ H.nodes.length → ∀ c, D c → y r c = y' r c := by
    intro r
    induction r with
    | zero => intro _ c hc; rw [hy0]; exact huv c hc
    | succ r ih =>
      intro hr c hc
      have hrlen : r < H.nodes.length := hr
      refine unitri_preimage_agree (J.Theta_uni r) hD ?_ c hc
      intro c' hc'
      rw [← hchain r hrlen, ← hchain' r hrlen]
      exact ih (le_of_lt hrlen) c' hc'
  refine ⟨y', rfl, hchain', ?_, ?_⟩
  · intro r hr cl hcl
    refine (cl.dep (y r) (y' r) ?_).mp (hsat r hr cl hcl)
    intro c hc
    exact hag r (le_of_lt hr) c (hsupp r hr cl hcl c hc)
  · intro c hc
    exact absurd hc (by simp [topLocus])

/-- a strictly increasing ℕ-valued sequence on `Fin m` with values below `m` is the
identity (both bounds by Nat induction — the finite-order sandwich). -/
lemma strictMono_fin_eq_id {m' : ℕ} (g : Fin m' → ℕ)
    (hmono : ∀ j j' : Fin m', j < j' → g j < g j') (hlt : ∀ j, g j < m') :
    ∀ j : Fin m', g j = (j : ℕ) := by
  have hlow : ∀ K : ℕ, ∀ j : Fin m', (j : ℕ) ≤ K → (j : ℕ) ≤ g j := by
    intro K
    induction K with
    | zero => intro j hj; omega
    | succ K ih =>
      intro j hj
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
      · omega
      · have hmk : ((j : ℕ) - 1) < m' := by have := j.isLt; omega
        have hv : ((⟨(j : ℕ) - 1, hmk⟩ : Fin m') : ℕ) = (j : ℕ) - 1 := rfl
        have h1 := ih ⟨(j : ℕ) - 1, hmk⟩ (by omega)
        have h2 := hmono ⟨(j : ℕ) - 1, hmk⟩ j (by rw [Fin.lt_def, hv]; omega)
        omega
  have hhigh : ∀ K : ℕ, ∀ j : Fin m', m' - 1 - (j : ℕ) ≤ K → g j ≤ (j : ℕ) := by
    intro K
    induction K with
    | zero =>
      intro j hj
      have h1 := hlt j
      have h2 := j.isLt
      omega
    | succ K ih =>
      intro j hj
      rcases Nat.lt_or_ge ((j : ℕ) + 1) m' with hup | hge
      · have hv : ((⟨(j : ℕ) + 1, hup⟩ : Fin m') : ℕ) = (j : ℕ) + 1 := rfl
        have h1 := ih ⟨(j : ℕ) + 1, hup⟩ (by omega)
        have h2 := hmono j ⟨(j : ℕ) + 1, hup⟩ (by rw [Fin.lt_def, hv]; omega)
        omega
      · have h1 := hlt j
        have h2 := j.isLt
        omega
  intro j
  have h1 := hlow (j : ℕ) j le_rfl
  have h2 := hhigh (m' - 1 - (j : ℕ)) j le_rfl
  omega

/-- the ≺-sorted in-box chart is FORCED level-major with base descending: its
lexicographic key `ℓ·n + (n−1−b)` enumerates `Fin m` in order (`C0_coordSort`'s
witness is the ONLY sorted chart). -/
lemma coordOf_key_eq {H : History p F} (J : JetSetup H n N m) (c : Fin m) :
    (J.coordOf c).1 * n + (n - 1 - (J.coordOf c).2) = (c : ℕ) := by
  have hn : 0 < n := by have := (J.coordOf_lt c).2; omega
  refine strictMono_fin_eq_id (fun j => (J.coordOf j).1 * n + (n - 1 - (J.coordOf j).2))
    ?_ ?_ c
  · intro j j' hjj
    have hp := (J.coordOf_sorted j j').1 hjj
    have hb := (J.coordOf_lt j).2
    have hb' := (J.coordOf_lt j').2
    rcases hp with hl | ⟨hl, hr⟩
    · calc (J.coordOf j).1 * n + (n - 1 - (J.coordOf j).2)
          < (J.coordOf j).1 * n + n := Nat.add_lt_add_left (by omega) _
        _ = ((J.coordOf j).1 + 1) * n := by ring
        _ ≤ (J.coordOf j').1 * n := Nat.mul_le_mul (Nat.succ_le_of_lt hl) (le_refl n)
        _ ≤ (J.coordOf j').1 * n + (n - 1 - (J.coordOf j').2) := Nat.le_add_right _ _
    · rw [hl]
      exact Nat.add_lt_add_left (by omega) _
  · intro j
    have h1 := (J.coordOf_lt j).1
    have h2 := (J.coordOf_lt j).2
    have hm := J.hm
    calc (J.coordOf j).1 * n + (n - 1 - (J.coordOf j).2)
        < (J.coordOf j).1 * n + n := Nat.add_lt_add_left (by omega) _
      _ = ((J.coordOf j).1 + 1) * n := by ring
      _ ≤ N * n := Nat.mul_le_mul (Nat.succ_le_of_lt h1) (le_refl n)
      _ = m := by rw [hm]; ring

/-- the chart's LEVEL slot is `⌊c/n⌋`. -/
lemma coordOf_fst {H : History p F} (J : JetSetup H n N m) (c : Fin m) :
    (J.coordOf c).1 = (c : ℕ) / n := by
  have hn : 0 < n := by have := (J.coordOf_lt c).2; omega
  have hr : n - 1 - (J.coordOf c).2 < n := by omega
  rw [← coordOf_key_eq J c, Nat.add_comm, Nat.add_mul_div_right _ _ hn,
    Nat.div_eq_of_lt hr]
  omega

/-- **the coordOf–levelIdx bridge**: the box-layout level index of T-D3's cap law IS
the chart level plus one (`levelIdx` is 1-indexed, the chart's `Coord.1` is the
0-indexed digit index — `pres_zero`/`baseDigit`). -/
lemma levelIdx_coordOf {H : History p F} (J : JetSetup H n N m) (c : Fin m) :
    levelIdx (n := n) c = (J.coordOf c).1 + 1 := by
  unfold levelIdx
  rw [coordOf_fst J c]

/-- every consumed fresh-support coordinate is TRANSPORTED at `Z = ⊤` (nothing is
pinned), so its chart level is bounded by the sup `jetTopLevel` reads. [Round-3
repair rider: the read bound is `r < H.nodes.length` — `transportedLevels`' fixed
range (the Defs item-1 repair; `fresh H.nodes.length` is unconstrained junk).] -/
lemma le_sup_of_transported {H : History p F} (J : JetSetup H n N m)
    {r : ℕ} (hr : r < H.nodes.length) {cl : LevelClause p m}
    (hcl : cl ∈ (J.fresh r).clauses) {c : Fin m} (hc : c ∈ cl.support) :
    (J.coordOf c).1 ≤ (transportedLevels J (topLocus p m)).sup Prod.fst := by
  have hmem : J.coordOf c ∈ transportedLevels J (topLocus p m) := by
    unfold transportedLevels
    refine Finset.mem_image_of_mem _ ?_
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [Finset.mem_biUnion]
    exact ⟨r, Finset.mem_range.mpr hr,
      mem_foldr_union (List.mem_map_of_mem (f := fun cl => cl.support) hcl) hc⟩
  exact Finset.le_sup (f := Prod.fst) hmem

/-- cross-level constancy: via T-D7 (NP-ID), each side's pinned-equation level set =
`bandLevels (P : ShapePrefix) n` — shape data. [Round-3 repair ripple (item 4, T-D7):
`np_id` now carries L12's own range premise, so BOTH levels are premised on it
(`hNP`/`hNP'`) — the sub-threshold countermodel refutes the unguarded ∀-N,N' form
(a jet at N < NPband transports a strictly smaller level set).] -/
theorem capIrr_uniform {P : Shape n} (i : PrefIdx n pol P)
    {N N' m m' : ℕ}
    (hNP : (P : ShapePrefix).NPband n ≤ N) (hNP' : (P : ShapePrefix).NPband n ≤ N')
    (J : JetSetup (reprOf i) n N m) (J' : JetSetup (reprOf i) n N' m') :
    capIrrOf J = capIrrOf J' := by
  -- the blueprint's EXPLICIT T-D7 consumption (NP-ID): both jets' transported level
  -- sets equal the SAME shape-side grid, so the sup — hence the cap — coincides.
  unfold capIrrOf jetTopLevel
  rw [np_id i hNP J, np_id i hNP' J']

/-- [STATEMENT REPAIR, adjudicated round-3 item (5) = the E-phase off-by-one residual,
option (ii) with minimal blast radius: the hagree window is INCLUSIVE, `levelIdx c ≤
capIrrOf (S.jet i)`. The note's OWN window includes the level-N residue classes —
MOVES 7178–7180: "§C C.2 (Z = ∅) cuts S(η′,⊤) at level N(η′,⊤) = 1 + the largest base
level among T(η′,⊤)'s finitely many equations — an EXACT finite union of
**level-N(η′,⊤) residue classes**" — and `levelIdx` is 1-INDEXED (⌊c/n⌋ + 1), so the
level-N(η′,⊤) classes are exactly the coordinates with `levelIdx ≤ capIrrOf`. The
former strict window stopped one level short (the sup is attained). Window ripple:
`tbcap_irr_family` / `tbcap_irr_npband` below (the in-file repair note's "ripple =
CapIrrLaw sites").] -/
theorem tbcap_irr {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx (n := n) c ≤ capIrrOf (S.jet i) → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i) := by
  -- the fiber IS the class locus S(η′,⊤); the kernel `shz_top_local` reduces the
  -- theorem to: every consumed fresh-support coordinate sits under the cap.
  refine shz_top_local (S.jet i)
    (D := fun c => levelIdx (n := n) c ≤ capIrrOf (S.jet i)) ?_ ?_ hagree
  · -- the levelIdx cut is downward closed
    intro c' c hle hc
    unfold levelIdx at hc ⊢
    have h1 : (c' : ℕ) / n ≤ (c : ℕ) / n := Nat.div_le_div_right (Fin.le_def.mp hle)
    omega
  · intro r hr cl hcl c hc
    -- the two PROVED halves of the support bound:
    have h1 : ((S.jet i).coordOf c).1
        ≤ (transportedLevels (S.jet i) (topLocus p m)).sup Prod.fst :=
      le_sup_of_transported (S.jet i) hr hcl hc
    have h2 : levelIdx (n := n) c = ((S.jet i).coordOf c).1 + 1 :=
      levelIdx_coordOf (S.jet i) c
    -- the inclusive window is exactly the provable (tight) bound:
    unfold capIrrOf jetTopLevel
    omega

/-- the COMPATIBLE FAMILY across all presented N and box sizes (Codex-2 #5 / Codex-3
#5): one cap per class — from `tbcap_irr` + T-D7. This theorem discharges
`CapIrrLaw` (§2.9, its window read inclusively through cap := capIrrOf J₀ + 1) at
T-D3's cap datum. [Round-3 repair ripple: (a) the window is INCLUSIVE (item 5, the
tbcap_irr flip above); (b) the REFERENCE jet carries L12's range premise `hNP₀`
(item 4 — `np_id` at J₀ needs it). The ∀ N' family quantifier is UNCHANGED: a
presented member at ANY N' consumes only the premise-free ⊆ half (`np_id_sub`), whose
cap is ≤ the over-threshold reference cap via the filters-agree identity.] -/
theorem tbcap_irr_family {P : Shape n} (i : PrefIdx n pol P)
    (hirr : IrrHalts (reprOf i))
    (hNP₀ : (P : ShapePrefix).NPband n ≤ N)
    (J₀ : JetSetup (reprOf i) n N m) :
    ∀ (N' m' : ℕ) (S : Presented p F n N' m' pol P) (x x' : Box p m'),
      (∀ c : Fin m', levelIdx (n := n) c ≤ capIrrOf J₀ → x c = x' c) →
      (x ∈ S.fiber i ↔ x' ∈ S.fiber i) := by
  intro N' m' S x x' hagree
  -- the presented jet's cap is bounded by the over-threshold reference cap
  have hsub : capIrrOf (S.jet i) ≤ capIrrOf J₀ := by
    have hmono : (transportedLevels (S.jet i) (topLocus p m')).sup Prod.fst
        ≤ (bandLevels (P : ShapePrefix) n).sup Prod.fst :=
      Finset.sup_mono (np_id_sub i (S.jet i))
    unfold capIrrOf jetTopLevel
    rw [np_id i hNP₀ J₀]
    omega
  refine tbcap_irr S i hirr x x' ?_
  intro c hc
  exact hagree c (le_trans hc hsub)

/-- the NPband corollary — T-D7a's conclusion an EXPLICIT premise `hnp`. [Round-3
repair ripple: the window is INCLUSIVE (`≤ NPband` — the tbcap_irr flip; the tight
case capIrrOf = NPband is attained at over-threshold jets).] -/
theorem tbcap_irr_npband {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) (hirr : IrrHalts (reprOf i))
    (hnp : transportedLevels (S.jet i) (topLocus p m) ⊆ bandLevels (P : ShapePrefix) n)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, levelIdx (n := n) c ≤ (P : ShapePrefix).NPband n → x c = x' c) :
    (x ∈ S.fiber i ↔ x' ∈ S.fiber i) := by
  have hbot : (0 : ℕ) < (P : ShapePrefix).NPband n := by
    unfold ShapePrefix.NPband; omega
  have hbound : capIrrOf (S.jet i) ≤ (P : ShapePrefix).NPband n := by
    unfold capIrrOf jetTopLevel
    have hlt : (transportedLevels (S.jet i) (topLocus p m)).sup Prod.fst
        < (P : ShapePrefix).NPband n := by
      rw [Finset.sup_lt_iff hbot]
      intro c hc
      have hcb : c ∈ bandLevels (P : ShapePrefix) n := hnp hc
      simp only [bandLevels, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hcb
      exact hcb.1.1
    omega
  refine tbcap_irr S i hirr x x' ?_
  intro c hc
  exact hagree c (le_trans hc hbound)

end LeanUrat.MovesT
