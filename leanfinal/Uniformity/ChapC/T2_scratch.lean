import Uniformity.ChapC.C108

set_option linter.style.longLine false
set_option linter.overlappingInstances false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Scratch

open Uniformity.Density.Tower

/-! ### chord arithmetic -/

private theorem chord_le {ℓ u : ℕ} (P : ℕ → ℕ) {i j k : ℕ} (hℓ : 0 < ℓ)
    (hij : i ≤ j) (hjk : j ≤ k)
    (h1 : ℓ * P j + u * j ≤ ℓ * P i + u * i)
    (h2 : ℓ * P j + u * j ≤ ℓ * P k + u * k) :
    (k - i) * P j ≤ (k - j) * P i + (j - i) * P k := by
  obtain ⟨a, rfl⟩ : ∃ a, j = i + a := ⟨j - i, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = i + a + b := ⟨k - i - a, by omega⟩
  have s1 : i + a + b - i = a + b := by omega
  have s2 : i + a + b - (i + a) = b := by omega
  have s3 : i + a - i = a := by omega
  rw [s1, s2, s3]
  set Pi := P i with hPi
  set Pj := P (i + a) with hPj
  set Pk := P (i + a + b) with hPk
  have e1 : b * (ℓ * Pj + u * (i + a)) ≤ b * (ℓ * Pi + u * i) := Nat.mul_le_mul (le_refl _) h1
  have e2 : a * (ℓ * Pj + u * (i + a)) ≤ a * (ℓ * Pk + u * (i + a + b)) :=
    Nat.mul_le_mul (le_refl _) h2
  have key : ℓ * ((a + b) * Pj) ≤ ℓ * (b * Pi + a * Pk) := by nlinarith [e1, e2]
  exact Nat.le_of_mul_le_mul_left key hℓ

private theorem nv_le_of_chord {ℓ u : ℕ} (P : ℕ → ℕ) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (hik : i < k)
    (hchord : (k - i) * P j ≤ (k - j) * P i + (j - i) * P k)
    (heq : ℓ * P i + u * i = ℓ * P k + u * k) :
    ℓ * P j + u * j ≤ ℓ * P i + u * i := by
  obtain ⟨a, rfl⟩ : ∃ a, j = i + a := ⟨j - i, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = i + a + b := ⟨k - i - a, by omega⟩
  have hab : 0 < a + b := by omega
  have s1 : i + a + b - i = a + b := by omega
  have s2 : i + a + b - (i + a) = b := by omega
  have s3 : i + a - i = a := by omega
  rw [s1, s2, s3] at hchord
  set Pi := P i with hPi
  set Pj := P (i + a) with hPj
  set Pk := P (i + a + b) with hPk
  have hc' : ℓ * ((a + b) * Pj) ≤ ℓ * (b * Pi + a * Pk) := Nat.mul_le_mul (le_refl ℓ) hchord
  have hq : a * (ℓ * Pi + u * i) = a * (ℓ * Pk + u * (i + a + b)) := by rw [heq]
  have key : (a + b) * (ℓ * Pj + u * (i + a)) ≤ (a + b) * (ℓ * Pi + u * i) := by
    nlinarith [hc', hq]
  exact Nat.le_of_mul_le_mul_left key hab

/-! ### the node's argmin set -/

private theorem mem_nodeSideSet {v : HTNode} {u ℓ j : ℕ} :
    j ∈ v.nodeSideSet u ℓ ↔ j ≤ v.m ∧ ∀ i, i ≤ v.m → ℓ * v.Pceil j + u * j ≤ ℓ * v.Pceil i + u * i := by
  classical
  have h : j ∈ Finset.filter (v.NodeOnSide u ℓ) (Finset.range (v.m + 1))
      ↔ j ∈ v.nodeSideSet u ℓ := Iff.rfl
  rw [← h, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  rfl

private noncomputable def nsMin (v : HTNode) (u ℓ : ℕ) : ℕ := (v.nodeSideSet u ℓ).min.getD 0
private noncomputable def nsMax (v : HTNode) (u ℓ : ℕ) : ℕ := (v.nodeSideSet u ℓ).max.getD 0

private theorem nsMin_eq (v : HTNode) {u ℓ : ℕ} (h : (v.nodeSideSet u ℓ).Nonempty) :
    nsMin v u ℓ = (v.nodeSideSet u ℓ).min' h := by
  rw [nsMin, ← Finset.coe_min' h]; rfl

private theorem nsMax_eq (v : HTNode) {u ℓ : ℕ} (h : (v.nodeSideSet u ℓ).Nonempty) :
    nsMax v u ℓ = (v.nodeSideSet u ℓ).max' h := by
  rw [nsMax, ← Finset.coe_max' h]; rfl

end Scratch

namespace S2

open Uniformity.Density.Tower Scratch

variable {v : HTNode} {u ℓ : ℕ}

private theorem ns_nonempty (hside : v.IsSide u ℓ) : (v.nodeSideSet u ℓ).Nonempty :=
  Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_two hside.2.2)

private theorem nsMin_mem (hside : v.IsSide u ℓ) : nsMin v u ℓ ∈ v.nodeSideSet u ℓ := by
  rw [nsMin_eq v (ns_nonempty hside)]; exact Finset.min'_mem _ _

private theorem nsMax_mem (hside : v.IsSide u ℓ) : nsMax v u ℓ ∈ v.nodeSideSet u ℓ := by
  rw [nsMax_eq v (ns_nonempty hside)]; exact Finset.max'_mem _ _

private theorem nsMin_le_of_mem (hside : v.IsSide u ℓ) {j : ℕ} (hj : j ∈ v.nodeSideSet u ℓ) :
    nsMin v u ℓ ≤ j := by
  rw [nsMin_eq v (ns_nonempty hside)]; exact Finset.min'_le _ _ hj

private theorem le_nsMax_of_mem (hside : v.IsSide u ℓ) {j : ℕ} (hj : j ∈ v.nodeSideSet u ℓ) :
    j ≤ nsMax v u ℓ := by
  rw [nsMax_eq v (ns_nonempty hside)]; exact Finset.le_max' _ _ hj

private theorem nsMin_lt_nsMax (hside : v.IsSide u ℓ) : nsMin v u ℓ < nsMax v u ℓ := by
  rw [nsMin_eq v (ns_nonempty hside), nsMax_eq v (ns_nonempty hside)]
  exact Finset.min'_lt_max'_of_card _ (lt_of_lt_of_le Nat.one_lt_two hside.2.2)

private theorem nv_le_of_mem {j : ℕ} (hj : j ∈ v.nodeSideSet u ℓ) {i : ℕ} (hi : i ≤ v.m) :
    ℓ * v.Pceil j + u * j ≤ ℓ * v.Pceil i + u * i := (mem_nodeSideSet.1 hj).2 i hi

private theorem le_m_of_mem {j : ℕ} (hj : j ∈ v.nodeSideSet u ℓ) : j ≤ v.m :=
  (mem_nodeSideSet.1 hj).1

private theorem nv_eq_of_mem (hside : v.IsSide u ℓ) {j : ℕ} (hj : j ∈ v.nodeSideSet u ℓ) :
    ℓ * v.Pceil j + u * j = ℓ * v.Pceil (nsMin v u ℓ) + u * nsMin v u ℓ :=
  le_antisymm (nv_le_of_mem hj (le_m_of_mem (nsMin_mem hside)))
    (nv_le_of_mem (nsMin_mem hside) (le_m_of_mem hj))

private theorem onHull_of_mem (hℓ : 0 < ℓ) {j : ℕ} (hj : j ∈ v.nodeSideSet u ℓ) : v.OnHull j := by
  intro i k hij hjk hkm
  exact chord_le v.Pceil hℓ hij hjk
    (nv_le_of_mem hj (le_trans hij (le_m_of_mem hj)))
    (nv_le_of_mem hj hkm)

private theorem mem_of_onHull_between (hside : v.IsSide u ℓ) {j : ℕ}
    (h1 : nsMin v u ℓ ≤ j) (h2 : j ≤ nsMax v u ℓ) (hoh : v.OnHull j) :
    j ∈ v.nodeSideSet u ℓ := by
  have hbm : nsMax v u ℓ ≤ v.m := le_m_of_mem (nsMax_mem hside)
  have hchord := hoh (nsMin v u ℓ) (nsMax v u ℓ) h1 h2 hbm
  have heq : ℓ * v.Pceil (nsMin v u ℓ) + u * nsMin v u ℓ
      = ℓ * v.Pceil (nsMax v u ℓ) + u * nsMax v u ℓ := (nv_eq_of_mem hside (nsMax_mem hside)).symm
  have hle := nv_le_of_chord v.Pceil h1 h2 (nsMin_lt_nsMax hside) hchord heq
  refine mem_nodeSideSet.2 ⟨le_trans h2 hbm, fun i hi => le_trans hle ?_⟩
  exact nv_le_of_mem (nsMin_mem hside) hi

private theorem dvd_sub_nsMin (hℓ : 0 < ℓ) (hside : v.IsSide u ℓ) {j : ℕ}
    (hj : j ∈ v.nodeSideSet u ℓ) : ℓ ∣ (j - nsMin v u ℓ) := by
  obtain ⟨d, hd⟩ : ∃ d, j = nsMin v u ℓ + d := ⟨j - nsMin v u ℓ, by
    have := nsMin_le_of_mem hside hj; omega⟩
  have heq := nv_eq_of_mem hside hj
  rw [hd] at heq
  have heq' : ℓ * v.Pceil (nsMin v u ℓ + d) + u * d = ℓ * v.Pceil (nsMin v u ℓ) := by
    have : u * (nsMin v u ℓ + d) = u * nsMin v u ℓ + u * d := by ring
    omega
  have hPle : v.Pceil (nsMin v u ℓ + d) ≤ v.Pceil (nsMin v u ℓ) :=
    Nat.le_of_mul_le_mul_left (by omega) hℓ
  obtain ⟨e, he⟩ : ∃ e, v.Pceil (nsMin v u ℓ) = v.Pceil (nsMin v u ℓ + d) + e :=
    ⟨v.Pceil (nsMin v u ℓ) - v.Pceil (nsMin v u ℓ + d), by omega⟩
  have hue : u * d = ℓ * e := by
    rw [he, Nat.mul_add] at heq'
    omega
  have hdvd : ℓ ∣ u * d := ⟨e, hue⟩
  have : ℓ ∣ d := (Nat.Coprime.dvd_of_dvd_mul_left hside.2.1.symm) hdvd
  simpa [hd] using this

end S2

namespace S3

open Uniformity.Density.Tower Scratch S2

variable {v : HTNode} {u ℓ : ℕ}

private theorem nodeSideDeg_eq (v : HTNode) (u ℓ : ℕ) :
    v.nodeSideDeg u ℓ = (nsMax v u ℓ - nsMin v u ℓ) / ℓ := rfl

private theorem nsMax_eq_add (hℓ : 0 < ℓ) (hside : v.IsSide u ℓ) :
    nsMax v u ℓ = nsMin v u ℓ + ℓ * v.nodeSideDeg u ℓ := by
  have hdvd := dvd_sub_nsMin hℓ hside (nsMax_mem hside)
  have hle := (nsMin_lt_nsMax hside).le
  rw [nodeSideDeg_eq, Nat.mul_div_cancel' hdvd]
  omega

private theorem nodeSideDeg_pos (hℓ : 0 < ℓ) (hside : v.IsSide u ℓ) :
    0 < v.nodeSideDeg u ℓ := by
  rcases Nat.eq_zero_or_pos (v.nodeSideDeg u ℓ) with h | h
  · have := nsMax_eq_add hℓ hside
    have := nsMin_lt_nsMax hside
    rw [h] at *; omega
  · exact h

private theorem mem_lattice (hℓ : 0 < ℓ) (hwf : v.WF) (hside : v.IsSide u ℓ) {t : ℕ}
    (ht : t ≤ v.nodeSideDeg u ℓ) : nsMin v u ℓ + ℓ * t ∈ v.nodeSideSet u ℓ := by
  obtain ⟨s, hs⟩ : ∃ s, v.nodeSideDeg u ℓ = t + s := ⟨v.nodeSideDeg u ℓ - t, by omega⟩
  set a := nsMin v u ℓ with hadef
  set b := nsMax v u ℓ with hbdef
  have hb : b = a + ℓ * (t + s) := by rw [hbdef, hadef, nsMax_eq_add hℓ hside, hs]
  have hb' : b = a + (ℓ * t + ℓ * s) := by rw [hb]; ring_nf
  have hab : a < b := nsMin_lt_nsMax hside
  have hts : 0 < t + s := by
    have := nodeSideDeg_pos hℓ hside; omega
  have hbm : b ≤ v.m := le_m_of_mem (nsMax_mem hside)
  set j := a + ℓ * t with hjdef
  have hjb : j ≤ b := by omega
  have hja : a ≤ j := Nat.le_add_right _ _
  have hjm : j ≤ v.m := le_trans hjb hbm
  -- the polygon drop across the side
  have hMab : ℓ * v.Pceil a + u * a = ℓ * v.Pceil b + u * b :=
    (nv_eq_of_mem hside (nsMax_mem hside)).symm
  have hPa : v.Pceil a = v.Pceil b + u * (t + s) := by
    refine Nat.eq_of_mul_eq_mul_left hℓ ?_
    have hexp : u * b = u * a + ℓ * (u * (t + s)) := by rw [hb]; ring
    rw [Nat.mul_add]
    omega
  -- the ceiled-consistency chord at `j`
  have hwf2 := hwf.2.1 a j b hja hjb hbm hab
  have s1 : b - a = ℓ * t + ℓ * s := by omega
  have s2 : j - a = ℓ * t := by omega
  have s3 : b - j = ℓ * s := by omega
  rw [s1, s2, s3] at hwf2
  have hup : (t + s) * v.Pceil j < s * v.Pceil a + t * v.Pceil b + (t + s) := by
    refine Nat.lt_of_mul_lt_mul_left (a := ℓ) ?_
    calc ℓ * ((t + s) * v.Pceil j) = (ℓ * t + ℓ * s) * v.Pceil j := by ring
      _ < ℓ * s * v.Pceil a + ℓ * t * v.Pceil b + (ℓ * t + ℓ * s) := hwf2
      _ = ℓ * (s * v.Pceil a + t * v.Pceil b + (t + s)) := by ring
  have hupper : v.Pceil j ≤ v.Pceil b + u * s := by
    have h1 : (t + s) * v.Pceil j < (t + s) * (v.Pceil b + u * s + 1) := by
      calc (t + s) * v.Pceil j < s * v.Pceil a + t * v.Pceil b + (t + s) := hup
        _ = s * (v.Pceil b + u * (t + s)) + t * v.Pceil b + (t + s) := by rw [hPa]
        _ = (t + s) * (v.Pceil b + u * s + 1) := by ring
    exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left h1)
  have hlower : v.Pceil b + u * s ≤ v.Pceil j := by
    have hge : ℓ * v.Pceil a + u * a ≤ ℓ * v.Pceil j + u * j :=
      nv_le_of_mem (nsMin_mem hside) hjm
    have hexp : u * j = u * a + ℓ * (u * t) := by rw [hjdef]; ring
    have h2 : ℓ * (v.Pceil b + u * (t + s)) ≤ ℓ * (v.Pceil j + u * t) := by
      rw [← hPa, Nat.mul_add]
      omega
    have h3 : v.Pceil b + u * (t + s) ≤ v.Pceil j + u * t := Nat.le_of_mul_le_mul_left h2 hℓ
    have h4 : u * (t + s) = u * t + u * s := by ring
    omega
  have hPj : v.Pceil j = v.Pceil b + u * s := le_antisymm hupper hlower
  refine mem_nodeSideSet.2 ⟨hjm, fun i hi => ?_⟩
  have hval : ℓ * v.Pceil j + u * j = ℓ * v.Pceil a + u * a := by
    rw [hPj, hjdef, hPa]; ring
  rw [hval]
  exact nv_le_of_mem (nsMin_mem hside) hi

end S3

namespace S4

open Uniformity.Density.Tower Scratch S2 S3

variable {v : HTNode}

/-- the steepest-descent construction: every on-hull abscissa below `m` is the left part of a
genuine side. -/
private theorem exists_side (hwf : v.WF) {j : ℕ} (hjm : j < v.m) (hoh : v.OnHull j) :
    ∃ U L : ℕ, v.IsSide U L ∧ j ∈ v.nodeSideSet U L ∧ j < nsMax v U L := by
  classical
  obtain ⟨k, hkT, hkmin⟩ := Finset.exists_min_image (Finset.Ioc j v.m)
      (fun k => ((v.Pceil k : ℚ) - (v.Pceil j : ℚ)) / ((k : ℚ) - (j : ℚ)))
      ⟨v.m, Finset.mem_Ioc.2 ⟨hjm, le_refl _⟩⟩
  obtain ⟨hjk, hkm⟩ := Finset.mem_Ioc.1 hkT
  -- minimality with denominators cleared
  have hclear : ∀ i, j < i → i ≤ v.m →
      v.Pceil k * (i - j) + v.Pceil j * (k - j)
        ≤ v.Pceil i * (k - j) + v.Pceil j * (i - j) := by
    intro i hji him
    have h := hkmin i (Finset.mem_Ioc.2 ⟨hji, him⟩)
    have hdk : (0:ℚ) < (k:ℚ) - (j:ℚ) := by
      have : (j:ℚ) < (k:ℚ) := by exact_mod_cast hjk
      linarith
    have hdi : (0:ℚ) < (i:ℚ) - (j:ℚ) := by
      have : (j:ℚ) < (i:ℚ) := by exact_mod_cast hji
      linarith
    rw [div_le_div_iff₀ hdk hdi] at h
    have hq : ((v.Pceil k * (i - j) + v.Pceil j * (k - j) : ℕ) : ℚ)
        ≤ ((v.Pceil i * (k - j) + v.Pceil j * (i - j) : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub hji.le, Nat.cast_sub hjk.le]
      nlinarith [h]
    exact_mod_cast hq
  -- the drop is nonnegative
  have hPm : v.Pceil v.m = 0 := hwf.1
  have hPk : v.Pceil k ≤ v.Pceil j := by
    have h := hclear v.m hjm (le_refl _)
    rw [hPm] at h
    have h2 : v.Pceil k * (v.m - j) ≤ v.Pceil j * (v.m - j) := by omega
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  -- opaque side coordinates
  obtain ⟨dk, hdk1⟩ : ∃ dk, k = j + dk := ⟨k - j, by omega⟩
  have hdk0 : 0 < dk := by omega
  obtain ⟨D, hD1⟩ : ∃ D, v.Pceil j = v.Pceil k + D := ⟨v.Pceil j - v.Pceil k, by omega⟩
  obtain ⟨g, U, L, hg0, hDg, hdkg, hcop⟩ :
      ∃ g U L : ℕ, 0 < g ∧ D = g * U ∧ dk = g * L ∧ Nat.Coprime U L :=
    ⟨Nat.gcd D dk, D / Nat.gcd D dk, dk / Nat.gcd D dk,
      Nat.gcd_pos_of_pos_right _ hdk0,
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left D dk)).symm,
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right D dk)).symm,
      Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hdk0)⟩
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hdkg; omega
    · exact h
  have hnvk : L * v.Pceil k + U * k = L * v.Pceil j + U * j := by
    rw [hD1, hdk1, hDg, hdkg]; ring
  have hjmem : j ∈ v.nodeSideSet U L := by
    refine mem_nodeSideSet.2 ⟨hjm.le, fun i hi => ?_⟩
    refine Nat.le_of_mul_le_mul_left ?_ hg0
    have g1 : g * (L * v.Pceil j + U * j) = v.Pceil j * dk + D * j := by
      rw [hDg, hdkg]; ring
    have g2 : g * (L * v.Pceil i + U * i) = v.Pceil i * dk + D * i := by
      rw [hDg, hdkg]; ring
    rw [g1, g2, hD1]
    rcases lt_trichotomy i j with hij | rfl | hij
    · -- to the LEFT: the node's own hull chord at `(i, k)`
      obtain ⟨e, he⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
      have hch := hoh i k (by omega) (by omega) hkm
      have s1 : k - i = e + dk := by omega
      have s2 : k - j = dk := by omega
      have s3 : j - i = e := by omega
      rw [s1, s2, s3, hD1] at hch
      have hDj : D * j = D * i + D * e := by rw [he]; ring
      nlinarith [hch, hDj]
    · rw [hD1]
    · -- to the RIGHT: the steepest-descent minimality
      obtain ⟨e, he⟩ : ∃ e, i = j + e := ⟨i - j, by omega⟩
      have hcl := hclear i hij hi
      have s1 : i - j = e := by omega
      have s2 : k - j = dk := by omega
      rw [s1, s2, hD1] at hcl
      have hDi : D * i = D * j + D * e := by rw [he]; ring
      nlinarith [hcl, hDi]
  have hkmem : k ∈ v.nodeSideSet U L := by
    refine mem_nodeSideSet.2 ⟨hkm, fun i hi => ?_⟩
    rw [hnvk]
    exact (mem_nodeSideSet.1 hjmem).2 i hi
  have hcard : 2 ≤ (v.nodeSideSet U L).card := by
    have hsub : ({j, k} : Finset ℕ) ⊆ v.nodeSideSet U L := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hjmem
      · exact hkmem
    have hjk2 : ({j, k} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    calc 2 = ({j, k} : Finset ℕ).card := hjk2.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hside : v.IsSide U L := ⟨hL0, hcop, hcard⟩
  exact ⟨U, L, hside, hjmem, lt_of_lt_of_le hjk (le_nsMax_of_mem hside hkmem)⟩

end S4

namespace S5

open Uniformity.Density.Tower Scratch S2 S3 S4

variable {v : HTNode} {U L : ℕ}

private theorem chord_strict {ℓ u : ℕ} (P : ℕ → ℕ) {i j k : ℕ}
    (hij : i < j) (hjk : j < k)
    (h1 : ℓ * P j + u * j ≤ ℓ * P i + u * i)
    (h2 : ℓ * P j + u * j ≤ ℓ * P k + u * k)
    (hstrict : ℓ * P j + u * j < ℓ * P i + u * i ∨ ℓ * P j + u * j < ℓ * P k + u * k) :
    (k - i) * P j < (k - j) * P i + (j - i) * P k := by
  obtain ⟨a, rfl⟩ : ∃ a, j = i + (a + 1) := ⟨j - i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = i + (a + 1) + (b + 1) := ⟨k - i - a - 2, by omega⟩
  have s1 : i + (a + 1) + (b + 1) - i = (a + 1) + (b + 1) := by omega
  have s2 : i + (a + 1) + (b + 1) - (i + (a + 1)) = b + 1 := by omega
  have s3 : i + (a + 1) - i = a + 1 := by omega
  rw [s1, s2, s3]
  set Pi := P i with hPi
  set Pj := P (i + (a + 1)) with hPj
  set Pk := P (i + (a + 1) + (b + 1)) with hPk
  have key : ℓ * (((a + 1) + (b + 1)) * Pj) < ℓ * ((b + 1) * Pi + (a + 1) * Pk) := by
    rcases hstrict with hstr | hstr
    · have e1 : (b + 1) * (ℓ * Pj + u * (i + (a + 1)) + 1) ≤ (b + 1) * (ℓ * Pi + u * i) :=
        Nat.mul_le_mul (le_refl _) hstr
      have e2 : (a + 1) * (ℓ * Pj + u * (i + (a + 1)))
          ≤ (a + 1) * (ℓ * Pk + u * (i + (a + 1) + (b + 1))) :=
        Nat.mul_le_mul (le_refl _) h2
      nlinarith [e1, e2]
    · have e1 : (b + 1) * (ℓ * Pj + u * (i + (a + 1))) ≤ (b + 1) * (ℓ * Pi + u * i) :=
        Nat.mul_le_mul (le_refl _) h1
      have e2 : (a + 1) * (ℓ * Pj + u * (i + (a + 1)) + 1)
          ≤ (a + 1) * (ℓ * Pk + u * (i + (a + 1) + (b + 1))) :=
        Nat.mul_le_mul (le_refl _) hstr
      nlinarith [e1, e2]
  exact Nat.lt_of_mul_lt_mul_left key

private theorem isVertex_nsMin (hside : v.IsSide U L) : v.IsVertex (nsMin v U L) := by
  classical
  intro i k hi hk hkm
  have hmem := nsMin_mem hside
  have hle := le_m_of_mem hmem
  have him : i ≤ v.m := le_trans hi.le hle
  have hinot : i ∉ v.nodeSideSet U L := fun hc => absurd (nsMin_le_of_mem hside hc) (not_le.2 hi)
  have hstr : L * v.Pceil (nsMin v U L) + U * nsMin v U L < L * v.Pceil i + U * i := by
    rcases lt_or_ge (L * v.Pceil (nsMin v U L) + U * nsMin v U L) (L * v.Pceil i + U * i) with h | h
    · exact h
    · exact absurd (mem_nodeSideSet.2 ⟨him, fun i' hi' => le_trans h (nv_le_of_mem hmem hi')⟩)
        hinot
  exact chord_strict v.Pceil hi hk (le_of_lt hstr) (nv_le_of_mem hmem hkm) (Or.inl hstr)

private theorem isVertex_nsMax (hside : v.IsSide U L) : v.IsVertex (nsMax v U L) := by
  classical
  intro i k hi hk hkm
  have hmem := nsMax_mem hside
  have hle := le_m_of_mem hmem
  have hknot : k ∉ v.nodeSideSet U L := fun hc => absurd (le_nsMax_of_mem hside hc) (not_le.2 hk)
  have hstr : L * v.Pceil (nsMax v U L) + U * nsMax v U L < L * v.Pceil k + U * k := by
    rcases lt_or_ge (L * v.Pceil (nsMax v U L) + U * nsMax v U L) (L * v.Pceil k + U * k) with h | h
    · exact h
    · exact absurd (mem_nodeSideSet.2 ⟨hkm, fun i' hi' => le_trans h (nv_le_of_mem hmem hi')⟩)
        hknot
  exact chord_strict v.Pceil hi hk (nv_le_of_mem hmem (le_trans hi.le hle)) (le_of_lt hstr)
    (Or.inr hstr)

/-- three on-side abscissae are exactly collinear. -/
private theorem chord_eq (hL : 0 < L) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : i ∈ v.nodeSideSet U L) (hj : j ∈ v.nodeSideSet U L) (hk : k ∈ v.nodeSideSet U L) :
    (k - i) * v.Pceil j = (k - j) * v.Pceil i + (j - i) * v.Pceil k := by
  obtain ⟨e, he⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  have s1 : k - i = e + d := by omega
  have s2 : k - j = d := by omega
  have s3 : j - i = e := by omega
  rw [s1, s2, s3]
  have h1 : L * v.Pceil i + U * i = L * v.Pceil j + U * j :=
    le_antisymm (nv_le_of_mem hi (le_m_of_mem hj)) (nv_le_of_mem hj (le_m_of_mem hi))
  have h2 : L * v.Pceil j + U * j = L * v.Pceil k + U * k :=
    le_antisymm (nv_le_of_mem hj (le_m_of_mem hk)) (nv_le_of_mem hk (le_m_of_mem hj))
  have e1 : L * v.Pceil i = L * v.Pceil j + U * e := by
    have hUj : U * j = U * i + U * e := by rw [he]; ring
    omega
  have e2 : L * v.Pceil j = L * v.Pceil k + U * d := by
    have hUk : U * k = U * j + U * d := by rw [hd]; ring
    omega
  refine Nat.eq_of_mul_eq_mul_left hL ?_
  calc L * ((e + d) * v.Pceil j) = (e + d) * (L * v.Pceil j) := by ring
    _ = d * (L * v.Pceil j) + e * (L * v.Pceil j) := by ring
    _ = d * (L * v.Pceil j) + e * (L * v.Pceil k + U * d) := by rw [← e2]
    _ = d * (L * v.Pceil j + U * e) + e * (L * v.Pceil k) := by ring
    _ = d * (L * v.Pceil i) + e * (L * v.Pceil k) := by rw [← e1]
    _ = L * (d * v.Pceil i + e * v.Pceil k) := by ring

private theorem isVertex_eq_endpoint (hside : v.IsSide U L) {j : ℕ}
    (hj : j ∈ v.nodeSideSet U L) (hv : v.IsVertex j) :
    j = nsMin v U L ∨ j = nsMax v U L := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 : nsMin v U L < j := lt_of_le_of_ne (nsMin_le_of_mem hside hj) (Ne.symm hcon.1)
  have h2 : j < nsMax v U L := lt_of_le_of_ne (le_nsMax_of_mem hside hj) hcon.2
  have heq := chord_eq hside.1 h1.le h2.le (nsMin_mem hside) hj (nsMax_mem hside)
  have hlt := hv (nsMin v U L) (nsMax v U L) h1 h2 (le_m_of_mem (nsMax_mem hside))
  omega

end S5

namespace S6

open Uniformity.Density.Tower Scratch S2 S3 S4 S5

variable {v : HTNode} {U L U' L' : ℕ}

private theorem mem_both (hS' : v.IsSide U' L') {x : ℕ} (hL : 0 < L)
    (hx : x ∈ v.nodeSideSet U L) (hlo : nsMin v U' L' ≤ x) (hhi : x ≤ nsMax v U' L') :
    x ∈ v.nodeSideSet U' L' :=
  mem_of_onHull_between hS' hlo hhi (onHull_of_mem hL hx)

private theorem side_unique (hS : v.IsSide U L) (hS' : v.IsSide U' L') {j : ℕ}
    (h1 : nsMin v U L ≤ j) (h2 : j < nsMax v U L)
    (h1' : nsMin v U' L' ≤ j) (h2' : j < nsMax v U' L') : U = U' ∧ L = L' := by
  have hL := hS.1
  have hL' := hS'.1
  -- the overlap endpoints, in BOTH argmin sets
  obtain ⟨α, hαL, hαR, hαj⟩ : ∃ α, α ∈ v.nodeSideSet U L ∧ α ∈ v.nodeSideSet U' L' ∧ α ≤ j := by
    rcases le_total (nsMin v U' L') (nsMin v U L) with h | h
    · exact ⟨nsMin v U L, nsMin_mem hS, mem_both hS' hL (nsMin_mem hS) h (by omega), h1⟩
    · exact ⟨nsMin v U' L', mem_both hS hL' (nsMin_mem hS') h (by omega), nsMin_mem hS', h1'⟩
  obtain ⟨β, hβL, hβR, hβj⟩ : ∃ β, β ∈ v.nodeSideSet U L ∧ β ∈ v.nodeSideSet U' L' ∧ j < β := by
    rcases le_total (nsMax v U L) (nsMax v U' L') with h | h
    · exact ⟨nsMax v U L, nsMax_mem hS, mem_both hS' hL (nsMax_mem hS) (by omega) h, h2⟩
    · exact ⟨nsMax v U' L', mem_both hS hL' (nsMax_mem hS') (by omega) h, nsMax_mem hS', h2'⟩
  have hαβ : α < β := by omega
  obtain ⟨d, hd⟩ : ∃ d, β = α + d := ⟨β - α, by omega⟩
  have hd0 : 0 < d := by omega
  have hnv : L * v.Pceil α + U * α = L * v.Pceil β + U * β :=
    le_antisymm (nv_le_of_mem hαL (le_m_of_mem hβL)) (nv_le_of_mem hβL (le_m_of_mem hαL))
  have hnv' : L' * v.Pceil α + U' * α = L' * v.Pceil β + U' * β :=
    le_antisymm (nv_le_of_mem hαR (le_m_of_mem hβR)) (nv_le_of_mem hβR (le_m_of_mem hαR))
  have hPle : v.Pceil β ≤ v.Pceil α := by
    refine Nat.le_of_mul_le_mul_left ?_ hL
    have hU : U * β = U * α + U * d := by rw [hd]; ring
    omega
  obtain ⟨D, hD⟩ : ∃ D, v.Pceil α = v.Pceil β + D := ⟨v.Pceil α - v.Pceil β, by omega⟩
  have hUL : U * d = L * D := by
    have hU : U * β = U * α + U * d := by rw [hd]; ring
    have hP : L * v.Pceil α = L * v.Pceil β + L * D := by rw [hD]; ring
    omega
  have hUL' : U' * d = L' * D := by
    have hU : U' * β = U' * α + U' * d := by rw [hd]; ring
    have hP : L' * v.Pceil α = L' * v.Pceil β + L' * D := by rw [hD]; ring
    omega
  -- a reduced ratio determines the pair
  have hstep : ∀ x y : ℕ, 0 < y → Nat.Coprime x y → x * d = y * D →
      ∃ c, 0 < c ∧ d = y * c ∧ D = x * c := by
    intro x y hy hcop hxy
    have hdvd : y ∣ d := hcop.symm.dvd_of_dvd_mul_left ⟨D, hxy⟩
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · rw [Nat.mul_zero] at hc; omega
      · exact h
    refine ⟨c, hcpos, hc, ?_⟩
    refine Nat.eq_of_mul_eq_mul_left hy ?_
    rw [hc] at hxy
    calc y * D = x * (y * c) := hxy.symm
      _ = y * (x * c) := by ring
  obtain ⟨c, hc0, hdc, hDc⟩ := hstep U L hL hS.2.1 hUL
  obtain ⟨c', hc0', hdc', hDc'⟩ := hstep U' L' hL' hS'.2.1 hUL'
  have hgcd : c = c' := by
    have e1 : Nat.gcd d D = c := by
      rw [hdc, hDc, Nat.mul_comm L c, Nat.mul_comm U c, Nat.gcd_mul_left,
        Nat.Coprime.gcd_eq_one hS.2.1.symm, Nat.mul_one]
    have e2 : Nat.gcd d D = c' := by
      rw [hdc', hDc', Nat.mul_comm L' c', Nat.mul_comm U' c', Nat.gcd_mul_left,
        Nat.Coprime.gcd_eq_one hS'.2.1.symm, Nat.mul_one]
    omega
  subst hgcd
  constructor
  · exact Nat.eq_of_mul_eq_mul_right hc0 (by omega)
  · exact Nat.eq_of_mul_eq_mul_right hc0 (by omega)

private theorem exists_next (hwf : v.WF) (hS : v.IsSide U L) (hlt : nsMax v U L < v.m) :
    ∃ U' L' : ℕ, v.IsSide U' L' ∧ nsMin v U' L' = nsMax v U L ∧
      nsMax v U L < nsMax v U' L' := by
  obtain ⟨U', L', hS', hmem, hltmax⟩ :=
    exists_side hwf hlt (onHull_of_mem hS.1 (nsMax_mem hS))
  refine ⟨U', L', hS', ?_, hltmax⟩
  rcases isVertex_eq_endpoint hS' hmem (isVertex_nsMax hS) with h | h
  · exact h.symm
  · omega

end S6

namespace S7

open Uniformity Uniformity.Density.Tower Polynomial

theorem factors_mul_unit {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    {c a : α} (hc : IsUnit c) :
    UniqueFactorizationMonoid.factors (c * a) = UniqueFactorizationMonoid.factors a := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hca : c * a ≠ 0 := fun h => ha (hc.mul_right_eq_zero.1 h)
  have hassoc : Associated (c * a) a := (associated_unit_mul_left a c hc)
  have hpred : (fun f : Multiset α => (∀ b ∈ f, Prime b) ∧ Associated f.prod (c * a))
      = (fun f : Multiset α => (∀ b ∈ f, Prime b) ∧ Associated f.prod a) := by
    funext f
    exact propext ⟨fun h => ⟨h.1, h.2.trans hassoc⟩, fun h => ⟨h.1, h.2.trans hassoc.symm⟩⟩
  rw [UniqueFactorizationMonoid.factors, UniqueFactorizationMonoid.factors,
    dif_neg hca, dif_neg ha]
  congr 1

variable {K : Type*} [CommRing K] [IsDomain K] [Finite K]

theorem isUnit_ne_zero {c : K} (hc : c ≠ 0) : IsUnit c := by
  obtain ⟨d, hd⟩ := (Finite.isField_of_domain K).mul_inv_cancel hc
  exact ⟨⟨c, d, hd, by rw [mul_comm]; exact hd⟩, rfl⟩

variable [UniqueFactorizationMonoid K]

theorem residualTypeOf_C_mul {c : K} (hc : c ≠ 0) (p : Polynomial K) :
    residualTypeOf (Polynomial.C c * p) = residualTypeOf p := by
  unfold residualTypeOf
  rw [factors_mul_unit (Polynomial.isUnit_C.2 (isUnit_ne_zero hc))]

theorem residualTypeOf_degree {p : Polynomial K} (hp : p ≠ 0) :
    (residualTypeOf p).degree = p.natDegree := by
  classical
  have h1 : (UniqueFactorizationMonoid.factors p).prod.natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.factors_prod hp))
  have hzero : (0 : Polynomial K) ∉ UniqueFactorizationMonoid.factors p := by
    intro h
    exact (UniqueFactorizationMonoid.irreducible_of_factor _ h).ne_zero rfl
  have h2 : ((UniqueFactorizationMonoid.factors p).map Polynomial.natDegree).sum
      = (UniqueFactorizationMonoid.factors p).prod.natDegree :=
    (Polynomial.natDegree_multiset_prod _ hzero).symm
  have h3 := Finset.sum_multiset_map_count (UniqueFactorizationMonoid.factors p)
      (fun q : Polynomial K => q.natDegree)
  show (((UniqueFactorizationMonoid.factors p).toFinset.val.map
      (fun q : Polynomial K => (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))).map
      (fun x : ℕ × ℕ => x.1 * x.2)).sum = p.natDegree
  rw [Multiset.map_map]
  have hcongr : ∀ q ∈ (UniqueFactorizationMonoid.factors p).toFinset,
      ((fun x : ℕ × ℕ => x.1 * x.2) ∘ (fun q : Polynomial K =>
        (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))) q
        = (UniqueFactorizationMonoid.factors p).count q • q.natDegree := by
    intro q _
    show q.natDegree * (UniqueFactorizationMonoid.factors p).count q
      = (UniqueFactorizationMonoid.factors p).count q • q.natDegree
    rw [smul_eq_mul, Nat.mul_comm]
  have key : ∑ q ∈ (UniqueFactorizationMonoid.factors p).toFinset,
      ((fun x : ℕ × ℕ => x.1 * x.2) ∘ (fun q : Polynomial K =>
        (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))) q = p.natDegree := by
    rw [Finset.sum_congr rfl hcongr, ← h3, h2, h1]
  exact key


end S7

namespace S8

open Uniformity Uniformity.Density.Tower Scratch S2 S3 S4 S5 S6 S7 Polynomial

variable {K : Type*} [CommRing K] [IsDomain K] [UniqueFactorizationMonoid K] [Finite K]

/-- the residual polynomial the sweep reads off an assignment at a side. -/
noncomputable def resOf (v : HTNode) (r : ℕ → K) (U L : ℕ) : Polynomial K :=
  ∑ k ∈ Finset.range (v.nodeSideDeg U L + 1),
    Polynomial.C (r (nsMin v U L + L * k)) * Polynomial.X ^ k

theorem resOf_coeff (v : HTNode) (r : ℕ → K) (U L t : ℕ) :
    (resOf v r U L).coeff t =
      if t ≤ v.nodeSideDeg U L then r (nsMin v U L + L * t) else 0 := by
  classical
  rw [resOf, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : t ≤ v.nodeSideDeg U L
  · rw [if_pos h, Finset.sum_eq_single t]
    · simp
    · intro b _ hb
      exact if_neg fun hc => hb hc.symm
    · intro hmem
      exact absurd (Finset.mem_range.2 (by omega)) hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => if_neg ?_
    intro hc
    rw [Finset.mem_range] at hb
    omega

theorem natDegree_resOf_le (v : HTNode) (r : ℕ → K) (U L : ℕ) :
    (resOf v r U L).natDegree ≤ v.nodeSideDeg U L := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun n hn => ?_
  rw [resOf_coeff]
  exact if_neg (by exact_mod_cast Nat.not_le.2 (by exact_mod_cast hn))

/-- the sweep's five clauses on an assignment. -/
def SweepCond (v : HTNode) (r : ℕ → K) : Prop :=
  (∀ j, r j ≠ 0 → j ≤ v.m) ∧
  (∀ j, j < v.m → ¬ v.OnHull j → r j = 0) ∧
  r v.m = 1 ∧
  (∀ j, j ≤ v.m → v.IsVertex j → r j ≠ 0) ∧
  (∀ U L : ℕ, (U, L) ∈ v.sides → residualTypeOf (resOf v r U L) = v.sideType U L)

theorem isSide_of_mem {v : HTNode} (hwf : v.WF) {U L : ℕ} (h : (U, L) ∈ v.sides) :
    v.IsSide U L := (hwf.2.2.2.1 U L).1 h

variable {v : HTNode}

theorem nsMax_le_m {U L : ℕ} (hS : v.IsSide U L) : nsMax v U L ≤ v.m :=
  le_m_of_mem (nsMax_mem hS)

theorem resOf_coeff_top {r : ℕ → K} {U L : ℕ} (hS : v.IsSide U L) :
    (resOf v r U L).coeff (v.nodeSideDeg U L) = r (nsMax v U L) := by
  rw [resOf_coeff, if_pos (le_refl _), ← nsMax_eq_add hS.1 hS]

theorem resOf_coeff_zero {r : ℕ → K} {U L : ℕ} :
    (resOf v r U L).coeff 0 = r (nsMin v U L) := by
  rw [resOf_coeff, if_pos (Nat.zero_le _), Nat.mul_zero, Nat.add_zero]

theorem r_nsMin_ne {r : ℕ → K} (hr : SweepCond v r) {U L : ℕ} (hS : v.IsSide U L) :
    r (nsMin v U L) ≠ 0 :=
  hr.2.2.2.1 _ (le_m_of_mem (nsMin_mem hS)) (isVertex_nsMin hS)

theorem r_nsMax_ne {r : ℕ → K} (hr : SweepCond v r) {U L : ℕ} (hS : v.IsSide U L) :
    r (nsMax v U L) ≠ 0 :=
  hr.2.2.2.1 _ (nsMax_le_m hS) (isVertex_nsMax hS)

theorem inv_ne_zero' {c : K} (hc : c ≠ 0) : Ring.inverse c ≠ 0 := by
  intro h
  have h2 := Ring.inverse_mul_cancel c (isUnit_ne_zero hc)
  rw [h, zero_mul] at h2
  exact zero_ne_one h2

/-- the monic normalization of the residual read at a side. -/
noncomputable def psiFun (v : HTNode) (r : ℕ → K) (U L : ℕ) : Polynomial K :=
  Polynomial.C (Ring.inverse (r (nsMax v U L))) * resOf v r U L

theorem psiFun_coeff (v : HTNode) (r : ℕ → K) (U L t : ℕ) :
    (psiFun v r U L).coeff t = Ring.inverse (r (nsMax v U L)) * (resOf v r U L).coeff t := by
  rw [psiFun, Polynomial.coeff_C_mul]

theorem psiFun_monic {r : ℕ → K} (hr : SweepCond v r) {U L : ℕ} (hS : v.IsSide U L) :
    (psiFun v r U L).Monic := by
  refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one (v.nodeSideDeg U L) ?_ ?_
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    simpa using natDegree_resOf_le v r U L
  · rw [psiFun_coeff, resOf_coeff_top hS]
    exact Ring.inverse_mul_cancel _ (isUnit_ne_zero (r_nsMax_ne hr hS))

theorem psiFun_coeff_zero_ne {r : ℕ → K} (hr : SweepCond v r) {U L : ℕ} (hS : v.IsSide U L) :
    (psiFun v r U L).coeff 0 ≠ 0 := by
  rw [psiFun_coeff, resOf_coeff_zero]
  exact mul_ne_zero (inv_ne_zero' (r_nsMax_ne hr hS)) (r_nsMin_ne hr hS)

theorem psiFun_type {r : ℕ → K} (hr : SweepCond v r) {U L : ℕ} (hmem : (U, L) ∈ v.sides)
    (hS : v.IsSide U L) : residualTypeOf (psiFun v r U L) = v.sideType U L := by
  rw [psiFun, residualTypeOf_C_mul (inv_ne_zero' (r_nsMax_ne hr hS))]
  exact hr.2.2.2.2 U L hmem

theorem onHull_of_isVertex {j : ℕ} (h : v.IsVertex j) : v.OnHull j := by
  intro i k hij hjk hkm
  rcases eq_or_lt_of_le hij with rfl | hij'
  · have : i - i = 0 := by omega
    rw [this, Nat.zero_mul, Nat.add_zero]
  · rcases eq_or_lt_of_le hjk with rfl | hjk'
    · have : j - j = 0 := by omega
      rw [this, Nat.zero_mul, Nat.zero_add]
    · exact le_of_lt (h i k hij' hjk' hkm)

/-! ### the backward map -/

variable (v)

/-- the product of the constant terms of the sides lying weakly to the right of `c`. -/
noncomputable def tailU (q : {x // x ∈ v.sides} → Polynomial K) (c : ℕ) : K :=
  ∏ p ∈ v.sides.attach.filter (fun p => c ≤ nsMin v p.1.1 p.1.2), (q p).coeff 0

/-- the assignment rebuilt from a tuple of monic residuals (the right-to-left sweep, in
closed form: no recursion, the unit at a position is the product of the constant terms of
the sides to its right). -/
noncomputable def gFun (q : {x // x ∈ v.sides} → Polynomial K) (j : ℕ) : K :=
  (∑ p ∈ v.sides.attach,
      if nsMin v p.1.1 p.1.2 ≤ j ∧ j < nsMax v p.1.1 p.1.2 ∧ p.1.2 ∣ (j - nsMin v p.1.1 p.1.2)
      then tailU v q (nsMax v p.1.1 p.1.2) * (q p).coeff ((j - nsMin v p.1.1 p.1.2) / p.1.2)
      else 0)
    + (if j = v.m then 1 else 0)

variable {v}

theorem tailU_ne_zero {q : {x // x ∈ v.sides} → Polynomial K}
    (hq : ∀ p, (q p).coeff 0 ≠ 0) (c : ℕ) : tailU v q c ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun p _ => hq p

theorem gFun_eq_of_side (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K} {U L : ℕ}
    (hmem : (U, L) ∈ v.sides) {j : ℕ} (h1 : nsMin v U L ≤ j) (h2 : j < nsMax v U L)
    (hdvd : L ∣ (j - nsMin v U L)) :
    gFun v q j = tailU v q (nsMax v U L) * (q ⟨(U, L), hmem⟩).coeff ((j - nsMin v U L) / L) := by
  classical
  have hjm : j ≠ v.m := by
    have := nsMax_le_m (isSide_of_mem hwf hmem); omega
  rw [gFun, if_neg hjm, Nat.add_zero,
    Finset.sum_eq_single (⟨(U, L), hmem⟩ : {x // x ∈ v.sides})]
  · rw [if_pos ⟨h1, h2, hdvd⟩]
  · intro p _ hne
    refine if_neg fun hc => hne ?_
    obtain ⟨hu, hl⟩ := side_unique (isSide_of_mem hwf p.2) (isSide_of_mem hwf hmem)
      hc.1 hc.2.1 h1 h2
    exact Subtype.ext (Prod.ext hu hl)
  · intro hmem'
    exact absurd (Finset.mem_attach _ _) hmem'

theorem gFun_eq_zero_of_no_side (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K} {j : ℕ}
    (hj : ∀ U L : ℕ, (U, L) ∈ v.sides →
      ¬(nsMin v U L ≤ j ∧ j < nsMax v U L ∧ L ∣ (j - nsMin v U L)))
    (hjm : j ≠ v.m) : gFun v q j = 0 := by
  classical
  rw [gFun, if_neg hjm, Nat.add_zero]
  refine Finset.sum_eq_zero fun p _ => ?_
  refine if_neg ?_
  intro hc
  exact hj p.1.1 p.1.2 p.2 hc

theorem gFun_m (hwf : v.WF) (q : {x // x ∈ v.sides} → Polynomial K) : gFun v q v.m = 1 := by
  classical
  rw [gFun, if_pos rfl]
  have : (∑ p ∈ v.sides.attach,
      if nsMin v p.1.1 p.1.2 ≤ v.m ∧ v.m < nsMax v p.1.1 p.1.2 ∧
          p.1.2 ∣ (v.m - nsMin v p.1.1 p.1.2)
      then tailU v q (nsMax v p.1.1 p.1.2) * (q p).coeff ((v.m - nsMin v p.1.1 p.1.2) / p.1.2)
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun p _ => if_neg ?_
    intro hc
    exact absurd hc.2.1 (not_lt.2 (nsMax_le_m (isSide_of_mem hwf p.2)))
  rw [this, Nat.zero_add]

theorem tailU_m (hwf : v.WF) (q : {x // x ∈ v.sides} → Polynomial K) : tailU v q v.m = 1 := by
  classical
  rw [tailU, Finset.filter_eq_empty_iff.2, Finset.prod_empty]
  intro p _
  have h1 := nsMin_lt_nsMax (isSide_of_mem hwf p.2)
  have h2 := nsMax_le_m (isSide_of_mem hwf p.2)
  omega

theorem tailU_step (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K} {U L : ℕ}
    (hmem : (U, L) ∈ v.sides) :
    tailU v q (nsMin v U L) = (q ⟨(U, L), hmem⟩).coeff 0 * tailU v q (nsMax v U L) := by
  classical
  have hS := isSide_of_mem hwf hmem
  have hlt := nsMin_lt_nsMax hS
  have hset : v.sides.attach.filter (fun p => nsMin v U L ≤ nsMin v p.1.1 p.1.2)
      = insert (⟨(U, L), hmem⟩ : {x // x ∈ v.sides})
        (v.sides.attach.filter (fun p => nsMax v U L ≤ nsMin v p.1.1 p.1.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_attach, true_and]
    constructor
    · intro hp
      by_cases hpe : p = (⟨(U, L), hmem⟩ : {x // x ∈ v.sides})
      · exact Or.inl hpe
      · refine Or.inr ?_
        by_contra hcon
        push_neg at hcon
        obtain ⟨hu, hl⟩ := side_unique (isSide_of_mem hwf p.2) hS
          (le_refl _) (nsMin_lt_nsMax (isSide_of_mem hwf p.2)) hp hcon
        exact hpe (Subtype.ext (Prod.ext hu hl))
    · rintro (rfl | hp)
      · exact le_refl _
      · omega
  have hnot : (⟨(U, L), hmem⟩ : {x // x ∈ v.sides})
      ∉ v.sides.attach.filter (fun p => nsMax v U L ≤ nsMin v p.1.1 p.1.2) := by
    simp only [Finset.mem_filter, Finset.mem_attach, true_and]
    omega
  rw [tailU, tailU, hset, Finset.prod_insert hnot]

theorem mul_lt_mul_pos {L t g : ℕ} (hL : 0 < L) (h : t < g) : L * t < L * g := by
  have h2 : L * (t + 1) ≤ L * g := Nat.mul_le_mul (le_refl L) h
  rw [Nat.mul_add, Nat.mul_one] at h2
  omega

theorem gFun_nsMax (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K}
    (hq0 : ∀ p, (q p).coeff 0 ≠ 0) {U L : ℕ} (hmem : (U, L) ∈ v.sides) :
    gFun v q (nsMax v U L) = tailU v q (nsMax v U L) := by
  have hS := isSide_of_mem hwf hmem
  rcases eq_or_lt_of_le (nsMax_le_m hS) with heq | hlt
  · rw [heq, gFun_m hwf, tailU_m hwf]
  · obtain ⟨U', L', hS', hmin', hlt'⟩ := exists_next hwf hS hlt
    have hmem' : (U', L') ∈ v.sides := (hwf.2.2.2.1 U' L').2 hS'
    have h1 : nsMin v U' L' ≤ nsMax v U L := le_of_eq hmin'
    have hdvd : L' ∣ (nsMax v U L - nsMin v U' L') := by rw [hmin', Nat.sub_self]; exact dvd_zero _
    have hz : (nsMax v U L - nsMin v U' L') / L' = 0 := by
      rw [hmin', Nat.sub_self, Nat.zero_div]
    rw [gFun_eq_of_side hwf hmem' h1 hlt' hdvd, hz, mul_comm, ← tailU_step hwf hmem', hmin']

theorem natDegree_of_type (hwf : v.WF) {y : Polynomial K} {U L : ℕ} (hmem : (U, L) ∈ v.sides)
    (hy : y.Monic) (hty : residualTypeOf y = v.sideType U L) :
    y.natDegree = v.nodeSideDeg U L := by
  have h1 := residualTypeOf_degree (p := y) hy.ne_zero
  rw [hty] at h1
  rw [← h1]
  exact hwf.2.2.2.2 U L hmem

theorem resOf_gFun (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K}
    (hqm : ∀ p, (q p).Monic) (hq0 : ∀ p, (q p).coeff 0 ≠ 0)
    (hqt : ∀ p, residualTypeOf (q p) = v.sideType p.1.1 p.1.2) {U L : ℕ}
    (hmem : (U, L) ∈ v.sides) :
    resOf v (gFun v q) U L
      = Polynomial.C (tailU v q (nsMax v U L)) * (q ⟨(U, L), hmem⟩) := by
  have hS := isSide_of_mem hwf hmem
  have hdeg : (q ⟨(U, L), hmem⟩).natDegree = v.nodeSideDeg U L :=
    natDegree_of_type hwf hmem (hqm _) (hqt _)
  ext t
  rw [resOf_coeff, Polynomial.coeff_C_mul]
  by_cases ht : t ≤ v.nodeSideDeg U L
  · rw [if_pos ht]
    rcases eq_or_lt_of_le ht with rfl | htlt
    · rw [← nsMax_eq_add hS.1 hS, gFun_nsMax hwf hq0 hmem, ← hdeg,
        (hqm ⟨(U, L), hmem⟩).coeff_natDegree, mul_one]
    · have h1 : nsMin v U L ≤ nsMin v U L + L * t := Nat.le_add_right _ _
      have h2 : nsMin v U L + L * t < nsMax v U L := by
        rw [nsMax_eq_add hS.1 hS]
        exact Nat.add_lt_add_left (mul_lt_mul_pos hS.1 htlt) _
      have hd : L ∣ (nsMin v U L + L * t - nsMin v U L) := by
        rw [Nat.add_sub_cancel_left]; exact Dvd.intro t rfl
      rw [gFun_eq_of_side hwf hmem h1 h2 hd, Nat.add_sub_cancel_left,
        Nat.mul_div_cancel_left t hS.1]
  · rw [if_neg ht, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

theorem sweepCond_gFun (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K}
    (hqm : ∀ p, (q p).Monic) (hq0 : ∀ p, (q p).coeff 0 ≠ 0)
    (hqt : ∀ p, residualTypeOf (q p) = v.sideType p.1.1 p.1.2) : SweepCond v (gFun v q) := by
  refine ⟨?_, ?_, gFun_m hwf q, ?_, ?_⟩
  · intro j hj
    by_contra hcon
    refine hj (gFun_eq_zero_of_no_side hwf ?_ (by omega))
    intro U L hmem hc
    have := nsMax_le_m (isSide_of_mem hwf hmem)
    omega
  · intro j hjm hoh
    refine gFun_eq_zero_of_no_side hwf ?_ (by omega)
    intro U L hmem hc
    refine hoh ?_
    have hS := isSide_of_mem hwf hmem
    obtain ⟨t, ht⟩ := hc.2.2
    have hjeq : j = nsMin v U L + L * t := by
      have := hc.1; omega
    have htg : t ≤ v.nodeSideDeg U L := by
      by_contra hcon2
      have hmm := nsMax_eq_add hS.1 hS
      have := mul_lt_mul_pos hS.1 (show v.nodeSideDeg U L < t by omega)
      have := hc.2.1
      omega
    rw [hjeq]
    exact onHull_of_mem hS.1 (mem_lattice hS.1 hwf hS htg)
  · intro j hjm hv
    rcases eq_or_lt_of_le hjm with heq | hlt
    · rw [← heq] at *
      rw [gFun_m hwf]
      exact one_ne_zero
    · obtain ⟨U, L, hS, hmemset, hltmax⟩ := exists_side hwf hlt (onHull_of_isVertex hv)
      have hmem : (U, L) ∈ v.sides := (hwf.2.2.2.1 U L).2 hS
      have hj0 : j = nsMin v U L := by
        rcases isVertex_eq_endpoint hS hmemset hv with h | h
        · exact h
        · omega
      have h1 : nsMin v U L ≤ j := le_of_eq hj0.symm
      have hdvd : L ∣ (j - nsMin v U L) := by rw [hj0, Nat.sub_self]; exact dvd_zero _
      have hz : (j - nsMin v U L) / L = 0 := by rw [hj0, Nat.sub_self, Nat.zero_div]
      rw [gFun_eq_of_side hwf hmem h1 hltmax hdvd, hz]
      exact mul_ne_zero (tailU_ne_zero hq0 _) (hq0 _)
  · intro U L hmem
    rw [resOf_gFun hwf hqm hq0 hqt hmem, residualTypeOf_C_mul (tailU_ne_zero hq0 _)]
    exact hqt ⟨(U, L), hmem⟩

theorem psiFun_gFun (hwf : v.WF) {q : {x // x ∈ v.sides} → Polynomial K}
    (hqm : ∀ p, (q p).Monic) (hq0 : ∀ p, (q p).coeff 0 ≠ 0)
    (hqt : ∀ p, residualTypeOf (q p) = v.sideType p.1.1 p.1.2) {U L : ℕ}
    (hmem : (U, L) ∈ v.sides) : psiFun v (gFun v q) U L = q ⟨(U, L), hmem⟩ := by
  rw [psiFun, resOf_gFun hwf hqm hq0 hqt hmem, gFun_nsMax hwf hq0 hmem, ← mul_assoc,
    ← Polynomial.C_mul, Ring.inverse_mul_cancel _ (isUnit_ne_zero (tailU_ne_zero hq0 _)),
    Polynomial.C_1, one_mul]

theorem sweep_inj (hwf : v.WF) {r r' : ℕ → K} (hr : SweepCond v r) (hr' : SweepCond v r')
    (h : ∀ U L : ℕ, (U, L) ∈ v.sides → psiFun v r U L = psiFun v r' U L) : r = r' := by
  have key : ∀ d j, v.m - j ≤ d → r j = r' j := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rcases eq_or_lt_of_le (show v.m ≤ j by omega) with heq | hgt
      · rw [← heq, hr.2.2.1, hr'.2.2.1]
      · have e1 : r j = 0 := by
          by_contra hc
          exact absurd (hr.1 j hc) (by omega)
        have e2 : r' j = 0 := by
          by_contra hc
          exact absurd (hr'.1 j hc) (by omega)
        rw [e1, e2]
    | succ d ih =>
      intro j hj
      by_cases hd : v.m - j ≤ d
      · exact ih j hd
      · have hjlt : j < v.m := by omega
        by_cases hoh : v.OnHull j
        · obtain ⟨U, L, hS, hmemset, hltmax⟩ := exists_side hwf hjlt hoh
          have hmem : (U, L) ∈ v.sides := (hwf.2.2.2.1 U L).2 hS
          have h1 : nsMin v U L ≤ j := nsMin_le_of_mem hS hmemset
          obtain ⟨t, ht⟩ := dvd_sub_nsMin hS.1 hS hmemset
          have hjeq : j = nsMin v U L + L * t := by omega
          have hmaxm := nsMax_le_m hS
          have htg : t ≤ v.nodeSideDeg U L := by
            by_contra hcon2
            have hmm := nsMax_eq_add hS.1 hS
            have := mul_lt_mul_pos hS.1 (show v.nodeSideDeg U L < t by omega)
            omega
          have hmax : r (nsMax v U L) = r' (nsMax v U L) := ih _ (by omega)
          have hco := congrArg (fun y : Polynomial K => Polynomial.coeff y t) (h U L hmem)
          simp only [psiFun_coeff, resOf_coeff, if_pos htg] at hco
          rw [hmax] at hco
          have hne : r' (nsMax v U L) ≠ 0 := r_nsMax_ne hr' hS
          have hcan := congrArg (fun x : K => r' (nsMax v U L) * x) hco
          simp only [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_ne_zero hne), one_mul] at hcan
          rw [hjeq]
          exact hcan
        · rw [hr.2.1 j hjlt hoh, hr'.2.1 j hjlt hoh]
  funext j
  exact key v.m j (by omega)

theorem sweep_card (hwf : v.WF) :
    Nat.card {r : ℕ → K // SweepCond v r}
      = ∏ p ∈ v.sides, sideCensus K (v.sideType p.1 p.2) := by
  classical
  have hbij : Function.Bijective (fun (r : {r : ℕ → K // SweepCond v r}) =>
      (fun p : {x // x ∈ v.sides} => (⟨psiFun v r.1 p.1.1 p.1.2,
        psiFun_monic r.2 (isSide_of_mem hwf p.2),
        psiFun_coeff_zero_ne r.2 (isSide_of_mem hwf p.2),
        psiFun_type r.2 p.2 (isSide_of_mem hwf p.2)⟩ :
        {y : Polynomial K // y.Monic ∧ y.coeff 0 ≠ 0 ∧
          residualTypeOf y = v.sideType p.1.1 p.1.2}))) := by
    constructor
    · intro r r' hrr
      refine Subtype.ext (sweep_inj hwf r.2 r'.2 fun U L hmem => ?_)
      exact congrArg Subtype.val (congrFun hrr ⟨(U, L), hmem⟩)
    · intro y
      refine ⟨⟨gFun v (fun p => (y p).1),
        sweepCond_gFun hwf (fun p => (y p).2.1) (fun p => (y p).2.2.1)
          (fun p => (y p).2.2.2)⟩, ?_⟩
      funext p
      refine Subtype.ext ?_
      exact psiFun_gFun hwf (fun p => (y p).2.1) (fun p => (y p).2.2.1)
        (fun p => (y p).2.2.2) p.2
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_pi,
    ← Finset.prod_coe_sort v.sides (fun p => sideCensus K (v.sideType p.1 p.2))]
  rfl

end S8
