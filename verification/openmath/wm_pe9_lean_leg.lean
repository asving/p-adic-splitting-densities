/- WELDMASTER PE9 — fresh-route leg: THE LEAN KERNEL (route unused by PE1–PE8).
   The note's integer cochain system as GENERAL ∀-theorems over ℤ — full
   generality (Int.ediv/emod, unbounded quantifiers), beyond interpolation and
   exhaustion. Conventions match the pinned `bez` / eq-12 / S0 weld cochain:
     s(β) := (ℓβ) % e   (0 ≤ s < e for e > 0),   t(β) := (ℓβ) / e = (ℓβ − s(β))/e.
   Verifier-written 2026-08-07; consumed by the PE9 report only. -/
import Mathlib

namespace WMPE9

/-- L1 (t-integrality + s-range): ℓβ = e·t(β) + s(β) with 0 ≤ s(β) < e.
    This is the note's "t_j(β) ∈ ℤ always (s(β) ≡ ℓβ mod e)" warrant. -/
theorem t_spec (l e beta : ℤ) (he : 0 < e) :
    l * beta = e * ((l * beta) / e) + (l * beta) % e
      ∧ 0 ≤ (l * beta) % e ∧ (l * beta) % e < e :=
  ⟨(Int.ediv_add_emod _ _).symm, Int.emod_nonneg _ (ne_of_gt he),
   Int.emod_lt_of_pos _ he⟩

/-- L2 (WM-COB(i), multiplied form — no division, so NO hypothesis at all):
    with β″ := β + β′ + S,
    s(β) + s(β′) − s(β″) + ℓS  =  e·( t(β″) − t(β) − t(β′) ).
    The left side is e·D_j ([ILN] S0.3 definition of D_j via the s-defect);
    the right side is e·(∂t)(γ,γ′). -/
theorem wm_cob_i_mul (l e beta beta' S : ℤ) :
    (l*beta % e) + (l*beta' % e) - (l*(beta+beta'+S) % e) + l*S
      = e * ((l*(beta+beta'+S))/e - (l*beta)/e - (l*beta')/e) := by
  have h1 := Int.ediv_add_emod (l*beta) e
  have h2 := Int.ediv_add_emod (l*beta') e
  have h3 := Int.ediv_add_emod (l*(beta+beta'+S)) e
  linear_combination h1 + h2 - h3

/-- L2′ (WM-COB(i), quotient form): D = ∂t exactly, every ℓ, β, β′, S ∈ ℤ, e ≠ 0. -/
theorem wm_cob_i (l e beta beta' S : ℤ) (he : e ≠ 0) :
    ((l*beta % e) + (l*beta' % e) - (l*(beta+beta'+S) % e) + l*S) / e
      = (l*(beta+beta'+S))/e - (l*beta)/e - (l*beta')/e := by
  rw [wm_cob_i_mul l e beta beta' S, Int.mul_ediv_cancel_left _ he]

/-- L3 (the key-lattice first difference — S3's seed identities + LAW-3 at
    exponent level, and WM-RHO's per-level increment): for W on the key
    lattice, W = e·c (e.g. c = g·γ giving A = ℓgγ, or c = E_{j−1} giving
    ℓE_{j−1}), the shift is CARRY-FREE:
    t(β + i·e·c) = t(β) + i·ℓ·c  and  s(β + i·e·c) = s(β). -/
theorem t_key_shift (l e beta i c : ℤ) (he : e ≠ 0) :
    (l*(beta + i*(e*c))) / e = (l*beta)/e + i*l*c
      ∧ (l*(beta + i*(e*c))) % e = (l*beta) % e := by
  have hexp : l*(beta + i*(e*c)) = l*beta + (i*l*c)*e := by ring
  constructor
  · rw [hexp, Int.add_mul_ediv_right _ _ he]
  · rw [hexp, Int.add_mul_emod_self_right]

/-- L4 (the pinned `bez` normalization is the + convention): if e ∣ (1 − ℓh)
    (the scan's ℓh ≡ 1 mod e) then ℓ′ := (1−ℓh)/e satisfies ℓh + ℓ′e = 1. -/
theorem bez_plus (l h e : ℤ) (hdvd : (1 - l*h) % e = 0) :
    l*h + ((1 - l*h)/e)*e = 1 := by
  have := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdvd)
  linarith

/-- L5 (the [r7] bracket's identity): under the + convention,
    ℓh − ℓ′e = 1 − 2ℓ′e. -/
theorem minus_eq (l l' h e : ℤ) (hbez : l*h + l'*e = 1) :
    l*h - l'*e = 1 - 2*(l'*e) := by linarith

/-- L6 (PE8 F-1 / the r7 falsification, GENERAL): under the + normalization
    with e ≥ 2, h ≥ 2, 0 ≤ ℓ < e, the minus-form value is ≥ 3 — hence the
    sealed "ℓ_j h_j − ℓ′_j e_j = ±1" is FALSE at EVERY read with e > 1, h > 1. -/
theorem minus_form_false (l l' h e : ℤ) (he : 2 ≤ e) (hh : 2 ≤ h)
    (hl0 : 0 ≤ l) (hle : l < e) (hbez : l*h + l'*e = 1) :
    3 ≤ l*h - l'*e := by
  have hl1 : 1 ≤ l := by
    by_contra hcon
    have hl : l = 0 := by omega
    rw [hl] at hbez
    simp only [zero_mul, zero_add] at hbez
    have hdvd : e ∣ 1 := ⟨l', by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have hlh : 2 ≤ l*h := by nlinarith
  linarith

/-- L6a (roster instance, read (3,2) — towers C2D/C3C/I4A/I4B):
    bez = (2, −1); plus-form 1, minus-form 7 ∉ {±1}. -/
theorem instance_32 : (2:ℤ)*2 + (-1)*3 = 1 ∧ (2:ℤ)*2 - (-1)*3 = 7 := by
  norm_num

/-- L6b (roster instance, read (2,3) — tower C3E):
    bez = (1, −1); plus-form 1, minus-form 5 ∉ {±1}. -/
theorem instance_23 : (1:ℤ)*3 + (-1)*2 = 1 ∧ (1:ℤ)*3 - (-1)*2 = 5 := by
  norm_num

/-- L7 (S0's "A_j = 0 ⟺ e_{j−1} = 1", general): with the + normalization,
    e ≥ 1, h ≥ 1, 0 ≤ ℓ < e, g ≥ 1, γ ≥ 1:  ℓgγ = 0 ↔ e = 1. -/
theorem A_zero_iff (l l' h e g gam : ℤ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (hl0 : 0 ≤ l) (hle : l < e) (hbez : l*h + l'*e = 1)
    (hg : 1 ≤ g) (hgam : 1 ≤ gam) :
    l*g*gam = 0 ↔ e = 1 := by
  constructor
  · intro hA
    by_contra hne
    have he2 : 2 ≤ e := by omega
    have hl1 : 1 ≤ l := by
      by_contra hcon
      have hl : l = 0 := by omega
      rw [hl] at hbez
      simp only [zero_mul, zero_add] at hbez
      have hdvd : e ∣ 1 := ⟨l', by linarith⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
    have hpos : 0 < l * g * gam :=
      mul_pos (mul_pos (by omega : (0:ℤ) < l) (by omega : (0:ℤ) < g))
        (by omega : (0:ℤ) < gam)
    linarith
  · intro he1
    have hl : l = 0 := by omega
    rw [hl]; ring

/-- L8 (the plain carry δ ∈ {0,1} — [ILN] S0.2's δ^pl line, LAW-2's face):
    0 ≤ s < e, 0 ≤ s′ < e ⟹ ⌊(s+s′)/e⌋ ∈ {0,1}. -/
theorem delta_01 (s s' e : ℤ) (he : 0 < e) (h1 : 0 ≤ s) (h2 : s < e)
    (h3 : 0 ≤ s') (h4 : s' < e) : (s+s')/e = 0 ∨ (s+s')/e = 1 := by
  rcases lt_or_ge (s+s') e with hlt | hge
  · left; exact Int.ediv_eq_zero_of_lt (by omega) hlt
  · right
    have hrw : s + s' = (s + s' - e) + 1*e := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ (ne_of_gt he),
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    norm_num

/-- L9 (the committed-eps exponent path ⟺ −t, under the + convention ONLY —
    the S5 WM-EPS gloss "the ℓ′s−ℓu exponent path" tied to EXP-KIT(a)):
    given eq-12 data β = sh + ue and ℓh + ℓ′e = 1:  e·(ℓ′s − ℓu) = s − ℓβ.
    (So z^{ℓ′s−ℓu} = z^{−t(β)} once s = (ℓβ) % e — the identity the minus-ℓ′
    would BREAK, which is why the S0 line's convention is load-bearing.) -/
theorem eps_exponent_tie (l l' h e s u beta : ℤ) (hbez : l*h + l'*e = 1)
    (heq : beta = s*h + u*e) : e*(l'*s - l*u) = s - l*beta := by
  have hsub : s - l*beta = s*(1 - l*h) - l*u*e := by rw [heq]; ring
  have h1le : 1 - l*h = l'*e := by linarith
  rw [hsub, h1le]; ring

end WMPE9

#print axioms WMPE9.t_spec
#print axioms WMPE9.wm_cob_i_mul
#print axioms WMPE9.wm_cob_i
#print axioms WMPE9.t_key_shift
#print axioms WMPE9.bez_plus
#print axioms WMPE9.minus_eq
#print axioms WMPE9.minus_form_false
#print axioms WMPE9.instance_32
#print axioms WMPE9.instance_23
#print axioms WMPE9.A_zero_iff
#print axioms WMPE9.delta_01
#print axioms WMPE9.eps_exponent_tie
