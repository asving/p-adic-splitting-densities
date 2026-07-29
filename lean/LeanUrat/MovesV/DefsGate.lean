/-
MovesV/DefsGate — the V.6 sealed data (concrete, decide-native) — §2.I.

Concrete data only (no laws): the root/s_blk2 rosters' closed-form polynomials,
the gate-B constants, the census q-list (ALL NINE, in-kernel — C20), the A2
chart/domain/weight (C3), the three prime-power fields F4/F8/F9 (explicit
tables; laws by decide), reduce2 + CoprimeLiftPack (V6-4c's typed premise).
E-PHASE DEVIATIONS (recorded in MANIFEST): the field tables use `![…]`
vec-notation (the blueprint's nested `List.get` display does not elaborate —
the inner length is not definitionally available after an abstract outer get);
the gate letters' OUTCOME-MEMBER ROSTERS (`omem` list literals) are deferred to
the V6/V2-9 unit files (they need concrete catalogue `Skeleton` members —
prose-specified, not displayed code).
-/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace LeanUrat.MovesV
open Polynomial

/-! ### The root roster (five letters, five closed forms) -/

noncomputable def TH3 : Polynomial ℚ := C (1/6 : ℚ) * (X * (X - 1) * (X - 2))
noncomputable def TH12 : Polynomial ℚ := C (1/2 : ℚ) * (X ^ 2 * (X - 1))
noncomputable def TH3c : Polynomial ℚ := C (1/3 : ℚ) * (X ^ 3 - X)
noncomputable def T21 : Polynomial ℚ := X * (X - 1)
noncomputable def T3 : Polynomial ℚ := X

/-! ### The s_blk2 roster -/

noncomputable def Tsplit : Polynomial ℚ := C (1/2 : ℚ) * ((X - 1) * (X - 2))
noncomputable def Tinert : Polynomial ℚ := C (1/2 : ℚ) * (X * (X - 1))
noncomputable def Tdbl : Polynomial ℚ := X - 1
noncomputable def Tw2 : Polynomial ℚ := X - 1
noncomputable def Tvv : Polynomial ℚ := (X - 1) ^ 2

/-! ### Gate-B constants (V.6.4) -/

def gateB_A : ℕ := 3
def gateB_Went : ℕ := 3
noncomputable def Ient : Polynomial ℚ := X * (X - 1)
def gateB_iota : ℚ := 1/4
def gateB_T : ℚ := 1
def gateB_g : ℚ := 1/8
def gateB_muhat : ℚ := 1/32
def gateB_shadow : ℕ := 2
def gateB_N0 : ℕ := 3

/-- the census q-list — ALL NINE prime-power points, in-kernel (C20). -/
def censusQ : List ℚ := [2, 3, 4, 5, 7, 8, 9, 11, 13]

/-! ### The A2 entry, note-faithfully reparameterized (C3) -/

/-- the (t,u) chart: chart (t,u) = (h₀, h₂) = (3t + 2u + 1, t). -/
def A2chart (h : Hpt 2) : Hpt 2 := ![3 * h 0 + 2 * h 1 + 1, h 0]

/-- the A2 height domain IN (t,u) COORDINATES: L((1,0); {(1,0),(0,1)}). -/
def A2dom : LinSet 2 := ⟨![1, 0], [![1, 0], ![0, 1]]⟩

/-- the A2 weight IN (t,u) COORDINATES: E = 6t + 3u + 1 (OUR derived chart
form — G-1 attribution; the note's (h₀,h₂) display is V6-2b's theorem). -/
def EA2 : AffineE 2 := ⟨1, ![6, 3], by decide⟩

noncomputable def TA2 : Polynomial ℚ := (X - 1) ^ 2

/-! ### The three prime-power fields (C20; tables displayed; provenance G-2) -/

def F4 : Type := Fin 4
instance : Fintype F4 := inferInstanceAs (Fintype (Fin 4))
instance : DecidableEq F4 := inferInstanceAs (DecidableEq (Fin 4))
def f4mul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => ![![0,0,0,0], ![0,1,2,3], ![0,2,3,1], ![0,3,1,2]] a b
def f4add : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]] a b
def f4inv : Fin 4 → Fin 4 := fun a => ![0,1,3,2] a

instance : Add F4 := ⟨f4add⟩
instance : Mul F4 := ⟨f4mul⟩
instance : Neg F4 := ⟨id⟩
instance : Inv F4 := ⟨f4inv⟩
instance : Zero F4 := ⟨(0 : Fin 4)⟩
instance : One F4 := ⟨(1 : Fin 4)⟩

/-- the field laws, each one `by decide` over the tables (the blueprint's
full-skeleton display realized through `Field.ofMinimalAxioms` — the pinned
Mathlib demands the smul/qsmul recursors otherwise; recorded deviation). -/
noncomputable instance : Field F4 :=
  Field.ofMinimalAxioms F4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨(0 : Fin 4), (1 : Fin 4), by decide⟩

def F8 : Type := Fin 8
instance : Fintype F8 := inferInstanceAs (Fintype (Fin 8))
instance : DecidableEq F8 := inferInstanceAs (DecidableEq (Fin 8))
def f8add : Fin 8 → Fin 8 → Fin 8 := fun a b =>
  ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6], ![2,3,0,1,6,7,4,5], ![3,2,1,0,7,6,5,4],
    ![4,5,6,7,0,1,2,3], ![5,4,7,6,1,0,3,2], ![6,7,4,5,2,3,0,1], ![7,6,5,4,3,2,1,0]] a b
def f8mul : Fin 8 → Fin 8 → Fin 8 := fun a b =>
  ![![0,0,0,0,0,0,0,0], ![0,1,2,3,4,5,6,7], ![0,2,4,6,3,1,7,5], ![0,3,6,5,7,4,1,2],
    ![0,4,3,7,6,2,5,1], ![0,5,1,4,2,7,3,6], ![0,6,7,1,5,3,2,4], ![0,7,5,2,1,6,4,3]] a b
def f8inv : Fin 8 → Fin 8 := fun a => ![0,1,5,6,7,2,3,4] a

instance : Add F8 := ⟨f8add⟩
instance : Mul F8 := ⟨f8mul⟩
instance : Neg F8 := ⟨id⟩
instance : Inv F8 := ⟨f8inv⟩
instance : Zero F8 := ⟨(0 : Fin 8)⟩
instance : One F8 := ⟨(1 : Fin 8)⟩

/-- the field laws, each one `by decide` over the tables (the blueprint's
full-skeleton display realized through `Field.ofMinimalAxioms` — the pinned
Mathlib demands the smul/qsmul recursors otherwise; recorded deviation). -/
noncomputable instance : Field F8 :=
  Field.ofMinimalAxioms F8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨(0 : Fin 8), (1 : Fin 8), by decide⟩

def F9 : Type := Fin 9
instance : Fintype F9 := inferInstanceAs (Fintype (Fin 9))
instance : DecidableEq F9 := inferInstanceAs (DecidableEq (Fin 9))
def f9add : Fin 9 → Fin 9 → Fin 9 := fun a b =>
  ![![0,1,2,3,4,5,6,7,8], ![1,2,0,4,5,3,7,8,6], ![2,0,1,5,3,4,8,6,7],
    ![3,4,5,6,7,8,0,1,2], ![4,5,3,7,8,6,1,2,0], ![5,3,4,8,6,7,2,0,1],
    ![6,7,8,0,1,2,3,4,5], ![7,8,6,1,2,0,4,5,3], ![8,6,7,2,0,1,5,3,4]] a b
def f9mul : Fin 9 → Fin 9 → Fin 9 := fun a b =>
  ![![0,0,0,0,0,0,0,0,0], ![0,1,2,3,4,5,6,7,8], ![0,2,1,6,8,7,3,5,4],
    ![0,3,6,2,5,8,1,4,7], ![0,4,8,5,6,1,7,2,3], ![0,5,7,8,1,3,4,6,2],
    ![0,6,3,1,7,4,2,8,5], ![0,7,5,4,2,6,8,3,1], ![0,8,4,7,3,2,5,1,6]] a b
def f9neg : Fin 9 → Fin 9 := fun a => ![0,2,1,6,8,7,3,5,4] a
def f9inv : Fin 9 → Fin 9 := fun a => ![0,1,2,6,5,4,3,8,7] a

instance : Add F9 := ⟨f9add⟩
instance : Mul F9 := ⟨f9mul⟩
instance : Neg F9 := ⟨f9neg⟩
instance : Inv F9 := ⟨f9inv⟩
instance : Zero F9 := ⟨(0 : Fin 9)⟩
instance : One F9 := ⟨(1 : Fin 9)⟩

/-- the field laws, each one `by decide` over the tables (the blueprint's
full-skeleton display realized through `Field.ofMinimalAxioms` — the pinned
Mathlib demands the smul/qsmul recursors otherwise; recorded deviation). -/
noncomputable instance : Field F9 :=
  Field.ofMinimalAxioms F9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨(0 : Fin 9), (1 : Fin 9), by decide⟩

/-! ### `CoprimeLiftPack` — CLOSED at REV 3 (Codex-18); V6-4c's typed premise -/

/-- reduction mod 2 of a mod-2^k polynomial (the one cast this pack uses). -/
noncomputable def reduce2 (k : ℕ) (hk : 1 ≤ k) :
    Polynomial (ZMod (2 ^ k)) →+* Polynomial (ZMod 2) :=
  Polynomial.mapRingHom
    (ZMod.castHom (dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hk)) (ZMod 2))

structure CoprimeLiftPack where
  hOf : ∀ (k : ℕ), Polynomial (ZMod (2 ^ k)) → Polynomial (ZMod (2 ^ k))
  lift_unique : ∀ (k : ℕ) (hk : 1 ≤ k) (f : Polynomial (ZMod (2 ^ k)))
    (hf : f.Monic) (ub hb : Polynomial (ZMod 2)) (hcop : IsCoprime ub hb)
    (hmh : hb.Monic) (hfac : reduce2 k hk f = ub * hb),
    ∃! uh : Polynomial (ZMod (2 ^ k)) × Polynomial (ZMod (2 ^ k)),
      uh.1 * uh.2 = f ∧ uh.2.Monic ∧
      reduce2 k hk uh.1 = ub ∧ reduce2 k hk uh.2 = hb
  hOf_spec : ∀ (k : ℕ) (hk : 1 ≤ k) (f : Polynomial (ZMod (2 ^ k)))
    (hf : f.Monic) (ub hb : Polynomial (ZMod 2)) (hcop : IsCoprime ub hb)
    (hmh : hb.Monic) (hfac : reduce2 k hk f = ub * hb),
    (∃ u, u * hOf k f = f) ∧ (hOf k f).Monic ∧ reduce2 k hk (hOf k f) = hb

end LeanUrat.MovesV
