/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/DictIII/Devid — DEVID's graded interface (BP_III §1.5)

E-phase transcription of `lean/blueprints/BP_III.md` §1.5.  This file currently
holds unit III-G15a: the `ValGr` structure (Gr/zero/add/mul/grade/inF + laws
inF_zero, grade_inF, g1, g2, mul_zero, dom — REV2 finding 7), the `KPaBlock`
def, and the `minDev` def — FIELDS ONLY, transcribed VERBATIM.  Source of
record: GD23 §1.3 (g1)(g2).

Forward dependency: `minDev`'s display consumes `devCoeff` (unit III-G1,
`devCoeff` def via `Polynomial.modByMonic`/`divByMonic`, not yet in the
corpus at transcription time); it is provided here per the III-G1 row's spec
so §1.5's displays compile.  When III-G1 lands in its own module this def is
the one to dedupe against.

Display adjustment (III-G15a): the §1.5 display declares `add mul : Gr → Gr → Gr`
on one field line; in the Lean-4.31 structure-`where` syntax pinned here that
parses as a single field `add` with a BINDER `mul` (exact downstream error:
"Type mismatch: add (inF A) (inF B) has type Gr → Gr but is expected to have
type Gr", with `mul` unknown).  The surviving spelling of the SAME two fields
is one line each (`add : Gr → Gr → Gr` / `mul : Gr → Gr → Gr`); the
propositions are unchanged.  Additionally `devCoeff`/`minDev` carry the
`noncomputable` modifier (forced by `Polynomial.modByMonic`; definition bodies
untouched).  No other token differs from the display.
-/

namespace LeanUrat.Scaffold.DictIII

open Polynomial

/-- Unit III-G1 (forward-provided dependency): the Φ-adic development
    coefficients, `devCoeff Φ B k` = the k-th coefficient `C_k` in
    `B = Σ_k C_k Φ^k` with `deg C_k < deg Φ`, via monic mod/div
    (`Polynomial.modByMonic`/`divByMonic`) — BP_III unit-table row III-G1,
    GD23 §3 DEV-g. -/
noncomputable def devCoeff {K : Type*} [CommRing K] (Φ : Polynomial K) :
    Polynomial K → ℕ → Polynomial K
  | B, 0 => B %ₘ Φ
  | B, k + 1 => devCoeff Φ (B /ₘ Φ) k

/-- The graded interface DEVID actually consumes: initial-form data for w with
    (g1) in(A)+… sum law at the min weight, (g2) in(AB) = in(A)·in(B), domain. An
    instance at order ≤ 1 is built from §1.4's explicit descriptions (unit III-G15b). -/
structure ValGr {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) where
  Gr : Type*
  zero : Gr
  add : Gr → Gr → Gr
  mul : Gr → Gr → Gr
  grade : Gr → WithTop ℤ
  inF : Polynomial K → Gr
  inF_zero : inF 0 = zero
  grade_inF : ∀ A, grade (inF A) = w A
  g1 : ∀ A B, w A = w B → inF (A + B) = add (inF A) (inF B)
  g2 : ∀ A B, inF (A * B) = mul (inF A) (inF B)
  mul_zero : ∀ a, mul a zero = zero ∧ mul zero a = zero
  dom : ∀ a b, mul a b = zero → a = zero ∨ b = zero

/-- Theorem DEVID (GD23 §4): under (V1) + (KPa)'s block, the Φ-development computes
    w from below: w(B) = min_k (w(C_k) + k·w(Φ)). -/
noncomputable def minDev {K : Type*} [CommRing K] (w : Polynomial K → WithTop ℤ)
    (Φ B : Polynomial K) : WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun k =>
    w (devCoeff Φ B k) + (k : ℕ) • w Φ

structure KPaBlock {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (G : ValGr w)
    (Φ : Polynomial K) : Prop where
  monic : Φ.Monic
  positiveDegree : 1 ≤ Φ.natDegree
  primeInitial : ∀ A B, G.mul (G.inF A) (G.inF B) = G.inF Φ →
    G.inF A = G.inF Φ ∨ G.inF B = G.inF Φ
  lowerDegree : ∀ B, B.natDegree < Φ.natDegree →
    B ≠ 0 → G.inF B ≠ G.inF Φ

end LeanUrat.Scaffold.DictIII
