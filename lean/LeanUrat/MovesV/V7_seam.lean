/-  MovesV unit V7-7 `seam_rekey_stmts` (ONE SHARED PACKAGE PARAMETER, REV 4
    Codex-10; Prop-TYPED REV 5, Codex-11) — the XRB re-key: `XHDFrame`,
    `gProdF`, and the four face-law Props (build NOW, MovesS-free).
    `xrbPackageOf` + the S-2 re-key are SEAM-PHASE deliverables gated on the
    MovesS wave-4 `XRBPackage` co-build (NOT BUILT — §8 boundary). -/
import LeanUrat.MovesV.V2_valA
import LeanUrat.MovesV.V3_entcount

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

/-- the [2b] DATA halves, bundled once (laws NOT included). -/
structure XHDFrame (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  E     : ∀ {α β} (m : S.Move α β), AffineE (S.dim m)
  ET    : ∀ {α v} (m : S.MoveT α v), AffineE (S.dimT m)
  dom   : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  Gc    : ∀ {α} (γ : Template n S α), Fin (dom γ).comps.length → Qq
  Gcell : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdom d c).comps.length), Qq
  GcellT : ∀ {v} (d : TermData n C v) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdomT d c).comps.length), Qq
  Gent  : ∀ (β₀ : S.Cell) (i : V.EntIx β₀), Qq

/-- the frame-keyed weight product (`gProdF (frameOf X) = gProd X.w`
definitionally). -/
noncomputable def gProdF {n : ℕ} {S : StepSys n} {C : CtsFamily n}
    {V : CtsMeasured n C S} (F : XHDFrame n S V) :
    ∀ {α} (γ : Template n S α), Hpt γ.D → ℚ → ℝ
  | _, .last m,  h, q₀ => (q₀ : ℝ) ^ (-((F.E m).eval h : ℤ))
  | _, .lastT m, h, q₀ => (q₀ : ℝ) ^ (-((F.ET m).eval h : ℤ))
  | _, .cons m γ, h, q₀ =>
      (q₀ : ℝ) ^ (-((F.E m).eval (Hpt.take h) : ℤ)) * gProdF F γ (Hpt.drop h) q₀

def XhdW_Stmt {n : ℕ} {S : StepSys n} {C : CtsFamily n}
    {V : CtsMeasured n C S} (F : XHDFrame n S V) : Prop :=
  (∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dim m))
     (a : S.Assign m x h), q₀ ∈ S.Pools → S.zc x →
     S.massOf m x h a = (q₀ : ℝ) ^ (-((F.E m).eval h : ℤ))) ∧
  (∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dimT m))
     (a : S.AssignT m x h), q₀ ∈ S.Pools → S.zc x →
     S.massOfT m x h a = (q₀ : ℝ) ^ (-((F.ET m).eval h : ℤ)))

def XhdU_Stmt {n : ℕ} (S : StepSys n) : Prop := Nonempty (XHDu n S)

def XhdD_Stmt {n : ℕ} {S : StepSys n} {C : CtsFamily n}
    {V : CtsMeasured n C S} (F : XHDFrame n S V) (TE : TmplEvents n S) : Prop :=
  (∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
     q₀ ∈ S.Pools → S.zc x → 0 < Tgam TE γ x h → (F.dom γ).Mem h) ∧
  (∀ {α} (γ : Template n S α) (h : Hpt γ.D), (F.dom γ).Mem h →
     ∀ {q₀}, q₀ ∈ S.Pools → ∀ x : S.Hist q₀ α, S.zc x →
     0 < Tgam TE γ x h) ∧
  Nonempty (XHDdC n S V) ∧ Nonempty (XHDdEnt n S V)

def XhdS_Stmt {n : ℕ} {S : StepSys n} {C : CtsFamily n}
    {V : CtsMeasured n C S} (F : XHDFrame n S V) : Prop :=
  ((∀ {α} (γ : Template n S α) (j : Fin (F.dom γ).comps.length),
      ∃ (b : ℕ) (as : Finset ℕ+), (F.Gc γ j).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   ∃ hOk : (∀ {α} (γ : Template n S α) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
      F.Gc γ j ∈ OKat q₀),
   (∀ {α} (γ : Template n S α) (j) (q₀) (hq : q₀ ∈ S.Pools),
      HasSum (fun h : {h // ((F.dom γ).comps.get j).Mem h} =>
          gProdF F γ h.1 q₀)
        ((evalAt q₀ ⟨F.Gc γ j, hOk γ j q₀ hq⟩ : ℚ) : ℝ))) ∧
  ((∀ (d : MoveData n C) (c) (j : Fin (V.cdom d c).comps.length),
      ∃ (b : ℕ) (as : Finset ℕ+), (F.Gcell d c j).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   (∃ hOk : (∀ d c j (q₀ : ℚ), q₀ ∈ S.Pools → F.Gcell d c j ∈ OKat q₀),
    ∀ d c j q₀ (hq : q₀ ∈ S.Pools),
      HasSum (fun h : {h // ((V.cdom d c).comps.get j).Mem h} =>
          (q₀ : ℝ) ^ (-((F.E (V.moveOf d)).eval h.1 : ℤ)))
        ((evalAt q₀ ⟨F.Gcell d c j, hOk d c j q₀ hq⟩ : ℚ) : ℝ)) ∧
   (∀ {v} (d : TermData n C v) (c) (j : Fin (V.cdomT d c).comps.length),
      ∃ (b : ℕ) (as : Finset ℕ+), (F.GcellT d c j).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   (∃ hOkT : (∀ {v} (d : TermData n C v) (c) (j) (q₀ : ℚ),
        q₀ ∈ S.Pools → F.GcellT d c j ∈ OKat q₀),
    ∀ {v} (d : TermData n C v) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
      HasSum (fun h : {h // ((V.cdomT d c).comps.get j).Mem h} =>
          (q₀ : ℝ) ^ (-((F.ET (V.moveOfT d)).eval h.1 : ℤ)))
        ((evalAt q₀ ⟨F.GcellT d c j, hOkT d c j q₀ hq⟩ : ℚ) : ℝ))) ∧
  ((∀ (β₀ : S.Cell) (i : V.EntIx β₀), ∃ (b : ℕ) (as : Finset ℕ+),
      (F.Gent β₀ i).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   ∃ hOk : (∀ β₀ i (q₀ : ℚ), q₀ ∈ V.Pools → F.Gent β₀ i ∈ OKat q₀),
   (∀ β₀ (i : V.EntIx β₀) q₀ (hq : q₀ ∈ V.Pools),
      HasSum (fun h : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
          (q₀ : ℝ) ^ (-((instA i.1.1 h.1 : ℕ) : ℤ)))
        ((evalAt q₀ ⟨F.Gent β₀ i, hOk β₀ i q₀ hq⟩ : ℚ) : ℝ)))

/-- the discharge direction: a full package's frame. -/
def frameOf {n : ℕ} {S : StepSys n} {TE : TmplEvents n S} {C : CtsFamily n}
    {V : CtsMeasured n C S} (X : XHD n S TE V) : XHDFrame n S V where
  E := X.w.E
  ET := X.w.ET
  dom := X.d.dom
  Gc := X.s.Gc
  Gcell := X.sC.Gcell
  GcellT := X.sC.GcellT
  Gent := X.sEnt.Gent

/-- (re-keying `Wsh17Package.cts_counts` — S-8's [1v] leg). -/
def cts_counts_stmt {n : ℕ} (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) : Prop :=
  ValA n C S V ∧ EntCount V

/-- the re-keyed Wsh17 package (REV 4: frozen three-field roster complete;
the [§C/HC-2]- and [3t]-owned legs are Prop PARAMETERS — SF-2 recorded). -/
structure Wsh17PackageV (c15V sibC : Prop) {n : ℕ} {S : StepSys n}
    {TE : TmplEvents n S} {C : CtsFamily n} {V : CtsMeasured n C S}
    (X : XHD n S TE V) : Prop where
  c15_volumes : c15V
  cts_counts  : cts_counts_stmt C S V
  sib_count   : sibC

end LeanUrat.MovesV
