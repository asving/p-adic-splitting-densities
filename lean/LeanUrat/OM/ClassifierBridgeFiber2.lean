/-
Scratch module (S3, FINISH): the fiber-bridge finish `classify_eq_selfloop_iff` + discharge + first
order-1 density theorem, over the RESPELLED `ClassifierBridgeFiber.Tselfloop`.
Namespace LeanUrat.OM.ClassifierBridgeFiber2.  Math-first, no sorry/axiom/native_decide.

This module BUILDS the finish of the single-side, all-μ=1 fiber characterization on top of the
LANDED pieces in `ClassifierBridgeFiber.lean`:

* STEP A  — backward Lemma A: `rootFace`/`rootSide` inversion off the emitted per-cell polygon.
* STEP B  — backward Lemma B: `SideAbove` + vertex-exactness off the two-vertex hull.
* STEP C  — `classify_eq_selfloop_iff` (forward = LANDED, backward assembled from A/B).
* STEP D  — the discharge analogues over the respelled `Tselfloop`
            (`stratumCount_selfloop_R`, `hnode_selfloop_over_Bclassify_R`).
* STEP E  — the first order-1 density theorem via `MontesAllOrders.montes_allorders_of_hnode`
            on the singleton menu `{Tselfloop n pr shape}`.

`Tselfloop` throughout means `ClassifierBridgeFiber.Tselfloop` (the RESPELLED shape carrying the
classifier's own per-cell polygon `toSideFace (mkSide pr)`).
-/
import LeanUrat.OM.ClassifierBridgeFiber
import LeanUrat.OM.ClassifierBridge
import LeanUrat.OM.MontesAllOrders
import LeanUrat.OM.Order0Alpha

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ClassifierBridgeFiber2

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.MontesAxiom (CountCell)

open scoped Classical

/-! ## STEP A — backward Lemma A (rootFace/rootSide inversion). -/

/-- Every cell of `M5.encodeCells T` carries the polygon slot `T.Nr` (the cells of `M5.cells T` are
built with `polygon := T.Nr`, and `encodeCells` copies that field). -/
theorem encodeCells_polygon (T : M5.OMType) :
    ∀ c ∈ M5.encodeCells T, c.polygon = T.Nr := by
  intro c hc
  rw [M5.encodeCells, List.mem_map] at hc
  obtain ⟨oc, hoc, rfl⟩ := hc
  -- oc ∈ M5.cells T, whose every cell carries `polygon := T.Nr`.
  show oc.polygon = T.Nr
  rw [M5.cells, List.mem_map] at hoc
  obtain ⟨ψ, _, rfl⟩ := hoc
  rfl

/-- `classify f`'s `.cells` payload is ALWAYS `M5.encodeCells (fRootCtx f)` (for `0 < N`): the
classifier dispatches `rootCtx → fRootCtx`, and the `classifyAux` output carries `encodeCells` of its
root context in the `cells` slot unconditionally. -/
theorem classify_cells {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    (B.classify p n N f).cells = M5.encodeCells (B.fRootCtx p N hN f) := by
  have hdisp : B.classify p n N f
      = B.classifyAux p N n n f (B.fRootCtx p N hN f) (B.clusterSize_fRootCtx p N hN f) :=
    Order0.classifyAux_congr_ctx p N n n f (dif_pos hN)
      (B.clusterSize_rootCtx p N f) (B.clusterSize_fRootCtx p N hN f)
  rw [hdisp, Order0.classifyAux_unfold]

/-- **Backward Lemma A (i)** — from `classify f = Tselfloop n pr shape` with `shape ≠ []`, read
`rootFace p N hN f = toSideFace (mkSide pr)` off the emitted head per-cell polygon.  `classify`'s
`.cells` are `encodeCells (fRootCtx)`, all carrying polygon `fRootCtx.Nr = rootFace`; the respelled
`Tselfloop`'s cells all carry polygon `toSideFace (mkSide pr)`; equal (nonempty) lists have equal
heads. -/
theorem rootFace_eq_toSideFace_of_classify {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hcl : B.classify p n N f = ClassifierBridgeFiber.Tselfloop n pr shape)
    (hne : shape ≠ []) :
    B.rootFace p N hN f = M7.toSideFace (mkSide pr) := by
  -- take `.cells` of both sides
  have hcells : M5.encodeCells (B.fRootCtx p N hN f)
      = (ClassifierBridgeFiber.Tselfloop n pr shape).cells := by
    rw [← classify_cells hN f, hcl]
  -- Tselfloop's cells = shape.map (fun q => ⟨q.1,1,toSideFace(mkSide pr),[]⟩)
  have hTcells : (ClassifierBridgeFiber.Tselfloop n pr shape).cells
      = shape.map (fun q => (⟨q.1, 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell)) := rfl
  -- the head of the RHS list has polygon toSideFace(mkSide pr)
  cases shape with
  | nil => exact absurd rfl hne
  | cons a t =>
      -- the head cell of encodeCells has polygon fRootCtx.Nr = rootFace
      have hheadmem : (⟨a.1, 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell)
          ∈ M5.encodeCells (B.fRootCtx p N hN f) := by
        rw [hcells, hTcells]; simp
      have hpoly := encodeCells_polygon (B.fRootCtx p N hN f) _ hheadmem
      -- hpoly : (⟨a.1,1,toSideFace(mkSide pr),[]⟩).polygon = fRootCtx.Nr
      have hNr : (B.fRootCtx p N hN f).Nr = B.rootFace p N hN f := rfl
      -- so toSideFace(mkSide pr) = rootFace
      rw [hNr] at hpoly
      exact hpoly.symm

/-- **`toSideFace` column-0 inversion.**  If two side faces are equal and the left side has positive
width, their left heights `v₀` agree (`sideCeilHeight _ 0 = v₀`). -/
theorem toSideFace_v0_eq {S S' : NewtonPolygon.Side} (h : M7.toSideFace S = M7.toSideFace S')
    (hw : 0 < S.length) : S.v₀ = S'.v₀ := by
  have hwidth : S.length = S'.length := congrArg L4.LatticePolygon.width h
  have hch : HEq (fun k : Fin S.length => M7.sideCeilHeight S k.val)
      (fun k : Fin S'.length => M7.sideCeilHeight S' k.val) := by
    have : HEq (M7.toSideFace S).ceilHeights (M7.toSideFace S').ceilHeights := by rw [h]
    exact this
  rw [Fin.heq_fun_iff hwidth] at hch
  have h0 := hch ⟨0, hw⟩
  rw [M7.sideCeilHeight_zero, M7.sideCeilHeight_zero] at h0
  exact h0

/-- **`toSideFace` width inversion.** Equal side faces have equal widths (`= length`). -/
theorem toSideFace_length_eq {S S' : NewtonPolygon.Side} (h : M7.toSideFace S = M7.toSideFace S') :
    S.length = S'.length := congrArg L4.LatticePolygon.width h

/-- **Backward Lemma A (ii), self-loop.**  From `classify f = Tselfloop n ((0,H),(n,0)) shape` with
`shape ≠ []` and `0 < n`, recover `rootSide p N hN f = some (mkSide ((0,H),(n,0)))`.

Route: Lemma A (i) gives `rootFace = toSideFace (mkSide ((0,H),(n,0)))` (width `n > 0`, left height
`H`).  `rootSide` cannot be `none` (that gives a width-`0` face).  For `rootSide = some S`,
`rootFace = toSideFace S`, so `S.length = n` and `S.v₀ = H`.  `S` is the FIRST Newton side, whose
endpoints `(S.i₀,S.v₀)`,`(S.j₀,S.v₁)` are consecutive `npVertices` (support dots, abscissae `≤ n`,
strictly increasing).  Width `S.j₀ − S.i₀ = n` with `S.j₀ ≤ n` forces `S.i₀ = 0`, `S.j₀ = n`; the
right endpoint `(n, S.v₁)` is on the hull with `(n,0)` a support dot, so `npHeight n ≤ 0` and the ℕ
height `S.v₁ = 0`.  Hence `S = ⟨0,n,H,0⟩ = mkSide ((0,H),(n,0))`. -/
theorem rootSide_eq_of_classify {p : ℕ} [Fact p.Prime] {n N H : ℕ} (hn0 : 0 < n) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (shape : List (ℕ × ℕ))
    (hcl : B.classify p n N f = ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)
    (hne : shape ≠ []) :
    B.rootSide p N hN f = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
  set S := B.boxValSupport p N f with hSdef
  set hS := B.boxValSupport_nonempty p N hN f with hShyp
  -- Lemma A (i): rootFace = toSideFace (mkSide ((0,H),(n,0)))
  have hface : B.rootFace p N hN f
      = M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :=
    rootFace_eq_toSideFace_of_classify hN f _ shape hcl hne
  -- the target face has width n and v₀ = H
  have hRHSwidth : (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).length = n := by
    show n - 0 = n; omega
  -- case on rootSide
  rw [B.rootFace] at hface
  cases hrs : B.rootSide p N hN f with
  | none =>
      -- rootFace = empty ⟨0,…⟩, but width n > 0
      rw [hrs] at hface
      -- hface : ⟨0,fun _ => 0,fun _ => false⟩ = toSideFace (mkSide …)
      have hw : (0 : ℕ) = (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).length :=
        congrArg L4.LatticePolygon.width hface
      -- hw : 0 = (mkSide …).length = n
      rw [hRHSwidth] at hw
      omega
  | some Sm =>
      rw [hrs] at hface
      -- hface : toSideFace Sm = toSideFace (mkSide ((0,H),(n,0)))
      -- length: Sm.length = n
      have hlen : Sm.length = n := by
        have := toSideFace_length_eq hface
        rw [hRHSwidth] at this; exact this
      have hlenpos : 0 < Sm.length := by rw [hlen]; exact hn0
      -- v₀: Sm.v₀ = H
      have hv0S : Sm.v₀ = H := by
        have := toSideFace_v0_eq hface hlenpos
        show Sm.v₀ = H
        rw [this]; rfl
      -- Sm is the first Newton side; unfold npSides.head? = some Sm
      rw [B.rootSide] at hrs
      -- extract npVertices = (i₀,v₀) :: (j₀,v₁) :: rest with Sm = ⟨i₀,j₀,v₀,v₁⟩
      have hverts : ∃ v1 rest, NewtonPolygon.npVertices S hS
          = (Sm.i₀, Sm.v₀) :: (Sm.j₀, v1) :: rest ∧ Sm.v₁ = v1 := by
        unfold NewtonPolygon.npSides at hrs
        cases hv : NewtonPolygon.npVertices S hS with
        | nil => rw [hv] at hrs; simp at hrs
        | cons a t =>
            cases t with
            | nil => rw [hv] at hrs; simp at hrs
            | cons b rest =>
                rw [hv] at hrs
                simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.head?_cons,
                  Option.some.injEq] at hrs
                -- hrs : ⟨a.1,b.1,a.2,b.2⟩ = Sm
                have hi : a.1 = Sm.i₀ := congrArg NewtonPolygon.Side.i₀ hrs
                have hj : b.1 = Sm.j₀ := congrArg NewtonPolygon.Side.j₀ hrs
                have hvv0 : a.2 = Sm.v₀ := congrArg NewtonPolygon.Side.v₀ hrs
                have hvv1 : b.2 = Sm.v₁ := congrArg NewtonPolygon.Side.v₁ hrs
                refine ⟨b.2, rest, ?_, hvv1.symm⟩
                rw [show a = (Sm.i₀, Sm.v₀) from Prod.ext hi hvv0,
                    show b = (Sm.j₀, b.2) from Prod.ext hj rfl]
      obtain ⟨v1, rest, hV, hv1eq⟩ := hverts
      -- both endpoints are npVertices, hence support dots with abscissae ≤ n
      have hmemL : (Sm.i₀, Sm.v₀) ∈ NewtonPolygon.npVertices S hS := by rw [hV]; simp
      have hmemR : (Sm.j₀, v1) ∈ NewtonPolygon.npVertices S hS := by rw [hV]; simp
      have hSmemL : (Sm.i₀, Sm.v₀) ∈ S :=
        ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS hmemL
      have hSmemR : (Sm.j₀, v1) ∈ S :=
        ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS hmemR
      -- abscissae ≤ n
      obtain ⟨_, hneR⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot p f hSmemR
      have hjle : Sm.j₀ ≤ n :=
        ClassifierBridgeFiber.support_le_deg p f (Polynomial.mem_support_iff.mpr hneR)
      -- width Sm.j₀ - Sm.i₀ = n
      have hwidth : Sm.j₀ - Sm.i₀ = n := hlen
      have hi0 : Sm.i₀ = 0 := by omega
      have hj0 : Sm.j₀ = n := by omega
      -- v₁ = 0: (n, v1) on hull, (n,0) support, npHeight n ≤ 0, v1 ≥ 0
      have hv1 : v1 = 0 := by
        -- (Sm.j₀, v1) on hull
        have honhull : ((v1 : ℕ) : ℚ) = NewtonPolygon.npHeight S hS ((Sm.j₀ : ℕ) : ℚ) := by
          have := NewtonPolygon.npVertices_on_hull S hS hmemR
          simpa using this
        rw [hj0] at honhull
        -- (n, 0) is a support dot (leading coeff), so npHeight n ≤ 0
        have hnmem : (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ S :=
          ClassifierBridgeFiber.mem_boxValSupport_right p hN f
        have hle : NewtonPolygon.npHeight S hS ((n : ℕ) : ℚ) ≤ ((0 : ℕ) : ℚ) :=
          NewtonPolygon.npHeight_le S hS hnmem
        rw [← honhull] at hle
        -- (v1 : ℚ) ≤ 0 and v1 : ℕ ⟹ v1 = 0
        have : (v1 : ℚ) ≤ 0 := by simpa using hle
        have hv1z : (v1 : ℚ) = 0 := le_antisymm this (by positivity)
        exact_mod_cast hv1z
      -- assemble Sm = mkSide ((0,H),(n,0))
      have : Sm = mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
        have hv1S : Sm.v₁ = 0 := by rw [hv1eq]; exact hv1
        show Sm = ⟨0, n, H, 0⟩
        cases Sm with
        | mk i j vv0 vv1 =>
            simp only at hi0 hj0 hv0S hv1S
            subst hi0 hj0 hv0S hv1S
            rfl
      rw [this]

/-! ## STEP B — backward Lemma B (SideAbove + vertex-exactness from the two-vertex hull).

The heart is the CONVERSE of `dropCollinear_collapse`: if `dropCollinear L = [a, z]` (exactly two
vertices) for a strictly-abscissa-sorted `L`, then every point of `L` lies on the integer line
`a`–`z`.  Applied to `npVerticesFull` (`dropCollinear npVerticesFull = npVertices = [(0,H),(n,0)]`)
this shows every on-hull dot is on the chord, so `npHeight = chord` and the chord is a valid
supporting line — recovering `SideAbove`. -/

open NewtonPolygon

/-- `collinear₃ a b c` (the integer cross-product test) means exactly `b` on the line `a`–`c`. -/
theorem collinear₃_iff_onLine (a b c : ℕ × ℕ) :
    (collinear₃ a b c = true) ↔ ClassifierBridgeFiber.OnLineℤ a c b := by
  unfold collinear₃ ClassifierBridgeFiber.OnLineℤ; rw [beq_iff_eq, eq_comm]

theorem onLine_refl_left (A Z : ℕ × ℕ) : ClassifierBridgeFiber.OnLineℤ A Z A := by unfold ClassifierBridgeFiber.OnLineℤ; ring
theorem onLine_refl_right (A Z : ℕ × ℕ) : ClassifierBridgeFiber.OnLineℤ A Z Z := by unfold ClassifierBridgeFiber.OnLineℤ; ring

/-- On-line gluing: `b` on line `a`–`z` and `Q` on line `b`–`z` (with `b.1 < z.1`) ⟹ `Q` on line
`a`–`z` (all three lie on the single line through `a`,`z`). -/
theorem onLine_glue {a b z Q : ℕ × ℕ}
    (hbz : (b.1 : ℤ) < z.1) (hb : ClassifierBridgeFiber.OnLineℤ a z b) (hQ : ClassifierBridgeFiber.OnLineℤ b z Q) : ClassifierBridgeFiber.OnLineℤ a z Q := by
  unfold ClassifierBridgeFiber.OnLineℤ at *
  have hd : ((z.1 : ℤ) - b.1) ≠ 0 := by omega
  apply mul_left_cancel₀ hd; nlinarith [hb, hQ]

/-- `dropCollinear` of a `≥ 2`-element list has `≥ 2` elements (it always keeps the first and last
hull vertices). -/
theorem dropCollinear_len_ge_two : ∀ (a b : ℕ × ℕ) (rest : List (ℕ × ℕ)),
    2 ≤ (dropCollinear (a :: b :: rest)).length
  | _, _, [] => by rw [show dropCollinear [_, _] = [_, _] from rfl]; simp
  | a, b, c :: rest => by
      have ihlen := dropCollinear_len_ge_two b c rest
      obtain ⟨u, hu, _⟩ := dropCollinear_cons_head b (c :: rest)
      rw [dropCollinear_cons3, hu]; rw [hu] at ihlen
      cases u with
      | nil => simp at ihlen
      | cons d' rest' =>
          cases hcol : collinear₃ a b d' with
          | true => simp only [hcol, if_true, List.length_cons]; omega
          | false => simp only [hcol, Bool.false_eq_true, if_false, List.length_cons]; omega
  termination_by a b rest => rest.length

/-- **The CONVERSE collinearity collapse.**  If `dropCollinear L = [a, z]` (exactly two vertices) for
a strictly-abscissa-sorted `L`, then every `Q ∈ L` lies on the integer line `a`–`z`.  The reverse of
`ClassifierBridgeFiber.dropCollinear_collapse`. -/
theorem dropCollinear_onLine : ∀ (L : List (ℕ × ℕ)) (a z : ℕ × ℕ),
      (L.map Prod.fst).Pairwise (· < ·) →
      dropCollinear L = [a, z] →
      ∀ Q ∈ L, ClassifierBridgeFiber.OnLineℤ a z Q
  | [], a, z, _, hdc => by simp [dropCollinear] at hdc
  | [b], a, z, _, hdc => by simp [dropCollinear] at hdc
  | [b, d], a, z, _, hdc => by
      rw [show dropCollinear [b, d] = [b, d] from rfl] at hdc
      obtain ⟨rfl, rfl⟩ : b = a ∧ d = z := by simpa using hdc
      intro Q hQ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact onLine_refl_left _ _
      · exact onLine_refl_right _ _
  | b :: d :: c :: rest, a, z, hsort, hdc => by
      have hsort' : ((d :: c :: rest).map Prod.fst).Pairwise (· < ·) := by
        simp only [List.map_cons] at hsort ⊢; exact hsort.tail
      obtain ⟨u, hu, husub⟩ := dropCollinear_cons_head d (c :: rest)
      have hlen := dropCollinear_len_ge_two d c rest
      rw [dropCollinear_cons3, hu] at hdc
      rw [hu] at hlen
      cases u with
      | nil => simp at hlen
      | cons d' rest' =>
          simp only at hdc
          cases hcol : collinear₃ b d d' with
          | false =>
              rw [hcol] at hdc; simp only [Bool.false_eq_true, if_false] at hdc
              simp at hdc
          | true =>
              rw [hcol] at hdc; simp only [if_true] at hdc
              obtain ⟨hb_eq, hd'_eq, hr⟩ : b = a ∧ d' = z ∧ rest' = [] := by
                rw [List.cons.injEq, List.cons.injEq] at hdc
                exact ⟨hdc.1, hdc.2.1, by simpa using hdc.2.2⟩
              subst hb_eq; subst hd'_eq; subst hr
              have hrec : dropCollinear (d :: c :: rest) = [d, d'] := hu
              have hall := dropCollinear_onLine (d :: c :: rest) d d' hsort' hrec
              have hbd : ClassifierBridgeFiber.OnLineℤ b d' d := (collinear₃_iff_onLine b d d').mp hcol
              have hzmem : d' ∈ c :: rest := by
                have hsub : ([d, d'] : List (ℕ × ℕ)).Sublist (d :: c :: rest) := by
                  rw [← hrec]; exact dropCollinear_sublist _
                exact (List.singleton_sublist).mp (List.cons_sublist_cons.mp hsub)
              have hdz : (d.1 : ℤ) < (d'.1 : ℤ) := by
                have hlt : d.1 < d'.1 := by
                  rw [List.map_cons, List.pairwise_cons] at hsort'
                  exact hsort'.1 d'.1 (List.mem_map_of_mem hzmem)
                exact_mod_cast hlt
              intro Q hQ
              rcases List.mem_cons.mp hQ with rfl | hQ'
              · exact onLine_refl_left _ _
              · exact onLine_glue hdz hbd (hall Q hQ')
  termination_by L => L.length

/-- A `pairLine` through two points on the self-loop chord line `(0,H)`–`(n,0)` (distinct abscissae)
IS the chord line. -/
theorem pairLine_eq_of_onChord {H n : ℕ} {A B : ℕ × ℕ} (hn : 0 < n)
    (hA : ClassifierBridgeFiber.OnLineℤ ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) A)
    (hB : ClassifierBridgeFiber.OnLineℤ ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) B)
    (hAB : A.1 ≠ B.1) (x : ℚ) :
    pairLine A B x = pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) x := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hAq : (A.2 : ℚ) = (H : ℚ) - (H : ℚ) * (A.1 : ℚ) / (n : ℚ) := by
    unfold ClassifierBridgeFiber.OnLineℤ at hA; simp only [Nat.cast_zero, sub_zero] at hA
    have hz : ((n : ℤ)) * ((A.2 : ℤ) - H) = ((A.1 : ℤ)) * (0 - H) := by simpa using hA
    have hq : (n : ℚ) * ((A.2 : ℚ) - H) = (A.1 : ℚ) * (0 - H) := by exact_mod_cast hz
    field_simp; nlinarith [hq]
  have hBq : (B.2 : ℚ) = (H : ℚ) - (H : ℚ) * (B.1 : ℚ) / (n : ℚ) := by
    unfold ClassifierBridgeFiber.OnLineℤ at hB; simp only [Nat.cast_zero, sub_zero] at hB
    have hz : ((n : ℤ)) * ((B.2 : ℤ) - H) = ((B.1 : ℤ)) * (0 - H) := by simpa using hB
    have hq : (n : ℚ) * ((B.2 : ℚ) - H) = (B.1 : ℚ) * (0 - H) := by exact_mod_cast hz
    field_simp; nlinarith [hq]
  have hd2 : ((B.1 : ℚ) - (A.1 : ℚ)) ≠ 0 := by
    have hne : (A.1 : ℚ) ≠ (B.1 : ℚ) := by exact_mod_cast hAB
    intro h; apply hne; linarith
  have hslope : pairSlope A B = -(H : ℚ) / (n : ℚ) := by
    unfold pairSlope; rw [hAq, hBq, div_eq_iff hd2]; field_simp; ring
  have hcslope : pairSlope ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) = -(H : ℚ) / (n : ℚ) := by
    unfold pairSlope; simp only [Nat.cast_zero, sub_zero, zero_sub]
  unfold pairLine
  rw [hslope, hcslope, hAq]
  simp only [Nat.cast_zero, sub_zero]
  field_simp; ring

section StepB

variable (p : ℕ) [Fact p.Prime]

/-- Every VALID supporting line's left endpoint is an on-hull dot (`(A.2 : ℚ) = npHeight A.1`): the
line passes through `A` (a dot, so `npHeight A.1 ≤ A.2`) and lies below `npHeight` (it is one of the
`sup'` terms, so `A.2 = pairLine A B A.1 ≤ npHeight A.1`). -/
theorem validLine_left_onHull (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    {A B : ℕ × ℕ} (hAB : (A, B) ∈ NewtonPolygon.validLines S) :
    (A.2 : ℚ) = NewtonPolygon.npHeight S hS (A.1 : ℚ) := by
  refine le_antisymm ?_ (NewtonPolygon.npHeight_le S hS (NewtonPolygon.validLines_mem_left S hAB))
  rw [← NewtonPolygon.pairLine_left A B, NewtonPolygon.npHeight, Finset.le_sup'_iff]
  exact ⟨(A, B), hAB, le_refl _⟩

/-- Symmetric: the right endpoint of a valid line is on-hull. -/
theorem validLine_right_onHull (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    {A B : ℕ × ℕ} (hAB : (A, B) ∈ NewtonPolygon.validLines S) (hne : (A.1 : ℚ) ≠ (B.1 : ℚ)) :
    (B.2 : ℚ) = NewtonPolygon.npHeight S hS (B.1 : ℚ) := by
  refine le_antisymm ?_ (NewtonPolygon.npHeight_le S hS (NewtonPolygon.validLines_mem_right S hAB))
  rw [← NewtonPolygon.pairLine_right A B hne, NewtonPolygon.npHeight, Finset.le_sup'_iff]
  exact ⟨(A, B), hAB, le_refl _⟩

/-- **Every on-hull support dot lies on the self-loop chord.**  Given `npVertices = [(0,H),(n,0)]`,
an on-hull dot `(i,v)` (with `v = npHeight i`) is a `npVerticesFull` entry (abscissa `i` is a hull
abscissa, `hullDotAt i = (i,v)`); by the converse-collinearity `dropCollinear_onLine` it lies on the
chord line `(0,H)`–`(n,0)`. -/
theorem onHull_onChord {N n H : ℕ} (hN : 0 < N) (f : QuotientBox.monicBox p N n)
    (hverts : NewtonPolygon.npVertices (B.boxValSupport p N f) (B.boxValSupport_nonempty p N hN f)
        = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))])
    {Q : ℕ × ℕ} (hQmem : Q ∈ B.boxValSupport p N f)
    (hQon : (Q.2 : ℚ) = NewtonPolygon.npHeight (B.boxValSupport p N f)
        (B.boxValSupport_nonempty p N hN f) (Q.1 : ℚ)) :
    ClassifierBridgeFiber.OnLineℤ ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) Q := by
  set S := B.boxValSupport p N f with hSdef
  set hS := B.boxValSupport_nonempty p N hN f with hShyp
  -- Q ∈ npVerticesFull
  have habs : Q.1 ∈ NewtonPolygon.hullAbscissae S hS := by
    rw [NewtonPolygon.mem_hullAbscissae_iff]; exact ⟨Q.2, hQmem, hQon⟩
  have hfullmem : Q ∈ NewtonPolygon.npVerticesFull S hS := by
    unfold NewtonPolygon.npVerticesFull
    rw [List.mem_map]
    refine ⟨Q.1, habs, ?_⟩
    -- hullDotAt Q.1 = (Q.1, ⌊npHeight Q.1⌋₊) = (Q.1, Q.2)
    unfold NewtonPolygon.hullDotAt
    rw [NewtonPolygon.hullHeightAt_of_onHull S hS hQmem hQon]
  -- dropCollinear npVerticesFull = npVertices = [(0,H),(n,0)]
  have hdc : NewtonPolygon.dropCollinear (NewtonPolygon.npVerticesFull S hS)
      = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] := by
    rw [← NewtonPolygon.npVertices]; exact hverts
  have hsort : ((NewtonPolygon.npVerticesFull S hS).map Prod.fst).Pairwise (· < ·) :=
    NewtonPolygon.npVerticesFull_sorted S hS
  exact dropCollinear_onLine _ _ _ hsort hdc Q hfullmem

/-- **The self-loop chord is a valid supporting line (BACKWARD).**  Given `npVertices = [(0,H),(n,0)]`
with `0 < H`, `((0,H),(n,0)) ∈ validLines`.  The `sup'` `npHeight 0 = H` is achieved by some valid
line `PR₀` (`Finset.exists_mem_eq_sup'`); its endpoints are on-hull (`validLine_*_onHull`) hence on
the chord (`onHull_onChord`).  `PR₀` is non-degenerate (a degenerate on-chord valid line forces value
`0 ≠ H`), so `pairLine PR₀ = chord` (`pairLine_eq_of_onChord`), and `PR₀ ∈ validLines` transports to
`((0,H),(n,0)) ∈ validLines`. -/
theorem chord_validLine_backward {N n H : ℕ} (hn0 : 0 < n) (hN : 0 < N) (hH : 0 < H)
    (f : QuotientBox.monicBox p N n)
    (hverts : NewtonPolygon.npVertices (B.boxValSupport p N f) (B.boxValSupport_nonempty p N hN f)
        = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))]) :
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ NewtonPolygon.validLines (B.boxValSupport p N f) := by
  set S := B.boxValSupport p N f with hSdef
  set hS := B.boxValSupport_nonempty p N hN f with hShyp
  -- (0,H) and (n,0) are on the hull
  have h0on : (((0 : ℕ), H) : ℕ × ℕ).2 = (H : ℕ) ∧ ((H : ℕ) : ℚ)
      = NewtonPolygon.npHeight S hS (((0 : ℕ), H) : ℕ × ℕ).1 := by
    refine ⟨rfl, ?_⟩
    have := NewtonPolygon.npVertices_on_hull S hS (P := (((0 : ℕ), H) : ℕ × ℕ)) (by rw [hverts]; simp)
    simpa using this
  have hnpH0 : NewtonPolygon.npHeight S hS ((0 : ℕ) : ℚ) = (H : ℚ) := by
    have := h0on.2; simpa using this.symm
  -- the sup' `npHeight 0 = H` is achieved by some valid line PR₀
  obtain ⟨PR₀, hPR₀mem, hPR₀eq⟩ := Finset.exists_mem_eq_sup' (NewtonPolygon.validLines_nonempty S hS)
    (fun PR => NewtonPolygon.pairLine PR.1 PR.2 ((0 : ℕ) : ℚ))
  -- npHeight 0 = pairLine PR₀ 0
  have hval0 : NewtonPolygon.pairLine PR₀.1 PR₀.2 ((0 : ℕ) : ℚ) = (H : ℚ) := by
    rw [← hnpH0, NewtonPolygon.npHeight]; exact hPR₀eq.symm
  -- PR₀ endpoints on hull → on chord
  have hA := PR₀.1; have hB := PR₀.2
  have hAonhull : (PR₀.1.2 : ℚ) = NewtonPolygon.npHeight S hS (PR₀.1.1 : ℚ) :=
    validLine_left_onHull S hS (by rw [Prod.mk.eta] at *; exact hPR₀mem)
  have hAchord : ClassifierBridgeFiber.OnLineℤ ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) PR₀.1 :=
    onHull_onChord p hN f hverts (NewtonPolygon.validLines_mem_left S hPR₀mem) hAonhull
  -- case on whether PR₀ is degenerate (same abscissa) or not
  by_cases hdeg : PR₀.1.1 = PR₀.2.1
  · -- degenerate: pairLine PR₀ is the constant PR₀.1.2 = value at 0 = H; but on-chord + valid ⟹ ≤ 0
    exfalso
    -- pairLine PR₀ 0 = PR₀.1.2 (left value) since ... actually degenerate: slope denom 0.
    -- Use: (n,0) ∈ S is a dot, PR₀ valid ⟹ pairLine PR₀ n ≤ 0. And pairLine PR₀ is constant (deg).
    have hnmem : (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ S :=
      ClassifierBridgeFiber.mem_boxValSupport_right p hN f
    have hle_n : NewtonPolygon.pairLine PR₀.1 PR₀.2 ((n : ℕ) : ℚ) ≤ ((0 : ℕ) : ℚ) :=
      NewtonPolygon.pairLine_le_of_valid S hPR₀mem hnmem
    -- degenerate pairLine is constant: pairLine PR₀ x = PR₀.1.2 for all x (slope = 0 denom)
    have hconst : ∀ x : ℚ, NewtonPolygon.pairLine PR₀.1 PR₀.2 x = (PR₀.1.2 : ℚ) := by
      intro x
      unfold NewtonPolygon.pairLine NewtonPolygon.pairSlope
      have : ((PR₀.2.1 : ℚ) - (PR₀.1.1 : ℚ)) = 0 := by
        have : (PR₀.1.1 : ℚ) = (PR₀.2.1 : ℚ) := by exact_mod_cast hdeg
        linarith
      rw [this]; simp
    have hval0' : (PR₀.1.2 : ℚ) = (H : ℚ) := by rw [← hconst ((0 : ℕ) : ℚ)]; exact hval0
    have hlen' : (PR₀.1.2 : ℚ) ≤ 0 := by rw [← hconst ((n : ℕ) : ℚ)]; simpa using hle_n
    rw [hval0'] at hlen'
    have : (0 : ℚ) < (H : ℚ) := by exact_mod_cast hH
    linarith
  · -- non-degenerate: pairLine PR₀ = chord, and PR₀ valid ⟹ chord valid
    have hne1 : (PR₀.1.1 : ℚ) ≠ (PR₀.2.1 : ℚ) := by exact_mod_cast hdeg
    have hBonhull : (PR₀.2.2 : ℚ) = NewtonPolygon.npHeight S hS (PR₀.2.1 : ℚ) :=
      validLine_right_onHull S hS hPR₀mem hne1
    have hBchord : ClassifierBridgeFiber.OnLineℤ ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) PR₀.2 :=
      onHull_onChord p hN f hverts (NewtonPolygon.validLines_mem_right S hPR₀mem) hBonhull
    -- chord validity: ∀ Q ∈ S, chord Q.1 ≤ Q.2, via pairLine PR₀ = chord
    rw [NewtonPolygon.validLines, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · -- (0,H) ∈ S : left endpoint dot; from npVertices membership + mem_S
      exact ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS (by rw [hverts]; simp)
    · exact ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS (by rw [hverts]; simp)
    · intro Q hQ
      show NewtonPolygon.pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) (Q.1 : ℚ) ≤ (Q.2 : ℚ)
      rw [← pairLine_eq_of_onChord hn0 hAchord hBchord hdeg (Q.1 : ℚ)]
      exact NewtonPolygon.pairLine_le_of_valid S hPR₀mem hQ

/-- **Backward Lemma B — `SideAbove` + vertex-exactness from the two-vertex hull.**  From
`npVertices = [(0,H),(n,0)]` (with `0 < n`, `0 < H`, `H < N`): the chord is a valid supporting line
(`chord_validLine_backward`), so every support dot lies on/above it and every non-support column has
`vOf = N > H ≥ chord`, giving `SideAbove f ((0,H),(n,0))`; and the two on-hull vertices are the unique
support dots at abscissae `0` and `n`, giving `vOf f 0 = H`, `vOf f n = 0`. -/
theorem sideAbove_of_npVertices {N n H : ℕ} (hn0 : 0 < n) (hN : 0 < N) (hH : 0 < H) (hHN : H < N)
    (f : QuotientBox.monicBox p N n)
    (hverts : NewtonPolygon.npVertices (B.boxValSupport p N f) (B.boxValSupport_nonempty p N hN f)
        = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))]) :
    SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
      ∧ vOf p f 0 = H ∧ vOf p f n = 0 := by
  set S := B.boxValSupport p N f with hSdef
  set hS := B.boxValSupport_nonempty p N hN f with hShyp
  have hval : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ NewtonPolygon.validLines S :=
    chord_validLine_backward p hn0 hN hH f hverts
  -- vertex exactness: (0,H) and (n,0) are support dots, unique per abscissa
  have h0mem : (((0 : ℕ), H) : ℕ × ℕ) ∈ S :=
    ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS (by rw [hverts]; simp)
  have hnmem : (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ S :=
    ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS (by rw [hverts]; simp)
  have hv0 : vOf p f 0 = H := by
    obtain ⟨hv, _⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot p f h0mem
    -- hv : (0,H).2 = vOf f (0,H).1, i.e. H = vOf f 0
    simpa using hv.symm
  have hvn : vOf p f n = 0 := by
    obtain ⟨hv, _⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot p f hnmem
    simpa using hv.symm
  refine ⟨?_, hv0, hvn⟩
  -- SideAbove: ∀ i, 0 ≤ i → i ≤ n → lineAt pr i ≤ vOf f i
  intro i _ hin
  -- lineAt pr = pairLine (0,H)(n,0)
  rw [← ClassifierBridgeFiber.pairLine_eq_lineAt]
  by_cases hc : (f.1).coeff i = 0
  · -- non-support: vOf f i = N; chord i ≤ H < N
    have hvi : vOf p f i = N := by
      rw [vOf, hc, PadicLift.zmodValuation_zero]
    rw [hvi]
    -- pairLine (0,H)(n,0) i ≤ H (chord decreasing from H); H < N
    have hchord_le_H : NewtonPolygon.pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) (i : ℚ) ≤ (H : ℚ) := by
      unfold NewtonPolygon.pairLine NewtonPolygon.pairSlope
      simp only [Nat.cast_zero, sub_zero, zero_sub]
      have hn0q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
      have hiq : (0 : ℚ) ≤ (i : ℚ) := by positivity
      have hnegdiv : (-(H : ℚ) / (n : ℚ)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by simp) (le_of_lt hn0q)
      have : (-(H : ℚ) / (n : ℚ)) * (i : ℚ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnegdiv hiq
      linarith
    have hHN' : (H : ℚ) < (N : ℚ) := by exact_mod_cast hHN
    linarith
  · -- support dot: (i, vOf f i) ∈ S, chord ≤ vOf f i by validLine
    have hmem : ((i, vOf p f i) : ℕ × ℕ) ∈ S := ClassifierBridgeFiber.mem_boxValSupport p f hc
    exact NewtonPolygon.pairLine_le_of_valid S hval hmem

end StepB

/-! ## STEP C — the fiber characterization `classify_eq_selfloop_iff`. -/

/-- **`polyShape` from squarefree residual + factor degrees + all-μ=1 shape.**  Reverse of
`classifierFactors_deg_eq_shape`: a squarefree residual whose normalized-factor degree multiset is
`shape.map fst` has `polyShape = ↑shape` (every factor multiplicity `1`, and `hmu` gives every shape
multiplicity `1`). -/
theorem polyShape_of_squarefree_degrees {p : ℕ} [Fact p.Prime] (R : Polynomial (ZMod p)) (hne : R ≠ 0)
    (hsq : Squarefree R) {shape : List (ℕ × ℕ)}
    (hdeg : (UniqueFactorizationMonoid.normalizedFactors R).map Polynomial.natDegree
      = (shape.map Prod.fst : Multiset ℕ))
    (hmu : ∀ q ∈ shape, q.2 = 1) :
    polyShape p R = (shape : Multiset (ℕ × ℕ)) := by
  letI := Classical.decEq (Polynomial (ZMod p))
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors R).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne).mp hsq
  have htf : (UniqueFactorizationMonoid.normalizedFactors R).toFinset.val
      = UniqueFactorizationMonoid.normalizedFactors R := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hpoly : polyShape p R
      = (UniqueFactorizationMonoid.normalizedFactors R).map (fun ψ => (ψ.natDegree, 1)) := by
    unfold polyShape
    rw [htf]
    apply Multiset.map_congr rfl
    intro ψ hψ
    rw [Multiset.count_eq_one_of_mem hnodup hψ]
  rw [hpoly]
  have h1 : (UniqueFactorizationMonoid.normalizedFactors R).map (fun ψ => (ψ.natDegree, 1))
      = ((UniqueFactorizationMonoid.normalizedFactors R).map Polynomial.natDegree).map
          (fun d => (d, 1)) := by
    rw [Multiset.map_map]; rfl
  rw [h1, hdeg, Multiset.map_coe]
  -- goal: ↑(List.map (fun d => (d,1)) (shape.map fst)) = ↑shape
  have hlist : List.map (fun d => ((d, 1) : ℕ × ℕ)) (shape.map Prod.fst) = shape := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id shape]
    apply List.map_congr_left
    intro q hq
    show ((q.1, 1) : ℕ × ℕ) = id q
    rw [id]; exact Prod.ext rfl (hmu q hq).symm
  rw [hlist]

/-- The `.cells` `dS` list of `classify f = Tselfloop` reads back the residual's sorted factor-degree
list as `shape.map fst`. -/
theorem factorDS_eq_shape_of_classify {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hcl : B.classify p n N f = ClassifierBridgeFiber.Tselfloop n pr shape) :
    (M5.encodeCells (B.fRootCtx p N hN f)).map (fun c => c.dS) = shape.map Prod.fst := by
  have hcells : M5.encodeCells (B.fRootCtx p N hN f)
      = (ClassifierBridgeFiber.Tselfloop n pr shape).cells := by
    rw [← classify_cells hN f, hcl]
  rw [hcells]
  show ((ClassifierBridgeFiber.Tselfloop n pr shape).cells).map (fun c => c.dS) = shape.map Prod.fst
  -- Tselfloop.cells = shape.map (⟨q.1,1,Nr,[]⟩); dS = q.1
  rw [show (ClassifierBridgeFiber.Tselfloop n pr shape).cells
      = shape.map (fun q => (⟨q.1, 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell)) from rfl,
    List.map_map]
  rfl

/-- The head `dr` of `classify f = Tselfloop` reads back `rootResidual.natDegree = (shape.map fst).sum`. -/
theorem rootResidual_natDegree_eq_of_classify {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hcl : B.classify p n N f = ClassifierBridgeFiber.Tselfloop n pr shape) :
    (B.rootResidual p N hN f).natDegree = (shape.map Prod.fst).sum := by
  -- take .tree of both sides; head tuple third component
  have hdisp : B.classify p n N f
      = B.classifyAux p N n n f (B.fRootCtx p N hN f) (B.clusterSize_fRootCtx p N hN f) :=
    Order0.classifyAux_congr_ctx p N n n f (dif_pos hN)
      (B.clusterSize_rootCtx p N f) (B.clusterSize_fRootCtx p N hN f)
  have htree : (B.classify p n N f).tree = (ClassifierBridgeFiber.Tselfloop n pr shape).tree := by
    rw [hcl]
  rw [hdisp, Order0.classifyAux_unfold] at htree
  -- LHS tree head = (fRootCtx.order, clusterSize, fRootCtx.dr); RHS = [(0,n,sum)]
  have hhead := List.head_eq_of_cons_eq htree
  -- hhead : (order, clusterSize, dr) = (0, n, sum) ; take third
  have h3 : (B.fRootCtx p N hN f).dr = (shape.map Prod.fst).sum := by
    have := congrArg (fun t => t.2.2) hhead
    simpa using this
  -- fRootCtx.dr = rootResidual.natDegree
  show (B.rootResidual p N hN f).natDegree = (shape.map Prod.fst).sum
  rw [show (B.rootResidual p N hN f).natDegree = (B.fRootCtx p N hN f).dr from rfl, h3]

/-- The `factorize_any` factor-degree multiset of `T.Rr` equals `(encodeCells T).map dS` (as a
multiset): `encodeCells`/`M5.cells` map the degree-`mergeSort`ed factor list, a permutation of the
factor `Finset`, through `natDegree`. -/
theorem factors_natDegree_eq_encodeCells_dS (T : M5.OMType) :
    (Classical.choice (M4.factorize_any T.Rr)).factors.val.map Polynomial.natDegree
      = (((M5.encodeCells T).map (fun c => c.dS) : List ℕ) : Multiset ℕ) := by
  set fact := Classical.choice (M4.factorize_any T.Rr) with hfact
  -- encodeCells T dS list = (mergeSort attach).map (·.1.natDegree)
  have hcells : (M5.encodeCells T).map (fun c => c.dS)
      = (fact.factors.attach.toList.mergeSort
          (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map (fun a => a.1.natDegree) := by
    rw [M5.encodeCells, M5.cells, List.map_map, List.map_map]
    rfl
  rw [hcells]
  -- as multiset = factors.val.map natDegree (mergeSort perm + attach plumbing)
  calc fact.factors.val.map Polynomial.natDegree
      = Multiset.map (fun (a : {x // x ∈ fact.factors}) => a.1.natDegree) fact.factors.attach.val :=
        (Multiset.attach_map_val' fact.factors.val Polynomial.natDegree).symm
    _ = Multiset.map (fun (a : {x // x ∈ fact.factors}) => a.1.natDegree)
          ((fact.factors.attach.toList : List {x // x ∈ fact.factors}) : Multiset _) :=
        congrArg (Multiset.map _) (Finset.coe_toList _).symm
    _ = ((fact.factors.attach.toList.map (fun a => a.1.natDegree) : List ℕ) : Multiset ℕ) :=
        (Multiset.map_coe _ _)
    _ = (((fact.factors.attach.toList.mergeSort
          (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
            (fun a => a.1.natDegree) : List ℕ) : Multiset ℕ) :=
        (Multiset.coe_eq_coe.mpr ((List.mergeSort_perm fact.factors.attach.toList _).map _)).symm

/-- Squarefree of a finset product of pairwise-`IsRelPrime` squarefree elements (used for the
all-multiplicity-1 residual `R = unit · ∏ ψ`). -/
theorem squarefree_finset_prod {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (s : Finset R) (hsq : ∀ x ∈ s, Squarefree x)
    (hcop : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsRelPrime x y) :
    Squarefree (∏ x ∈ s, x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have hprodsq : Squarefree (∏ x ∈ t, x) :=
        ih (fun x hx => hsq x (Finset.mem_insert_of_mem hx))
          (fun x hx y hy => hcop x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
      have harel : IsRelPrime a (∏ x ∈ t, x) := by
        apply IsRelPrime.prod_right
        intro x hx
        exact hcop a (Finset.mem_insert_self a t) x (Finset.mem_insert_of_mem hx)
          (by rintro rfl; exact ha hx)
      rw [squarefree_mul_iff]
      exact ⟨harel, hsq a (Finset.mem_insert_self a t), hprodsq⟩

/-- `normalizedFactors` of a field-poly is independent of which `DecidableEq` the ambient
`NormalizedGCDMonoid` was built from (the two `NormalizationMonoid` instances agree after the deep
`DecidableEq` is identified by subsingleton). -/
theorem normalizedFactors_decEq_irrel {K : Type*} [Field K] (I1 I2 : DecidableEq K)
    (x : Polynomial K) :
    @UniqueFactorizationMonoid.normalizedFactors _ _
        (@Polynomial.instNormalizationMonoid K _ _
          (@CommGroupWithZero.instNormalizedGCDMonoid K _ I1).toNormalizationMonoid) _ x
      = @UniqueFactorizationMonoid.normalizedFactors _ _
        (@Polynomial.instNormalizationMonoid K _ _
          (@CommGroupWithZero.instNormalizedGCDMonoid K _ I2).toNormalizationMonoid) _ x := by
  rw [Subsingleton.elim I1 I2]

/-- **`polyShape (residualOf f pr) = ↑shape` (BACKWARD).**  From `classify f = Tselfloop n pr shape`
(with `residualOf f pr ≠ 0` and `hmu`): the residual's factor-degree multiset is `shape.map fst`
(`factorDS_eq_shape_of_classify`), and its `natDegree = (shape.map fst).sum`
(`rootResidual_natDegree_eq_of_classify` + `rootResidual = residualOf f pr`).  Since
`∑ mult·deg = natDegree = ∑ deg`, every factor multiplicity is `1` (`degree_budget`), so the residual
is squarefree; `polyShape_of_squarefree_degrees` then gives `polyShape = ↑shape`. -/
theorem polyShape_residual_of_classify {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hcl : B.classify p n N f = ClassifierBridgeFiber.Tselfloop n pr shape)
    (hRr : B.rootResidual p N hN f = residualOf p f pr)
    (hne : residualOf p f pr ≠ 0)
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hmu : ∀ q ∈ shape, q.2 = 1) :
    polyShape p (residualOf p f pr) = (shape : Multiset (ℕ × ℕ))
      ∧ Squarefree (residualOf p f pr) := by
  set R := residualOf p f pr with hRdef
  set RT := (B.fRootCtx p N hN f).Rr with hRTdef
  set fact := Classical.choice (M4.factorize_any RT) with hfactdef
  have hRTR : RT = R := hRr
  -- (i) factor-degree multiset = shape.map fst
  have hRrT : RT = R := hRTR
  have hdegDS : (M5.encodeCells (B.fRootCtx p N hN f)).map (fun c => c.dS) = shape.map Prod.fst :=
    factorDS_eq_shape_of_classify hN f pr shape hcl
  have hfacdeg : fact.factors.val.map Polynomial.natDegree = (shape.map Prod.fst : Multiset ℕ) := by
    rw [factors_natDegree_eq_encodeCells_dS (B.fRootCtx p N hN f), hdegDS]
  -- (ii) natDegree = shape-sum
  have hdegN : R.natDegree = (shape.map Prod.fst).sum := by
    rw [← hRr]; exact rootResidual_natDegree_eq_of_classify hN f pr shape hcl
  -- (iii) all mult = 1: ∑ mult·deg = natDegree = ∑ deg, mult ≥ 1, deg ≥ 1
  have hbudget : ∑ ψ ∈ fact.factors, fact.mult ψ * ψ.natDegree = R.natDegree := by
    rw [← hRrT]; exact fact.degree_budget
  -- ∑ deg (distinct) = shape-sum
  have hsumdeg : ∑ ψ ∈ fact.factors, ψ.natDegree = (shape.map Prod.fst).sum := by
    have h := congrArg Multiset.sum hfacdeg
    rw [Multiset.sum_coe] at h
    rw [Finset.sum]
    exact h
  -- all mult = 1: ∑ mult·deg = ∑ deg with mult ≥ 1, deg ≥ 1
  have hmult1 : ∀ ψ ∈ fact.factors, fact.mult ψ = 1 := by
    -- ∑ (mult·deg - deg) = 0, each term ≥ 0, deg ≥ 1 ⟹ mult = 1
    have heq : ∑ ψ ∈ fact.factors, fact.mult ψ * ψ.natDegree
        = ∑ ψ ∈ fact.factors, ψ.natDegree := by rw [hbudget, hdegN, hsumdeg]
    -- each mult ψ * deg ψ ≥ deg ψ (mult ≥ 1); equality of sums with termwise ≥ ⟹ termwise =
    have hle : ∀ ψ ∈ fact.factors, ψ.natDegree ≤ fact.mult ψ * ψ.natDegree := by
      intro ψ hψ
      have := fact.mult_pos ψ hψ
      calc ψ.natDegree = 1 * ψ.natDegree := (one_mul _).symm
        _ ≤ fact.mult ψ * ψ.natDegree := Nat.mul_le_mul_right _ this
    have hterm : ∀ ψ ∈ fact.factors, ψ.natDegree = fact.mult ψ * ψ.natDegree := by
      rw [← Finset.sum_eq_sum_iff_of_le hle]; exact heq.symm
    intro ψ hψ
    have hpos_deg : 1 ≤ ψ.natDegree := by
      -- deg ψ ∈ shape.map fst degrees, all ≥ 1
      have hmem : ψ.natDegree ∈ (shape.map Prod.fst : Multiset ℕ) := by
        rw [← hfacdeg, Multiset.mem_map]
        exact ⟨ψ, by rwa [Finset.mem_val], rfl⟩
      rw [Multiset.mem_coe, List.mem_map] at hmem
      obtain ⟨q, hq, hqeq⟩ := hmem
      rw [← hqeq]; exact hpos q hq
    have hte := (hterm ψ hψ).symm
    -- mult·deg = deg, deg ≥ 1 ⟹ mult = 1
    nlinarith [hte, hpos_deg, fact.mult_pos ψ hψ]
  -- Work over RT := (fRootCtx).Rr (where `fact` naturally lives), transport to R via hRTR.
  have hRTne : RT ≠ 0 := hRTR ▸ hne
  -- squarefree RT: all factor multiplicities 1 ⟹ RT = C(lc) · ∏ ψ, product of distinct irreducibles
  have hsqT : Squarefree RT := by
    have hprodeq : RT = Polynomial.C RT.leadingCoeff * ∏ ψ ∈ fact.factors, ψ := by
      have hpe := fact.prod_eq
      have hpr : ∏ ψ ∈ fact.factors, ψ ^ fact.mult ψ = ∏ ψ ∈ fact.factors, ψ := by
        apply Finset.prod_congr rfl
        intro ψ hψ
        rw [hmult1 ψ hψ, pow_one]
      rw [← hpr]; exact hpe
    rw [hprodeq]
    have hunit : IsUnit (Polynomial.C RT.leadingCoeff) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
        rw [Polynomial.leadingCoeff_ne_zero]; exact hRTne))
    rw [squarefree_mul_iff]
    refine ⟨hunit.isRelPrime_left, hunit.squarefree, ?_⟩
    apply squarefree_finset_prod
    · intro ψ hψ; exact (fact.factors_irreducible ψ hψ).squarefree
    · intro ψ hψ φ hφ hne'
      exact (fact.pairwise_coprime ψ hψ φ hφ hne').isRelPrime
  -- normalizedFactors RT degree multiset = shape.map fst
  have hnfT : (UniqueFactorizationMonoid.normalizedFactors RT).map Polynomial.natDegree
      = (shape.map Prod.fst : Multiset ℕ) := by
    have hnodup : (UniqueFactorizationMonoid.normalizedFactors RT).Nodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hRTne).mp hsqT
    have hfset := Order0.factors_eq_normalizedFactors_toFinset RT hRTne fact
    -- `factors.val = normalizedFactors` (dedup of a nodup multiset), across the DecidableEq flavor.
    have hval : fact.factors.val = UniqueFactorizationMonoid.normalizedFactors RT := by
      have key : ∀ (I : DecidableEq (Polynomial (B.fRootCtx p N hN f).Fr))
          (t s : Multiset (Polynomial (B.fRootCtx p N hN f).Fr)),
          t = s → s.Nodup → (@Multiset.toFinset _ I t).val = s := by
        intro I t s hts hnd
        subst hts
        rw [Multiset.toFinset_val]; exact (@Multiset.dedup_eq_self _ I _).mpr hnd
      rw [hfset]
      exact key _ _ (UniqueFactorizationMonoid.normalizedFactors RT) rfl hnodup
    rw [← hval]; exact hfacdeg
  -- Compute polyShape over RT, then transport the whole pair to R via hRTR (avoids instance-flavor
  -- mismatch on `normalizedFactors`).
  -- transport the RT-facts to R (rewrites the type to `Polynomial (ZMod p)` with ZMod instances)
  have hsq : Squarefree R := hRTR ▸ hsqT
  -- Prove the pair for RT (native flavor, all facts match), then transport the WHOLE pair to R via
  -- hRTR : RT = R (polyShape p _ / Squarefree _ carry ZMod instances fixed by `p`, so `▸` is clean).
  -- align hnfT to the canonical `Polynomial (ZMod p)` NormalizationMonoid flavor that
  -- `polyShape_of_squarefree_degrees` demands (differs only in the deep `DecidableEq (ZMod p)`).
  -- Inline `polyShape_of_squarefree_degrees` at RT so ALL `normalizedFactors` share `fact`'s native
  -- flavor (avoids the `ZMod p` vs `(fRootCtx).Fr` NormalizationMonoid instance mismatch).
  -- align `hnfT`'s `normalizedFactors` to the ZMod-canonical NormalizationMonoid flavor that
  -- `polyShape` uses (the two instances differ only in a `DecidableEq (ZMod p)` subsingleton).
  have hpsRT : polyShape p RT = (shape : Multiset (ℕ × ℕ)) := by
    refine polyShape_of_squarefree_degrees RT hRTne hsqT ?_ hmu
    -- convert `hnfT` (fRootCtx-flavored NormalizationMonoid) to the canonical `ZMod p` flavor;
    -- the instances differ only in the deep `DecidableEq (ZMod p)` (a subsingleton).
    convert hnfT using 2 <;>
      first
      | rfl
      | exact normalizedFactors_decEq_irrel _ _ RT
      | exact heq_of_eq (normalizedFactors_decEq_irrel _ _ RT)
  exact ⟨hRTR ▸ hpsRT, hRTR ▸ hsqT⟩

/-- **STEP C — the fiber characterization `classify_eq_selfloop_iff`.**  On the single-side, all-μ=1
locus, the genuine order-0 classifier collapses to the respelled `Tselfloop` iff `f` lies in the
order-1 cell.  Forward = `classify_eq_selfloop_of_inCell` (LANDED); backward assembles Steps A/B and
`polyShape_residual_of_classify` into `Matches`, then `inCell_mkCell_iff`. -/
theorem classify_eq_selfloop_iff {p : ℕ} [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hmu : ∀ q ∈ shape, q.2 = 1)
    (hne : shape ≠ []) (f : QuotientBox.monicBox p N n) :
    B.classify p n N f = ClassifierBridgeFiber.Tselfloop n pr shape
      ↔ InCell p f (mkCell n P [shape]) := by
  -- single-side normal form: P = [(0,H),(n,0)], pr = ((0,H),(n,0)), 1 ≤ H ≤ N-1.
  obtain ⟨H, hPeq, hpreq, hH1, hH2⟩ := ClassifierBridgeFiber.menuPath_single_side hPmenu hsingle
  subst hpreq
  subst hPeq
  constructor
  · -- backward direction (classify = Tselfloop → InCell)
    intro hcl
    have hHN : H < N := by omega
    have hH0 : 0 < H := by omega
    -- Step A: rootSide = some (mkSide pr)
    have hrs : B.rootSide p N hN f = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :=
      rootSide_eq_of_classify hn hN f shape hcl hne
    -- npVertices = [(0,H),(n,0)]  (LANDED)
    have hverts := ClassifierBridgeFiber.npVertices_of_rootSide p hn hN f hrs
    -- Step B: SideAbove + vertex exactness
    obtain ⟨hside, hv0, hvn⟩ := sideAbove_of_npVertices p hn hN hH0 hHN f hverts
    -- residual data: rootResidual = residualOf f pr
    have hexact : ∀ q ∈ ([((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] : List (ℕ × ℕ)), vOf p f q.1 = q.2 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq2
      · simpa using hv0
      · rcases List.mem_cons.mp hq2 with rfl | hq3
        · simpa using hvn
        · simp at hq3
    have hRr : B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) :=
      ClassifierBridgeFiber.rootResidual_eq_residualOf p hn hN f hPmenu hexact hsingle hv0 hHN hside
    have hRne : residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ≠ 0 := by
      have hpr_mem : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ sidePairs ([((0:ℕ),H),((n:ℕ),(0:ℕ))] : List (ℕ × ℕ)) := by rw [hsingle]; simp
      exact (residual_facts p hN hPmenu hexact hpr_mem).1
    -- degree positivity of the shape (side degrees ≥ 1) from ShapesFor
    have hpos : ∀ q ∈ shape, 1 ≤ q.1 := by
      have := hSF
      rw [ShapesFor, hsingle] at this
      cases this with
      | cons hh _ =>
          intro q hq
          exact ((mem_shapesOfDegree_iff.mp hh).2.1 q hq).1
    -- Step C polyShape: polyShape (residualOf f pr) = shape
    obtain ⟨hpsh, _⟩ :=
      polyShape_residual_of_classify hN f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape hcl hRr hRne
        hpos hmu
    -- assemble Matches, then InCell
    rw [inCell_mkCell_iff p hPmenu hSF]
    refine ⟨hexact, ?_⟩
    rw [hsingle]
    exact List.Forall₂.cons ⟨hside, hpsh⟩ List.Forall₂.nil
  · -- forward direction (LANDED)
    intro hInCell
    exact ClassifierBridgeFiber.classify_eq_selfloop_of_inCell p n N hN hn
      ([((0:ℕ),H),((n:ℕ),(0:ℕ))] : List (ℕ × ℕ)) hPmenu
      (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) hsingle shape hSF hmu f hInCell

/-! ## STEP D — the discharge analogues over the RESPELLED `Tselfloop`. -/

/-- **`stratumCount_selfloop_R` (respelled).**  The schematic `M8.stratumCount (M9.rawCount n)` count of
the RESPELLED `Tselfloop n pr shape` equals the genuine order-1 stratum count `stratumCount1 realP n N
(mkCell n P [shape])` (cast to ℚ).  `rfl`-unfold of the schematic count to the `Nat.card` classify
fiber, `stratumCount1_eq_cellCard`, then `Nat.card_congr` on `classify_eq_selfloop_iff` at `realP`. -/
theorem stratumCount_selfloop_R (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hmu : ∀ q ∈ shape, q.2 = 1)
    (hne : shape ≠ []) :
    M8.stratumCount (M9.rawCount n) (ClassifierBridgeFiber.Tselfloop n pr shape) N
      = ((StratumOrder1.stratumCount1 M9.realP n N (mkCell n P [shape]) : ℕ) : ℚ) := by
  show ((M9.rawCount n (ClassifierBridgeFiber.Tselfloop n pr shape) N : ℕ) : ℚ) = _
  rw [show M9.rawCount n (ClassifierBridgeFiber.Tselfloop n pr shape) N
      = Nat.card {f : QuotientBox.monicBox M9.realP N n //
          B.classify M9.realP n N f = ClassifierBridgeFiber.Tselfloop n pr shape} from rfl]
  rw [StratumOrder1.stratumCount1_eq_cellCard]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun f => classify_eq_selfloop_iff n N hN hn P hPmenu pr hsingle shape hSF hmu hne f))

/-- **`hnode_selfloop_over_Bclassify_R` (respelled, UNCONDITIONAL).**  The `h_node` limit in
`montes_allorders_of_hnode`'s shape for the respelled `Tselfloop n pr shape`, on a self-loop menu
path `pr = ((0,H),(n,0))`.  Transport `PathShape.hnode_oneSideShape` along the RESPELLED engine
identity `omCount_selfloop_eq_oneSideShape` (limit value) and `stratumCount_selfloop_R` (sequence). -/
theorem hnode_selfloop_over_Bclassify_R (n N₀ : ℕ) (hN₀ : 0 < N₀) (hn : 0 < n)
    (H : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ []) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M9.rawCount n)
          (ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) N
          / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (omCount (ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)
        M9.realP)) := by
  have hbase := PathShape.hnode_oneSideShape n N₀ hN₀
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) P hP hsingle shape hsh hpos hμ hne M9.realP
  -- rewrite the LIMIT VALUE by the respelled engine identity.
  rw [← ClassifierBridgeFiber.omCount_selfloop_eq_oneSideShape n H shape hne M9.realP] at hbase
  -- `P = [(0,H),(n,0)]` and `1 ≤ H` from the level-`N₀` menu path.
  obtain ⟨H', hPeq, hpreq, hH1', _⟩ := ClassifierBridgeFiber.menuPath_single_side hP hsingle
  have hHH' : H' = H := by
    have heq : (((0, H'), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
      have h1 : sidePairs P = [(((0, H'), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))] := by
        rw [hPeq]; rfl
      rw [hsingle] at h1
      exact (List.cons.injEq _ _ _ _ ▸ h1).1.symm
    have := congrArg (fun pr => pr.1.2) heq
    simpa using this
  subst H'
  have hH1 : 1 ≤ H := hH1'
  -- rewrite the SEQUENCE by the count identity, EVENTUALLY (for `N ≥ H+1`, so `1 ≤ H ≤ N-1`).
  refine hbase.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (H + 1)] with N hNge
  have hNpos : 0 < N := by omega
  -- build `MenuPath n N [(0,H),(n,0)]` at level N (self-loop path, `1 ≤ H ≤ N-1`).
  have hPN : MenuPath n N P := by
    rw [hPeq]
    exact ⟨H, ((n : ℕ), (0 : ℕ)), [], rfl, hH1, by omega, hn, by omega,
      ChainOK.nil rfl rfl⟩
  rw [stratumCount_selfloop_R n N hNpos hn P hPN
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) hsingle shape hsh hμ hne]

/-! ## STEP E — the first order-1 density theorem (singleton self-loop menu). -/

/-- **`montes_order1_selfloop_density` — the FIRST order-1 density theorem (UNCONDITIONAL).**  For a
single-side, all-μ=1 self-loop `pr = ((0,H),(n,0))` (menu path `P`, shape `shape`), the singleton
menu `{Tselfloop n pr shape}` density function `q' ↦ omCount (Tselfloop …) q'` is a uniform rational
function of `q'` (one `num/den`, `den` nonvanishing at every `q' > 1`), and the REAL normalized
singleton-menu counts at `realP` converge to `num(realP)/den(realP)`.

Instantiates `MontesAllOrders.montes_allorders_of_hnode` at the singleton menu, with `h_node`
discharged from `hnode_selfloop_over_Bclassify_R` on the single menu element. -/
theorem montes_order1_selfloop_density (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (N₀ : ℕ) (hN₀ : 0 < N₀) (H : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ []) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape}
            : Finset ClusterShape), omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n
              (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape} : Finset ClusterShape),
            M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) := by
  apply MontesAllOrders.montes_allorders_of_hnode n σ
    ({ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape}
      : Finset ClusterShape)
  intro T hT
  rw [Finset.mem_singleton] at hT
  subst hT
  exact hnode_selfloop_over_Bclassify_R n N₀ hN₀ hn H P hP hsingle shape hsh hpos hμ hne

end LeanUrat.OM.ClassifierBridgeFiber2
