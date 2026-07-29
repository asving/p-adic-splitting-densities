/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D12 `packages_rekey` — the S-9 packages DECLARED VERBATIM from MovesS §W4-SYNC
(the contract's own field rosters), every [3t] field a NAMED §2.10 DEF with a
displayed body. DECLARATION-SITE WARRANT: the MovesS contract's own preamble assigns
the re-key here. NS_NULL RIDER (binding wherever `ns_null` is consumed): the field's
value is the FINITE-LEVEL statement ∧ the two OPEN owner legs of the REV-9 three-way
split; the note's profinite μ-claim is NOT stated in Lean. PROVED-BY-CONSTRUCTION
(definitional — the E-phase prove-now set's D12 row; zero sorry). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

structure XRBPackage where
  xhd_w : Prop
  xhd_u : Prop
  xhd_d : Prop
  xhd_s : Prop
  jc_inv : Prop
  sib : Prop
  jc_multi : Prop
  tb_cap : Prop
  vp : Prop
  rel2_a : Prop
  rel2_b : Prop
  rel2_d : Prop
  ns_null : Prop

structure RS1GivenPackage where
  tree_exp_fin : Prop
  tree_exp_ns : Prop
  tree_n : Prop
  one_f : Prop
  sib : Prop
  tb_cap : Prop
  vp : Prop
  pci : Prop
  rel2_a : Prop
  rel2_b : Prop
  rel2_c : Prop
  rel2_d : Prop
  rel2_e : Prop

structure Wsh17Package where
  c15_volumes : Prop
  cts_counts : Prop
  sib_count : Prop

/-- the RS.1 GIVEN package at the MovesT values (REV 5: the vp leg TOWER-KEYED;
REV 8: the FULL W4-1 interface rides). -/
def rs1GivenOfMovesT (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    {N₀ : ℕ} (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (CAat : ∀ N' h,
      CellAssign p F n N' (n * N') pol (Tat N' h) (χat N') trackOf)
    (rel2_a rel2_b rel2_c rel2_d rel2_e : Prop) : RS1GivenPackage :=
  { tree_exp_fin := TreeExpFin T χ trackOf CA,
    tree_exp_ns := TreeExpNs (n := n) pol,
    tree_n := TreeNStmt (n := n) pol,
    one_f := OneFStmt T χ,
    sib := SibCount T CA.toCellData χ,
    tb_cap := TBCapPinned (n := n) pol m ∧ NsAmendedPair (n := n) pol,
    vp := VPPinned pol Tat χat trackOf CAat,
    pci := PCI T CA.toCellData χ,
    rel2_a := rel2_a, rel2_b := rel2_b, rel2_c := rel2_c,
    rel2_d := rel2_d, rel2_e := rel2_e }

/-- the contract's premise row. -/
def RS1GivenHolds (Pi' : RS1GivenPackage) : Prop :=
  Pi'.tree_exp_fin ∧ Pi'.tree_exp_ns ∧ Pi'.tree_n ∧ Pi'.one_f ∧ Pi'.sib ∧
  Pi'.tb_cap ∧ Pi'.vp ∧ Pi'.pci ∧
  Pi'.rel2_a ∧ Pi'.rel2_b ∧ Pi'.rel2_c ∧ Pi'.rel2_d ∧ Pi'.rel2_e

/-- the XRB package at the MovesT values. REV 9 (T1): `ns_null` carries the (ns) pair
AT ITS FINITE FACE ∧ the two OPEN owner legs (`NsPricing`/`NsGrowth`) of the
three-way split; the analysis leg `nsNull_of_pricing_growth` is the corpus's own
theorem (Defs §2.10). -/
def xrbOfMovesT (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    {N₀ : ℕ} (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (CAat : ∀ N' h,
      CellAssign p F n N' (n * N') pol (Tat N' h) (χat N') trackOf)
    (xhd_w xhd_u xhd_d xhd_s jc_inv rel2_a rel2_b rel2_d : Prop) : XRBPackage :=
  { sib := SibCount T CA.toCellData χ,
    -- [T RATIFICATION 2026-07-31: exact-cell keying — the JC-multi row prices the
    --  site's EXACT cell event (`siteCellEvent (parentSt H) (cellAt H)`, the side
    --  split's own cell), per verdict §2.]
    jc_multi := (∀ (Tr : VTree p F) (L : SiteLedger Tr T CA.toCellData χ),
      ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ L) (h2 : 2 ≤ L.sides H),
        JCmultiAt T CA.toCellData χ (L.parentSt H)
          (L.splitAt H hH.1 h2)),
    tb_cap := TBCapPinned (n := n) pol m ∧ NsAmendedPair (n := n) pol,
    vp := VPPinned pol Tat χat trackOf CAat,
    ns_null := NsAmendedPair (n := n) pol ∧ NsPricing (n := n) pol ∧
      NsGrowth (n := n) pol,
    xhd_w := xhd_w, xhd_u := xhd_u, xhd_d := xhd_d, xhd_s := xhd_s,
    jc_inv := jc_inv, rel2_a := rel2_a, rel2_b := rel2_b, rel2_d := rel2_d }

/-- the Wsh17 package (S-8): `sib_count` = the DEFINED `SibCountShallow` statement. -/
def wsh17OfMovesT (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (c15 cts : Prop) : Wsh17Package :=
  { c15_volumes := c15, cts_counts := cts, sib_count := SibCountShallow T CA χ }

/-- the W1m addendum's premise row, TYPED (REV 4: the REAL imported
`MovesS.LedgerIV`). -/
def w1mObligation {n' : ℕ} (T' : MovesS.TableShape n') (M : MovesS.MeasuredSide T')
    (Pi' : RS1GivenPackage) (concl : Prop) : Prop :=
  RS1GivenHolds Pi' → MovesS.LedgerIV T' M → concl

end LeanUrat.MovesT
