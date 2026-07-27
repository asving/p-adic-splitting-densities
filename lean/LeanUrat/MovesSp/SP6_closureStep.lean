/-
Unit Sp.n3closureStep [REV 4, Codex-6 — Bool-routed via List.contains] —
moves_ref: "the (G5) closure from the root stage (1,1,3) generates exactly the
five displayed stage groups … nothing further from Q2/Q3; W = 1 terminal by (G6)".
sketch: decide (≈53 × |enum3| succStepB evals — THE perf hotspot; pre-split into
5 per-group units if needed, blueprint §1.6). difficulty: medium (perf).

PROOF NOTE (F-phase): the `speciesEnum` generator routes through `compEnum` /
`lamEnumAux`, which are WELL-FOUNDED recursive (`decreasing_by`), so `WellFounded.fix`
does NOT reduce in the kernel — plain `decide`/`rfl` gets stuck on `speciesEnum 3`
(the pre-rebase oleans predate this and are stale). We restore reducibility with
STRUCTURAL fuel surrogates `compEnumF` / `lamEnumAuxF`, proved equal to the originals,
then rewrite them in and `decide`. Two further perf facts drove the shape below:
  (1) `decide` re-reduces the 567-element enum once per outer catalogue letter, so the
      outer loop is discharged letterwise via `List.all_eq_true` + `fin_cases`.
  (2) the derived `DecidableEq Species` STICKS in `whnf` when comparing two equal
      Species whose `lam : Multiset` differ only by list-order permutation. The
      catalogue writes the two 2-element residual partitions in DESCENDING order
      (`{(1,2),(1,1)}`, `{(2,1),(1,1)}`) whereas the generator emits them ASCENDING;
      `contains` then needs exactly that stuck comparison. We pre-reorder the catalogue's
      two literals to the generator's canonical order (`r1`,`r2`, equal as multisets),
      after which `contains` compares identical representatives and reduces.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-! ### Structural (fuel-driven) surrogates for the two well-founded generators.

`compEnum`/`lamEnumAux` recurse on non-structural arguments, so their kernel
`WellFounded.fix` form does not reduce under `decide`. `compEnumF`/`lamEnumAuxF`
recurse structurally on an explicit fuel argument and DO reduce; the `_eqF` lemmas
show they agree with the originals when the fuel is at least the recursion argument
(taking fuel = argument gives the unconditional rewrite used below). -/

private def compEnumF : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | f + 1, n + 1 =>
      (List.range (n + 1)).flatMap fun k => (compEnumF f (n - k)).map fun c => (k + 1) :: c

private theorem compEnumF_eq : ∀ f n, n ≤ f → compEnum n = compEnumF f n := by
  intro f
  induction f with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [compEnum, compEnumF]
  | succ f ih =>
    intro n hn
    match n with
    | 0 => simp only [compEnum, compEnumF]
    | m + 1 =>
      simp only [compEnum, compEnumF]
      congr 1
      funext k
      rw [ih (m - k) (by omega)]

private theorem compEnum_eqF (n : ℕ) : compEnum n = compEnumF n n := compEnumF_eq n n (le_refl n)

private def lamEnumAuxF (bound : ℕ) : ℕ → ℕ → ℕ → List (List (ℕ × ℕ))
  | _, 0, _ => [[]]
  | 0, _ + 1, _ => []
  | f + 1, w + 1, lo =>
      ((List.range (bound * bound)).drop lo).flatMap fun k =>
        let g := k / bound + 1
        let μ := k % bound + 1
        if g * μ ≤ w + 1 then (lamEnumAuxF bound f (w + 1 - g * μ) k).map fun l => (g, μ) :: l
        else []

private theorem lamEnumAuxF_eq : ∀ f bound w lo, w ≤ f →
    lamEnumAux bound w lo = lamEnumAuxF bound f w lo := by
  intro f
  induction f with
  | zero =>
    intro bound w lo hn
    obtain rfl : w = 0 := by omega
    simp only [lamEnumAux, lamEnumAuxF]
  | succ f ih =>
    intro bound w lo hn
    match w with
    | 0 => simp only [lamEnumAux, lamEnumAuxF]
    | w + 1 =>
      simp only [lamEnumAux, lamEnumAuxF]
      congr 1
      funext k
      have hpos : 0 < (k / bound + 1) * (k % bound + 1) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      split
      · rw [ih bound (w + 1 - (k / bound + 1) * (k % bound + 1)) k (by omega)]
      · rfl

private theorem lamEnumAux_eqF (bound w lo : ℕ) :
    lamEnumAux bound w lo = lamEnumAuxF bound w w lo :=
  lamEnumAuxF_eq w bound w lo (le_refl w)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem closure_step3 : (catalogue3.all fun s => (speciesEnum 3).all fun s' =>
    !(succStepB 3 s s') || catalogue3.contains s') = true := by
  -- reorder the catalogue's two 2-element partitions to the generator's canonical
  -- (ascending) representative, so `contains` never needs a permuted-multiset compare
  have r1 : ({(1, 2), (1, 1)} : Multiset (ℕ × ℕ)) = {(1, 1), (1, 2)} := by decide
  have r2 : ({(2, 1), (1, 1)} : Multiset (ℕ × ℕ)) = {(1, 1), (2, 1)} := by decide
  rw [List.all_eq_true]
  intro s hs
  -- discharge the outer loop letterwise (avoids re-reducing the 567-element enum
  -- 53 times), rewriting the well-founded generators to their structural surrogates
  fin_cases hs <;>
    (simp only [speciesEnum, compEnum_eqF, lamEnumAux_eqF, catalogue3, groupR, groupQ3,
      groupQ2, groupQ1, groupI, List.map_cons, List.map_nil, r1, r2]; decide)

end LeanUrat.MovesSp
