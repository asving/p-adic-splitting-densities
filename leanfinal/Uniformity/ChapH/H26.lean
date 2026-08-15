/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H25

/-!
# Uniformity.ChapH.H26 — THE CLOSED FORM of the `m = 2` conservative complement

**Chapter H, NODE H.26** (`blueprint/CHAP-H_general_induction.md` §5). The `m = 2` conservative
complement `uTwo` (H.23), which is *defined* by its first-step recursion, is computed in closed
form: for `2 ≤ Q` and `M ≥ 2`

`uTwo Q M = Q^(M−1) + ⌊(M−1)/2⌋ · (Q−1) · Q^(M−2)`

(`ℕ` division is exactly the corpus's `⌊(M−1)/2⌋`), together with the two parity forms the corpus
also displays, stated subtraction-free:

* `uTwo_even` : `uTwo Q (2ℓ) + (ℓ−1)·Q^(2ℓ−2) = ℓ·Q^(2ℓ−1)` for `ℓ ≥ 1`, i.e.
  `u(2ℓ) = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}`;
* `uTwo_odd` : `uTwo Q (2ℓ+1) + ℓ·Q^(2ℓ−1) = (ℓ+1)·Q^(2ℓ)` for every `ℓ` (including `ℓ = 0`, where
  it is H.24's window-1 boundary `u(1) = 1`), i.e. `u(2ℓ+1) = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}`.

DEPENDS: H.23 (`uTwo`), H.24 (`uTwo_one`, `uTwo_two` — the two bases), H.25 (`uTwo_rec`, the
telescoped recursion that drives the two-step induction).

SOURCE: `EFF.GENIND.150`, verbatim: *"iterating from `u(1) = 1`, `u(2) = Q` gives the CLOSED FORMS
`u(2ℓ) = ℓ·Q^{2ℓ−1} − (ℓ−1)·Q^{2ℓ−2}`, `u(2ℓ+1) = (ℓ+1)·Q^{2ℓ} − ℓ·Q^{2ℓ−1}`, equivalently
`u(M) = Q^{M−1} + ⌊(M−1)/2⌋·(Q−1)·Q^{M−2}` — which is LETTER-FOR-LETTER the committed `R(M)`
displayed inside `THEOREM HEX3.A`"*.

## The proof, as transcribed

Strong induction on the window in steps of two, on the shifted statement
`uTwo Q (m+2) = Q^(m+1) + ⌊(m+1)/2⌋·((Q−1)·Q^m)` (the private `uTwo_closed_aux`, which needs no
`2 ≤ M` side condition because the shift carries it):

* `m = 0` is H.24's `uTwo Q 2 = Q`, since `⌊1/2⌋ = 0`;
* `m = 1` is H.25's recursion at `N = 3` fed by H.24's `uTwo Q 1 = 1`: `u(3) + Q = Q² + Q²`, and
  the target `Q² + 1·(Q−1)Q` satisfies `(Q² + (Q−1)Q) + Q = Q² + Q²`, so the two agree by
  cancelling `Q` — the only place `2 ≤ Q` is used, via `Q = q + 1`;
* `m + 2` uses H.25 at `N = m+4` and the induction hypothesis at `m`: `u(m+4) + Q^{m+2} =
  Q^{m+3} + Q²·u(m+2)`, and `⌊(m+3)/2⌋ = ⌊(m+1)/2⌋ + 1` (`omega`), after which both sides differ
  by the single `ℕ`-cancellable summand `Q^{m+2}` and `ring` closes.

Every step is additive: no `ℕ`-subtraction is introduced anywhere, and the letter factor `Q − 1`
is eliminated at the start of each computation by `obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1`.

**⚠ THE `R(M)` TIE IS A CROSS-CHAPTER CHECK, NOT A DEPENDENCY** (blueprint's ⚠ block, carried
forward). `EFF.GENIND.150` claims this closed form is letter-for-letter W-11's `R(M)` as displayed
inside `THEOREM HEX3.A`, machine-checked at `M = 1..14` (leg B). Chapter G lands `hex3R` and
`hex3R_rec` (`ChapG/G64.lean`, `ChapG/G65.lean`) — **the `n = 3` `R`-recursion, a different
object**. This file therefore does NOT import chapter G and does NOT wire `uTwo` to `hex3R`: the
corpus's tie is at the *value* level for the `m = 2` cluster, whereas chapter G's `hex3R` is
HEX3's `R(M)` inside the `n = 3` telescope. A generated DAG edge `BP.H.26 → BP.G.65` exists only
because H.26's fidelity note cites `G65.lean`; it must be read as *"H.26 was checked against
`BP.G.65` and found distinct"* (§16 item 6). The proof below is self-contained in chapter H
(H.23–H.25), so no chapter-G statement can be upgraded through it.

**ARITHMETIC AUDIT (blueprint, reproduced).** `Q = 2`: `M=2 → 2 + 0 = 2`; `M=3 → 4 + 1·1·2 = 6`;
`M=4 → 8 + 1·1·4 = 12`; `M=5 → 16 + 2·1·8 = 32`; `M=6 → 32 + 2·1·16 = 64`. `Q = 3`:
`M=2 → 3`; `M=3 → 9 + 1·2·3 = 15`; `M=4 → 27 + 1·2·9 = 45`; `M=5 → 81 + 2·2·27 = 189`;
`M=6 → 243 + 2·2·81 = 567`. Ten cells, two values of `Q`, all matching H.23's certified column;
the parity form at `Q = 3, ℓ = 3` reads `3·3^5 − 2·3^4 = 729 − 162 = 567` ✓. The `#guard` block
below runs all three statements at `Q ∈ {2,3,4,9}` out to `M = 9`; **`Q = 3` is the mandatory
column**, since at `Q = 2` the letter factor `(Q − 1) = 1` is invisible.

TEETH: `EFF.GENIND.150`'s machine legs A and B (the symbolic solve of the recursion at
`N = 2..14`, and the `R(M)` equality at `M = 1..14`) → **Lean theorem** (this file), at every `N`
and every `Q ≥ 2`. Those two legs are the corpus's only evidence for the closed form; this node
replaces them with a proof.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The closed form in shifted coordinates (`M = m + 2`), which is the shape the two-step
induction runs in: no `2 ≤ M` hypothesis and no `ℕ`-subtraction in the exponents. Private: H.26's
signed contract is `uTwo_closed` below. -/
private lemma uTwo_closed_aux (Q : ℕ) (hQ : 2 ≤ Q) (m : ℕ) :
    uTwo Q (m + 2) = Q ^ (m + 1) + ((m + 1) / 2) * ((Q - 1) * Q ^ m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ =>
      -- `⌊1/2⌋ = 0`, so the claim is H.24's `uTwo Q 2 = Q`.
      simpa using uTwo_two Q
    | 1, _ =>
      -- H.25 at `N = 3`, fed by H.24's window-1 boundary `uTwo Q 1 = 1`.
      have hrec := uTwo_rec Q hQ (N := 3) (by omega)
      rw [show (3 : ℕ) - 2 = 1 from by omega, show (3 : ℕ) - 1 = 2 from by omega, uTwo_one,
        mul_one] at hrec
      obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
      have hsplit : (q + 1) ^ 2 + (q + 1) ^ 2
          = ((q + 1) ^ (1 + 1) + ((1 + 1) / 2) * ((q + 1 - 1) * (q + 1) ^ 1)) + (q + 1) ^ 1 := by
        simp only [Nat.add_sub_cancel]
        norm_num
        ring
      exact Nat.add_right_cancel (hrec.trans hsplit)
    | (m + 2), ih =>
      -- H.25 at `N = m + 4`, with the induction hypothesis at the window `m + 2`.
      have ihm := ih m (by omega)
      have hrec := uTwo_rec Q hQ (N := m + 4) (by omega)
      rw [show m + 4 - 2 = m + 2 from by omega, show m + 4 - 1 = m + 3 from by omega,
        show m + 4 = m + 2 + 2 from by omega, ihm] at hrec
      have hdiv : (m + 2 + 1) / 2 = (m + 1) / 2 + 1 := by omega
      obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
      rw [hdiv]
      simp only [Nat.add_sub_cancel] at hrec ⊢
      refine Nat.add_right_cancel (m := (q + 1) ^ (m + 2)) ?_
      rw [hrec]
      ring

/-- **NODE H.26, THE CLOSED FORM.** For `2 ≤ Q` and `M ≥ 2`,
`uTwo Q M = Q^(M−1) + ⌊(M−1)/2⌋ · ((Q−1) · Q^(M−2))` — `EFF.GENIND.150`'s `u(M)`, proved at every
window rather than checked at `M = 2..14`. -/
theorem uTwo_closed (Q : ℕ) (hQ : 2 ≤ Q) {M : ℕ} (hM : 2 ≤ M) :
    uTwo Q M = Q ^ (M - 1) + ((M - 1) / 2) * ((Q - 1) * Q ^ (M - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]
  exact uTwo_closed_aux Q hQ m

/-- **NODE H.26, the even parity form.** `u(2ℓ) = ℓ·Q^{2ℓ−1} − (ℓ−1)·Q^{2ℓ−2}` for `ℓ ≥ 1`, in
the subtraction-free form `uTwo Q (2ℓ) + (ℓ−1)·Q^(2ℓ−2) = ℓ·Q^(2ℓ−1)`. -/
theorem uTwo_even (Q : ℕ) (hQ : 2 ≤ Q) {l : ℕ} (hl : 1 ≤ l) :
    uTwo Q (2 * l) + (l - 1) * Q ^ (2 * l - 2) = l * Q ^ (2 * l - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  have hclosed := uTwo_closed Q hQ (M := 2 * (j + 1)) (by omega)
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 from by omega,
    show 2 * (j + 1) - 2 = 2 * j from by omega, show (2 * j + 1) / 2 = j from by omega] at hclosed
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 from by omega,
    show 2 * (j + 1) - 2 = 2 * j from by omega, show j + 1 - 1 = j from by omega, hclosed]
  obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  rw [show (2 : ℕ) * j + 1 = 2 * j + 1 from rfl, pow_succ]
  simp only [Nat.add_sub_cancel]
  ring

/-- **NODE H.26, the odd parity form.** `u(2ℓ+1) = (ℓ+1)·Q^{2ℓ} − ℓ·Q^{2ℓ−1}`, in the
subtraction-free form `uTwo Q (2ℓ+1) + ℓ·Q^(2ℓ−1) = (ℓ+1)·Q^(2ℓ)`. Holds at `ℓ = 0` too, where
it is H.24's window-1 boundary `uTwo Q 1 = 1` (`EFF.GENIND.160`'s two-way coherence check). -/
theorem uTwo_odd (Q : ℕ) (hQ : 2 ≤ Q) (l : ℕ) :
    uTwo Q (2 * l + 1) + l * Q ^ (2 * l - 1) = (l + 1) * Q ^ (2 * l) := by
  match l with
  | 0 => simpa using uTwo_one Q
  | (j + 1) =>
    have hclosed := uTwo_closed Q hQ (M := 2 * (j + 1) + 1) (by omega)
    rw [show 2 * (j + 1) + 1 - 1 = 2 * j + 2 from by omega,
      show 2 * (j + 1) + 1 - 2 = 2 * j + 1 from by omega,
      show (2 * j + 2) / 2 = j + 1 from by omega] at hclosed
    rw [hclosed, show 2 * (j + 1) - 1 = 2 * j + 1 from by omega,
      show 2 * (j + 1) = 2 * j + 2 from by omega]
    obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
    rw [show 2 * j + 2 = (2 * j + 1) + 1 from by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring

end Uniformity.Density.Induction

/-! ## Numeric gate — the closed form and both parity forms, at four values of `Q`.
`#guard` fails elaboration when the proposition evaluates to `false`, so this block is a
build-time regression against H.23's recursion (the values are H.29's certified column). Both
`q = 2` and `q = 3` are mandatory: at `Q = 2` the letter factor `(Q − 1) = 1` is invisible, so a
`q = 2`-only audit cannot see a missing or spurious factor (the chapter's G.23 lesson). The
prime powers `Q = 4, 9` are the intended `Q = q^d` reading. -/

section NumericGate

open Uniformity.Density.Induction

/-! The closed form at `M = 2, …, 9`. -/
#guard [2, 3, 4, 9].all fun Q => [2, 3, 4, 5, 6, 7, 8, 9].all fun M =>
  uTwo Q M == Q ^ (M - 1) + ((M - 1) / 2) * ((Q - 1) * Q ^ (M - 2))

/-! The even parity form at `ℓ = 1, …, 4` (windows `2, 4, 6, 8`). -/
#guard [2, 3, 4, 9].all fun Q => [1, 2, 3, 4].all fun l =>
  uTwo Q (2 * l) + (l - 1) * Q ^ (2 * l - 2) == l * Q ^ (2 * l - 1)

/-! The odd parity form at `ℓ = 0, …, 4` (windows `1, 3, 5, 7, 9`); `ℓ = 0` is the window-1
boundary. -/
#guard [2, 3, 4, 9].all fun Q => [0, 1, 2, 3, 4].all fun l =>
  uTwo Q (2 * l + 1) + l * Q ^ (2 * l - 1) == (l + 1) * Q ^ (2 * l)

/-! The blueprint's ten audited cells, spelled out: `Q = 2` and `Q = 3` at `M = 2, …, 6`. -/
#guard [uTwo 2 2, uTwo 2 3, uTwo 2 4, uTwo 2 5, uTwo 2 6] == [2, 6, 12, 32, 64]

#guard [uTwo 3 2, uTwo 3 3, uTwo 3 4, uTwo 3 5, uTwo 3 6] == [3, 15, 45, 189, 567]

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo_closed
#print axioms Uniformity.Density.Induction.uTwo_even
#print axioms Uniformity.Density.Induction.uTwo_odd

end AxCheck
