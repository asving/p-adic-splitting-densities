/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Uniformity.ChapH.H23 — `uTwo`, the `m = 2` conservative complement

**Chapter H, NODE H.23** (`blueprint/CHAP-H_general_induction.md` §5). The `m = 2` conservative
complement, by its first-step recursion: `uTwo Q 0 = 1`, `uTwo Q 1 = 1`, and for `N ≥ 2`

`uTwo Q N = Q ^ (N − 1) + Σ_{k : 1 ≤ k, 2k ≤ N − 1} (Q − 1) * Q ^ k * uTwo Q (N − 2k)`.

Definitional, no proof obligation. DEPENDS: none.

SOURCE: `EFF.GENIND.150` (`R1.1`, verbatim: *"the first-step recursion degenerates to head + α:
`u(N) = Q^{N−1} + Σ_{k ≥ 1, 2k ≤ N−1} (Q−1)·Q^k · u(N−2k)`, `u(1) = 1` (the window-1 boundary: R3's
rider below), writing `u := u_{2,d}`, `Q := q^d`, `c(2) = 1`"*); `EFF.GENIND.45` (the general
first-step recursion this specializes).

**⚠ THE `c(2) = 1` COINCIDENCE, DECLARED** (blueprint). The α-term's coefficient is
`(Q−1)Q^{k·c(m)}` with `c(2) = 1`, so it reads `(Q−1)Q^k` — the exponent is `k`, **not** `k·c(m)`
in general. An agent extending this to `m ≥ 3` must write `Q ^ (k * clusterC m)` (H.13) and must
NOT copy the `Q ^ k`. `EFF.GENIND.150`'s own scope is `m = 2` only, because *"at `m = 2` the
recursion of S5.2 closes without β-terms"* (`m = 2 < 4` excludes CS, and a repeated linear `e = 1`
factor at `m = 2` spans the whole polygon, i.e. is α).

**Repair record [A-H.1/D1].** The committed body wrote the guard as the NON-dependent
`if 1 ≤ k ∧ 2 * k ≤ N + 1 then … else 0`, under which the well-founded-recursion goal is
`N + 2 - 2 * k < N + 2` with `k` unconstrained — false at `k = 0` — so the definition did not
elaborate. Landed here with the DEPENDENT `if h : …`, which puts `1 ≤ k` into the termination
context, plus `decreasing_by omega`. `dite` and `ite` agree on a `Decidable` proposition, so the
function's VALUES are unchanged; the twelve certified values (H.29's column, `q = 2` and `q = 3`)
are reproduced as `#guard`s below.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The conservative-undecided count of the `(2, d)` cluster system at window `N`, in `Q = q^d`
units, by `GENIND` §S5.2's first-step recursion specialized to `m = 2` (where the recursion has no
β-terms: `m = 2 < 4` excludes CS, and a repeated linear `e = 1` factor at `m = 2` spans the whole
polygon, i.e. is α). -/
def uTwo (Q : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (N + 2) => Q ^ (N + 1) +
      ∑ k ∈ Finset.range (N + 2),
        if h : 1 ≤ k ∧ 2 * k ≤ N + 1 then (Q - 1) * Q ^ k * uTwo Q (N + 2 - 2 * k) else 0
  decreasing_by omega

end Uniformity.Density.Induction

/-! ## Numeric gate — the twelve certified values (H.29's column, both primes).
`#guard` fails elaboration if the proposition evaluates to `false`, so this block is a build-time
gate on the recursion, not a print-out. Both `q = 2` and `q = 3` are mandatory here: at `Q = 2` the
letter factor `(Q − 1) = 1` vanishes and `Q ^ k` versus `Q ^ (k · c(m))` coincide at `m = 2`, so a
`q = 2`-only audit cannot see a missing or spurious factor (the chapter's G.23 lesson). -/

section NumericGate

open Uniformity.Density.Induction

#guard uTwo 2 1 == 1
#guard uTwo 2 2 == 2
#guard uTwo 2 3 == 6
#guard uTwo 2 4 == 12
#guard uTwo 2 5 == 32
#guard uTwo 2 6 == 64

#guard uTwo 3 1 == 1
#guard uTwo 3 2 == 3
#guard uTwo 3 3 == 15
#guard uTwo 3 4 == 45
#guard uTwo 3 5 == 189
#guard uTwo 3 6 == 567

/-! The two columns in list form, as a single check each. (`decide` cannot close these: `uTwo` is
compiled by well-founded recursion, so its equations are not kernel-definitional — `#guard`'s
evaluator is what certifies the values here, and H.29 proves them as theorems.) -/
#guard [uTwo 2 1, uTwo 2 2, uTwo 2 3, uTwo 2 4, uTwo 2 5, uTwo 2 6] == [1, 2, 6, 12, 32, 64]

#guard [uTwo 3 1, uTwo 3 2, uTwo 3 3, uTwo 3 4, uTwo 3 5, uTwo 3 6] == [1, 3, 15, 45, 189, 567]

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo

end AxCheck
