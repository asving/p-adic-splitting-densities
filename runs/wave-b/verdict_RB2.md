# Verdict — unit RB2 (Chapter C, READY batch 2 from `verdict_CCUR.md`)

Deliverable: `leanfinal/Uniformity/ChapC/C150rb2.lean` (only new file written by this unit).

Batch-2 assignment (`runs/wave-b/verdict_CCUR.md`, "Ranked READY batches" §, batch 2 — "pure
arithmetic, zero chapter-C vocabulary"): `window_consultation` (C.58),
`level3_dead_at_mult2_three` (C.49), `tower_termination_instance` (C.49), `gentow5_selffeed`
(C.91). Three landed verbatim; the fourth is a genuine refutation, not a wiring nit — see below.

## `window_consultation` (C.58) — **LANDED**

`(d N m w : ℕ) (hd : 0 < d) (hw : w < d) (hm : m < d*N) (hcong : m%d = w%d) : m ≤ d*(N-1)+w`.
Proved via the toolchain's documented mixed-mod/div workaround (pre-reduce before `omega`):
`w%d = w` (`Nat.mod_eq_of_lt`), hence `m%d = w`; then bound `m/d < N` by contradiction
(`Nat.mul_le_mul_left` monotonicity + `omega` on the `Nat.div_add_mod` identity, since `omega`
cannot itself multiply a variable modulus), giving `m/d ≤ N-1` and
`d*(m/d) ≤ d*(N-1)`, closed by `omega`. Signature verified byte-identical to
`leanspec/Leanspec/ChapC.lean:2215-2216`.

## `level3_dead_at_mult2_three` (C.49) — **LANDED**

`(mr ℓ₃ d₃ L μ₂ : ℕ) (hμ : μ₂=3) (hm : 2≤mr) (hjump : 2≤ℓ₃*d₃) (hL : mr*(ℓ₃*d₃)≤L)
(hLμ : L≤μ₂) : False`. The one nonlinear step (`omega` cannot multiply two hypotheses) is
supplied explicitly: `Nat.mul_le_mul hm hjump : 2*2 ≤ mr*(ℓ₃*d₃)`; from there `4 ≤ mr*(ℓ₃*d₃) ≤
L ≤ μ₂ = 3` is a linear contradiction, closed by `omega`. Signature verified byte-identical to
`leanspec/Leanspec/ChapC.lean:2418-2419`.

## `tower_termination_instance` (C.49) — **LANDED**

`(J : ℕ) (a : Fin (J+1) → ℕ) (ha0 : a 0 ≤ 6) (hfloor : ∀ j, 4 ≤ a j)
(hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) : J = 0`. By contradiction: if `J ≠ 0` there
is an index `j0 = ⟨0, _⟩ : Fin J`; `hdrop j0` plus `Fin.castSucc j0 = (0 : Fin (J+1))`
(`Fin.ext` + `simp`) gives `2 * a j0.succ ≤ a 0 ≤ 6`, while `hfloor j0.succ` gives `4 ≤ a
j0.succ`, so `8 ≤ 2 * a j0.succ ≤ 6` — `omega` closes. Signature verified byte-identical to
`leanspec/Leanspec/ChapC.lean:2421-2422`.

## `gentow5_selffeed` (C.91) — **NAKED FORM REFUTED**; repaired form landed as `_resigned`

The leanspec axiom (`ChapC.lean:3888-3891`, `blueprint/CHAP-C_tower_grammar.md` NODE C.91) is:

```
axiom gentow5_selffeed (P : ℕ → ℕ∞) (μ E : ℕ) (hμ : 0 < μ)
    (hpins : ∀ j < μ, (((μ - j) * E + 1 : ℕ) : ℕ∞) ≤ P j) (htop : P μ = (0 : ℕ∞))
    {u ℓ j : ℕ} (hℓ : 0 < ℓ) (hside : hOnSide P μ u ℓ j) :
    ℓ * E < u
```

**This is false as stated**, independent of the FGMNCalculus content the blueprint attaches to
it, because it never restricts `j` to be an interior index (`j < μ`). At `j = μ`, `hOnSide`
degenerates: taking `u = 0` makes the endpoint objective `ℓ • P μ + u*μ = 0` (via `htop`)
automatically equal to `hSupp` (every other term is `≥ 0`), so `hside` holds for *any* `P`
satisfying `hpins`/`htop`, any `μ,E,ℓ`. The conclusion then demands `ℓ*E < 0`, impossible in
`ℕ`. `gentow5_selffeed_false` proves `¬ Gentow5SelffeedStatement` (`Gentow5SelffeedStatement`
being the axiom's exact `Prop`, so the refutation names what it refutes) via the smallest
instance: `μ=1, E=0, P = (fun | 0 => 1 | _ => 0), u=0, ℓ=1, j=1`.

The content the blueprint's own PROOF field describes ("two-line convexity + floor-chain
telescoping", "the induction feeds itself" at *every interior side*) is exactly the `j < μ`
case, which is true and is what `gentow5_selffeed_resigned` proves (same conclusion, one
restored hypothesis `hj : j < μ`): `hSupp ≤ ℓ•P μ + u*μ = u*μ` (μ is always in the support
range, `htop`) combined with `hside`'s exact value at `j` gives `ℓ*P j + u*j ≤ u*μ`; casting `P
j` to its finite value `m` (`hside.2`/`ENat.ne_top_iff_exists`, the same pattern `C98.lean`
uses) and setting `d := μ - j > 0`, this is `ℓ*m ≤ u*d` after cancelling `u*j`; `hpins`'s floor
`d*E+1 ≤ m` gives `ℓ*d*E + ℓ ≤ u*d`; if `u ≤ ℓ*E` this forces `ℓ*d*E+ℓ ≤ u*d ≤ ℓ*E*d = ℓ*d*E`,
contradicting `ℓ > 0` — hence `ℓ*E < u`.

Per this repo's standing statement-change authority (honest repairs proceed without per-item
sign-off; no fake axioms, no contradictions introduced), this is the same-shape repair already
established for `blockDeg_eq`/`towerLocus_fibration` (`C64.lean`, `C53b.lean`, unit RB1): the
naked name is refuted under its own name; the true content is landed under a `_resigned` name
with the missing hypothesis restored. **No declaration under the exact name `gentow5_selffeed`
is added** — landing one would require either an unsafe proof of a false statement or silently
weakening the signature, both disallowed.

## Verification

```sh
cd leanfinal
lake env lean Uniformity/ChapC/C150rb2.lean
# 0 errors, 0 sorry; 4 harmless linter warnings (2x deprecated-`push_neg` notices, and `hd`/`hμ`
# unused-variable notices — both binders are part of the frozen signed signatures and are
# genuinely redundant given the other hypotheses, kept for byte-fidelity); exit 0.
```

`#print axioms` footprint (AxCheck footer, also run inline by `lake env lean`):

```
Uniformity.Density.Tower.window_consultation           : [propext, Quot.sound]
Uniformity.Density.Tower.level3_dead_at_mult2_three    : [propext, Quot.sound]
Uniformity.Density.Tower.tower_termination_instance    : [propext, Quot.sound]
Uniformity.Density.Tower.Gentow5SelffeedStatement      : [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.gentow5_selffeed_false        : [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.gentow5_selffeed_resigned     : [propext, Classical.choice, Quot.sound]
```

Lean core only for every declaration (`Classical.choice` appears only because `ℕ∞ =
Uniformity.Density.Tower.ℕ∞`'s `ENat.ne_top_iff_exists`/`Finset.inf` machinery pull it in — same
as `C98.lean`'s own footprint — not a cite of any kind).

No file other than `leanfinal/Uniformity/ChapC/C150rb2.lean` and this verdict was created or
modified by this unit. `leanspec/`, roll-ups, and sibling units' files were read-only
referenced (`C98.lean` for `hSupp`/`hOnSide`, `C64.lean`/`C53b.lean` for the `_resigned`-family
precedent), never edited.
