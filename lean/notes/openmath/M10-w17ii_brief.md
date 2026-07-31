# M10-w17ii — Problem brief: the height-sum census law (W17ii clause (ii))

**Target obligation:** the single `sorry` at
`lean/LeanUrat/MovesV/V7_w17ii.lean:48` — clause (ii) of the theorem
`w17ii_wave4`, to be proved at the *repaired* field roster described in §4
(the field repair is landing concurrently; this brief states both the current
roster and the repair spec). Date: 2026-07-31.

This brief is self-contained. It re-expands every project-internal name; the
reader is assumed to know p-adic fields, Newton polygons, Okutsu–Montes theory
and Igusa zeta functions, but nothing about this repository.

---

## 1. The Lean obligation (normative form)

The theorem carrying the obligation (`lean/LeanUrat/MovesV/V7_w17ii.lean`):

```lean
theorem w17ii_wave4 {n : ℕ} {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) :
    W17ii T M F C.WshP C.WshVal C.shDom C.shWeightH
```

with (`lean/LeanUrat/MovesS/Interfaces.lean:111`):

```lean
def W17ii (T : TableShape n) (M : MeasuredSide T) (F : ShapeFam T)
    (WshP : Shape T → PolyGeom) (WshVal : Shape T → ℚ → ℝ)
    (shDom : Shape T → Set M.Hgt) (shWeightH : Shape T → M.Hgt → ℚ → ℝ) : Prop :=
  ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools,
    (∃ hok : (WshP Ŝ).val ∈ OKat q₀,
      ((evalAt q₀ ⟨(WshP Ŝ).val, hok⟩ : ℚ) : ℝ) = WshVal Ŝ q₀) ∧
    HasSum (fun h : shDom Ŝ => shWeightH Ŝ (↑h) q₀) (WshVal Ŝ q₀)
```

Clause (i) — the first conjunct — is already proved (it is definitional at the
structure's own fields). **The obligation is exactly the second conjunct, the
`HasSum`, for EVERY instance `C` of the structure `RS4Chain`** (a ∀-statement
over instances, not a statement about one intended model), after the repair of
§4 adjoins new fields to `RS4Chain`. The projection
`RS4Chain.wsh17_pin C := W17ii T M F C.WshP C.WshVal C.shDom C.shWeightH`
is the form consumed downstream; it is byte-identical content.

---

## 2. Standard-mathematics translation

Everything in `RS4Chain` that interacts with the goal is listed here; this
list was verified complete against the source (no other field of the
structure, or of the structures it extends, mentions the six carriers
appearing in the goal). The rest of the structure — transition-matrix
hypotheses, rational-function solves, a measured family of conditional
subtree values — is irrelevant to clause (ii) but must still be *inhabitable*
alongside any countermodel data (see §5 for what is known there).

### 2.1 Counting frame

Fixed ambient data (from the structure `MeasuredSide`):

- A set 𝒫 ⊆ ℚ of **pools**: every q₀ ∈ 𝒫 is of the form q₀ = p^δ with p
  prime, δ ≥ 1; 𝒫 is infinite and closed under q₀ ↦ q₀^δ (δ ≥ 1).
  (Intended, non-normative reading: evaluation points "residue-field size" for
  splitting-density rational functions.)
- For every pool q₀ and **level** N ∈ ℕ: a nonempty finite set Box(q₀, N)
  (Lean `M.Box q₀ N` with `Fintype` and `Nonempty` instances). Write
  b(N) := #Box(q₀, N) ≥ 1 (q₀ fixed and suppressed).
  **No other law constrains Box**: the cardinalities are arbitrary, and there
  are no maps or compatibilities between different levels or pools.
  (Intended reading: a level-N approximation space, e.g. coefficient tuples
  mod p^N; events are subsets of it; densities are event-proportions.)
- A type ℋ of **heights** (Lean `M.Hgt`): a completely arbitrary type — no
  order, no topology, no arithmetic.
  (Intended reading: valuation parameters indexing depth-h strata of a
  splitting event, e.g. discriminant/resolvent valuations.)

### 2.2 Shape-census data

A finite family 𝔉 of **shapes** (Lean `ShapeFam`, a `Finset` of tokens `Shape
T`; their internal structure — a tuple of block indices, states and
multiplicities — never enters this obligation). For each shape Ŝ ∈ 𝔉 the
chain instance supplies, as *data*:

| math | Lean field | type |
|---|---|---|
| height domain D(Ŝ) ⊆ ℋ | `shDom : Shape T → Set M.Hgt` | arbitrary subset |
| per-height events E_{Ŝ,h}(q₀,N) ⊆ Box(q₀,N) | `shEvtH : Shape T → M.Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)` | finite set |
| visible heights V_Ŝ(q₀,N) ⊆ ℋ, finite | `visH : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset M.Hgt` | finite set |
| aggregate event E_Ŝ(q₀,N) ⊆ Box(q₀,N) | `shEvt : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)` | finite set |
| weight w_Ŝ(h, q₀) ∈ ℝ | `shWeightH : Shape T → M.Hgt → ℚ → ℝ` | real number |
| value W_Ŝ(q₀) ∈ ℝ | `WshVal : Shape T → ℚ → ℝ` | real number |

(Ŝ and q₀ are suppressed below: D, E_h(N), V(N), E(N), w(h), W.)

### 2.3 Laws currently on the structure (quoted, then translated)

```lean
  shevt_grouping : ∀ Ŝ (q₀ : ℚ) (N : ℕ),
    shEvt Ŝ q₀ N = (visH Ŝ q₀ N).biUnion (fun h => shEvtH Ŝ h q₀ N)
  shDom_ne : ∀ Ŝ ∈ F.Sh, (shDom Ŝ).Nonempty
  sh_realized : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ allActivePools M,
    ∃ N₀, ∀ N ≥ N₀, (shEvt Ŝ q₀ N).Nonempty
  shweight_card : ∀ Ŝ ∈ F.Sh, ∀ h : M.Hgt, h ∈ shDom Ŝ → ∀ q₀ ∈ M.Pools,
    ∃ N₀, ∀ N ≥ N₀, shWeightH Ŝ h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((shEvtH Ŝ h q₀ N).card : ℝ)
  wshval_card : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, ∃ N₀, ∀ N ≥ N₀,
    WshVal Ŝ q₀ * (Fintype.card (M.Box q₀ N) : ℝ) = ((shEvt Ŝ q₀ N).card : ℝ)
  wshval_bdd : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, WshVal Ŝ q₀ ∈ Set.Icc (0 : ℝ) 1
```

In standard language, for every Ŝ ∈ 𝔉 and q₀ ∈ 𝒫:

- **(L1) grouping** — for every N: E(N) = ⋃_{h ∈ V(N)} E_h(N).
  (NOTE: as at HEAD there is NO disjointness law for this union.)
- **(L2) per-height census** — for every h ∈ D there is a threshold N₀(h)
  with: for all N ≥ N₀(h), w(h)·b(N) = #E_h(N). (Per-height thresholds.)
- **(L3) aggregate census** — there is N₀ with: for all N ≥ N₀,
  W·b(N) = #E(N).
- **(L4) value bound** — W ∈ [0, 1].
- **(L5) realization** — at every *all-active* pool, E(N) is nonempty for all
  large N. ("All-active" refers to a positivity flag on block states,
  `allActivePools M = {q₀ ∈ M.Pools | ∀ e ∈ Icc 1 n, ∀ τ, M.activeState q₀ e τ}`;
  there are legal instances where this is all of 𝒫 and instances where it is
  empty — in particular, if the state types are empty, every pool is
  all-active vacuously.)
- **(L6) domain nonemptiness** — D ≠ ∅.

Clause (i) of the goal ties W to the evaluation of an explicit rational
function (numerator/denominator polynomials with a geometric-factor
denominator of shape X^k·Π(1 − X^a)) at q₀, regular there; it is proved and
supplies nothing about the height decomposition.

---

## 3. The obligation, mathematically

For every chain instance (post-repair, §4), every Ŝ ∈ 𝔉, every q₀ ∈ 𝒫:

> the family (w(h))_{h ∈ D} is unconditionally summable with sum W

in the net sense (this is Lean/Mathlib `HasSum` over the subtype ↥D): for
every ε > 0 there is a finite F₀ ⊆ D such that every finite F with
F₀ ⊆ F ⊆ D has |Σ_{h∈F} w(h) − W| < ε. Recall `HasSum f a` is equivalent to
"f is summable and its unconditional sum is a"; over ℝ, unconditional =
absolute summability.

---

## 4. The repair (the fields being adjoined — attack THIS form)

The unguarded form of §3 (from §2 laws alone) is REFUTED — see §5. The
adjudicated repair ("queue item 4: census fields + shevt_disj", executing
concurrently) adjoins new fields to `RS4Chain`, specified in the blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.G as:

> (a′) census fields: `shdom_no_stray` (h ∈ shDom → shEvtH eventually
> nonempty), an off-visH vanishing law (h ∈ shDom \ visH → shEvtH = ∅
> eventually, and visH ⊆ shDom eventually), AND `shevt_disj` (pairwise
> disjointness) […] IF shDom is also tied finite/summable

That is, for every Ŝ ∈ 𝔉 and q₀ ∈ 𝒫:

- **(R1) `shevt_disj`** — the sets E_h(N), h ∈ V(N), are pairwise disjoint
  (for all N, or eventually in N — placement not frozen).
- **(R2) visible-domination** — eventually in N: V(N) ⊆ D.
- **(R3) off-visible vanishing** — for each h ∈ D, eventually in N:
  h ∉ V(N) ⟹ E_h(N) = ∅.
- **(R4) `shdom_no_stray`** — for each h ∈ D, eventually in N: E_h(N) ≠ ∅.
- **(G) a guard** on the domain, with the choice left open by the spec
  ("tied finite/summable"), i.e. either
  **(G-fin)** D(Ŝ) is finite (each Ŝ ∈ 𝔉), or
  **(G-sum)** the family (w(h))_{h∈D} is summable (each Ŝ ∈ 𝔉, q₀ ∈ 𝒫).

The exact eventual-threshold structure of (R1)–(R4) is not yet frozen in
Lean; the default reading is per-(Ŝ, q₀) (and per-h where h is quantified)
thresholds, matching (L2)/(L3). A solution should state explicitly which
threshold placements it uses and where the argument is sensitive to them.

---

## 5. What is already proved in the corpus (all machine-checked)

1. **Clause (i) is proved** at the chain's own fields (V7_w17ii.lean:27).
2. **The unguarded clause (ii) is refuted.** A compiled countermodel
   (quarantined at `lean/quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt`)
   builds a full ~30-field chain instance over degenerate carriers — block
   state types empty (which makes every hypothesis guarded by states vacuous
   and every pool all-active), n = 1, a single shape, Box(q₀,N) a one-point
   set, ℋ = ℕ — with D = ℕ (infinite), w ≡ 1, E_h(N) = Box, V(N) = {0},
   E(N) = Box, W ≡ 1. All §2 laws hold; `HasSum (const 1 over ℕ) 1` is false.
   Note: this countermodel violates NONE of the §4 census fields (R1)–(R4)
   (V(N) is a singleton, so pairwise disjointness is vacuous; the other
   three hold at the stated data); it is excluded only by the guard (G) —
   under (G-fin) outright, under (G-sum) because the constant-1 family is
   not summable. This is why the repair carries a guard at all.
3. **The n = 2 gate instance** (the one substantive in-corpus instance,
   `lean/LeanUrat/MovesS/N2Sigmas.lean:1051`) has literals
   D = {0} ⊆ ℋ = ℕ, E_h(N) = Box, V(N) = {0}, E(N) = Box, w ≡ 1, W ≡ 1,
   with (L2)/(L3) holding at threshold N₀ = 0. Any repaired form must remain
   true (and cheaply re-dischargeable) at these literals.
4. **Interface freedom.** Box and ℋ are unconstrained beyond
   finiteness/nonemptiness of Box (§2.1) — a refutation may choose them
   freely, and the quarantined countermodel demonstrates that the
   non-census fields of the chain are inhabitable over such degenerate
   carriers with all state-guarded laws vacuous. Conversely a proof may use
   nothing beyond the listed laws.
5. **Intended-instance context (non-normative, for faithfulness judgment
   only).** In the design notes the height sums that clause (ii) abstracts
   are of the form Σ_{h ∈ H(γ)} Π_i g_i(h_i) ∈ ℚ(q) with geometric
   denominators (1 − q^{−a}), over semilinear domains H(γ) ⊆ Π_i ℕ^{d_i} —
   i.e. genuinely **infinite** height domains in the intended deeper
   instances, with positive weights and convergence at every prime-power
   evaluation. The finite-domain n = 2 gate is the degenerate first case.

---

## 6. What a solution must deliver

For each guard reading (G-fin), (G-sum) — and for any strictly stronger or
weaker variant of (R1)–(R4)/(G) the solver finds more natural, stated
explicitly as a deviation:

- **either** a rigorous proof of §3 from §2.3 + §4 for arbitrary instances
  (this is what un-banks the Lean `sorry`; the proof should be elementary
  enough to formalize: real analysis of unconditional sums + finite
  combinatorics of the census identities),
- **or** an explicit countermodel: instance data for the six carriers
  satisfying every law of §2.3 + §4 with the `HasSum` false, together with an
  argument that the remaining (non-census) fields of the chain are
  inhabitable alongside it (the §5.2 degenerate-carrier pattern is the
  established route),
- plus: the threshold-sensitivity notes of §4, and a check of the repaired
  form at the n = 2 gate literals of §5.3.
