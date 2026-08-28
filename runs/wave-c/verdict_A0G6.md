# VERDICT — unit A0G6, node A0G-NP (the finite face-schema skeletons)

Date: 2026-08-28.  Target landed: `leanfinal/Uniformity/ChapI/IFCG5.lean` (NEW, 864 lines,
zero `sorry`, zero warnings, 40/40 AxCheck lines Lean-core only).  Source of authority:
`docs/in-progress/A0_GENERAL_2026-08-28.md` §4.2 + the §6 `A0G-NP0` row.
Verification: `timeout 580 lake env lean Uniformity/ChapI/IFCG5.lean` per increment (5
increments, each green before the next; never bare `lake build`).  No other file touched.

## 1. THE SKELETON DESIGN DECISIONS (first, per the unit charge — these BIND A0G-GC)

The unit charge: where §4.2 leaves a representation choice open, choose for GC's exhaustion
proof — disjointness by construction beats disjointness by lemma.  The choices:

* **D1 — redundancy-free face carrier.**  `FaceShape := ℕ × FactorizationType`: the reduced
  slope DENOMINATOR `b` and the residual pattern σ (multiset of `(D, μ)`).  The residual
  degree `d` is DERIVED (`faceResDeg = σ.degree = Σ D·μ`) and the face length is DERIVED
  (`faceLen = b·d`) — neither is a stored field, so **no two representations of the same face
  exist** and GC0's classifying map has one possible image per NP face.  Child positions are
  also derived (the `μ ≥ 2` entries), per §4.2's "recursive child positions" being generated,
  not stored.  The pattern constraint is LITERALLY IFCG0's (A0G-RP) residue-pattern membership
  at total `d` (`validFace_iff_mem_residuePatternFinset`) — dedup, not re-derivation.
* **D2 — faces are a `List`, ordered by slope.**  `ValidSkeleton m s` takes `s : List
  FaceShape` = the lower-NP faces read left-to-right (increasing slope; the slopes `h/b`
  themselves are A0G-NP1 parameters, only denominators survive here).  List, NOT multiset:
  the classifier reads the hull deterministically, so input ↦ skeleton is a *function* and
  different orders are disjoint cells by construction.  (A multiset would fuse genuinely
  distinct NP shapes: which face carries the smaller slope is a real cell distinction with
  its own parameter region and weight.)  `SlopesOrdered` (§7) is the cross-multiplied,
  rational-free form NP1 must instantiate.
* **D3 — integral faces are first-class; the loop is a distinguished skeleton.**  `b = 1`
  faces are ordinary skeleton faces, and the π-rescale loop is the skeleton
  `loopSkeleton m = [(1, {(1, m)})]` — NOT an unclassified leftover.  Consequence for GC1
  (the stop line): exhaustion needs no integral-slope side case — every recentred NP has a
  full face list, and the rescale cell is one of the finitely many skeletons.  Consequence
  for GC3: the same-mass edge is unique BY CONSTRUCTION (`eq_loopSkeleton_of_entry_snd_eq_mass`:
  a single multiplicity-`m` entry anywhere forces b = 1, D = 1, d = m, pattern = {(1,m)},
  and the face list = [that face] — all seven conclusions from arithmetic on the mass law).
* **D4 — no unbounded datum, structurally.**  Slope numerators, heights, gaps appear ONLY as
  explicit arguments of the binding surfaces (`genreDatumOfChildEntry`'s `h`/`Q`,
  `RealizesFaceAt`'s `h`), never as skeleton fields.  The formal gate is the complete finite
  enumeration + the `Fintype` instance (below), plus per-component `≤ m` bounds.
* **D5 — exact mass law.**  `Σ faceLen = m` EXACTLY (a recentred size-`m` cluster polynomial
  has all `m` roots at positive valuation; its lower NP spans `[0, m]`).  This makes the §6
  gate `b·d ≤ m` a one-line consequence and clears §4.2's division chain `μ ≤ d ≤ m/b` into
  subtraction-free ℕ arithmetic.

**Scoping recorded** (what NP0 deliberately does NOT bind): the face pattern is NOT yet tied
to the factorization of `dvResPoly` — the realization predicate pins side LENGTH/DEGREE (what
C.07/C.29 alone can say); certifying the residual factorization is A0G-HE1's work.  No
measures/weights (A0G-RW), no parameters/Presburger regions (A0G-NP1).

## 2. Per-piece status (all PROVED, Lean-core)

| piece | declarations | status |
|---|---|---|
| §1 face layer | `FaceShape`, `faceDen/facePat/faceResDeg/faceLen`, `ValidFace`, `validFace_iff_mem_residuePatternFinset` (IFCG0 dedup), `faceLen_pos`, `entry_weight/fst/snd_le_resDeg`, `card_le_resDeg` | proved |
| §2 mass law + **THE GATE** | `ValidSkeleton`, **`faceLen_le_mass` (`b·d ≤ m`)**, `faceDen_le_mass`, `faceResDeg_le_mass`, `length_le_mass`, `entry_fst/snd_le_mass`, `den_mul_entry_weight_le_mass`, `validSkeleton_zero_iff` | proved |
| §3 finite enumeration (**no-unbounded-datum gate**) | `skAlphabet`, `SKSigma` (ordered-tuple Sigma ambient — IFCG0's technique with `Fin k → _` replacing `Sym`, per D2), `skEmbed`, `clusterSkeletonFinset`, **`mem_clusterSkeletonFinset_iff`** (completeness: every valid skeleton is caught), `ClusterSkeleton m`, **`instFintypeClusterSkeleton`**, `ClusterSkeleton.valid/ofValid` | proved |
| §4 loop (D3) | `loopFace`, `loopSkeleton`, `faceResDeg/faceLen_loopFace`, `validSkeleton_loopSkeleton`, **`eq_loopSkeleton_of_entry_snd_eq_mass`** (GC3's sole-same-mass-edge, by construction) | proved |
| §5 children (A0G-CH feed) | `IsChildEntry`/`IsLeafEntry`, `entry_snd_lt_mass_of_ne_loop` (μ < m off loop), `childEntry_lt_mass_or_loop`, `two_mul_entry_snd_le_mass_of_two_le_den` (fractional faces: `2μ ≤ m`, §4.2's `μ ≤ d ≤ m/b` cleared of division), `leaf_ef_le_mass` (`b·D ≤ m`), `mass_conservation` (`Σ b·D·μ = m`), `childSizes` + `mem_childSizes_iff` + `childSizes_lt_mass_of_ne_loop` + `childSizes_loopSkeleton` | proved |
| §6 H.01 binding | `genreDatumOfChildEntry` (child entry `(b,D,μ)` + NP1 params `Q,h` ⊢ a well-formed `GenreDatum` with `e₁=b, f₁=D`; `hkey : 2 ≤ b·D` excludes exactly the rational-recentre child, matching H.01's own exclusion), 5 field simp-lemmas, `two_le_den_mul_fst_of_two_le_den` (hkey automatic on fractional faces), `stage_degree_le_mass` (`e₁f₁μ ≤ m`) | proved |
| §7 dvSide/IsDvPure binding (A0G-HE surface) | `RealizesFaceAt` (purity + side length = `b·d`), `dvSideMin_eq_zero_of_isDvPure`, `dvSideMax_eq_of_realizes`, **`dvSideDeg_eq_of_realizes`** (C.07's `d_λ = len/ℓ` ≡ the skeleton's `d = (b·d)/b`, exact division), `natDegree_div_le_of_realizes`, `SlopesOrdered`, `RealizesSkeletonAt`, `realization_sideLen_sum` (block side lengths sum to `m`) | proved |
| §9 pins + mirror | `clusterSkeletonFinset_zero = {[]}`, `clusterSkeletonFinset_one = {loopSkeleton 1}` (PROVED, official object); executable mirror `facesCountFast`/`skCountFast` (partial defs, never cited — IFCG0 `rpGen` precedent) | proved / evals green |

## 3. Gate discharge

* **`b·d ≤ m`**: `faceLen_le_mass` — from D5's exact mass law, no height bound anywhere (the
  §6 row's "no height bound" is D4: heights are NP1 parameters, absent from the carrier).
* **No unbounded datum**: `Fintype (ClusterSkeleton m)` via the complete finite enumeration
  (`mem_clusterSkeletonFinset_iff` — completeness is unconditional: any valid skeleton,
  wherever its data a priori lives, embeds in the `(k : Fin (m+1)) × (Fin k → skAlphabet m)`
  ambient).  Component bounds: `b, d, D, μ, #faces, #entries ≤ m` all proved.
* Regression: skeleton counts at m = 0..6 are **1, 1, 5, 15, 56, 179, 629** (per-length face
  counts 1, 4, 6, 15, 18, 43), triple-checked: (i) the in-file `#eval` mirror; (ii) an
  independent Python composition/divisor recursion over IFCG0's verified pattern counts
  1, 1, 3, 5, 11, 17, 34; (iii) m = 0, 1 additionally PROVED on the official noncomputable
  Finset.  The official `clusterSkeletonFinset` is noncomputable (`FactorizationType`'s
  DecidableEq is classical — same as IFCG0's situation), so the mirror is the executable arm.

## 4. Notes for downstream nodes

* **A0G-NP1** must supply, per face: reduced numerator `h` (coprime to `b`, `SlopesOrdered`
  across the list) and the vertex-height/gap parameters; the constraint carrier should
  target `SlopesOrdered` + `RealizesFaceAt` as the interface pinned here.
* **A0G-HE1** owes the residual-pattern certification: extend `RealizesFaceAt` with
  `dvResPoly`-factorization matching (deliberately NOT asserted here).
* **A0G-CH** can consume `childSizes_lt_mass_of_ne_loop` (+ `two_mul_entry_snd_le_mass_of_two_le_den`
  for the quantitative form) essentially as-is; the loop's sole same-mass child is
  `childSizes_loopSkeleton`.
* **A0G-GC** disjointness: at the skeleton level there is nothing left to prove — the carrier
  admits no double representation (D1) and no order quotient (D2).  GC2's remaining content is
  parameter-level uniqueness (NP1's job) only.
* Dedup findings: no prior face bank existed (the "DWC face banks" pointer resolves to C.07's
  `dvSide*` cluster, which is per-polynomial, not schema-level; chapter H's `GenreDatum` is
  per-stage and carries the unbounded `h`, so it is a binding TARGET, not a carrier).  IFCG0's
  residue-pattern bank was reused wholesale for the face patterns.
* One deliberate interface argument: `genreDatumOfChildEntry`'s `_hp : p ∈ f.2.data` is unused
  by the construction but kept so the constructor cannot be honestly invoked on entries not in
  the face (faithfulness of the binding claim).

## 5. Build discipline log

Increments: (1) §1+§2 — 2 repairs (omega cannot commute variable products; explicit
`Nat.mul_comm` calcs). (2) §3 — clean first pass (incl. `List.ofFn_get`, classical filter).
(3) §4+§5 — 1 repair (simp unfolded `loopFace` before the `faceResDeg_loopFace` rewrite
could fire; reordered). (4) §6+§7 — 2 repairs (`List.finRange_map_get` does not exist in the
pin; replaced by `ofFn_eq_map`/`map_ofFn`/`ofFn_get` chain; `_hp` rename). (5) §9+footer —
1 lint repair (`simpa`→`simp at`).  Final: exit 0, no output except the 11 expected `#eval`
values and 40 Lean-core axiom lines.
