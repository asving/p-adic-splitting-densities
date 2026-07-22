# WILD_WAVE56_BLUEPRINT — the n=2 descent towers and the first full per-type density

**Date: 2026-07-22. Ground truth: `MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md`, ACCEPTED at pass 6
("Accept as ground truth for W5+W6: yes"). Everything below lives inside the note's PROVED
perimeter: Lemma 2.3 (whole-window recenter–rescale staircase bijection, general s/m/depth),
Lemma 3.4′(a) (the n=2 undecided envelope `(⌊N/2⌋+1)·p^{−(N−1)}`, pure counting), the class
partition, and the §7 Case-A ledger (46 strata through depth 3, brute-force exact).**

## §0. The prize

W6's endpoint: `montes_unconditional_n2_full` — for every degree-2 type σ, the FULL decided
density (the entire descent tower, not a window) equals a single certified rational function,
with **`hExhaust` PROVED** (the first unconditional discharge — the n=2 envelope is pure counting,
NO new axiom), so the exhaustive capstone's bracket-uniqueness clause fires outright: the complete
per-type density of a wild type, machine-checked, conditional only on the faithfulness axiom
(+ `htameFE` for palindromy, as always). This is the program's first "one type fully done."

## §1. The n=2 stratum tree (from the accepted note, Lean-ready form)

A stratum = a DESCENT CHAIN: `ms : List ℕ+` (the per-step whole-window recentering slopes
m₁,…,m_k; at n=2 every descend is whole-window — note §5's n=2 scope argument) followed by a
TERMINATING LEAF in the depth-k frame: either the order-0 leaf (split `[(1,1),(1,1)]` /
inert `[(2,1)]`-pattern separable reduction) or the odd-H ramified leaf (H, [(1,1)]) — the W1/W3
shapes, relocated to the recentered frame. SHAPE index = (ms, leaf); VALUES (the c̃ ∈ F_p^× digit
choices per step) are counted, not indexed: each step contributes a factor (p−1) and mass
p^{−(3m_t)} per the chain formula (2.3c) at s=2 (`p^{−s−m·s(s+1)/2}` with the s cluster digits
priced once = the note's exact Case-A ledger: ramified-leaf chains 1/8, 1/64·…; depth masses
1/16, 1/128, 1/1024 at p=2 — externally verified to depth 3 in the note §7).
σ-keying: typeOf5 (ms, leaf) = the leaf's type (recentering does not change the factorization
type — the substitution x ↦ x + c is a ℤ_p-algebra automorphism of ℤ_p[x]; this is [COUNT], a
one-lemma fact, NOT an axiom).

## §2. Wave plan

### W5a — the Lean staircase bijection (the long pole; pure counting)
`OM/RecenterBox.lean`: the level-N box-level recenter–rescale map at s=n=2, m ≥ 1:
for the parent stratum digit conditions (side exact at slope −m·(2)/2… the n=2 whole-window side
(0,2m)–(2,0)? NO — careful: at n=2 the descend stratum is the slope −m side (0,2m)? The note's
Case-A: descend step = the residual (y−c̃)² on the side of slope −m, i.e. v(a₀) = 2m EXACT, v(a₁)
≥ m, residual double root ⟹ a₁/p^m ≡ 2c̃ ∧ a₀/p^{2m} ≡ c̃² (p=2: the two conditions degenerate
per the ledger — follow the NOTE's displayed digit conditions (2.3b), not this gloss) — the map
`f(x) ↦ g(y) = f(c·p^m·lift + p^m y)/p^{2m}` as a bijection
(stratum at level N) ≃ (step digits) × (monicBox p (N−2m… the staircase M_k = N − m(2−k), i.e.
levels N−2m for a₀-slot, N−m for a₁-slot — the TRUE child frame is the staircase box; define
`stairBox p N m` and prove `card_stairBox`) — statement per the note's Lemma 2.3(2), proof =
the displayed coefficient identity (2.3a) + digit bookkeeping. Deliverables: the equiv, the card
identity, functoriality over chains (composition), and the CHAIN fiber predicate `ChainCell`
(digit conditions composed through recenterings) with `chainStratumCount` = the exact closed form
((p−1)^k · leaf count · p^{−Σ3m_t −…} per the ledger) and its level threshold + N-stability.

### W5b — chain menu + model + capstone (depth-windowed)
`OM/ChainMenu.lean` + `OM/RealInstanceW5.lean`: `chainLit (ms, leaf) : ClusterShape` (extend the
tree-index encoding: tree carries ms numerically + the leaf head; injective decode);
`typeOf5`; `omMenu5 n D K σ` := the W4 menu ∪ chains of total depth ≤ D with leaf-type σ
(n=2-only emission for now: `chainOK` requires n=2 — general-n chains are OPEN-D3/D5 territory,
enumerator must not emit them); unified stratumCount5 (chain branch := chainStratumCount via the
ChainCell fibers); disjointness (chain fibers vs all W4 families and vs each other — the digit
conditions pin v(a₀) exactly per depth, distinct chains conflict on some pinned digit — prove via
the staircase decode); monotone staircase; box bound. `realMW5/realDW5/realFW5` + capstone
`montes_unconditional_w5 (n D K)` verbatim-modulo; recovery gate at D=0. Gates: the Case-A ledger
values through depth 2 at p=2 (chain (m=1) + ramified leaf: 1/16·?, per the note's exact table),
window growth in D, census, mutation.

### W5c — axiom scope #4 + the lift-invariance pin
Extend `om_leaf_faithful` to omMenu5 (chain leaves: Cor 1.20 IN THE RECENTERED FRAME + the
type-invariance-under-translation lemma [COUNT — prove it, don't import]). ⚠ DECLARATION GATE:
boundary #5 (lift invariance — the recentered read is a genuine Montes run) has pin "TBD at
declaration"; W5c MUST complete the GMN_citations pin (re-fetch the paper §§2.4/3 text; the
extraction is /tmp/gmn_v2.txt if it survives, else re-download) BEFORE declaring, per the standing
policy + the note's acceptance caveat. fiberOf5 dispatch (chain branch: the ChainCell fiber).
Anchors: at the depth-1 chain gate, the recentered-Eisenstein irreducibility is exactly
`QpTypeEisenstein.ef_of_eisenstein` applied to the translated polynomial (translation is an
algebra automorphism — the anchor is nearly free); probes: wrong-type mutation at a chain
stratum. Guardian audit #5 gates the push.

### W6 — the series assembly (n=2)
`OM/SeriesAssembly.lean`: (1) the depth-window limit: `value(D) = ∑_{chains ≤ D} …` is monotone in
D, and the limit is the geometric-closure rational function (L5fix machinery: the per-step ratio
is `Σ_m (p−1)p^{−3m} = (p−1)/(p³−1) = 1/(p²+p+1)`-shaped — the note's per-step descend ratio;
prove the closed form of the full series per σ as ONE rational function via `isRationalFn` closure
under the geometric sum — the SHAPE-grouped series, finitely many shape families at n=2);
(2) **the envelope**: Lean-prove 3.4′(a) (`undecided(N) ≤ (⌊N/2⌋+1)·p^{−(N−1)}` for the FULL-menu
model at n=2 — stall containment + the ≤-relaxed chain sum, per the note's displayed proof);
(3) `hExhaust` DISCHARGED for the n=2 full model (the envelope → 0); (4) the capstone
`montes_unconditional_n2_full` = the exhaustive capstone with hExhaust supplied + the series
value: full-density bracket-uniqueness LIVE. Gates: the full ramified density value at p=2
(the note's β_ram — compute the exact rational: per-type; the ramified-type series sums to
(the tower value 1/7-related quantities… use the note's §7 symbolic ledger: ramified total
q/(q+1)·? — pin from the note/Python before Lean); Python cross-check to depth 5; census; audit.

## §3. Model-structure note (the infinite menu)
CountingModel/MontesDataV2 menus are Finsets: W5 keeps finite depth-windows (capstone family in
D); W6's full model takes decidedCount := the D→∞ monotone limit COUNT-side (decidedCount σ N is
itself a FINITE sum at each N — chains with threshold > N have empty fibers, small-N vanishing —
so the full model's decidedCount is definable WITHOUT an infinite menu: define it as the sum over
the (finite) set of chains with threshold ≤ N; the MontesDataV2 instance then needs shapesOf to be
that N-independent… ⚠ DESIGN: shapesOf is N-independent in the spine. Resolution: W6's model
bypasses MontesDataV2's Finset menu — state the full capstone directly (rationality via the series
theorem, value tie via the envelope squeeze), reusing the spine only for the windowed family.
Blueprint the exact statement in W6a before implementation.)

## §4. Risks
- W5a's staircase equiv is the genuinely new Lean machinery (mixed-level product boxes); prototype
  at m=1 first.
- The p=2 degeneracies in the digit conditions (2c̃ ≡ 0 at p=2) — follow the note's (2.3b) exactly;
  the Case-A ledger at p=2 is the gate.
- W5c's pin completion is a hard gate — do not declare scope #4 without it.
- W6's model-structure resolution (§3) needs its own mini-design before code.
