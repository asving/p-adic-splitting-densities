# §C.10B derivation — general window-nesting bookkeeping (2026-07-26)

Derivation unit for the corrected C.1.0(b) of MOVES_2026-07-24.md §C.
Staged build; each section appended after its derivation.

## S2. Setup and notation

(to be appended)

## S3. The increment case

## S4. The recentering case and the iterated invariant

## S5. Endpoint-block pin inventory

## S6. Instance checks

## S7. Proposed replacement text for C.1.0(b)

---
*(S2 appended.)*

### S2.1 Frames, blocks, base labels

Nodes ν₀, ν₁, …, ν_k; node ν_i is read in frame i with key Φ_i (root: Φ₀ = x,
D₀ := deg Φ₀ = 1), reading a side of slope h_i/e_i (lowest terms, stage scale)
whose residual factor is ψ_i (deg g_i ≥ 1, ψ_i ≠ z) with multiplicity μ_i ≥ 1.
An increment sets Φ_{i+1} := Φ̂_i, D_{i+1} = e_i·g_i·D_i; a recentering
(e_i = 1, g_i = 1) sets Φ_{i+1} := Φ'_i, D_{i+1} = D_i.

BLOCKS (C.1.0(a), unshifted — this is load-bearing below): in frame r, the
slot-j coefficient of the Φ_r-development of f occupies the base index block
  blk_r(j) := [j·D_r, (j+1)·D_r) ∩ [0, n).
Iterating inner developments refines blocks; frame coordinates are a
relabeling of base coordinates (bijective), and C.0.5's maps are unitriangular
against the base order ≺.

LEVELS: all vertical bookkeeping below is done in ABSOLUTE v_p-scale
(rational levels; a digit coordinate is a pair (base index b, integer level ℓ)).
A frame-r stage height converts to v_p by dividing by the accumulated stretch
(C.1.0(c)); strict inequalities transfer. A LINE of a node, drawn over the
base index axis, is the affine function
  line_i(b) := (v_p-value of the side line at base index b),
of constant v_p-slope −h_i/(e_i·STR_i·D_i) per base index (STR_i := the
product of stretches down to frame i); "the staircase of line_i" = b ↦ the
set of integer levels ≤ line_i(b) (vanishing demands) resp. = line_i(b)
(digit demands, only where line_i(b) is an achievable integer level — the
e-lattice congruence).

### S2.2 D.8's slot positions, recomputed — where the anchor does and does not enter

From D.8's displayed proof: R(f) = Σ_{minimizing j} z^{j·m̂}·R(B_j)·ψ^j, each
term of ψ-order EXACTLY j (D.3(d): each R(B_j) is z-shift × polynomial of
degree < g, ψ-free). Hence

  (0)  ord_ψ R(f) = the least minimizing slot of the Φ̂-development.

CONSEQUENCE 1 (child slots are absolute). The BOX slots are j = 0, …, μ−1 and
the VERTEX slot is j = μ, counted from slot 0 of the Φ̂-development of f — NO
anchor offset. The anchor a := ord_z R(f) is a z-order; (0) is a ψ-order
statement, and z ≠ ψ, so a cannot shift which Φ̂-slots minimize. The child
window is [0, μ] absolutely.

CONSEQUENCE 2 (where the anchor DOES sit: inside blocks, and at the parent
span). Two distinct appearances, both forced by D.3(c)'s stride rule
p_j(γ) = (j − tγ)/e:
(i) PARENT SPAN ↔ ANCHOR. For f's own frame-i development (coefficients in C,
    monomial residuals by S5), R(f) = Σ_{min j} c_j·z^{p_j(γ)} with p_j
    strictly increasing on the minimizing set; so ord_z R(f) = p_{s₀}(γ)
    where s₀ = the LEAST minimizing slot = the side's left endpoint:

      (†)  s₀ = e·a + t·γ,   a = (s₀ − tγ)/e,   γ := w(f).

    The anchor is exactly the (Bézout-transported) left endpoint of the side.
    Likewise the top position a + w/e is the right endpoint s₀ + w in
    disguise (deg R_anch = w/e).
(ii) INNER MINIMIZING SLOTS OF A COEFFICIENT. For a single coefficient
    B ∈ Ĉ with Φ-development over inner slots j' ∈ [0, eg), the minimizing
    inner slots satisfy the anchor congruence j' ≡ tγ_B (mod e) and START at

      (‡)  j'₀ = e·a_B + t·γ_B,   a_B := ord_z R(B),  γ_B := w(B)

    — anchor-DEPENDENT. So when a child-frame digit equation (VERTEX digit,
    transport digit) is unfolded to base coordinates, its leading coordinates
    sit at inner slots offset by (‡), not at inner slot 0.

RESOLUTION of the S2 charge: the minimizing slots of the CHILD development
start at μ (never anchor-shifted); the anchor enters only (i) as the parent
side's left endpoint via (†) and (ii) as the within-block offset (‡) of digit
realizations. §C's current C.1.0(b) phrase "at the side's base offset" is a
conflation of (†) with a (nonexistent) shift of the child blocks.

### S2.3 The pin-set toolkit (used throughout S3–S5)

LEMMA PIN-WELLDEF. A digit-cylinder locus (solution set of a digit system at
level N) determines its pin set: solving in ≺-order, a coordinate c is pinned
iff its fiber over each solvable prefix is a single value, free iff full —
the dichotomy holds coordinate by coordinate for a unitriangular system, and
it is a property of the locus alone. Hence two digit systems with the same
solution set have the same pins (and volume).

COROLLARY MOVE-INV (with C.0.5). For every move, the landing system and the
stratum system present the SAME locus up to a unitriangular bijection fixing
base labels; therefore pins(landing) = pins(stratum) as sets of base
coordinates. All pin bookkeeping can be done stratum-side, node by node; no
child-frame block placement is ever needed to locate PINS (only to locate
CLAUSES, which is where S3's regions matter).

---
*(S3 appended.)*

### S3.1 What a read's stratum actually asserts: three clause species

Node ν_{i+1} reads a side of the CHILD polygon of ν_i's landing — the hull of
f's frame-(i+1) points over the window Win_i := slots [0, μ_i]. For the side
S' = frame-(i+1) slots [s₀', s₀'+w'] (line L', slope h_{i+1}/e_{i+1} over the
current scale) to BE a hull side with the given pattern, E(ν_{i+1}) must
assert, at EVERY slot of Win_i — not only on the span:

  (α) SPAN slots j ∈ [s₀', s₀'+w']: point weakly above L'; digits AT L' equal
      the pattern (nonzero at both endpoints; zero forced off the
      e_{i+1}-lattice, where L' is not an achievable level);
  (β) LEFT slots j ∈ [0, s₀'): point STRICTLY above the extension of L';
  (γ) RIGHT slots j ∈ (s₀'+w', μ_i]: point strictly above the extension of L'.

§C rev 2's C.1 case analysis inventories only (α) (interior + right endpoint).
(β) and (γ) are genuinely part of the stratum whenever s₀' > 0 resp.
s₀'+w' < μ_i: without them the locus contains f whose hull dips below L'
outside the span, i.e. f whose classifier read is a DIFFERENT side.

### S3.2 Which base blocks the clauses occupy — regions, not nesting

CLAUSE REGION: by S3.1, ν_{i+1}'s clause region is the FULL window Win_i,
base span [0, (μ_i+1)·D_{i+1}) ∩ [0, n) — anchored at base 0 (blocks are
unshifted, S2.1), NOT inside the parent side's translated span
[s₀·D_i, (s₀+w+1)·D_i) when s₀ > 0. §C's claim (ii) of C.1.0(b) is FALSE as a
span containment; what survives of it is the width inequality, which governs
FACTOR spans:

  (W)  μ_{i+1}·D_{i+2} = μ_{i+1}·e_{i+1}·g_{i+1}·D_{i+1} ≤ w'·D_{i+1}
       ≤ (s₀'+w')·D_{i+1} ≤ μ_i·D_{i+1},

(μ_{i+1}g_{i+1} ≤ w'/e_{i+1} because ψ_{i+1}^{μ_{i+1}} divides the residual,
of degree w'/e_{i+1}). So:
  (N1) FACTOR spans nest: [0, μ_{i+1}·D_{i+2}) ⊆ [0, μ_i·D_{i+1});
  (N2) the window adds one vertex block: Win_{i+1} base span =
       [0, μ_{i+1}D_{i+2}) ∪ blk_{i+2}(μ_{i+1}), and ONLY the vertex block
       can overhang Win_i's base span — by up to (e_{i+1}g_{i+1} − 1)·D_{i+1}
       + (μ_{i+1}D_{i+2} − μ_iD_{i+1}) ≤ … in total the overhang is
       Win_{i+1}-span ∖ Win_i-span ⊆ blk_{i+2}(μ_{i+1}). At an increment with
       e_{i+1}g_{i+1} ≥ 2 the overhang is generically NONEMPTY (e.g.
       s₀' = 0, w' = μ_i = μ_{i+1}e_{i+1}g_{i+1}: right end
       (μ_{i+1}+1)D_{i+2} = (μ_i + e_{i+1}g_{i+1})·D_{i+1} >
       (μ_i+1)·D_{i+1}). The right-endpoint block is thus STRUCTURAL, not an
       edge case; its pins are inventoried in S5.

ANCHOR CORRECTIONS: within each clause's block, digit-equation leading
coordinates sit at the (‡)-offset inner slots (S2.2(ii)); the parent-frame
location of the whole side is (†). Neither shifts the block spans above.

### S3.3 Fresh / inherited / exceptional, clause by clause (increment)

All comparisons are between ν_{i+1}'s clauses and Λ(ν_i) = (BOX)+(VERTEX)
+(TRANSPORT) — the SAME frame i+1, which is what makes the value structure
clean: within slots [0, μ_i) the old system asserts ZEROS only (BOX carries
no values); values sit at slot μ_i (VERTEX) and slots > μ_i (TRANSPORT).
Write old(j) := the old line γ_i − j·w(Φ̂_i) (v_p-converted), new(j) := L'
extended to all of [0, μ_i]. By (I-aug), h_{i+1}/e_{i+1} > w(Φ̂_i): the new
line is STEEPER than the old.

- (α) SPAN, interior slots: hull convexity gives new(j) ≥ old(j) on the span.
  Levels ≤ old(j): BOX zeros — inherited, implied clause by clause (C.1(i)'s
  accepted kernel). Levels in (old(j), new(j)): FRESH zero pins. Level new(j)
  on the e_{i+1}-lattice: FRESH digit pin (pattern value). No collision with
  values: there are none below slot μ_i. The strips start exactly at the
  local floor, so the per-index pin downset is preserved.
- (α) RIGHT ENDPOINT s₀'+w': the hinge, unchanged in substance:
  ADJACENT (s₀'+w' = μ_i): the endpoint's prefix zeros and its value are
  (VERTEX)'s own equations — inherited entirely; the pattern's leading
  coefficient must equal the transported vertex value z̄^{−μ_i·m̂_i}·(…)
  (D.8's explicit unit) — a DATA consistency identity, not an f-pin.
  NON-ADJACENT (s₀'+w' < μ_i): new(s₀'+w') > old(s₀'+w') strictly (the
  endpoint is a hull vertex strictly above the old line by BOX), and the
  whole endpoint content — prefix zeros in (old, new), the nonzero value
  digit at new — is FRESH.
- (β) LEFT slots j < s₀': new is steeper and new(s₀') ≥ old(s₀'), so
  new(j) > old(j) STRICTLY for all j < s₀': the strip (old(j), new(j)] is
  nonempty — FRESH zero pins at every left slot. (Omitted by §C rev 2; these
  are real pins whenever s₀' > 0, and their volume factors belong to
  E_fresh(ν_{i+1}).)
- (γ) RIGHT slots j ∈ (s₀'+w', μ_i]: new descends faster than old from a
  start new(s₀'+w') ≥ old(s₀'+w'); there is a single crossing slot j×. For
  j < j×: fresh zero strips (old(j), new(j)]. For j ≥ j×: new(j) ≤ old(j) —
  the clause is IMPLIED by BOX (weaker bound), no pins. At j = μ_i the point
  is pinned exactly at old(μ_i) with a NONZERO value, so the clause
  "strictly above new(μ_i)" is the arithmetic condition old(μ_i) > new(μ_i)
  on the HISTORY DATA alone: if it fails the history is unrealizable (the
  classifier never emits it); it contributes no f-pin. EXCEPTION CLASS:
  nonempty only in the non-adjacent case (adjacent: (γ) is empty).
- TRANSPORT slots j > μ_i: OUTSIDE ν_{i+1}'s clause region — untouched. For
  LATER nodes whose vertex-block overhang (N2) reaches these blocks: the old
  pins there are zeros below old(j) and a value AT old(j); any later node's
  demand at those blocks unfolds to a staircase of the SAME per-slot slope
  w(Φ̂_i) as old(j) (inner developments in Φ̂_i), lying strictly below old at
  the window rim and hence at every slot rightward — IMPLIED by the
  transport zeros; the value at old(j) is never contradicted. (Checked
  numerically in S6; this is the load-bearing new step for iterated windows,
  restated as (INV) in S4.)

COUNT: vol(E_fresh(ν_{i+1})) = the product over the fresh pins above —
(α)-strips + line digits (minus the adjacent endpoint) + (β)-strips +
(γ)-strips up to j×. D.11's per-move exactness is unchanged; what changes is
the INVENTORY of which base coordinates the fresh pins occupy.

---
*(S4 appended.)*

### S4.1 The recentering case

A recentering node ν_i (e_i = 1 read; D.10) is the g = 1 instance: ψ' = z−c̃,
Φ_{i+1} = Φ̂_i − t, D_{i+1} = D_i. Everything in S3 applies verbatim with
e_{i+1}g_{i+1} = 1 at the NEXT step; for the recentering step itself:
- The three clause species (α)(β)(γ) are unchanged; with e_i = 1 every span
  slot is on the lattice and the pattern digits are the coefficients of
  z^a·(z−c̃)^{μ_i}·h(z) (whence D.10's a' = μ_i, R'_anch = (z'+c̃)^a·h(z'+c̃)).
- ANCHOR = LEFT ENDPOINT literally: at e_read = 1 frames T is coefficient-pure
  and t = 0, so (†) reads s₀ = a. The side's base offset IS the anchor times
  D_i. (At e ≥ 2 frames the Bézout correction t·γ intervenes — (†) in full.)
- WINDOWS NEST WITHOUT OVERHANG: D_{i+2} = D_{i+1} and μ_{i+1} ≤ w' ≤
  s₀'+w' ≤ μ_i give Win_{i+1}-span = [0, (μ_{i+1}+1)D_{i+1}) ⊆
  [0, (μ_i+1)D_{i+1}) = Win_i-span. The overhang phenomenon (N2) is exclusive
  to increments with e_{i+1}g_{i+1} ≥ 2.
- Lift dependence: per §C's lift-carrying histories; the invariant below is
  per lift-carrying history (D.10's scope clause; nothing new needed).

### S4.2 The iterated invariant (INV), along a whole history

State after node ν_i (all pins as base coordinates (b, ℓ), MOVE-INV):

 (INV-a) DOWNSET: pinned levels at each base index b form an initial segment
   {ℓ ∈ ℤ≥0 : ℓ ≤ F_i(b)}, F_i(b) = the pointwise max over nodes m ≤ i of
   node m's extended-line staircase at b, restricted to node m's clause
   region (S3.1); F_i ≥ F_{i−1} pointwise.
 (INV-b) ZEROS IN THE FACTOR INTERIOR: at base indices b < μ_i·D_{i+1}, all
   pins through ν_i are zero pins. Value pins (pattern digits, vertex,
   transport) sit only at indices ≥ μ_i·D_{i+1} — "the rim" — each at its
   own node's line level at its index, hence ≤ F_i.
 (INV-c) RIM DOMINATION: for every m ≤ i, at frame-(m+1) slots j > μ_m
   (node m's transport/co-factor territory), the demand staircases of ALL
   later nodes lie pointwise ≤ node m's extended line old_m(j); node m's
   transport zeros (below old_m) and values (at old_m) are never contradicted
   and never re-pinned.

STEP PROOF SKETCH (ν_{i+1} appended):
1. Interior (frame-(i+1) slots < μ_i): S3.3's (α)(β)(γ) analysis against
   Λ(ν_i). Inherited parts implied (hull convexity; steeper extension; BOX
   zeros — and by (INV-b)+(N1) the interior indices [0, μ_iD_{i+1}) ⊆
   [0, μ_{i−1}D_i) carry only zeros from ALL older nodes, so no clause ever
   demands vanishing on an old value). Fresh strips start at the local floor:
   (INV-a) preserved; new values only on ν_{i+1}'s line within its span and
   at its landing rim: (INV-b) preserved via (N1) at the next index cutoff
   μ_{i+1}D_{i+2} ≤ μ_iD_{i+1}.
2. Rim (slots ≥ μ_i, reached by ν_{i+1}'s vertex-block content and by later
   overhangs): the PARALLEL-UNFOLDING lemma: a frame-(i+2) clause
   "w(B″_j) ≥ β", unfolded through B″_j = Σ_{j'} C_{j'}·Φ̂_i^{j'}, demands
   w(C_{j'}) ≥ β − j'·w(Φ̂_i) — a staircase of slope w(Φ̂_i) per
   frame-(i+1) slot, PARALLEL to old_i; across outer slots the new line
   drops at h_{i+1}/e_{i+1} > w(Φ̂_i) (I-aug), i.e. faster. Anchored by
   demand(μ_i) ≤ old_i(μ_i) (adjacent: equality — the clause IS (VERTEX);
   non-adjacent: strict, by (γ)'s data arithmetic), the whole rim demand
   staircase lies ≤ old_i pointwise: implied by transport zeros; values
   untouched. Iterating the same lemma one frame up extends (INV-c) to all
   later nodes (each handoff anchors the next staircase below the previous
   line at the rim entry slot, and unfolding slopes only ever equal the
   BLOCK's own key weight, matching that block's old line slope).
3. Consistency identities (adjacent endpoint value; the (γ)-arithmetic at
   μ_i) constrain HISTORY DATA, not f: they either hold (and pin nothing) or
   the history is unrealizable and its stratum empty. They must be stated in
   C.1 as data-side side conditions, not as equations of E_fresh.

CONSEQUENCE (what Theorem C's induction actually needs): pins(E_fresh(ν_{i+1}))
∩ Π_i = ∅ AND the inherited clauses implied on T_i's locus — both now hold
with the corrected inventory: fresh = (α)-strips and line digits (minus the
adjacent endpoint) + (β)-strips + (γ)-strips left of the crossing; inherited =
below-old-line prefixes + the adjacent endpoint; exceptional (data-side) = the
two consistency identities. The uncorrected §C text under-counts E_fresh
whenever s₀' > 0 or the read is non-adjacent with a crossing slot j× > s₀'+w'.

---
*(S5 appended.)*

### S5.1 Two distinct "right-endpoint blocks" — disambiguation first

(a) The SIDE's endpoint block B* := blk_{i+1}(j*), j* := s₀'+w' — width
    D_{i+1}; the hinge of C.1 lives here.
(b) The CHILD's vertex block blk_{i+2}(μ_{i+1}) — width D_{i+2} =
    e_{i+1}g_{i+1}·D_{i+1}, left edge μ_{i+1}D_{i+2} ≤ w'·D_{i+1}. It equals
    (a) only when s₀' = 0 AND w' = μ_{i+1}e_{i+1}g_{i+1}; for s₀' large it
    lies strictly LEFT of (a), and its right edge can OVERHANG Win_i (N2).
§C's C.1.0(b) conflates (a) and (b). The hinge concerns (a); the nesting
exception concerns (b).

### S5.2 Full inventory of B* (the side's endpoint block), by level

Per base index b ∈ B*, shallow → deep; "old" = old_i staircase, "new" = ν_{i+1}
line staircase at b.

1. FLOOR ZEROS, levels ≤ old(b): inherited. Source: ν_i's BOX prefix
   (j* < μ_i) or VERTEX prefix (j* = μ_i); plus older nodes' strips deeper in
   the history at the same indices — all zeros by (INV-b) when b < μ_iD_{i+1}.
2. OLD VALUE PINS inside the floor: only when j* = μ_i — ν_i's VERTEX digit:
   g_i·d_i base coordinates (an F'-digit in block convention) at the
   (‡)-anchored inner positions, level = old(μ_i)-staircase. Inherited. In
   vertex-CHAIN configurations (successive adjacent reads), still-earlier
   vertex/transport values of nodes m < i can also cohabit B* (possible iff
   μ_mD_{m+1} < (μ_i+1)D_{i+1}, i.e. only near the factor rim) — always at
   floor levels, never re-pinned, all later demands there implied by (INV-c).
3. FRESH STRIP ZEROS, levels in (old(b), new(b)): nonempty iff NON-ADJACENT
   (j* < μ_i forces new(j*) > old(j*): the endpoint is a hull vertex strictly
   above the old line). Fresh, part of E_fresh(ν_{i+1}).
4. THE ENDPOINT VALUE PIN at level new(b) on the lattice: the pattern's
   leading coefficient — one F^{(i)}-digit = d_i base coordinates at the
   weight-forced positions (S5-monomial recursion; offsets per (‡)).
   ADJACENT: these are literally case 2's coordinates (MOVE-INV forces the
   coordinate sets to coincide); the required VALUE equality — pattern lead =
   z̄^{−μ_i m̂_i}·((R(f)/ψ^{μ_i}) mod ψ_i) — is a DATA consistency identity,
   pinning nothing. NON-ADJACENT: fresh value pin.
5. LEVELS BELOW new(b): FREE. Later nodes' territory; under iteration their
   fresh pins land only at indices < μ_{i+1}D_{i+2} ≤ w'D_{i+1} — i.e. they
   re-enter B* only if B* intersects the next factor interior, which for the
   endpoint block means only via the s₀'-translate degenerate cases; the
   generic endpoint block is never freshly pinned again by this history.
6. TRANSPORTED/CO-FACTOR DATA OF ν_{i+1} ITSELF: none in B* beyond items 3–4
   — ν_{i+1}'s transport clauses (its landing slots > μ_{i+1}) re-solve, by
   MOVE-INV, to exactly its stratum pins (items 3–4 + span content), adding
   no new base coordinates.

### S5.3 Inventory of the child vertex block (b) and its overhang

Interior part (indices < μ_iD_{i+1}): ordinary window-interior content —
zeros-only floor (INV-b); later reads pin fresh strips here as usual.
Rim/overhang part (indices ≥ μ_iD_{i+1}, up to (μ_{i+1}+1)D_{i+2} when it
overhangs Win_i): carries ν_i's (and, deeper, older nodes') transport zeros
and line values. NO fresh pin of any later node ever lands here: by the
parallel-unfolding lemma + (I-aug) (S4.2 step 2), every later demand
staircase at these indices lies pointwise ≤ the local old line — implied.
CONSEQUENCE (clean restatement): along any history, node ν_{i+1}'s fresh pins
all lie at base indices < μ_iD_{i+1} (the current factor interior), at levels
in its fresh strips or on its line. The apparent overhang of window SPANS is
harmless because it is clause-region overhang, never pin overhang.

### S5.4 Honesty notes

- Item 2's vertex-chain cohabitation and item 5's degenerate re-entry are
  stated as POSSIBLE (index-arithmetic permitting), not exhaustively
  classified; the invariant (INV) covers them uniformly, which is all C.1
  consumes. The instance checks (S6) exercise a chain case.
- The (‡)-offsets fix WHICH base coordinates carry digit equations; nothing
  in C.1's counting depends on them beyond MOVE-INV (pin sets, not
  positions-within-block, drive the volume product). They matter only if one
  wants the pins' explicit addresses (e.g. for a Lean-side digit census).

---
*(S6 appended. Script: /tmp/c10b_check.py, full output /tmp/c10b_check.txt.
Label arithmetic: per-index v_p-bounds via the block-offset recursion
off(b) = Σ innerslot_r(b)·κ_r, κ_r = h_r/(e_r·STR_r); pins as base labels.)*

### S6.1 Instance A — the depth-3 chain (e,h,g) = (1,1,2)→(2,5,1)→(1,11)

n = 5; x-cluster root, side [0,4] slope 1, μ₀ = 2; frame-1 side [0,2] slope
5/2 adjacent, μ₁ = 1; frame-2 side [0,1] slope 11 adjacent (I-aug: 5/2 > 2,
11 > 10 ✓). VERDICTS (all machine-checked):
- Node 0: 15 pins (staircase, digits on the line). Node 1 fresh = exactly
  {(0,5),(1,4)} — ONE F_{p²}-digit at the skewed (κ₀ = 1) positions; all 15
  old labels re-demanded and inherited. Node 2 fresh = {(2,3),(3,2)}: the
  frame-2 slot-0 digit realized at ANCHOR-OFFSET inner slot j″₀ ≡ t₁γ ≡ 1
  (mod 2), i.e. displaced one Φ₁-slot right of the block edge — (‡) confirmed.
- Downset OK at every node; final floor 5,4,3,2,0 — a gapless staircase.
- N1 (factor spans μ_{i+1}D_{i+2} ≤ μ_iD_{i+1}): OK at both steps.
- Vertex chain: the label (4,0) is the endpoint digit of ALL THREE nodes —
  pinned once (node 0), flagged inherited-hinge twice. S5.2 item 2 exercised.

### S6.2 Instance B — second read with s₀ = 1, then a tail read

n = 9; root (1,1,2) μ₀ = 4 side [0,8]; node 1 = (3,7,1) side [1,4] (s₀ = 1,
adjacent, 7/3 > 2 ✓); node 2 = tail read on window [0,1], frame-2 vertex at
v_p 7/3. VERDICTS:
- Node 1 fresh = {(0,9),(1,8)} — the (β)-strips at slot 0 LEFT of the span
  (levels above node-0's extended-line floor 8,7): REAL fresh pins that §C
  rev 2's inventory omits — plus {(2,7),(3,6)}, the fresh pattern digit.
- Node 2, first configuration (h₂ = 28, naive): REJECTED by the checker —
  naive digit labels (2,7),(3,6) already value-pinned (DISPLACEMENT flag),
  fresh = 0 ≠ nominal 2. Diagnosis: the floor FORCES the hull height at
  slot 0 (BOX excludes 28; the corrected candidates are 29 via inner slot 2,
  ≥ 30, 31), so the emitted read is h₂ = 22 (= 29 − 7), and its digit sits
  at j″₀ ≡ t₁·29 ≡ 2 (mod 3).
- Node 2 corrected (h₂ = 22): fresh = exactly {(4,5),(5,4)} = nominal (one
  F_{p²}-digit, the tail digit), at the anchor-displaced inner slot 2;
  everything else inherited; downset OK; N1 OK; the vertex hinge (8,0)
  auto-detected through the offset arithmetic (off(idx 8) = κ₁ = 7/3 lands
  the digit at level 0 = node-0's endpoint label).
- MORAL (feeds S7): line-staircase label arithmetic is exact for strips and
  for digits at unpinned labels; when a naive digit label is already pinned,
  the read's data is either FORCED (realizability arithmetic on the history
  data — h₂ = 28 was unrealizable) or the digit equation resolves through
  carries to a strictly ≺-later fresh label. Counts are always nominal
  (D.11); addresses are naive-exact only off the pinned set.

---
*(S7 appended — the deliverable.)*

### S7 Proposed replacement for C.1.0(b), with C.1 adjustments

DIVERGENCES FROM THE CURRENT §C TEXT (stated plainly): (1) the child window
is anchored at base 0, NOT "at the side's base offset" — the span containment
in the current (b)(ii) is FALSE for s₀ > 0, and the width inequality bounds
FACTOR spans, not window spans; (2) window spans can OVERHANG at increments
(the child vertex block, up to (e'g'−1)D beyond Win_i) — nesting holds for
factor spans + a rim clause, not for windows; (3) E(ν) has three clause
species — the (β)/(γ) out-of-span clauses are missing from C.1's case
analysis and contribute REAL fresh pins ((β): S6.2) plus two DATA-side
consistency conditions; (4) digit-pin ADDRESSES are naive only off the
pinned set (S6.2's tail read) — C.1 must consume pin COUNTS and freshness,
never addresses.

------------------------------------------------------------------
REPLACEMENT TEXT — C.1.0(b):

(b) REGIONS AND NESTING, corrected. (i) ν_{i+1}'s clause region is the FULL
current window Win_i = frame-(i+1) slots [0, μ_i] (base span
[0, (μ_i+1)D_{i+1}) ∩ [0,n), anchored at 0): a hull-side read asserts (α)
span clauses on [s₀', s₀'+w'], AND (β) strictly-above-extended-line clauses
at slots < s₀', AND (γ) the same at slots in (s₀'+w', μ_i]. (ii) FACTOR
spans nest: μ_{i+1}D_{i+2} ≤ w'D_{i+1} ≤ μ_iD_{i+1} (the width inequality);
Win_{i+1} = factor span ∪ its vertex block, and only the vertex block can
overhang Win_i (never at recenterings: D_{i+2} = D_{i+1}). (iii) RIM: no
node ever places a fresh pin at base indices ≥ μ_iD_{i+1} carrying ν_i's
transport data — every later demand there unfolds, per block, parallel to
ν_i's line (slope w(Φ̂_i) per slot) from an entry value ≤ old_i, hence is
implied (I-aug + the vertex-entry inequality). (iv) LEVELS: as before
(affine conversion, strictness transfers).

ADJUSTMENTS TO C.1 (the decomposition lemma):
- (i) [implication] extend the clause comparison to (β)/(γ): (β) clauses and
  (γ) clauses left of the crossing slot j× are STRONGER than BOX — their
  strips (old, new-ext] are FRESH and belong to E_fresh; (γ) at and right of
  j× is implied by BOX; the two purely-data conditions — old(μ_i) > new(μ_i)
  in the non-adjacent case, and endpoint/vertex value matches at hinges —
  are SIDE CONDITIONS on the history data (unrealizable histories excluded),
  not equations of any E.
- (ii) [freshness] the case analysis runs per clause species: interior-span
  strips/digits (as now), the right-endpoint hinge (as now), (β)-strips
  (always fresh), (γ)-strips (fresh iff non-adjacent, up to j×). Fresh pins
  always lie at base indices < μ_iD_{i+1} at levels strictly above the
  cumulative floor (downset invariant, (INV) of the derivation note); pin
  COUNTS are D.11-nominal. No claim is made about the base ADDRESS of a
  digit equation whose naive (line-staircase) label is already pinned: such
  an equation re-solves through the D.8 carries to a fresh ≺-later label,
  and C.2's counting consumes only |pins| and freshness.
- Everything else in C.1/C.2 (canonical E_fresh selection, Π-recursion,
  transport corollary, the volume product) is unchanged; the pin-set
  well-definedness lemma (PIN-WELLDEF, S2.3) should be added to C.0.5's
  corollary, since the freshness bookkeeping silently uses it.
------------------------------------------------------------------

Derivation record: S2–S6 above; instances machine-checked
(/tmp/c10b_check.txt). Sealed-gate cross-check recommended before adoption:
a Case-L-style census with s₀ > 0 (the (β)-strip prediction is new).
