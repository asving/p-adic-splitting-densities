# GD23 — the GD dictionary unit (GD-2 ⊕ GD-3): frame/valuation tie, development identity, residual dictionary, over an ARBITRARY complete DVR — verification brief (rev 0)

Unit: SYNTH4 (`lean/notes/SYNTHESIS_PASS4_2026-08-01.md`) §1 families **GD-2**
(frame/valuation tie + development identity) and **GD-3** (residual dictionary),
merged into ONE MacLane/GMN unit and stated over an arbitrary complete DVR with
perfect residue field, per the adjudicated plan (§3.2 step 3: "stated over an
arbitrary absolutely-unramified complete DVR from the start — kills most of
D-3"; this brief states everything over an arbitrary complete DVR, which is
wider and costs nothing). Author: Fable prover, 2026-07-31. Status protocol:
PROVED-UNVERIFIED until hostile fresh-context passes accept it.

Composed sources (the ~30% named by SYNTH4's mapping table): O-1thr rev 4
(`O1thr_phaseB_verifybrief_rev4.md` §§1.1, 2.1–2.5 — Lemmas DEV/POS/VAL1/KEY1/
DIV1/WGEO, the (V1)/(V2) statements); O-2a rev 5
(`O2a_phaseB_verifybrief_rev5.md` §§1, 4 — the (L1)–(L9) GMN transcriptions,
the stage interface [F.0]–[F.2], OL-2/OL-2-min/OL-3/OL-3-min, the PROVED (D3));
M08 (`M08-cl6-general_fable.md` §3 — OL-B); `docs/GMN_citations.md` (pinned
loci). Falsifier: `verification/openmath/gd23_check.py` — run BEFORE this brief
was written (§9).

## 0. What is claimed, in one paragraph

Over an arbitrary complete DVR O (fraction field K, normalized valuation v,
residue field F — perfectness of F carried as a standing hypothesis for the
consumers, USED NOWHERE in this brief's proofs, §1.1), the engine/GMN seam's
mathematical middle term is the MacLane augmented-valuation chain w_i (§1.2).
The brief proves, outright and self-contained at the displayed perimeters:
the full order-≤1 layer at EVERY root-key degree d₀ (Lemmas DEV-g/POS-g/
GAUSS-g, Theorems VAL-g/KEY-g/RES-1 — generalizing O-1thr's VAL1/KEY1/DIV1
from d₀ = 1 over ℤ_p to any d₀ over any O, and closing the order-1 residual
dictionary in full, twists absent); the **development identity at EVERY order**
(Theorem DEVID — the (V2b) family member, proved from (V1) + the key-minimality
block by a graded argument that replaces DIV1's slot-chase and is degree- and
ring-free); the uniqueness half of the frame tie (Lemma UNIQ) so that the
MacLane↔GMN identification w_i = v_{i+1} (Theorem TIE) rests on exactly three
GMN transcriptions, two already pinned and one flagged; and the stage-polygon/
record dictionary (Corollary REC-c1) as a corollary shape. GD-3's general-order
residual dictionary is split: the MIN CORE (all the recut cluster consumes, per
V25) gets TWO independent routes — one through a single flagged GMN lemma
(T-2), one through the displayed residue-structure input (GR-B); the FULL form
and the OL-B slot-bijection law are proved FROM (GR-B), whose order-1 instance
is proved here (RES-1) and whose general form is the note's one genuinely open
input, pinned to MacLane §§9–12 / FGMN 2015 (§7, §11). The engine-conformance
half of every carrier statement (that the ENGINE's emitted records are computed
by these formulas) is NOT claimed — it is displayed as the GD-4/GD-6/S-1
residue, and the brief instead proves the interface-instantiation clause: the
stage-interface axioms hold AT the MacLane/GMN valuation (Corollary IFACE).

**Status table.**

| claim | scope | status |
|---|---|---|
| DEV-g, POS-g, GAUSS-g | any O, any d₀ | PROVED (§3) |
| VAL-g: w₁ valuation, gr = K₀[π̄^{±1}][Φ̄₀] UFD | any O, any d₀ | PROVED (§3) |
| KEY-g: standard lift key laws + min core at order 1 | any O, any d₀ | PROVED (§3) |
| RES-1: order-1 residual dictionary, full form, OL-B order-1 | any O, any d₀ | PROVED (§3) |
| DEVID: development identity, every order | any O | PROVED given (V1)+(KPa) at that order (§4) |
| V1-tower: every w_i a valuation | any O | PROVED order ≤ 1; MacLane Thm 4.2 + (KP) beyond (§5; pin + one scope flag) |
| UNIQ (tie uniqueness) | any O | PROVED (§6) |
| TIE: w_i = v_{i+1} (GMN) | GMN's scope (K/ℚ_p finite) | PROVED modulo pins (L2)/(L4-P2.7) [in hand] + T-1 [FLAGGED] (§6) |
| REC-c1: window polygon = N_{i+2}(f), record verbatim (c1) | as TIE | corollary of TIE + DEVID (§6) |
| GD3-MIN (general order) | as TIE | route A: TIE + T-2 [FLAGGED]; route B: (GR-B) (§7) |
| GD3-FULL + OL-B (general order) | any O | PROVED from (GR-B) [displayed open/cited input] (§7) |
| IFACE: [F.0]–[F.2] hold at w | any O | (S-K1)+(u-mult) PROVED; dig laws = (GR-B); order 1 PROVED (§7.4) |
| engine conformance (u = w for the implemented engine) | — | NOT CLAIMED (GD-4/GD-6/S-1 residue; §8) |

## 1. Setting

### 1.1 The base ring, and where each standing hypothesis is used

O: a complete discrete valuation ring, π a uniformizer, v the normalized
valuation (v(π) = 1), K := Frac O, F := O/πO. Standing hypotheses per the unit
spec: O complete, F perfect. **Usage display (attackable):**

* **Completeness is used in NO proof of this brief.** Its consumers are the
  GMN factorization theorems (Thms 1.15/1.19/3.1/3.7 — splitting f into
  factors needs Hensel-type completeness), which this brief cites only inside
  the FLAGGED route-A input T-2 and nowhere else. Every PROVED statement below
  holds over any DVR.
* **Perfectness of F is used in NO proof of this brief.** The residue tower
  K_{i+1} = K_i[z]/(ψ_i) is a tower of fields for any F. Perfectness is
  carried because the project's consumers (separability of residual counts,
  the BB3/L3 finite-field layer) assume it, and because GMN's own scope is
  F finite. It costs nothing to carry.
* Consequently the statements INSTANTIATE at O = ℤ_p, at O = O_δ = W(F_{p^δ})
  (the unramified re-base of D-3/O-8b — **this is the D-3 kill**: T-1-style
  stage laws over O_δ are instances, not a transfer theorem), and at
  equal-characteristic O = F_q[[t]] (exercised by the falsifier, §9).
* GMN's own theorems remain scoped to K/ℚ_p finite (their standing hypothesis,
  `GMN_citations.md` audit-fix); the TIE/T-2 clauses are therefore claimed at
  GMN's scope, and their arbitrary-DVR generalization rides the (GR-B)/FGMN
  pin (FGMN 2015 works over an arbitrary discretely valued field — scope flag
  in §11).

### 1.2 The tower: policy, frames, the MacLane chain, and the three-term seam

Transcribed from O-1thr rev 4 §1.1 with ℤ_p → O throughout (the transcription
is verbatim except v_p → v, p → π, 𝔽_p → F).

* **Policy 𝒫**: (i) to each monic irreducible φ̄ ∈ F[X], a monic lift
  Φ₀ ∈ O[X] with deg Φ₀ = deg φ̄ =: d₀; (ii) to each lawful node ν over a
  frame of order i, a monic key Φ_{i+1} ∈ O[X] with
  deg Φ_{i+1} = e_i·g_i·deg Φ_i. All statements are relative to one fixed 𝒫.
* **Order 0**: w₀(B) := min_j v-content(c_j) over the Φ₀-adic development
  B = Σ_j c_j Φ₀^j (v-content := min of coefficient valuations);
  K₀ := F[z]/(φ̄). (Lemma GAUSS-g: w₀ = the plain Gauss valuation, and a
  valuation.)
* **Order i+1**: given the frame (Φ_i, w_i, K_i) and a read ν_i with data
  (e_i, h_i) coprime ≥ 1 and ψ_i ∈ K_i[z] monic irreducible of degree g_i with
  ψ_i(0) ≠ 0: set γ_{i+1} := e_i·w_i(Φ_i) + h_i and
  w_{i+1}(B) := min_j ( e_i·w_i(c_j) + j·γ_{i+1} ) over the Φ_i-adic
  development; K_{i+1} := K_i[z]/(ψ_i). E_i := w_i(π) = e₀e₁⋯e_{i−1};
  γ̂_i := w_{i+1}(Φ_{i+1}).
* **The MacLane display.** w_{i+1} is EXACTLY MacLane's augmented value
  [e_i·w_i ; w_{i+1}(Φ_i) = γ_{i+1}]: the augmentation of the (rescaled)
  order-i valuation at its own key Φ_i, assigning Φ_i the strictly larger
  value γ_{i+1} > e_i·w_i(Φ_i) (h_i ≥ 1). This display is what closes the
  V24-G6 "owed correspondence" for (V1): the §1.1 chain of O-1thr IS the
  MacLane composite, now said with the augmentation exhibited (§5).
* **The three-term seam.** Three valuation-like objects appear at the
  carriers: **u** (the engine's [F.0] side valuation — an axiom of the stage
  interface, O-2a §4), **w** (the MacLane chain above — a mathematical
  object), **v_r** (GMN's order-r valuation, (L2)). This brief proves
  statements about w and about w = v (TIE); the u = w half is engine
  conformance (the intended proof routes of OL-2/OL-5/OL-6, owned by
  GD-4/GD-6 and the S-1 transcription audit) and is NOT claimed here. What
  IS proved here about u's axioms: they are SATISFIED by w (Corollary IFACE,
  §7.4) — "the engine's axiom holds at the GMN valuation" (SYNTH4 §1, GD-2
  note).
* **Index dictionary (a standing transcription hazard, displayed).** O-1thr's
  0-based reads vs GMN's 1-based orders: Φ_i ↔ φ_{i+1}, w_i ↔ v_{i+1},
  (e_i, h_i) ↔ (e_{i+1}, h_{i+1}), K_i ↔ F_{i+1}, ψ_i ∈ K_i[z] ↔
  ψ_{i+1} ∈ F_{i+1}[y]. Constants check: w_i(π) = E_i = e₀⋯e_{i−1} =
  e₁^{GMN}⋯e_i^{GMN} = v_{i+1}(π) — matching (L2)'s index e₁⋯e_{r−1} at
  r = i+1. O-2a's stage at level i+1 speaks GMN indexing (its constant test
  u_{i+1}(π) = E_i is the same number).

### 1.3 Graded vocabulary

For a function w : K[x]∖{0} → ℤ with w(AB) ≥ w(A) + w(B) and
w(A+B) ≥ min(w(A), w(B)) (a semivaluation): P_γ := {A : w(A) ≥ γ} ∪ {0},
P_γ⁺ := {A : w(A) > γ} ∪ {0}, gr(w) := ⊕_{γ∈ℤ} P_γ/P_γ⁺ (graded pieces over
K[x]; π̄ := in(π) is then invertible, since w(π^{−1}) = −w(π) makes
in(π)·in(π^{−1}) = in(1) = 1). in(A) := the class of A in gr_{w(A)}.
Facts used (displayed, elementary): (g1) if each w(x_j) = γ and
w(Σ x_j) > γ then Σ in(x_j) = 0 in gr_γ; (g2) w is a VALUATION
(w(AB) = w(A)+w(B) always) iff in(A)·in(B) = in(AB) ≠ 0 for all A, B, iff
gr(w) is a domain; (g3) ord_δ(α) := max{k : δ^k | α} is well-defined in a
domain for homogeneous δ of positive weight-or-degree data bounding the chain.

## 2. The merged statements (what GD-2 ⊕ GD-3 assert)

Fix a policy 𝒫 and a lawful chain of reads ν₀, …, ν_i building frames through
order i+1 as in §1.2, and let f ∈ O[x] be monic with the creating read ν_i
satisfying, on f, (R1) at all slots and (R2) at its strides (the standing
WGEO hypothesis of O-1thr §2.5 — side support with equality only at strides,
and exact digit pins at the strides; at a root state, ROOT-M's
ord_{φ̄}(f̄) = m ≥ 2 setting).

**GD-2 (frame/valuation tie + development identity).**
(a) each w_j (j ≤ i+1) is a valuation on K[x], ℕ-valued on O[x]∖{0}
    ((V1)); and w_j = v_{j+1}, GMN's order-(j+1) valuation over the same
    (policy-pinned) representatives — the engine ℤ-normalization being the
    SAME normalization (no rescaling; §1.2 index dictionary);
(b) the state key's development computes the state valuation from below:
    for every nonzero B ∈ K[x], with B = Σ_k C_k Φ_{i+1}^k the
    Φ_{i+1}-development, w_{i+1}(B) = min_k ( w_{i+1}(C_k) + k·γ̂_i ) ((V2b));
(c) hence the state window polygon — the lower hull of the sheared points
    (k, u_k), u_k := w_{i+1}(C_k) + k·γ̂_i, of f's Φ_{i+1}-development — IS
    GMN's N_{i+2}(f), vertex for vertex, and the (c1) side data
    (e, h, ℓ, s, u) of any principal side agree verbatim in the order-(i+2)
    integer frame.

**GD-3 (residual dictionary).** With ψ̂_hom := in(Φ_{i+1})·(unit monomial)^{−1}
the key initial form ((KPa)):
(min core) ord_{ψ̂_hom}(in(f)) = ord_{ψ_i}(R_λ(f)) — the level-i residual
    polynomial computes the ψ-order of the initial form ((V2c); all the recut
    cluster consumes, per V25's split);
(full form) the anchor-normalized stage residual satisfies
    R^{nrm} = c·R_λ(f), c ∈ K_i^× — the z-power twists of GMN Def 2.20 are
    absorbed exactly by the single anchor-unit division of [F.2];
(slot law, = O-9's OL-B) each stride's residual-coefficient read is
    (fixed unit twist)·(residue), a BIJECTION of K_i per slot; no un-cancelled
    z ↦ z^a, a ≥ 2, survives.

**Displayed inputs** (each with owner and proved perimeter):

* **(KP_j), j ≤ i (from GD-1, cumulative).** Φ_{j+1} is monic of degree
  e_j·g_j·deg Φ_j and: **(KPa)** in_{w_{j+1}}(Φ_{j+1}) = u·ψ̂_hom^{(j)} with u
  an invertible homogeneous element of gr(w_{j+1}), and ψ̂_hom^{(j)} ∤ in(B)
  for EVERY nonzero B ∈ K[x] with deg B < deg Φ_{j+1} (the minimality/degree
  block); **(KPb)** R_j(Φ_{j+1}) ∼ ψ_j (the Def-2.12 residual normalization).
  Proved perimeter: at j = 0 for the STANDARD lift at any d₀ — Theorem KEY-g
  (§3), extending O-1thr's KEY1 (d₀ = 1, ℤ_p). At the order-0 key itself the
  analogous block is FREE for any monic lift (Lemma GAUSS-g(iii)). Beyond:
  GD-1's business (GMN Thm 2.11/Def 2.12; MacLane Def 4.1).
* **(ML) MacLane Thm 4.2** (augmented values are valuations) — §5, pinned.
* **(T-1), (T-2)** — two GMN transcriptions, §6/§7, one in hand, one flagged.
* **(GR-B)** — the residue-structure package at orders ≥ 2, §7.2, cited
  (MacLane §§9–12; FGMN 2015) and proved at order 1 here.

END-OF-PART-1
