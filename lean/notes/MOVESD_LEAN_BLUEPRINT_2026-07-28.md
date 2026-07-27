# MOVESD LEAN BLUEPRINT — REV 4

Campaign unit-spec per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2. Writer: Fable.
REV 4 (2026-07-28): triage of the CONFLICTING rev-3 verdicts — Codex FINAL#2
(`MOVESD_AUDIT_CODEX_FINAL2_2026-07-28.md`, REJECT 8/2) vs Fable#2
(`MOVESD_AUDIT_FABLE2_2026-07-28.md`, REJECT 1/1, WITH gate-numeric evidence:
reproduced Nshape(P̂*) = 5, A(P̂*) = 11, W = 7, M = 1, and counterexampled rev 3's
class construction at the sealed gate). Protocol: evidence beats plausibility; every
Codex finding contradicted by Fable's re-derivation is re-verified here and either
FIXED or PUSHED BACK with note lines + gate numbers (§10 table). HEADLINE REPAIRS:
the η-granularity is REBUILT conjugation-free (the canonical RESIDUE-ROOT rule joins
the canonical-lift rule — Fable C1; the gate numbers re-derived in §0.6, MANDATORY);
`EligibleImage` is the explicit TRANSPORTED predicate (Fable G1 ≈ Codex 3);
the unconditional coarse pool bound W3 (Codex 5); `hne` on the C-carrying mass laws
(Codex 6, second half); the honest presentability hypothesis PRESENT-EXIST named and
wired (Codex 7); representative-independence pinned as ClassFiberWelldef (Codex 9);
VerdictModel gains the finite-level locality law (Codex 10). PUSHBACKS (evidence in
§10): Codex 1 (monicTop — partially conceded: root-species guard added), Codex 4
(CanonPolicy), Codex 6 first half (empty ontology), Codex 8 (TreeModel).
REV-2 table at §9, REV-3 at §10, REV-4 at §11.

## 0. Source and ground truth

SOURCE: `lean/notes/MOVES_2026-07-24.md`, `## §D4-R — the per-shape-prefix mass law`
(lines ~4580–5432), **rev 9**, DUAL-ACCEPTED 2026-07-27 (Codex pass 11 + Fable confirm
CLEAN on identical text). KERNEL STATUS: D4R.0-K parts (a) L1 totality and (b) L5
digit-cell exhaustiveness DISCHARGED by `D4R0K_DERIVATION_2026-07-26.md` rev 3
(dual-verified); residual (c) = the verdict pin VP (alphabet V + halting rule τ + the
uniform per-class detection cap), OPEN, owned by §T-ASSEMBLY → MovesT. §D4-R's
conditionality: dual-accepted §C (rev 14) + §B2-DEF (D¹¹d) + (c)/VP.

TARGET DISPLAYS: D4R.1-SUM, D4R.1-EV (equality iff mult ≡ 1), D4R.2′ (C ≤ M·p^W,
M ≤ n^{|P̂|}), Corollary D4R.2 (A_net), D4R.4-SUM/EV at every N ≥ N(P̂), and the η = ∅
dispatch (Pref(∅) = {∅}, C_∅ = 1, A(∅) = 0, S(∅,⊤) = the full box) — quoted per unit.

## 0.5 THE ROUTE-(1) ADJUDICATION REPORT (offSlots_forced — what the note supports)

Re-reading L11's injectivity proof verbatim: "given the shape and the digit tuples
through read i−1 AND the indices s₀,…,s_{i−1}, the node data … are reconstructed
(digits give each R_anch; s_r picks ψ_r; canonical lifts are functions of node data,
L1)". The mechanism is: digit tuple → R_anch → (with s_r) → ψ. It needs NO off-slot
data at any read where the digit tuple covers all of R_anch's coefficients — which by
the note's own pinned instance is EVERY read except one case: the ROOT full-span read,
where "slot 3 = the monic lead, digit 1" (§D4-R.6) is excluded from the tuple
(d₀ = 3, not 4) and R₀ = z³+d₂z²+d₁z+d₀ is reconstructed using the MONIC lead 1 — a
fact of the monic degree-n BOX, displayed by the note, not a per-shape convention.
At depth ≥ 1 the lead IS in the tuple (d'₁ counted in W, "the (HV)-forced lead makes
the pool bound strict — slack displayed"). VERDICT: **route (i) holds at every slot
except the root monic lead, whose forcing the note itself displays as the monic-box
convention.** REV 3 therefore DELETES the blanket `offSlots_forced` and replaces the
free `slots` field by a single Boolean `monicTop` per read (is the side's top slot the
box's monic lead?) with the ONE scoped Matches tie `monicTop → sideDigit(ℓ_r) = 1` —
an interface equality justified by the quoted display; d_r := ℓ_r + (monicTop ? 0 : 1)
reproduces the note's counts (d₀ = 3 at ℓ₀ = 3; d₁ = 2 at ℓ₁ = 1). No blanket rule,
no new open hypothesis.

## 0.6 THE η-GRANULARITY REBUILD + THE MANDATORY GATE CHECK (Fable#2 C1)

THE REV-3 DEFECT (gate-evidenced): ambient-valued `etaData` split one note-η into
Galois-conjugate presentations. Fable#2's witness at the sealed gate (§D4-R.6, P̂*,
p = 2): ν₀.zbar ∈ {ω, ω²} (the two roots of ψ = z²+z+1 in the order-4 subfield);
both choices extend to PrefSet members (conjugated stages satisfy every law by
equivariance); (HV) forces the depth-1 lead d'₁ = z̄ − r = ω−1 vs ω²−1 — DISTINCT
F-values, distinct rev-3 classes, ONE note-η. Corpus C = 6 vs the SEALED
C_P̂*(2) = 3; corpus mult ≡ 2 vs the note's gate re-derivation "mult_P̂* ≡ 1 …
EV-equality". The note's η carries NO residue-root datum (L2: children are "(side s,
its digit tuple, ψ, canonical lift)"; digits range in the abstract pool 𝔸_r).

THE REBUILD (Fable#2's recommended route, parallel to the lift normalization): the
CANONICAL PRESENTATION rule gains a residue-root clause. `canonRoot ν` := the
`fieldEnum`-least root of `ψImage ν` in F (§3.4); `IsCanonPres pol H` := the lift
rule AND `(ν_r.zbar : F) = canonRoot ν_r` at every read (§3.2). `PrefSet` requires
`IsCanonPres`. Each note-η then has exactly ONE presentation class: the root choice
at every read is pinned (recenterings were already pinned — `hspecRecCenter`), so
`etaData` no longer sees a conjugation orbit, and by induction the residue-tower
embedding per read is CANONICAL (root: the prime field embeds uniquely; depth r+1:
z ↦ the pinned least root) — abstract-η data ⟺ image data. The residual semantic
duty (every η HAS a root-normalized presentation, via conjugation equivariance of
the Stage/Node laws — Fable#2 exhibited the action; and uniqueness via embedding
rigidity of finite fields) is the DECLARED pin **PRESENT-NORM** (§2 ledger, HC-2) —
exactly parallel to the junk-lift normalization already declared.

THE MANDATORY GATE CHECK (re-derived step by step from the rebuilt construction;
acceptance test per the triage protocol):
- P̂* data: read 0: (e,h,g,μ,a) = (1,1,2,1,0), span [0,3], u*₀ = 0, monicTop = true,
  ℓ₀ = 3, d₀ = 3, w₀ = 1; read 1: (1,3,1,1,0), span [0,1], u*₁ = 1, monicTop = false,
  ℓ₁ = 1, d₁ = 2, w₁ = 2. W = 1·3 + 2·2 = 7 ✓; m̄₀ = ⌊3/2⌋ = 1, m̄₁ = ⌊1/1⌋ = 1,
  M = 1 ✓; Nshape = 1 + max(⌈3⌉, ⌈4⌉) = 5 = N(P̂*) ✓; A = 9 + 2 = 11 ✓ (Fable#2
  reproduced all four from these defs).
- C_P̂*(2), by enumerating the rebuilt classes: read-0 digit tuples (d₂,d₁,d₀) ∈ F₂³
  with realizability R₀ = ψ·(z−r): the unique irreducible quadratic ψ = z²+z+1 and
  r = 1 give R₀ = z³+1, tuple (0,0,1) — 1 tuple × 1 ψ-image. zbar₀: rev 3 had 2
  choices (ω, ω²) → NOW PINNED to canonRoot = the fieldEnum-least root: ×1. Read 1:
  recentering — ψ₁ = z − s determined by the digits (s = −d'₀/d'₁), zbar₁ = center
  pinned by `hspecRecCenter`; digit tuple (d'₀, d'₁): d'₁ = z̄ − r is (HV)-FORCED
  (×1, now the CANONICAL value ω₀ + 1), d'₀ ∈ F₄ˣ free (×3).
  **C_P̂*(2) = 1·1·3 = 3 ✓ = the sealed count** (note: "C_P̂*(2) = 1·1·3 = 3").
  Likewise p = 3: 3 quadratics × r ∈ {1,2} = 6 tuples, d'₀ ∈ F₉ˣ free (×8):
  **C_P̂*(3) = 6·8 = 48 ✓**.
- mult ≡ 1: within P̂*, distinct classes occupy distinct digit cells (per cell the
  eligible quadratic is UNIQUE: deg R₀ = 3 < 2·g₀·μ₀ = 4, and R₁ is linear — the
  note's FACTOR SELECTION line), and the rev-3 conjugate pair is now ONE class; so
  each f in the event realizes exactly the one class of its cell: **mult_P̂* ≡ 1 ✓**,
  D4R.1-EV/D4R.4-EV with EQUALITY — the note's gate re-derivation verbatim.

## 1. The consumption design (what is consumed, what is proved, what remains open)

CONSUMED from MovesC (36/36 PROVED): `History`/`Node` (a realized prefix IS a MovesC
history; `ustar`/`gam`/`pat` are the rev-9 retained fields), `Realizable`
((NA)+(HV)+(SAE)), `HistoryCoherent`, `JetSetup`/`SHZ`/`totalPins`/`mstar_eq`,
`C6_thmC_b` (each summand), the node Props `hRanch`/`hpat0`/`hpatTop`/`hψmonic`/
`hψdeg`/`hψirr`/`hOrd`/`hbezCanon` (these power the PROVED encoding chain).

PROVED IN-CORPUS at rev 3 (previously assumed — findings 3/4/7 of the final audit):
- L8 finiteness and the L11 injection: the note's η is (shape, digit tuples, ψ's,
  canonical lifts) with lifts FUNCTIONS of node data (L1) — so the corpus counts the
  η-CLASS `etaData H` (digit tuples + ψ-coefficient tuples, ambient-field-valued) of
  histories in `PrefSet`. `EtaData` is a finite type, L8 is structural, and the
  injection (digits, factor-rank) ↦ class is PROVED (chain E1–E9) from the node Props:
  deg R_anch = ℓ_r, g·μ ≤ ℓ, the eligible-factor count ≤ m̄_r (coprimality of distinct
  monic irreducibles), the frame-field image = THE p^w subfield (uniqueness in a
  finite field), rank injectivity on the common eligible set. D4R.2′ follows PROVED.
- "deg R_anch,r ≤ n always" (finding 4): PROVED for members via `InBox` (the root side
  lies in the degree-n box — a clause of `PrefSet`, i.e. of "§C history of the
  degree-n box") + the coherence window chain + g·μ ≤ ℓ; `Mfac_le` carries the
  shape-transported `Wellformed` hypothesis PROVED for every inhabited shape (W1) —
  no free rider remains.
- The family is CONSTRUCTED (finding 3): `PrefIdx := ↥(etaData '' PrefSet)`,
  `reprOf` a classical section (a def, not a field), enumeration laws are THEOREMS
  (F1). The SOLE assumed field left is `Presented.jet` (HC-2 presentations).

REMAINING OPEN SURFACE (each a named, typed object — §2 ledger):
`CanonPolicy` parameter `pol` (WHICH policy = the (S6b) offset-P formula; §B2-DEF/
HC-1 pins it; the POLICY LAWS — lift a function of node data, per-node, hence
prefix-monotone and never-empty — are structural, so `Canon := False` is gone:
finding 2); `Presented.jet` (HC-2); the pinned Prop `D4R_CYL` (L6's theorem —
EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus, a hypothesis of D15's bridges,
never a structure field restated as a theorem: finding 7); the `TreeModel` child-
relation data with L2's laws (gap 8); `VerdictModel`'s typed (c)/VP surface with the
halt dichotomy and the per-class detection-cap law (gap 9).

FINITE-LEVEL POLICY: unchanged — `Nat.card` over `Box p m`, division-free. NEW at
rev 3 (finding 5): the count C := `Nat.card (PrefIdx n pol P)` is N-FREE by
construction; the exponent `A′ P n := P.A n (Nshape P)` is N-free via the shape
height bound `Nshape` (the note: "an a priori shape bound on N(P̂) is available");
D10/D12/D13 quantify `∀ N ≥ Nshape P` over all presented setups at that N — D4R.4's
uniform quantifier, with cross-level compatibility automatic (same C, same A′).

## 2. Open-surface ledger (never silently strengthened or dropped)

| object | encodes | status |
|---|---|---|
| `pol : CanonPolicy p F` (parameter) | WHICH canonical policy (the (S6b) offset-P formula) | OPEN parameter, pinned by §B2-DEF/HC-1; its LAWS (lift = function of node data, per-node) are structure fields — `False` not expressible |
| `Matches.hmonic` | root monic lead digit = 1 (scoped, §0.5) | interface equality justified by §D4-R.6's display + the monic box; the ONLY off-tuple forcing |
| `InBox n` (PrefSet clause) | the root side lies in the degree-n box | part of "§C history of the degree-n box" (the note's setting); consumed by W1 |
| `Presented.jet` | per-class presentation at level N (N ≥ N(η,⊤), §C C.2) | HC-2 bridge — THE sole assumed structure field of the corpus |
| `D4R_CYL S T` (pinned Prop, def) | L6's (D4R-CYL) | note-PROVED given kernel (a)+(b) (both dual-verified-discharged) + Thm C(a); Lean proof EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus; D15 consumes it as a named hypothesis |
| `TreeModel` data (`mem`, `child`) + laws | L2's T_can | interface data; laws are fields; uniqueness/eligibility semantics = kernel-(b) content, HC-2 |
| `VerdictModel` (whole) | D4R.0-K(c)/VP: alphabet V, emission, halt dichotomy, per-class cap law | **OPEN** — owned by §T-ASSEMBLY → MovesT; typed, consumed by nothing in MovesD |
| `hN : 1 ≤ N`, `hm : m = n*N` (D14a/D14b hyps) | L12's empty-case N(P̂) := 1 convention; the box shape | explicit theorem hypotheses (no jet available) |
| **PRESENT-NORM** (declared pin) [REV 4] | every note-η has EXACTLY ONE root-normalized presentation class (conjugation equivariance of the Stage/Node laws + finite-field embedding rigidity — Fable#2 C1's repair route; §0.6) | HC-2; the classes ↔ η dictionary rests on it; gate-checked at §0.6 (3/48, mult ≡ 1) |
| **PRESENT-EXIST** (declared hyp) [REV 4, Codex#2 f.7] | `∀ N ≥ Nshape P, Nonempty (Presented p F n N (n*N) pol P)` — presentability at every sufficient level (§C C.2's N(η,⊤) presentations) | HC-2; consumed EXPLICITLY by the wrapper unit D4R4_all; D10/D12/D13 remain ∀-statements over supplied S |
| **ClassFiberWelldef** (pinned Prop, def) [REV 4, Codex#2 f.9] | representative independence: `∀ H H' ∈ PrefSet, etaData H = etaData H' → ∀ jets J, J', J.SHZ ⊤ = J'.SHZ ⊤` (one η-class, one classifier locus — §C L4's semantic content) | HC-2 (wave-4 tree corpus, with D4R_CYL); D15's specs cite BOTH pins |
| **POL-PIN** (future unit, named) [REV 4, Codex#2 f.4] | the instance `pol := the (S6b) offset-P policy` with its realizer laws | owned by HC-1/§B2-DEF corpus; until then all MovesD theorems are ∀-pol |

GONE at rev 3 (previously assumed): `henc` (→ PROVED, E1–E9), `hn : ℓ_r ≤ n`
(→ PROVED, W1), `complete`/`hist_inj`/`hshape`/`hcanon` (→ the construction, F1),
`offSlots_forced` (→ the scoped `hmonic`), `TreeModel.cyl` field (→ the pinned
deferred Prop `D4R_CYL`), bare `cap`/`hcap` (→ the typed cap law).

## 3. Defs skeleton — `lean/LeanUrat/MovesD/Defs.lean` (definitions only)

### 3.1 Box, top locus, shape reads (monicTop replaces slots — §0.5)

```lean
import Mathlib
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

abbrev Box (p m : ℕ) : Type := Fin m → ZMod p

/-- Z = ⊤ (§D4-R L6: "no constraint, vol(⊤) = 1"). -/
def topLocus (p m : ℕ) : Locus p m := { pinned := fun _ => false, solve := fun _ _ => 0 }

/-- One read of a shape-prefix — §D4-R L3 rev 9 retained fields: species, (e,h,g,μ,a),
side data (s0, wSide, Dwidth), the height PAIR (h, u*) [pass-10 F1 CRITICAL], γ, pool
degree w (Q_r = p^w, w ≥ 1), and `monicTop` — whether the side's top slot is the box's
monic lead (§0.5; the stride-position/slot-set datum of L3, reduced to its one degree
of freedom: all other positions always carry tuple digits). Values and lifts forgotten. -/
structure ShapeRead where
  species : ReadSpecies
  e h g μ : ℕ
  a : ℤ
  s0 wSide Dwidth : ℕ
  ustar : ℚ
  gam : ℤ
  w : ℕ
  monicTop : Bool
  he : 1 ≤ e
  hg : 1 ≤ g
  hμ : 1 ≤ μ
  hw : 1 ≤ w
  hDw : 1 ≤ Dwidth
  /-- [REV 4, Codex#2 finding 1 — partial concession]: the monic lead exists only at
  the ROOT read (the box's top coefficient; deeper windows sit inside the box). -/
  hmonicRoot : monicTop = true → species = ReadSpecies.root

def ShapeRead.len (R : ShapeRead) : ℕ := R.wSide / R.e         -- ℓ_r = deg R_anch,r
def ShapeRead.d (R : ShapeRead) : ℕ :=                          -- d_r (the tuple size)
  R.len + (if R.monicTop then 0 else 1)
def ShapeRead.mbar (R : ShapeRead) : ℕ := R.len / (R.g * R.μ)   -- m̄_r (Nat ⌊·⌋)
def ShapeRead.childWidthS (R : ShapeRead) : ℕ := R.e * R.g * R.Dwidth

structure ShapePrefix where
  reads : List ShapeRead

def ShapePrefix.W (P : ShapePrefix) : ℕ := (P.reads.map (fun R => R.w * R.d)).sum
def ShapePrefix.Mfac (P : ShapePrefix) : ℕ := (P.reads.map ShapeRead.mbar).prod

/-- Shape wellformedness over the degree-n box (W1 proves it for every shape with a
member; W2 turns it into M ≤ n^{|P̂|}): the root side fits the box and the window/
degree chain descends — the note's "deg R_anch,r ≤ n ALWAYS", shape-side. -/
def ShapePrefix.Wellformed (P : ShapePrefix) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (hr : r < P.reads.length), (P.reads[r]'hr).len ≤ n
```

### 3.2 Canonical policy, PrefSet, η-classes, the constructed family (findings 1–3)

```lean
section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- A node's side digit at pattern position k, in the AMBIENT field. -/
def _root_.LeanUrat.MovesC.Node.sideDigit (ν : Node p F) (k : ℕ) : F :=
  ((ν.pat k : ↥ν.σ.K) : F)

/-- `R.Matches ν` — field equalities on the retained data (heights INCLUDED), the pool
card, and the ONE scoped monic tie (§0.5). -/
def ShapeRead.Matches (R : ShapeRead) (ν : Node p F) : Prop :=
  ν.species = R.species ∧ ν.e = R.e ∧ ν.h = R.h ∧ ν.g = R.g ∧ ν.μ = R.μ ∧
  ν.a = R.a ∧ ν.s0 = R.s0 ∧ ν.wSide = R.wSide ∧ ν.Dwidth = R.Dwidth ∧
  ν.ustar = R.ustar ∧ ν.gam = R.gam ∧ Nat.card ↥ν.σ.K = p ^ R.w ∧
  (R.monicTop = true → ν.sideDigit R.len = 1)

def ShapePrefix.MatchesHist (P : ShapePrefix) (H : History p F) : Prop :=
  ∃ hlen : H.nodes.length = P.reads.length,
    ∀ (r : ℕ) (hr : r < H.nodes.length), (P.reads[r]'(hlen ▸ hr)).Matches (H.nodes[r]'hr)

/-- **The canonical-lift policy** [REV 3, finding 2]: a DETERMINISTIC per-node lift
rule — L1's defining law "the digits t_k are FUNCTIONS of the node data … the policy
is deterministic", as structure. `liftOf` reads the node MINUS its lift (`blind`), so
a policy can never encode "no history is canonical": `IsCanon pol` is per-node,
automatically prefix-monotone (unit T1a) and total on lift-assignments — the REV-2
lawless `Canon := fun _ => False` is NOT expressible as any `IsCanon pol`. WHICH
policy (the (S6b) offset-P formula) is the open parameter, pinned by §B2-DEF/HC-1.
Junk normalization (documented): the note's policy constrains RECENTERING lifts; we
apply `liftOf` at EVERY node so the non-recentering `lift` junk field is normalized —
this is what makes the η-class granularity (below) carry the note's "canonical lifts
are functions of node data" exactly. -/
structure CanonPolicy (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  liftOf : Node p F → Polynomial ℤ_[p]
  blind : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), liftOf { ν with lift := t } = liftOf ν

def CanonPolicy.IsCanon (pol : CanonPolicy p F) (H : History p F) : Prop :=
  ∀ (r : ℕ) (hr : r < H.nodes.length), (H.nodes[r]'hr).lift = pol.liftOf (H.nodes[r]'hr)

/-- [REV 4, Fable#2 C1] The canonical RESIDUE-ROOT of a node: the `fieldEnum`-least
root of `ψImage ν` in F (junk 0 if none — realizable nodes always have one,
`hzbarRoot`). The presentation-normalization twin of the lift rule. -/
noncomputable def canonRoot (ν : Node p F) : F :=
  ((ψImage ν).roots.toFinset.image (fieldEnum F)).min.elim 0 (fun j => (fieldEnum F).symm j)

/-- **The CANONICAL PRESENTATION class** [REV 4, Fable#2 C1 — the η-granularity
rebuild, §0.6]: canonical lifts (the policy) AND the canonical residue root at every
read. The note's η carries NO root datum (L2's child data: side, digits, ψ, lift);
the root clause is a presentation normalization — each η has exactly ONE normalized
presentation class (PRESENT-NORM, §2 ledger: conjugation equivariance + finite-field
embedding rigidity, HC-2). Recenterings were already pinned (`hspecRecCenter`). -/
noncomputable def CanonPolicy.IsCanonPres (pol : CanonPolicy p F) (H : History p F) : Prop :=
  pol.IsCanon H ∧
  ∀ (r : ℕ) (hr : r < H.nodes.length),
    (((H.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H.nodes[r]'hr)

/-- The root read's side fits the degree-n box (part of "§C history of the degree-n
box" — the note's ambient setting; powers W1's ℓ_r ≤ n chain). -/
def InBox (n : ℕ) (H : History p F) : Prop :=
  ∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).s0 + (H.nodes[0]'hj).wSide ≤ n

/-- **The LITERAL Lean Pref(P̂)** (L3: shape-match + realizable + canonical lifts, in
the degree-n box). -/
def PrefSet (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) : Set (History p F) :=
  {H | P.MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧ InBox n H ∧ pol.IsCanonPres H}
-- [REV 4] `IsCanon` → `IsCanonPres` (the root-normalized presentation class, §0.6).
-- Defs-file order note: `RanchImage`/`ψImage`/`poolSubfield` (§3.4) precede this
-- section in the actual `Defs.lean` (canonRoot consumes ψImage).

/-- **The η-class data** — the note's η-granularity [REV 3, finding 3's enabler]: per
read, the side-digit tuple AND ψ's coefficient tuple, ambient-field-valued. Everything
else in the note's η is shape-pinned (Matches), derived (line by coherence+u*; (s,t)
the canonical Bézout pair; Ranch by hRanch), or policy-determined (lifts, L1). A
FINITE type: L8 is structural, and C is N-free. -/
def EtaData (F : Type*) (P : ShapePrefix) : Type :=
  ∀ r : Fin P.reads.length,
    (Fin ((P.reads.get r).len + 1) → F) × (Fin ((P.reads.get r).g + 1) → F)

noncomputable def etaData (P : ShapePrefix) (H : History p F) : EtaData F P :=
  fun r => ((H.nodes[(r : ℕ)]?).elim (fun _ => 0) (fun ν k => ν.sideDigit k),
            (H.nodes[(r : ℕ)]?).elim (fun _ => 0) (fun ν k => ((ν.ψ.coeff k : ↥ν.σ.K) : F)))

/-- **The canonical index of Pref(P̂)**: the η-classes of PrefSet. C_P̂(p) counts THESE
(the note's C counts η's = (shape, digits, ψ's, canonical lifts); lifts are
policy-determined, so classes ↔ η's — F1's semantic display). N-FREE. -/
def PrefIdx (n : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) : Type :=
  ↥(etaData P '' PrefSet n pol P)

/-- The classical representative section (a DEF, not a field — finding 3). -/
noncomputable def reprOf {n : ℕ} {pol : CanonPolicy p F} {P : ShapePrefix}
    (i : PrefIdx n pol P) : History p F := i.2.choose

/-- The corpus C with the note's η = ∅ dispatch baked in at the note's own
definition level (Pref(∅) = {∅} — §D4-R L12/D4R.1: "present iff P̂ = ∅"). -/
noncomputable def ShapePrefix.CD (P : ShapePrefix) (n : ℕ) (pol : CanonPolicy p F) : ℕ :=
  if P.reads = [] then 1 else Nat.card (PrefIdx n pol P)

/-- S(∅,⊤) — §C C.0's EMPTY HISTORY clause at Z = ⊤ (the FULL BOX; never Thm C(b)). -/
def emptyFiber (p m : ℕ) : Set (Box p m) := Set.univ

/-- **The presented family** [REV 3, finding 3]: everything is CONSTRUCTED from
`PrefSet` except the one genuinely-open datum — the HC-2 presentations. -/
structure Presented (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : ShapePrefix) where
  jet : (i : PrefIdx n pol P) → JetSetup (reprOf i) n N m

def Presented.fiber (S : Presented p F n N m pol P) (i : PrefIdx n pol P) :
    Set (Box p m) := (S.jet i).SHZ (topLocus p m)
def Presented.event (S : Presented p F n N m pol P) : Set (Box p m) := ⋃ i, S.fiber i
noncomputable def Presented.mult (S : Presented p F n N m pol P) (x : Box p m) : ℕ :=
  Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i}
```

REPRESENTATIVE CAVEAT (displayed for the audit): `fiber i` is the chosen
representative's `SHZ ⊤`. That all representatives of one η-class present the SAME
classifier locus is HC-2 semantic content (the class determines the classifier run);
formally the corpus is exact about the chosen representatives, and every mass-law
statement consumes only `jet`, Theorem C(b), and the class count — nothing
representative-dependent beyond the jet itself. Flagged for the guardian.

### 3.3 The ledger exponent A(P̂), Nshape, the N-free A′ (findings 4/5)

Unchanged mechanism from rev 2 (the shape-side replica of MovesC's fresh band; u*
enters through the line intercept — the rev-9 point), plus the N-stabilization:

```lean
def ShapePrefix.strS (P : ShapePrefix) (i : ℕ) : ℕ := ((P.reads.take i).map ShapeRead.e).prod
noncomputable def ShapePrefix.lineS (P : ShapePrefix) (r : ℕ) : Line :=
  (P.reads[r]?).elim ⟨0, 0⟩ (fun R =>
    let sl : ℚ := (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ) * (R.Dwidth : ℚ))
    ⟨R.ustar + sl * (((R.s0 + R.wSide) * R.Dwidth : ℕ) : ℚ), sl⟩)
noncomputable def ShapePrefix.kappaS (P : ShapePrefix) (r : ℕ) : ℚ :=
  (P.reads[r]?).elim 0 (fun R => (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ)))
def ShapePrefix.innerslotS (P : ShapePrefix) (r b : ℕ) : ℕ :=
  (P.reads[r]?).elim 0 (fun R => (b % R.childWidthS) / R.Dwidth)
noncomputable def ShapePrefix.htS (P : ShapePrefix) (i : ℕ) (c : Coord) : ℚ :=
  (c.1 : ℚ) + (Finset.range i).sum (fun r => (P.innerslotS r c.2 : ℚ) * P.kappaS r)
noncomputable def ShapeRead.staircaseS (R : ShapeRead) (L : Line) (b : ℕ) : WithBot ℚ :=
  if b < R.μ * R.childWidthS then ((L.at ((b / R.childWidthS) * R.childWidthS) : ℚ) : WithBot ℚ) else ⊥
noncomputable def ShapePrefix.floorS (P : ShapePrefix) (i b : ℕ) : WithBot ℚ :=
  ((List.range i).map (fun r => (P.reads[r]?).elim ⊥ (fun R => R.staircaseS (P.lineS r) b))).foldr max ⊥
def ShapePrefix.prevRimS (P : ShapePrefix) (n : ℕ) : ℕ → ℕ
  | 0 => n | i + 1 => (P.reads[i]?).elim n (fun R => R.μ * R.childWidthS)
noncomputable def ShapePrefix.bandS (P : ShapePrefix) (n r : ℕ) (c : Coord) : Prop :=
  c.2 < P.prevRimS n r ∧ P.floorS r c.2 < ((P.htS r c : ℚ) : WithBot ℚ) ∧
  (P.reads[r]?).elim False (fun R => P.htS r c ≤ (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth))
open Classical in
noncomputable def ShapePrefix.A (P : ShapePrefix) (n N : ℕ) : ℕ :=
  (Finset.range P.reads.length).sum (fun r =>
    ((Finset.range N ×ˢ Finset.range n).filter (fun c => P.bandS n r c)).card)
/-- The a-priori SHAPE bound on the band's levels (the note's L12: "an a priori shape
bound on N(P̂) is available"): 1 + max over reads of ⌈intercept of lineS⌉₊ — every
band coordinate has level ℓ ≤ htS ≤ line value ≤ intercept, so levels ≥ Nshape are
band-free. -/
noncomputable def ShapePrefix.Nshape (P : ShapePrefix) : ℕ :=
  1 + ((List.range P.reads.length).map (fun r => ⌈(P.lineS r).intercept⌉.toNat)).foldr max 0
/-- **The N-FREE ledger exponent A′(P̂, n)** (finding 5): A at the stabilization level. -/
noncomputable def ShapePrefix.A' (P : ShapePrefix) (n : ℕ) : ℕ := P.A n (P.Nshape)
noncomputable def ShapePrefix.Anet (P : ShapePrefix) (n : ℕ) : ℤ := (P.A' n : ℤ) - (P.W : ℤ)
```

### 3.4 The encoding target, the tree, the verdict layer (findings 3/7 + gaps 8/9)

```lean
/-- The pool: THE order-p^w root set in F (units E1–E3 identify it with every matched
frame field's image). -/
def pool (p w : ℕ) (F : Type*) [Field F] : Set F := {x : F | x ^ (p ^ w) = x}

/-- A classically-fixed enumeration of F — the shared "fixed residue bases" order
(D.3(e)) for the rank; one choice for the whole corpus. -/
noncomputable def fieldEnum (F : Type*) [Finite F] : F ≃ Fin (Nat.card F) :=
  (Finite.equivFin F).trans (finCongr (Nat.card_eq_fintype_card (α := F)).symm)

/-- The rank of ψ among the eligible same-shape factors of Ranch (L11's s_r), via the
shared enumeration — DEFINED, not data. Stated on F-coefficient images so classes
compare across members (units E6–E8 give rank < m̄ and rank-injectivity). -/
/-- [REV 4, Fable#2 G1 ≈ Codex#2 finding 3 — the gloss was FALSE as written: without
irreducibility E7 fails (Fable's counterexample: 4 distinct linear factors, g = 2,
μ = 1 → SIX monic ord-1 quadratic divisors vs m̄ = 2); with Irreducible-over-F it
fails the other way (a deg-≥2 image SPLITS over F ⊇ F_{p^{w·g}}). The correct
predicate is the TRANSPORTED one, spelled out:] -/
def RanchImage (ν : Node p F) : Polynomial F := ν.Ranch.map (SubfieldClass.subtype _ …)
def ψImage (ν : Node p F) : Polynomial F := ν.ψ.map (SubfieldClass.subtype _ …)
/-- `pool p w F` as a subfield (Frobenius-power fixed points — closed under the field
operations in char p). -/
def poolSubfield (p w : ℕ) (F : Type*) [Field F] : Subfield F := ⟨…carrier := pool p w F…⟩
/-- **The transported eligibility predicate** (the note's "{ψ monic irreducible :
deg ψ = g_r, ord_ψ R_anch = μ_r}", read on F-images): q is monic of degree g with
ord_q(Rq) = μ AND q is the image of an IRREDUCIBLE polynomial over the POOL SUBFIELD
(equivalently: coefficients in the pool + irreducible over it — never over F). -/
def EligibleImage (p w g μ : ℕ) {F : Type*} [Field F] (Rq q : Polynomial F) : Prop :=
  q.Monic ∧ q.natDegree = g ∧ OrdPsiPoly q Rq μ ∧
  ∃ q₀ : Polynomial ↥(poolSubfield p w F),
    Irreducible q₀ ∧ q₀.map (poolSubfield p w F).subtype = q

noncomputable def selRank {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (w : ℕ) (ν : Node p F) : ℕ :=
  Nat.card {q : {q : Polynomial F // EligibleImage p w ν.g ν.μ (RanchImage ν) q} //
    lexLt (fieldEnum F) q.1 (ψImage ν)}
  -- `lexLt` = coefficient-lex through the classically fixed `fieldEnum` (the
  -- D.3(e)-order substitute; the encoding bound is order-invariant — Fable#2 §3.8).

/-- The L11 encoding target (pool-valued digit tuples of the RETAINED sizes d_r +
selection indices). -/
def EncTargetP (p : ℕ) (F : Type*) [Field F] (P : ShapePrefix) : Type :=
  ∀ r : Fin P.reads.length,
    ((Fin (P.reads.get r).d → ↥(pool p (P.reads.get r).w F)) × Fin (P.reads.get r).mbar)

/-- Appending a non-root node to a history (for the tree's child laws). -/
def _root_.LeanUrat.MovesC.History.snoc (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) : History p F := ⟨H.nodes ++ [ν], by simp, …⟩

def _root_.LeanUrat.MovesC.History.IsPrefixOf (H H' : History p F) : Prop := H.nodes <+: H'.nodes

/-- **T_can(f) with L2's structure** [REV 3, gap 8]: membership AND the child
relation (`none` = children of the EMPTY chain — the root reads), with the two
generation laws; prefix-closure becomes a THEOREM (T1a). Eligibility semantics of
`child` ("ALL eligible (side, ψ) continuations", cell data) is kernel-(b) content —
HC-2; uniqueness of the tree per input is the model's meta-duty, documented. -/
structure TreeModel (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) where
  mem : History p F → Box p m → Prop
  child : Option (History p F) → Node p F → Box p m → Prop
  mem_single : ∀ (ν : Node p F) (h1 : _) (x), mem ⟨[ν], h1.1, h1.2⟩ x ↔ child none ν x
  mem_snoc : ∀ (H ν hν x), mem (H.snoc ν hν) x ↔ (mem H x ∧ child (some H) ν x)
  mem_realizable : ∀ H x, mem H x → HistoryCoherent H ∧ Realizable H ∧ pol.IsCanonPres H

/-- [REV 4, Codex#2 finding 8 — PUSHBACK, the falsifying computation displayed]:
`mem := False, child := False` satisfies the generation laws, but it cannot enter
ANY consuming theorem: D15 requires `D4R_CYL S T`, and by D0c every enumerated fiber
is NONEMPTY (Theorem C(b)'s positive mass), so the empty tree FAILS `D4R_CYL` for
every family with a realized class — the degenerate instance is data that no
consumer accepts, exactly like a junk shape. A root-inhabitation law would be
UNFAITHFUL: L5's (ns) case ("the window polygon admits no eligible side: a terminal
verdict") makes ∅ a LEAF for some inputs — nonempty chains need not exist.
Exhaustive-children semantics is kernel-(b) cell content, carried by the D4R_CYL /
ClassFiberWelldef pins. §11 row 8. -/

/-- L6's (D4R-CYL), as the PINNED Prop [REV 3, finding 7]: S(η,⊤) = {f : η ∈ T_can(f)}
for every enumerated class. Note-PROVED (kernel (a)+(b) dual-verified-discharged +
Thm C(a)); its LEAN proof is EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus.
D15 consumes it as a named hypothesis — it is NOT a TreeModel field. -/
def D4R_CYL {n N m : ℕ} {pol : CanonPolicy p F} {P : ShapePrefix}
    (S : Presented p F n N m pol P) (T : TreeModel p F n N m pol) : Prop :=
  ∀ (i : PrefIdx n pol P) (x : Box p m), x ∈ S.fiber i ↔ T.mem (reprOf i) x

/-- **The (c)/VP surface, typed** [REV 3, gap 9]: alphabet V; the emission map vdict
(none = the read continues); the HALT DICHOTOMY = L2's "a chain has NO children iff
its read returns a terminal verdict" (both directions in one iff — `leaf` is now the
DEFINED `T.mem H x ∧ vdict H x ≠ none`, not a field, so no `leaf := False` instance
exists); the PER-CLASS DETECTION CAP with its law: verdict v is determined by the
digits below level `cap v` — the "uniform per-class detection cap" typed against
vdict. τ-as-cell-data and the VP-1/VP-2 semantics remain MovesT's — this structure is
the OPEN kernel-(c) surface, consumed by nothing in MovesD. -/
structure VerdictModel {n N m : ℕ} {pol : CanonPolicy p F}
    (T : TreeModel p F n N m pol) where
  V : Type
  hVfin : Finite V
  hVne : Nonempty V
  vdict : History p F → Box p m → Option V
  halt_iff : ∀ H x, T.mem H x →
    (vdict H x ≠ none ↔ ∀ (ν : Node p F) (hν : ν.species ≠ ReadSpecies.root),
      ¬ T.child (some H) ν x)
  /-- the box level of each digit coordinate (the presented charts' first component;
  MovesT pins it to the jets' `coordOf`). -/
  levelOf : Fin m → ℕ
  /-- [REV 4, Codex#2 finding 10] the chart-range consistency of `levelOf` (the full
  chart tie `levelOf = (coordOf ·).1` per presented jet is MovesT's, at consumption). -/
  levelOf_lt : ∀ c : Fin m, levelOf c < N
  cap : V → ℕ
  cap_law : ∀ (v : V) (H : History p F) (x x' : Box p m),
    vdict H x = some v → (∀ c : Fin m, levelOf c < cap v → x c = x' c) →
      vdict H x' = some v
  /-- [REV 4, Codex#2 finding 10] FINITE-LEVEL LOCALITY (both branches, `none`
  included): vdict is a function of the digits below the cap envelope — the typed
  finite-level shadow of "τ is a function of CELL data alone, never of f" (VP-2).
  The cell-exact tie (vdict factors through the digit-cell of H's frame) needs the
  frames and is MovesT's VP duty — documented, not silently claimed. -/
  vdict_local : ∀ (H : History p F) (x x' : Box p m),
    (∀ c : Fin m, (∃ v : V, levelOf c < cap v) → x c = x' c) → vdict H x = vdict H x'

end
end LeanUrat.MovesD
```

## 4. Unit specs (45 units [REV 4: +W3, +D4R4_all]; all in `lean/LeanUrat/MovesD/`)

Common binders (elided): `{p} [Fact p.Prime] {F} [Field F] [Finite F] {n N m : ℕ}
{pol : CanonPolicy p F} {P : ShapePrefix}`; `S : Presented p F n N m pol P`;
`top := topLocus p m`. AUX = no note display; informal statement given.

### D0a — topLocus_laws · `D0a_topLocus.lean` — as rev 2 (sol/numPinned/admissible).
moves_ref: "Z = ⊤: no constraint, vol(⊤) = 1" (L6). deps: MovesC. easy.

### D0b — thmC_top · `D0b_thmCtop.lean` — as rev 2 (`totalPins_top`, `thmC_top`).
moves_ref: "Each NONEMPTY summand is Theorem C(b) with Z = ⊤". deps: C6_thmC_b, D0a.
easy. hypothesis_fields: none (J a binder; existence = `Presented.jet`, HC-2).

### D0c — fiber_pos · `D0c_fiberPos.lean`
statement: `theorem fiber_pos (S) (i : PrefIdx n pol P) : (S.fiber i).Nonempty`
moves_ref: "Theorem C(b) gives mass p^{−A(P̂)} > 0" (L6 corollary). deps: D0b. easy.

### THE ENCODING CHAIN E1–E9 (L11 PROVED — final-audit findings 1/3/4)

### E1 — digit_in_pool · `E1_digitPool.lean` (AUX)
informal: a matched node's side digits lie in the order-p^w root set.
statement: `theorem digit_in_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) (k : ℕ) : ν.sideDigit k ∈ pool p R.w F`
deps: Defs. sketch: `FiniteField.pow_card` on ↥ν.σ.K (card p^w by hM); ring-hom
coercion. medium.

### E2 — pool_card_le · `E2_poolCard.lean` (AUX)
statement: `theorem pool_card_le (hp : 2 ≤ p) (hw : 1 ≤ w) : Nat.card ↥(pool p w F) ≤ p ^ w`
deps: Defs. sketch: roots of the nonzero X^{p^w} − X; `Polynomial.card_roots`. medium.

### E3 — frameField_eq_pool · `E3_frameField.lean` (AUX)
informal: the frame field's image in F IS the pool (the unique subfield per order —
what lets classes of DIFFERENT members share one eligible-factor universe).
statement: `theorem frameField_eq_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) : (Set.range (fun a : ↥ν.σ.K => (a : F))) = pool p R.w F`
deps: E1, E2. sketch: range is a subfield of card p^w inside pool (E1); pool has ≤ p^w
elements (E2); equal cards force equality. medium.

### E4 — Ranch_deg · `E4_ranchDeg.lean` (AUX)
informal: deg R_anch = ℓ_r — the note's "deg R_anch,r equals that side's NORMALIZED
horizontal length ℓ_r := w'_r/e_r" (L11), PROVED from the node Props.
statement: `theorem Ranch_deg (ν : Node p F) : ν.Ranch.natDegree = ν.wSide / ν.e`
deps: MovesC. sketch: `hRanch` (the pattern sum) + `hpatTop` (top digit ≠ 0):
natDegree of Σ_{k≤len} C(pat k)·X^k with nonzero top. medium.

### E5 — gmu_le_len · `E5_gmuLe.lean` (AUX)
informal: g·μ ≤ ℓ_r (each eligible factor contributes g·μ to deg R_anch — L11).
statement: `theorem gmu_le_len (ν : Node p F) : ν.g * ν.μ ≤ ν.wSide / ν.e`
deps: E4. sketch: `hOrd` gives ψ^μ ∣ Ranch, Ranch ≠ 0 (hpatTop); degrees:
μ·g = deg ψ^μ ≤ deg Ranch = ℓ (hψdeg, E4). medium.

### E6 — eligible_card_le · `E6_eligibleCard.lean` (AUX)
informal: R_anch holds at most m̄ = ⌊ℓ/(g·μ)⌋ monic irreducible degree-g ord-μ
factors — L11's "each contributes g_r·μ_r to its degree".
statement: `theorem eligible_card_le (ν : Node p F) : Nat.card {q : Polynomial ↥ν.σ.K // q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ} ≤ (ν.wSide / ν.e) / (ν.g * ν.μ)`
deps: E4. sketch: distinct monic irreducibles are coprime; the product of q^μ over
any k eligible factors divides Ranch (UFD), so k·g·μ ≤ deg Ranch = ℓ, k ≤ ⌊ℓ/(gμ)⌋.
medium-hard.

### E7 — selRank_lt · `E7_rankLt.lean` (AUX)  [REV 4: re-verified against the
TRANSPORTED `EligibleImage` (§3.4) — Fable#2 G1's counterexample (six reducible
ord-1 quadratics vs m̄ = 2) hits only the withdrawn gloss]
informal: the defined rank is a legal selection index: selRank < m̄_r.
statement: `theorem selRank_lt {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) : selRank R.w ν < R.mbar`
deps: E3, E6. sketch: (i) MEMBERSHIP: ψImage ν satisfies the transported predicate —
monic/deg/ord push through the coefficient embedding, and ν.ψ itself is the
irreducible lift over ↥σ.K ≃ poolSubfield (E3's identification); (ii) CARD: the
transported eligible set pulls back injectively to E6's K-side set (map injective on
poolSubfield-coefficient polynomials), so its card ≤ m̄ (E6 + Matches ties ℓ, g, μ);
rank = a proper-initial-segment count in a set of card ≤ m̄ containing ψImage.
medium-hard.

### E8 — rank_inj · `E8_rankInj.lean` (AUX)
informal: on ONE eligible set, rank determines the factor (lex through the shared
`fieldEnum` is a strict total order — the note's "ordered lexicographically by
coefficient vectors in D.3(e)'s fixed residue bases").
statement: `theorem rank_inj {R : ShapeRead} {ν ν' : Node p F} (hM : R.Matches ν) (hM' : R.Matches ν') (hg : ν.g = ν'.g) (hμ : ν.μ = ν'.μ) (hR : RanchImage ν = RanchImage ν') (hs : selRank R.w ν = selRank R.w ν') : ψImage ν = ψImage ν'`
deps: E3, E6. sketch: equal Ranch-images + E3's common subfield give literally equal
F-side eligible sets; two members of a finite set with equal strict-initial-segment
counts under a strict total order are equal. medium-hard.

### E9 — encIdx_inj · `E9_encInj.lean`
statement: `theorem encIdx_inj : Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F P)`
  (Defs addendum: `encIdx i := fun r => (digits of the class at the d_r counted
  positions, ⟨selRank (node r of reprOf i), E7⟩)`.)
moves_ref: "The map enc′: η ⟼ (the side-digit tuples (d_j) of its reads; the
selection indices (s_r)) is an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1,…,m̄_r})"
(L11 — now a THEOREM at the η-class granularity).
deps: E1, E3, E4, E7, E8; Defs (Matches.hmonic). sketch: classes are (digit-tuple,
ψ-image) sequences; the d_r counted digits + the scoped monic tie (§0.5) recover the
FULL digit tuple; the digit tuple determines RanchImage (hRanch, coefficient images);
E8 recovers ψImage from the rank. So encIdx equal ⟹ etaData equal ⟹ i = j
(subtype ext). [REV 4: classes are now ROOT-NORMALIZED (§0.6) — the injection's
source is conjugation-free, so its count is the note's C; the chain itself is
unchanged (Fable#2: "NOT contaminated: the E1–E9 chain itself").] medium-hard.

### D2a — L8_finite_C · `D2a_finite.lean`
statement:
  `instance : Finite (PrefIdx n pol P)` — L8, structural (a subtype of the finite `EtaData`).
  `theorem CD_eq (hne : P.reads ≠ []) : P.CD n pol = Nat.card (PrefIdx n pol P)`
moves_ref: "L8: Pref(P̂) is FINITE … Hence #Pref(P̂) ≤ M(P̂)·∏_r Q_r^{d_r} < ∞".
deps: Defs. sketch: EtaData is a Pi of finite types; `if_neg`. easy.
hypothesis_fields: none — the finiteness mechanism is now the η-class construction
itself (final-audit finding 3 repaired).

### F1 — the constructed enumeration · `F1_enum.lean`
statement:
  `theorem reprOf_mem (i : PrefIdx n pol P) : reprOf i ∈ PrefSet n pol P`
  `theorem etaData_reprOf (i : PrefIdx n pol P) : etaData P (reprOf i) = (i : EtaData F P)`
  `theorem card_classes : Nat.card (PrefIdx n pol P) = Nat.card (etaData P '' PrefSet n pol P)`
moves_ref: "Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts }, C_P̂(p) :=
#Pref(P̂)" — the enumeration is CONSTRUCTED, completeness/injectivity are definitional
theorems (final-audit finding 3: nothing assumed). [REV 4: classes are the
ROOT-NORMALIZED presentation classes; "classes ↔ η's" is the PRESENT-NORM pin (§2),
gate-checked at §0.6 — C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1.]
deps: Defs. sketch: `Exists.choose_spec` twice; `Nat.card` of a subtype of a set
coerced. easy.

### W1 — wellformed_of_mem · `W1_wellformed.lean`
statement: `theorem wellformed_of_mem {H : History p F} (hH : H ∈ PrefSet n pol P) : P.Wellformed n`
moves_ref: "COARSE CHAIN … deg R_anch,r ≤ n always" (L11) — PROVED: no `hn` rider
(final-audit finding 4).
deps: E4, E5. sketch: induction down the reads: root — ℓ₀ = wSide/e ≤ s0+wSide ≤ n
(`InBox`, a PrefSet clause); step — coherence's window containment
s0'+wSide' ≤ μ_prev, so ℓ_{r+1} ≤ wSide' ≤ μ_prev ≤ ℓ_prev/(g·μ)·(g·μ) ≤ ℓ_prev
(E5 at the parent) ≤ n; transport each ℓ to the shape via Matches. medium.

### W2 — Mfac_le · `W2_MfacLe.lean`
statement: `theorem Mfac_le (hwf : P.Wellformed n) : P.Mfac ≤ n ^ P.reads.length`
moves_ref: "M(P̂) := ∏_r m̄_r ≤ ∏_r ⌊n/(g_rμ_r)⌋ ≤ n^{|P̂|} (m̄_r as above … coarse
chain displayed)". deps: Defs. sketch: m̄_r = ℓ_r/(gμ) ≤ ℓ_r ≤ n (hwf, Nat.div_le_self);
List.prod ≤ pow. easy-medium. hypothesis_fields: `hwf` — PROVED by W1 for every
inhabited shape; for uninhabited shapes the D4R.2 chain never needs it (C = 0).

### W3 — D4R2'_coarse · `W3_coarseBound.lean`  [REV 4, Codex#2 finding 5]
statement: `theorem D4R2'_coarse : Nat.card (PrefIdx n pol P) ≤ n ^ P.reads.length * p ^ P.W`
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, M(P̂) ≤ n^{|P̂|} p-FREE (L11)" — the two displayed
inequalities CHAINED ON C, now UNCONDITIONAL: no Wellformed hypothesis survives.
deps: D3a, W1, W2, F1. sketch: case split on `Nonempty (PrefIdx n pol P)`: empty —
C = 0 ≤ anything; nonempty — pull a member via `reprOf`/F1, W1 gives `Wellformed n`,
chain D3a with W2. easy. hypothesis_fields: NONE. [The BARE `Mfac ≤ n^{|P̂|}` for
junk shape data (ℓ_r > n) is FALSE and not the note's claim — the note's "always"
ranges over shapes of degree-n classifier histories; on C-carrying territory the
display is now hypothesis-free. Pushback recorded at §11 row 5.]

### D1c — encTargetP_card · `D1c_encCard.lean` (AUX)
statement: `theorem encTargetP_card (hp : 2 ≤ p) : Nat.card (EncTargetP p F P) ≤ P.Mfac * p ^ P.W`
moves_ref: (L11's codomain count ∏_r Q_r^{d_r}·m̄_r). deps: E2. sketch: Pi/product
cards; (card pool)^{d} ≤ (p^w)^d; regroup = p^W·Mfac. medium.

### D3a — D4R2' · `D3a_poolBound.lean`
statement: `theorem D4R2' : Nat.card (PrefIdx n pol P) ≤ P.Mfac * p ^ P.W`
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}" (D4R.2′ display; the M ≤ n^{|P̂|} clause is W2).
deps: E9, D1c. sketch: `Nat.card_le_card_of_injective encIdx encIdx_inj` + D1c.
easy. hypothesis_fields: NONE — the injection is PROVED (final-audit finding 4
repaired: nothing assumed, no rider).

### D3b — D4R2_cor · `D3b_corD4R2.lean`
statement: `theorem D4R2_cor (hne : P.reads ≠ []) (N : ℕ) (hN : P.Nshape ≤ N) (S : Presented p F n N m pol P) : Nat.card S.event * p ^ (P.A' n) ≤ P.Mfac * p ^ (P.W + n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} ≤ M(P̂)·p^{W(P̂)−A(P̂)} = M(P̂)·p^{−A_net(P̂)},
A_net(P̂) := A(P̂) − W(P̂)" (Corollary D4R.2), division-free (`Anet` records the named
exponent). deps: D12, D3a, D2a. sketch: chain D4R1_EV with D4R2' (via CD_eq);
pow_add. easy.

### THE L9 CHAIN (D4a–D9, L9s) — substance unchanged from rev 2 (no final-audit
finding hit it except D10's quantifier); one lemma per unit; specs abbreviated.

### D4a — chart_bij · `D4a_chartBij.lean` (AUX) — as rev 2: `Injective J.coordOf` +
surjectivity onto the N×n grid (sorted chart + card pigeonhole via `J.hm`). medium.
### D4b — chart_count · `D4b_chartCount.lean` (AUX) — as rev 2: pulled-back predicate
counts over `Fin m` = grid filter counts. deps: D4a. medium.
### D5a — Dwidth_pos · `D5a_dwidthPos.lean` (AUX) — as rev 2 (root deg 1 + width
chain). deps: MovesC. medium.
### D6a — strFrame_shape · `D6a_strShape.lean` — `H.strFrame i = P.strS i` under
`MatchesHist`. easy.
### D5b — line_shape · `D5b_lineShape.lean` — `(H.nodes[r]'hr).line = P.lineS r`
under coherence + Matches (slope law; `hLineU` pins the intercept THROUGH u* — the
rev-9 bracket, quoted in the unit). deps: D5a, D6a. medium.
### D6b — kappaH_shape · easy. D6c — innerslot_shape · easy. D6d — htH_shape ·
deps D6b/D6c, easy. D6e — prevRim_shape · easy. (Files `D6*_*.lean`; moves_ref: L9's
"SHAPE data" sentence, one formula each.)
### D7a — staircase_shape · deps D5b. easy. D7b — floorH_shape · deps D7a (fold
congruence). medium. D7c — slotVal_shape · deps D5b (the fine-slot edge). easy.
### D8 — band_shape · `D8_bandShape.lean` — `inFreshBand H n J.coordOf r ν c ↔
P.bandS n r (J.coordOf c)` under Matches (+ J.coherent). deps: D6d, D6e, D7b, D7c.
medium.
### D9 — L9_A · `D9_L9.lean`
statement: `theorem L9_A (S : Presented p F n N m pol P) (i : PrefIdx n pol P) : totalPins (S.jet i) (topLocus p m) = P.A n N`
moves_ref: "∏ vol(E_fresh(νᵢ)) = p^{−A(P̂)} … the product depends on P̂ alone; A(P̂) :=
the resulting shape exponent" (L9). deps: D0b, D8, D4b, F1 (reprOf ∈ PrefSet gives
Matches/coherence); MovesC `mstar_eq`. sketch: as rev 2 (mstar_eq per read → band
count → grid filter → A's summand). medium.
### L9s — A_stable · `L9s_Astable.lean` (AUX)
informal: A(P̂, n, N) is N-stable above the shape height bound (the note's "a priori
shape bound … available but not needed" — HERE it IS needed, to make A′ N-free).
statement: `theorem A_stable (hN : P.Nshape ≤ N) : P.A n N = P.A' n`
deps: Defs. sketch: band coordinates satisfy ℓ ≤ htS ≤ line value ≤ intercept <
Nshape, so levels in [Nshape, N) contribute nothing; filter congruence on the grid
split. medium.

### THE MASS LAWS (final-audit finding 5: the uniform quantifier ∀ N ≥ N(P̂))

### D10 — D4R1_SUM · `D10_sumLaw.lean`
statement: `theorem D4R1_SUM (hne : P.reads ≠ []) (N : ℕ) (hN : P.Nshape ≤ N) (S : Presented p F n N m pol P) : (∑ᶠ i : PrefIdx n pol P, Nat.card (S.fiber i)) * p ^ (P.A' n) = Nat.card (PrefIdx n pol P) * p ^ (n * N)`
moves_ref: "Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (D4R.1-SUM)" ≡ "N(P̂) is
finite, and for EVERY N ≥ N(P̂): Σ_η #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)}
(D4R.4-SUM)". THE QUANTIFIER: N and S are UNIVERSALLY bound at every level ≥ the
shape threshold; C and A′ are N-FREE (PrefIdx/A′ do not mention N), so the equations
at different levels share their constants — D4R.4's content. `Nshape ≥ the note's
N(P̂)` on presented shapes is the jets' existence side (§C C.2, HC-2); the theorem
is stated at every N ≥ Nshape where a presentation exists, which is the note's "for
every N ≥ N(P̂)" read through the HC-2 boundary (documented).
deps: D0b, D9, L9s, D2a (Fintype from Finite for ∑ᶠ). sketch: per summand
thmC_top + D9 + A_stable; sum the constant. NO disjointness consumed. medium.
hypothesis_fields: `S.jet` only.

### D11a — mult_sum · `D11a_multSum.lean` — as rev 2 on the new types:
`∑ x, S.mult x = ∑ᶠ i, Nat.card (S.fiber i)` (double counting). medium.
### D11b — event_iff_mult · `D11b_eventMult.lean` — `x ∈ S.event ↔ 1 ≤ S.mult x`.
easy.

### D12 — D4R1_EV · `D12_evBound.lean`
statement: `theorem D4R1_EV (hne : P.reads ≠ []) (N : ℕ) (hN : P.Nshape ≤ N) (S : Presented p F n N m pol P) : Nat.card S.event * p ^ (P.A' n) ≤ Nat.card (PrefIdx n pol P) * p ^ (n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡ "(D4R.4-EV) …
the union bound within the level-N box", at every N ≥ N(P̂) (same quantifier note as
D10). deps: D10, D11a, D11b. sketch: card event = #{mult ≥ 1} ≤ Σ mult. medium.

### D13 — D4R1_EV_iff · `D13_evIff.lean`
statement: `theorem D4R1_EV_iff (hne : P.reads ≠ []) (N : ℕ) (hN : P.Nshape ≤ N) (S : Presented p F n N m pol P) : (Nat.card S.event * p ^ (P.A' n) = Nat.card (PrefIdx n pol P) * p ^ (n * N)) ↔ (∀ x ∈ S.event, S.mult x = 1)`
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … count-equality ⟺ …
mult_P̂ ≡ 1 POINTWISE on the event — the finite-level statement carries no
measure-zero exception" (D4R.1/L12). deps: D10, D11a, D11b. sketch: cancel p^{A′}
(p ≥ 2); Finset double counting, pointwise. medium-hard.

[REV 4, Codex#2 finding 6, second half — CONCEDED: D10/D12/D13/D3b now carry
`hne : P.reads ≠ []`, so with `CD_eq` their constant IS the corpus C (`P.CD`) on
their whole domain, and the P̂ = ∅ display is carried ONLY by D14a — the note's own
two-mechanism proof ("The EMPTY prefix η = ∅ … is dispatched FIRST, separately from
Theorem C(b)"). First half PUSHED BACK — §11 row 6.]

### D4R4_all — the quantified law with witnessed non-vacuity · `D4R4all_wrapper.lean`
[REV 4, Codex#2 finding 7]
statement: `theorem D4R4_all (hne : P.reads ≠ []) (hex : ∀ N, P.Nshape ≤ N → Nonempty (Presented p F n N (n*N) pol P)) : ∀ N, P.Nshape ≤ N → ∃ S : Presented p F n N (n*N) pol P, ((∑ᶠ i, Nat.card (S.fiber i)) * p ^ (P.A' n) = P.CD n pol * p ^ (n * N) ∧ Nat.card S.event * p ^ (P.A' n) ≤ P.CD n pol * p ^ (n * N))`
moves_ref: "N(P̂) is finite, and for EVERY N ≥ N(P̂): …(D4R.4-SUM)…(D4R.4-EV)" — the
uniform quantifier WITH a witness at every level, under the DECLARED presentability
hypothesis `hex` = **PRESENT-EXIST** (§2 ledger: §C C.2's N(η,⊤) presentations,
HC-2). The honest reading: the note's unconditional quantifier rests on §C's
presentability, which is this corpus's HC-2 boundary — stated, not smuggled.
deps: D10, D12, D2a (CD_eq). sketch: instantiate hex; apply D10/D12. easy.
hypothesis_fields: `hex` (PRESENT-EXIST — the sole consumer of the declared pin).

### D14a — emptyShape_law · `D14a_emptyShape.lean` (final-audit finding 6)
statement:
  `theorem Pref_empty_shape (hP : P.reads = []) : PrefSet n pol P = ∅ ∧ P.CD n pol = 1`
  `theorem A'_nil (hP : P.reads = []) : ∀ n, P.A' n = 0`
  `theorem emptyShape_law (hm : m = n * N) (hN : 1 ≤ N) (hP : P.reads = []) : Nat.card (emptyFiber p m) * p ^ (P.A' n) = P.CD n pol * p ^ (n * N)`
moves_ref: "Pref(∅) = {∅} … its fiber is the FULL BOX, level-N count p^{nN} =
C_∅·p^{nN − A(∅)} (C_∅ = 1, A(∅) = 0), by L5's normalized full-box display — NOT by
Theorem C(b)". CONNECTED IN CORPUS VOCABULARY: `emptyFiber` IS the defined S(∅,⊤),
`P.CD` IS the corpus C (its `if` branch is the note's own definition-level dispatch
Pref(∅) = {∅} — the History type has no empty chain, which is WHY CD carries the
dispatch; `Pref_empty_shape` displays that the History-level set is empty, so 1 is
the η = ∅ class and nothing else), `P.A'` IS the corpus A. deps: Defs. sketch:
if_pos; card univ = p^m; empty sum. easy. hypothesis_fields: `hm`, `hN` explicit.

### D14b — D4R4_emptyPref · `D14b_emptyPref.lean`
statement: `theorem D4R4_emptyPref (hne : P.reads ≠ []) (hemp : IsEmpty (PrefIdx n pol P)) (hN : 1 ≤ N) (hm : m = n * N) (S : Presented p F n N m pol P) : S.event = ∅ ∧ P.CD n pol = 0 ∧ Nat.card S.event * p ^ (P.A' n) = P.CD n pol * p ^ (n * N)`
moves_ref: "If Pref(P̂) = ∅ then S(P̂,⊤) = … = ∅ and C_P̂(p) = 0, so for EVERY N ≥ 1:
#{f mod p^N ∈ ∅} = 0 = C_P̂(p)·p^{nN − A(P̂)}" (L12). deps: Defs, D2a. sketch: empty
iUnion over an empty index; CD_eq + Nat.card of an empty type. easy.
hypothesis_fields: `hN`, `hm` explicit (L12's N(P̂) := 1 convention).

### THE TREE UNITS (final-audit finding 7 + gap 8)

### T1a — tree_prefix_closed · `T1a_prefixClosed.lean`
statement: `theorem tree_prefix_closed (T : TreeModel p F n N m pol) : ∀ H H' x, H.IsPrefixOf H' → T.mem H' x → T.mem H x`
moves_ref: "T_can(f) is prefix-closed — a tree" (L2) — now a THEOREM from the
generation laws, not a field. deps: Defs. sketch: downward induction along
`mem_snoc` (peel the last node; a prefix of a snoc is the history or a prefix of it).
medium.

### D15 — tree_bridge · `D15_tree.lean`
statement:
  `theorem mult_eq_tree (S) (T : TreeModel p F n N m pol) (hcyl : D4R_CYL S T) (x : Box p m) : S.mult x = Nat.card {i : PrefIdx n pol P // T.mem (reprOf i) x}`
  `theorem event_iff_tree (S) (T) (hcyl : D4R_CYL S T) (x : Box p m) : x ∈ S.event ↔ ∃ i : PrefIdx n pol P, T.mem (reprOf i) x`
moves_ref: "mult_P̂(f) := #{ η ∈ Pref(P̂) : η ∈ T_can(f) } … S(P̂,⊤) = {f : mult_P̂(f)
≥ 1}" (L6 corollary). `hcyl` is the PINNED, EXPLICITLY DEFERRED L6 obligation (§2
ledger; wave-4/HC-2 owns its proof) — a named theorem hypothesis, NOT a structure
field restated as a theorem (final-audit finding 7). deps: Defs, D11b. sketch:
rewrite fibers along hcyl; `Nat.card_congr`. easy.
[REV 4, Codex#2 finding 9 — the per-representative scope: the second pinned Prop
**ClassFiberWelldef** (§2 ledger — one η-class, one classifier locus, over ALL
representatives and jets; §C L4's semantic content) is DECLARED alongside D4R_CYL;
together they restore the note's every-η reading of (D4R-CYL). Both deferred to the
wave-4/HC-2 tree corpus; D15 stays exact about the constructed enumeration.]

## 5. Perimeter (mirror of §D4-R.5 — unchanged from rev 2 except as noted)

No p-polynomiality of C ([1v]); no catalogue/aggregation ([2a]/[2b] — the events are
a multiplicity-weighted COVER, consumer duty in Defs docstrings); no resummation/
drainage/termination ([3]/[5]); no L7 unit (VerdictModel carries the typed object for
MovesT); no D4-n3 re-derivation; the literal (3i) not stated (D3a+W2 is the
M-carrying D4R.2′). NEW: the representative caveat (§3.2, displayed) — per-class
fibers are the chosen representative's SHZ; class-independence is HC-2 semantic
content. `Nshape ≥ N(η,⊤)`-adequacy of the presentations is existence-side (HC-2).

## 6. Build order

  wave A (parallel): D0a, E1, E2, E4, D5a, D6a, D6c, D6e, D14a → D0b, E3, E5, D0c.
  wave B: E6 → E7, E8 → E9; D2a, F1 → D3a, D1c; W1 → W2.
  wave C: D5b → D6b, D6d, D7a, D7c → D7b → D4a → D4b → D8 → D9; L9s.
  wave D: D10 → D11a, D11b → D12 → D13 → D3b (Corollary D4R.2, as rev 2 §D3b with
    A′); D14b; T1a; D15.
  Hardest: E6/E8 (polynomial arithmetic over the frame field), D13, D4a, T1a.

## 7. Codex-audit checklist (gate A)

1. ShapeRead retains rev-9 L3 exactly (heights PAIRED; `monicTop` is the slot-set
   datum reduced per §0.5 — reject if that reduction misreads L3).
2. No disjointness anywhere; sums over the INDEX type (rev-6 F1).
3. `D4R_CYL` consumed only as a named deferred hypothesis; no unit proves or assumes
   it as a field. Kernel (a)/(b) cited as MATH-discharged only; (c)/VP only in
   `VerdictModel`.
4. The EV criterion pointwise-on-the-event; ∀ N ≥ Nshape quantifier present on
   D10/D12/D13 with N-free C and A′.
5. `ShapePrefix.A`/`A'`/`CD` are DEFINITIONS; `CD`'s if-branch is the note's own
   Pref(∅) = {∅} dispatch — reject any unit weakening it to a hypothesis.
6. The encoding chain E1–E9 must consume ONLY MovesC node Props + Matches — any new
   assumption there is a statement-fence breach.
7. `Presented.jet` is the ONLY assumed structure field in the corpus.

## 8. MANIFEST stub

corpus: MovesD · source: §D4-R rev 9 (DUAL-ACCEPTED 2026-07-27) · consumes: MovesC ·
units: 45 (D0a–c; E1–E9; D1c; D2a; F1; W1–W3; D3a–b; D4a–b; D5a–b; D6a–e; D7a–c; D8;
D9; L9s; D10; D4R4_all; D11a–b; D12; D13; D14a–b; T1a; D15; 13 AUX) · defs: 1 file ·
open surface: `pol : CanonPolicy` (parameter), `Presented.jet` (HC-2), `D4R_CYL`
(deferred pinned Prop), `TreeModel`/`VerdictModel` data + laws, `Matches.hmonic`
(scoped, §0.5), explicit `hN`/`hm` on the empty units — §2 ledger.

## 9. REV 2 findings→repairs table (first audit, `MOVESD_AUDIT_CODEX_2026-07-28.md`)

[Kept for the record; several REV-2 repairs are SUPERSEDED by REV 3 — see §10.]
1 empty-family vacuity → PrefSet + complete/hcanon fields (superseded: rev 3
constructs the enumeration outright). 2 enc untied → encOf on actual data + henc
field (superseded: rev 3 PROVES the injection, E1–E9). 3 M ≤ n^{|P̂|} dropped →
restored with `hn` rider (superseded: rev 3 proves it, W1/W2). 4 A undefined →
`ShapePrefix.A` defined; D9 = L9 theorem; hA gone. 5 empty shape mis-modeled →
`hne` + connected display (extended at rev 3: corpus-level CD/emptyFiber). 6 N = 0
leak → explicit hN/hm. 7 TreeModel degenerate → mem_realizable + D0c (extended at
rev 3: child relation + generation laws). 8 VerdictModel vacuous → typed fields
(extended at rev 3: halt dichotomy + cap law). 9 chart unit hidden multi-lemma →
split D4a/D4b. 10 D6/D7 bundles → one lemma per unit.

## 10. REV 3 findings→repairs table (final audit, `MOVESD_AUDIT_CODEX_FINAL_2026-07-28.md`)

| # | finding (short) | repair |
|---|---|---|
| 1 | `offSlots_forced` invented (off-slot ≡ 1 not in the note) | ADJUDICATED §0.5: route (i) holds everywhere except the root monic lead, which the note itself displays (§D4-R.6 "slot 3 = the monic lead, digit 1"); blanket clause DELETED; `slots` → per-read Boolean `monicTop` with the ONE scoped tie `monicTop → sideDigit(ℓ) = 1`; d_r := ℓ_r + (monicTop ? 0 : 1) reproduces the note's d-counts |
| 2 | `Canon` lawless; `False` kills PrefSet | `CanonPolicy` structure: `liftOf` a FUNCTION of node data (L1's determinism), `blind` to the lift field; `IsCanon` per-node ⟹ prefix-monotone (T1a-style, free) and total on lift-assignments; `fun _ => False` is not an `IsCanon pol` for any pol; the open content is exactly WHICH pol (offset-P, §B2-DEF/HC-1) |
| 3 | family fields (`complete`, `henc`) assume what L8/L11 prove; no construction | the family is CONSTRUCTED: `PrefIdx := ↥(etaData '' PrefSet)` (the note's η-granularity: digits + ψ-images; lifts policy-determined per L1), `reprOf` classical, F1 proves the enumeration laws; L8 structural (D2a); L11's injection PROVED (E1–E9: pool identification, deg R_anch = ℓ, g·μ ≤ ℓ, eligible count ≤ m̄, rank injectivity); sole assumed field: `Presented.jet` (HC-2) |
| 4 | D3a consumes `henc` (assumed L11) + `hn` rider on the coarse bound | D4R2′ now PROVED with NO hypothesis (E9 + D1c); `hn` DELETED — W1 proves ℓ_r ≤ n for every member from `InBox` (the degree-n box clause of PrefSet) + the coherence window chain + E5; W2 gives M ≤ n^{|P̂|} from the proved `Wellformed` |
| 5 | one fixed N; no ∀ N ≥ N(P̂); no cross-level compatibility | D10/D12/D13 quantify `(N) (hN : Nshape P ≤ N) (S : Presented … N …)`; `Nshape` DEFINED (the note's "a priori shape bound"); C := Nat.card PrefIdx and A′ := A n Nshape are N-FREE, so constants agree across levels; L9s proves A-stability |
| 6 | empty-shape law a bare box identity, disconnected from Pref/C/S(∅,⊤) | corpus vocabulary supplied: `emptyFiber` (= S(∅,⊤), §C's empty-history clause), `ShapePrefix.CD` (C with the note's own Pref(∅) = {∅} dispatch at definition level), `Pref_empty_shape` (the History-level set is empty — so CD's 1 is exactly the η = ∅ class), `A'_nil`; D14a states the law on THESE |
| 7 | D15 restates the assumed `cyl` field as a theorem | `cyl` field DELETED; `D4R_CYL S T` is a PINNED Prop (def), EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus (§2 ledger); D15's bridges consume it as a named hypothesis |
| 8 | TreeModel lacks T_can structure (children, maximality) | `child : Option (History) → Node → Box → Prop` (none = root children) + generation laws `mem_single`/`mem_snoc`; prefix-closure now a THEOREM (T1a); maximal branch DEFINABLE (mem ∧ no child) and consumed by VerdictModel's dichotomy; eligibility semantics = kernel-(b), HC-2 (documented) |
| 9 | cap/τ law missing; `leaf := False` satisfiable | `leaf` field deleted (leaf := mem ∧ vdict ≠ none, DEFINED); `halt_iff` = L2's "NO children iff terminal verdict" (both directions); `cap : V → ℕ` with `cap_law`: a class-v verdict is determined by digits below level cap v (the uniform per-class detection cap, typed against vdict via `levelOf`); τ-as-cell-data remains MovesT's VP |

## 11. REV 4 adjudication table (Codex FINAL#2 8/2 vs Fable#2 1/1 — evidence-triaged)

| # | finding (verdict) | adjudication | disposition |
|---|---|---|---|
| F-C1 = C-2 | η-granularity: Fable#2 C1 (ambient etaData SPLITS one η by the residue-root choice — gate numbers C = 6 vs sealed 3, mult ≡ 2 vs 1) vs Codex 2 (classes might MERGE distinct η's; injectivity unproved) | Fable's direction gate-evidenced and verified (the note's η has no root datum — L2's child data quoted). Codex 2's merge direction: with root-normalized classes the per-read embedding is canonical by induction (§0.6), so abstract-η ⟺ image data; the residual two-sided dictionary is ONE declared pin | **FIXED** (Fable's route): `canonRoot` + `IsCanonPres` (§3.2), PrefSet root-normalized; PRESENT-NORM declared (§2); MANDATORY gate check §0.6 re-derives C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1, plus Nshape = 5, A = 11, W = 7, M = 1 |
| F-G1 ≈ C-3 | `EligibleImage` gloss omits irreducibility/subfield (Fable: gloss FALSE both ways, counterexamples; Codex: irreducibility transport invalid) | both verifiers right about the GLOSS; the intended transported predicate (E7's own deps line) is sound — Fable verified the chain with it | **FIXED**: explicit `RanchImage`/`ψImage`/`poolSubfield`/`EligibleImage` Defs (§3.4 — irreducible OVER THE POOL SUBFIELD via the ∃-lift clause, never over F); E7/E8 restated and re-verified |
| C-1 | monicTop reduction unsupported; Boolean unconstrained | Fable#2 §3.2 accepted §0.5 with the gate numbers (d₀ = 3, d₁ = 2, W = 7 ✓); my re-check: side slots map into the box except at most the single degree-n slot, which exists only at the ROOT full span ("slot 3 = the monic lead, digit 1", §D4-R.6); junk `monicTop` shapes constrain their OWN PrefSet coherently (smaller W, pinned digit — the encoding stays injective) | **PUSHBACK + partial concession**: root-species guard `hmonicRoot` added to `ShapeRead`; the Boolean stays (at most ONE off-box slot exists, so a Boolean is exact) |
| C-4 | CanonPolicy lawless (constant liftOf; junk normalization; no pinning) | Fable#2 §3.3 verified: `False` inexpressible, `blind` kills the real attack, liftOf-as-function IS L1's determinism ("the digits t_k are FUNCTIONS of the node data … deterministic"); WHICH policy is §B2-DEF/HC-1's by the campaign DAG — encoding offset-P laws here would formalize (S6b) out of scope; adversarial pol = junk data, no consumer | **PUSHBACK**: POL-PIN named in §2 (the future HC-1 instance unit); junk-lift normalization already documented |
| C-5 | Mfac_le conditional; Wellformed unenforced; false for junk shapes | correct that the BARE M ≤ n^{|P̂|} fails on junk data (ℓ_r > n) — but the note's "always" ranges over degree-n classifier shapes; on C-carrying territory the display can be made hypothesis-free | **FIXED**: W3 `D4R2'_coarse` — `C ≤ n^{|P̂|}·p^W` UNCONDITIONAL (empty case + W1/W2 via a member); Mfac_le keeps `Wellformed`, discharged by W1 whenever a member exists; bare-junk case pushed back |
| C-6 | empty ontology: "Pref_empty_shape gives the wrong set"; mass laws lack `hne` and yield a vacuous zero law at ∅ | FIRST half — Fable#2 §3.5 verified the D14a decomposition faithful ("mirrors the note's own two-mechanism proof"; the History type HAS no empty chain — CD's if-branch IS the note's definition-level dispatch, `Pref_empty_shape` honestly displays it); SECOND half — correct: D10-at-∅ read `Nat.card PrefIdx = 0` where the note's C_∅ = 1 | **half PUSHBACK / half FIXED**: `hne` added to D10/D12/D13/D3b (their constant now = `P.CD` via CD_eq on their whole domain); P̂ = ∅ carried ONLY by D14a |
| C-7 | no Presented witness at any/every N; Nshape-domination unproved | genuine: JetSetup existence IS the HC-2 boundary (MovesC's declared honest boundary — D0c gives fiber nonemptiness GIVEN a jet, not a jet); the note's unconditional quantifier rests on §C C.2 presentability | **FIXED (honest-hypothesis route)**: PRESENT-EXIST declared (§2) + wrapper unit `D4R4_all` — ∀ N ≥ Nshape ∃ witness S with SUM+EV, under `hex`; Nshape-domination documented (in-box levels are automatic — the note's own remark) |
| C-8 | TreeModel admits mem := False; no root inhabitation / exhaustive children | falsifying computation DISPLAYED at §3.4: the empty tree fails `D4R_CYL` against D0c's nonempty fibers — no consumer accepts it; root-inhabitation would be UNFAITHFUL (L5 (ns): ∅ can be a leaf — quoted); exhaustive children = kernel-(b) cell content behind the pins | **PUSHBACK** (with the displayed construction) |
| C-9 | D4R_CYL covers representatives only; representative-independence missing | correct as a scope gap | **FIXED**: ClassFiberWelldef pinned (§2) + D15 spec cites both pins |
| C-10 | VerdictModel: no vdict↔cell tie, no levelOf↔chart link | partially correct: full cell tie needs frames (MovesT); a finite-level locality law and chart-range consistency are expressible here | **FIXED (partial, typed)**: `vdict_local` (vdict a function of the digits below the cap envelope — the finite-level shadow of "τ is a function of CELL data, never of f") + `levelOf_lt`; the cell-exact tie documented as MovesT's VP duty |

Unit count: 45 (rev 3's 43 + W3 + D4R4_all); AUX still 13. Gate acceptance test
(per the triage protocol): §0.6 — C_P̂*(2) = 3 ✓, C_P̂*(3) = 48 ✓, mult_P̂* ≡ 1 ✓,
Nshape(P̂*) = 5 ✓, A(P̂*) = 11 ✓, W = 7 ✓, M = 1 ✓.
