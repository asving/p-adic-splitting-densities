# HETOW passPE1 — hostile verification report (fresh context)

**VERDICT: NOT CLEAN — 1 CRITICAL + 2 GAP + 2 MINOR.** The tower-node-locus
instantiation rows, the termination/peel rows, THEOREM HETOW.A's μ₂ = 3
exclusion, the n_min = 12 derivation, and the sealed battery all HELD; the
CRITICAL is a wrap-cocycle seam in the ϖ-twist bridge (HETOW-1/HETOW-2's
identification of the DISPLAYED composed key with a (κ₂, r̃)-key), invisible
at the battery's η = 1 gauge and machine-confirmed at an η ≠ 1 frame by the
fresh route (both oracle routes agreeing; the wrap-corrected key restores
every prediction).

Target: `lean/notes/openmath/HETOW_RECON_2026-08-09.md` @ HEAD (3e19eba).
Protocol: quote-and-classify, fix nothing. Verifier legs: independent
re-derivation of HETOW-1/2/3 and every §S1 row; seal + pin audit; isolated
re-run of the sealed battery; fresh-route instrument
`verification/openmath/hetow_pe1_fresh.py` (disjoint from the battery:
zero reader imports, exact residue algebra + dual PARI oracle routes).

---

## FINDINGS

### F-1 — CRITICAL — HETOW-1's two definitions of r̃ DIVERGE at wrap frames; the DISPLAYED Φ₂ is then not a (κ₂, r̃)-key and not the composed carrier

**Quote (§S2, LEMMA HETOW-1):** "r̃ ∈ K[Z] as the monic degree-f₂ polynomial
whose t-coefficient is the ϖ-residue of Φ₂'s slot-e₂t development
coefficient at height (f₂−t)u₂ (equivalently: the minimal polynomial of
β := η_θ^{−Q}·η₂ over K)" and (proof) "since it is monic of degree
f₂ = [K(β):K] and kills β, it IS the minimal polynomial."

**Quote (§S2, LEMMA HETOW-2, f₁ = 1 branch):** "ϖ-residue = r̃'s
t-coefficient (HETOW-1); Φ₂ is LITERALLY of DEFINITION HE6-1's displayed
form … So w = 0."

**The defect (derived, then machine-confirmed).** GENHN's normalizer
monomials n̂(k) = x^{i(k)}π^{a(k)} are NOT multiplicative:
n̂(a)n̂(b)/n̂(a+b) = (x^{e₁}π^{−h})^{wrap}. Writing Q(k) = (i₀k − i(k))/e₁,
one has Q((f₂−t)u₂) = (f₂−t)·Q(u₂) + W(t) with
**W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋ ≥ 0**, so the ϖ-residue of the displayed key's
slot-e₂t coefficient is −c_t·η^{−(f₂−t)Q(u₂)−W(t)}, while r̃ = minpoly(β)
= η^{−Qf₂}ψ₂(η^QZ) has t-coefficient −c_t·η^{−(f₂−t)Q(u₂)}. The two
definitions differ by η^{−W(t)} — a NON-LINEAR-in-t exponent, so the
development polynomial r̂ is not even a K₂^×-rescale of r̃, and it can be
REDUCIBLE. At any frame with η ≠ 1 and some W(t) ≢ 0 (mod ord η):
HETOW-1's equivalence fails; HETOW-2's f₁ = 1 branch ("w = 0", DEF HE6-1
form at datum (κ₂, r̃)) fails; §S1 table row "Φ₂ = Ψ_{κ₂,r̃} − w …
LEMMA HE7-12" fails; THEOREM HETOW.A(i)'s key clause fails on part of its
displayed scope ("any (e₁, f₁, h)", "any e₂f₂ ≥ 2").

**Failure scenario (concrete, in scope, machine-confirmed both oracle
routes).** Frame X: p = 3, Φ′ = x² − 6 — a legal outer genre
(Q; e₁, f₁, h) = (3; 2, 1, 1) per GENHN §S3.1's invariants (v(const) = f₁h
exactly; η := res(θ²/π) = 2 ≠ 1, no unit normalization anywhere in the
genre). Tower (e₂, f₂) = (1, 2), u₂ = 3 = κ₂ > D′h = 2 (node floor ✓),
ψ₂ = Z² + Z + 2 irreducible over F₃, μ₂ = 3, n = 12, T₂ = 6, K₂ = F₉.
Here i(u₂) = 1, W(0) = 1. Measured (`hetow_pe1_fresh.py`, exact algebra +
PARI):
* minpoly(β) = minpoly(η^{−1}η₂) = Z² + 2Z + 2 (irreducible, ≠ ψ₂ — the
  twist layer is real at this frame);
* the DISPLAYED Φ₂ (= Φ′² + 3xΦ′ + 54): slot ϖ-residues give
  r̂ = Z² + 2Z + 1 = **(Z+1)² — reducible, β_ξ rational**; PARI σ(Φ₂) =
  **{(4,1)}** ≠ {(e₁e₂, f₁f₂)} = {(2,2)} — the displayed key is NOT the
  composed carrier (e = 4, f = 1: even GENHN-T(b)′(i)'s letter claim
  "η₂(ξ) a root of ψ₂" fails at its roots, which forces f ≥ 2);
* the wrap-CORRECTED key (ĉ₀ ↦ lift(c₀·η^{W(0)}), i.e. Φ′² + 3xΦ′ + 108):
  slot residues = Z² + 2Z + 2 = minpoly(β) exactly, PARI σ = {(2,2)}, and
  all 15 preregistered μ₂ = 3 menu members over it land inside the case-B
  shape menu {(6,2)},{(2,6)},{(2,2)}³,{(2,4),(2,2)},{(4,2),(2,2)} — the
  theorem's CONTENT survives under the repaired key; members built on the
  displayed key leave the menu (e.g. PARI {(2,1),(2,1),(2,2),(4,1)}).

**Classification: CRITICAL** — the bridge-lemma chain HETOW-1 → HETOW-2 →
THEOREM HETOW.A(i) breaks at wrap frames, which the theorem's stated scope
includes. Root cause is upstream (GENHN-T(b)′'s displayed Φ₂ and its (i)
carry the same seam — an erratum candidate for the GENHN fold; GENHN is
frozen to this unit), but HETOW §S2 owns and "proves" the bridge, and the
proof's [K(β):K] = f₂ step silently consumes T(b)′(i)'s letter claim at
the displayed key's roots — exactly the false clause. Downstream damage is
bounded: the tower-NODE-LOCUS rows (HETOW-1(b) pointwise, HETOW-3(a)(b),
the (SLOT₂)/pins/termination rows) are wrap-free and survive my
re-derivation; the repair shape is a coherent-lift correction
ĉ_t ↦ lift(c_t·η^{W(t)}) (equivalently: define Φ₂ := Ψ_{κ₂,r̃} through
ϖ-multiplicative normalizers), after which HETOW-1/2 as re-derived here go
through and the fresh route is GREEN on every scored coherent-key check.
Both battery frames sit at η = 1 (Φ′ = x² − p), where W-wraps act
trivially — the seal could not see this.

### F-2 — GAP — HETOW-2's carry estimate tracks only the slot-raising piece; the tail piece of every reduction sits AT value T₂, not above it

**Quote (§S2, LEMMA HETOW-2 proof):** "replacing x^{D′+r'} by
x^{r'}·(Φ′ − tail) moves a monomial contribution at Φ′-slot s and dv-height
m to slot s+1 at dv-height m − D′h; its slot VALUE … a STRICT increase by
u₂ − e₂D′h > 0 … so every carry — and every iterated carry — sits at slot
value ≥ T₂ + (u₂ − e₂D′h) > T₂."

**The defect.** The displayed replacement generates TWO pieces:
x^{r'}π^aΦ′^{s+1} (tracked; value increase EXACTLY u₂ − e₂D′h — the
"exactly" is right for this piece, and strictness ≥ 1 holds at every genre
since u₂ > e₂D′h in integers) AND −x^{r'}·tail·π^aΦ′^{s} (untracked), where
tail := Φ′ − x^{D′} has slot value D′h exactly, so the second piece stays
at slot s at value exactly T₂ (at tail's attaining monomials) with x-degree
r' + D′ − 1, possibly still ≥ D′ (iteration). "Every carry … > T₂" is
therefore FALSE at face value; if the tail pieces were collected into −w as
the sentence directs ("the carries into −w"), dv₂(w) = T₂ and LEMMA
HE7-12's STRICT hypothesis ν > T₂ fails — the lemma would not apply.

**Why the conclusion nonetheless survives (verifier's re-derivation, not a
fix of the text):** value-T₂ tail pieces are exact-height in slot e₂t, so
under the lemma's own definition of Ψ ("B_t := the height-(f₂−t)u₂ part of
Φ₂'s slot e₂t" — of the LITERAL reduced development) they land in B_t, not
in w; exact-height parts have automatically nonzero slot residue
(independent η-powers), preserving DEF HE6-1's B_t ≠ 0 ⟺ c_t ≠ 0; the
above-height tail monomials sit > T₂ by ≥ e₂; and iterated reduction only
reaches slots e₂t and e₂t + 1 (the moved piece has x-degree
r' ≤ e₁ − 2 < D′ and never re-reduces). None of this accounting is in the
note. **Classification: GAP** (justification gap in a load-bearing bridge
proof — the displayed argument does not establish dv₂(w) > T₂; the correct
accounting does, and rides the same B_t-residue identification that F-1
already forces to be re-derived at the coherent key).

### F-3 — GAP — the η-gauge blindness of the battery is disclosed in the runner but NOT in HETOW-BOX-3, and it is the axis on which F-1 bites

**Quote (runner docstring, sealed):** "eta = 1 — the eta-twist layer is
INVISIBLE at this frame, disclosed as HETOW-BOX-3."
**Quote (note, HETOW-BOX-3):** "NOT exercised: μ₂ ≥ 4 …, e₂f₂ ≥ 4 …,
f₁ ≥ 2 outer frames (HETOW-2's carry leg is proof-only …), organic
(non-planted) refine chains. The proofs are uniform in all of these."

**The defect.** The note's box list does not contain the η ≠ 1 axis; the
runner's cross-reference points at a disclosure that is not there. η ≠ 1
occurs already at f₁ = 1 (frame X above), so the listed "f₁ ≥ 2 outer
frames" item does not cover it. On this axis the machine leg is fully
blind (both frames Φ′ = x² − p have η = 1, where HETOW-1's r̃ = ψ₂ up to
nothing and the wrap layer acts trivially), and "the proofs are uniform in
all of these" is asserted over a list that omits the falsifying direction.
**Failure scenario:** an acceptance reading §S5–S6 plus HETOW-BOX-3 as the
complete coverage disclosure concludes the σ read is machine-corroborated
across the claimed scope, when the entire battery sits in the one gauge
where F-1's seam vanishes. **Classification: GAP** (coverage-disclosure
integrity, load-bearing given F-1).

### F-4 — MINOR — HETOW-2 cites the f₁ ≥ 2 overflow as T(b)′'s, but under the (LIFT)-slot reading of ĉ_t no overflow occurs at all

Under the only in-repo lift construction that keeps every product monomial
at exact height ((LIFT): Σ_j ĉ_j x^{i(k)+e₁j}π^{a(k)−jh}, x-degree
≤ D′ − 1), deg(ĉ_t·n̂) never reaches D′ (max i(k) + e₁j = D′ − 1) — e.g.
frame Y below (f₁ = 2) has lift x³π⁴ at height 11, degree 3 < D′ = 4. The
overflow branch then treats a representation the construction never
produces; if instead ĉ_t means a plain x-basis letter lift, its terms sit
at DIFFERENT heights and the "pre-reduction terms … at slot value exactly
T₂" premise needs an argument. Either way the f₁ ≥ 2 branch's object needs
pinning before the carry algebra can be graded. (MINOR because at f₁ = 1 —
the only machine-exercised leg — the branch is moot, and F-2 already
reopens this proof.)

### F-5 — MINOR — §S6's "300/300 PARI agreements" headline undercounts the leg's own scope conditions

The 300/300 P2 figure is honest against the artifacts (re-verified), but
the S6 phrase "the machine form of THEOREM HETOW.A: the code written for
the ordinary-leaf box decides the tower box with no change" states the
literal-instance corroboration without the gauge caveat that the runner
itself discloses (η = 1). One sentence in §S6 restating the gauge would
have carried it. (MINOR: presentation; the substantive coverage issue is
F-3.)

---

## CLEAN CHARGES (attacked and held)

1. **HETOW-2 moved-piece increment**: derived independently — the
   slot-raising piece gains EXACTLY u₂ − e₂D′h per step; strictness
   integer-quantized (≥ 1) at every genre from the [r1] node floor; LEMMA
   HE7-12's strict hypothesis ν > T₂ and [r3] W ≠ 0 split line up with
   HETOW-2's "w = 0 or dv₂(w) > T₂" disjunction.
2. **HETOW-1(a)**: r̃ := minpoly(β) is monic irreducible of degree f₂ with
   no gcd side-conditions — Z ↦ η^QZ is a K-affine substitution,
   K(β) = K(η₂) since η^{−Q} ∈ K^×; r̃(0) ≠ 0 from the full side's attained
   left endpoint (ψ₂(0) ≠ 0). Holds verbatim (it is the OTHER definition
   of r̃ that F-1 breaks).
3. **§S1 verbatim rows re-verified**: dv₂ = e₁e₂v arithmetic; T₂ = e₂f₂u₂;
   K₂ ≅ F_{Q^{f₁f₂}}; (SLOT₂) = GENHN-2′ formula identity
   (e₂(e₁v + ih) + su₂ = e₁e₂v + ie₂h + su₂); pins row; node floor row.
4. **Termination row**: HE6R1-1's displays re-read — μ₁ ≥ μ₂·ℓd_r =
   μ₂e₂f₂ with equality exactly at the full side (L = μ₁);
   J ≤ log₂μ₁ − 1; level-3 floor μ₂ ≥ 4 = HE7.A(3)'s display; HETOW.A(iv)
   consistent, n = 12 admits exactly one jump.
5. **Ψ ∤ f_S row**: LEMMA HE7-12(c) item (11) re-read — roots of a
   perturbed key are level-2 points by (b)'s disk criterion, so LEMMA
   HE6R1-3's peel transports; HETOW-3(c) cites it correctly.
6. **HETOW-3(a)(b)**: full-side block identities re-derived (attained
   endpoint ⟹ A₀ ≠ 0 ⟹ Φ′ ∤ f; every locus root carries the (κ₂, r̃)
   label pointwise — the POINTWISE β = η^{−Q}η₂ translation is wrap-free).
7. **n_min = 12 derivation and both σ menus** (dictionary
   e = e₁e₂ℓ₂, f = f₁f₂·deg r₂ at all 5 genres per case) — arithmetic ✓.
8. **P4's p = 3 disclosure**: {(4,1)}³ impossible at p = 3 (F₃^× has 2
   elements; a cubic with r(0) ≠ 0 cannot have 3 distinct roots) —
   structural, correctly disclosed as a hole, not a violation.
9. **Seal integrity**: runner md5 31935fe8… identical at seal commit
   2e5c4b1 and HEAD; artifacts at 3e19eba byte-identical to working tree;
   import pins printed in the artifacts match live files AND match
   he6/he7_checks at HE7's freeze commit ca3754d (321fa4d4…/688adbe8…) —
   the readers really are the frozen instruments.
10. **Census arithmetic**: 33+33+65+65+52+52 = 300 members; row sums
    match; 1,200 = 4 scored legs × 300; teeth details match artifacts.

## MACHINE LEG (isolated re-run + tautology audit)

* **Isolated re-run**: staged `/tmp/hetow_pe1_iso` purely from commit
  3e19eba (runner + 5 pinned imports + their import closure), fresh
  `__pycache__`-free run: **GREEN, TOTAL checks 1200, violations 0, teeth
  4/4** (43.2s vs committed 42.9s — a genuine re-execution), output and
  results JSON **content-identical to the committed artifacts modulo the
  timing fields only**.
* **Tautology audit**: decisions by frozen `he7_checks.level2_read` /
  `he6r1_checks.level2_read`; adjudication by the external gp binary
  (factorpadic route) — non-tautological. Shared surface between member
  construction/parse gate and the readers (he6_checks plumbing) is
  disclosed by the pins; it cannot manufacture reader-vs-PARI agreement.
  P1's parse gate is program-internal (instrument-grade, as the note
  states).
* Note for the record: a pre-existing `/tmp/hetow_rerun` output found on
  disk was bit-identical to the committed artifact INCLUDING the 42.9s
  timing string (a copy, not evidence); this pass's re-run above is the
  evidence.

## FRESH ROUTE (`verification/openmath/hetow_pe1_fresh.py` — disjoint instrument)

Zero code shared with the program's readers; exact ℤ[x]/F₉ residue algebra
plus PARI on TWO routes per job (factorpadic+idealprimedec vs
factor-over-ℚ+idealprimedec), routes compared on every job. Two
instrument defects found and fixed during the pass (a minpoly-of-β
transcription slip computing 2η₂² for 2η₂, and an 8MB default PARI stack
overflowing on the degree-24 frame-Y jobs — fixed by parisize 2000M;
neither touches the scored semantics; both disclosed here).

* **FRAME X (η ≠ 1, f₁ = 1)** — the first wrap-live tower contact
  anywhere: FL1/FL2 confirm F-1 exactly (displayed key σ {(4,1)},
  degenerate r̂ = (Z+1)²; coherent key σ {(2,2)}, slot residues =
  minpoly(β) = Z²+2Z+2 ≠ ψ₂); FL3: 15 coherent-key μ₂ = 3 members
  (ONE-side λ₂ = 7 sweep, 3RAM λ₂ = 20/3, 2+1) ALL inside the
  preregistered menu with forced rows exact ({(6,2)} at 3RAM,
  {(2,2),(4,2)} at 2+1); displayed-key members leave the menu
  (informative rows).
* **FRAME Y (f₁ = 2 outer, wrap-free at f₂ = 1)** — the first f₁ ≥ 2
  composed-carrier machine contact (n = 24, composed (e₁e₂, f₁f₂) =
  (4,2), a composed profile outside the battery's two): key σ {(4,2)};
  the λ₂ = 67/3 member {(12,2)}; integer-slope μ₂ = 3 members inside the
  (4,2)-menu {(12,2)},{(4,6)},{(4,2)}³,{(4,4),(4,2)},{(8,2),(4,2)}.
  Scope note: frame Y's lift is a single monomial of degree 3 < D′ = 4,
  so the OVERFLOW-carry leg stays machine-unexercised (per F-4 it may be
  unexercisable as displayed); e₂f₂ ≥ 4 remains open as HETOW-BOX-3 says.
* **Verdict of the leg**: **GREEN — 43 gp jobs, 0 violations on scored
  checks, both oracle routes agreeing on all 43** (artifacts
  `hetow_pe1_fresh_output.txt` / `hetow_pe1_fresh_results.json`); the two
  NAIVEKEY rows are informative and confirm F-1's failure mode
  (out-of-menu σ at the displayed key).

## GRADE LINE

**NOT CLEAN.** F-1 CRITICAL (wrap seam in HETOW-1/HETOW-2/HETOW.A(i)'s key
clause at η ≠ 1 frames; battery blind at its gauge; repair shape displayed
and machine-validated at the coherent key), F-2 GAP (carry-estimate tail
accounting), F-3 GAP (coverage-disclosure omission of the η-gauge), F-4/F-5
MINOR. HETOW attempt grade stays **0/2**; a repair round (coherent-lift
correction + carry accounting + BOX-3 disclosure, plus a GENHN erratum tag
for T(b)′'s display at the next GENHN fold) is required before this note
can enter an acceptance arc. The reconciliation's ARCHITECTURE survives:
at the coherent composed key every hypothesis row I could re-derive holds,
and the fresh route's coherent-key σ decisions sat inside the
preregistered menus at both new frames.
