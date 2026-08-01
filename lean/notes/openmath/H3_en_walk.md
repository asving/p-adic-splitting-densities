/-
# EN-U1 — (E-N) route (b): the consumption-walk rescope (walk note, Fable prover EN-U1, 2026-08-05)

Unit EN-U1 of `lean/blueprints/HDISCHARGE_H3.md` (§3.3 route (b), §4 unit table,
wave 0, deps none). This file is a LITERATE LEAN MARKDOWN NOTE (the H4-M2/H4-M7
format): prose in comment blocks, every Lean line compiles. Gate command (from
`lean/`): `lake env lean notes/openmath/H3_en_walk.md` — green, zero sorry.

CHARGE (blueprint §3.3, route (b), verbatim): "Walk, display-by-display: (i) CU-4
F4-S/F4-C's five supply legs (the §4 assembly display) — record for each whether
the consumed count/acceptance object carries thr ≤ N (expected: yes — F4-C's own
hypothesis is N ≥ N\*(𝐇), a thr-majorant by the N\* join clause); (ii) the O3adj
R2 risk row — re-adjudicate against the walked display; (iii) Step 16's (UB-X)(a)
transport of the same content at q^δ; (iv) the squeeze-side: input (vii)'s
displayed thr-scoped sum + the drainage absorption of the thr>N decided boxes
(cite the envelope displays, Step 13/Step 19). Deliverable: a walk note in the
CU_cluster style with a per-site table (site / consumed object / thr-scoped? /
display quoted), ending in one of: RESCOPE-CLEAN ((E-N) consumed nowhere
unrestricted) or a NAMED consuming site." Duty W-3 (§3.2 circularity guard) is
executed at §4.3 below with the envelope definitions quoted.

STATEMENT-FENCE RECORD: EN-U1 is kind "walk note (doc)"; the blueprint assigns
it NO Lean statement (the §3.4 Lean spec `ENRedundancyAt` belongs to unit EN-U4,
a different unit, untouched here). Nothing is transcribed, weakened, proved, or
discharged by this note; the Lean content at the foot is compile-checked
cross-reference PINS only. No file outside this note is edited. Cross-ref:
G-EN-1 (unit EN-U2, `verification/h3_en_falsifier.py`) is NOT yet on file at
walk time; EN-U1 has no dependency on it (blueprint deps: none). A future
G-EN-1 hit supplies the worked instance for checking §4.3's absorption displays
numerically; it would not change this walk's verdict mechanism (see §5).

Sources read (all verbatim quotes below carry their line provenance):
`lean/blueprints/HDISCHARGE_H3.md` §3 · `lean/notes/openmath/CU_cluster_phaseB.md`
§0/§4 · `lean/notes/openmath/O3adj_adjudication.md` §4 ·
`docs/ROOT_ASSEMBLY_2026-08-02.md` §1, §3.1 (E-N) row, Steps 6/13/16/19 ·
`lean/notes/ASSEMBLY_PLAN_2026-07-26.md` (†-AGG)/input (vii) ·
`lean/notes/openmath/O4T_phaseB_verifybrief_rev4.md` §1/§2.

## 0. The object walked, and the W-3 vocabulary split

**(E-N), statement of record (blueprint §3.1, verbatim core):** "whether the
clause thr(T) ≤ N inside D_σ(N) is redundant — i.e. whether a level-N box can
fiber a decided ns-free tree of threshold > N — is NOT settled." Here (same
display) thr(T) := max(1, max over T's chains H of L(H)), and O-1thr rev 4 §6
Theorem 3(c) defines

    D_σ(N) := #{x level-N : fiber(T, x) for some decided ns-free T
               with type(T) = σ and thr(T) ≤ N}
    and proves D_σ(N) = Σ_{T : type(T)=σ, thr(T) ≤ N} mass(T)·p^{nN}.

Note the shape: the thr(T) ≤ N clause sits INSIDE the definition of D_σ(N).
Theorem 3(c) is therefore itself a thr-scoped display; (E-N) is the question
whether an UNRESTRICTED reading ("x fibers a decided ns-free tree, any
threshold") would count more boxes. The walk asks: does any mandatory-path site
consume the unrestricted reading?

**W-3 vocabulary (the two predicates the circularity guard separates):**
* SEMANTIC decidedness of a box x — x fibers a decided ns-free tree (the tree
  predicate; threshold unconstrained). This is (E-N)'s unrestricted reading.
* OPERATIONAL decided-at-cap-N — the detected class: the classifier's level-N
  datum decides x (certificate fires by level N; equivalently membership in a
  thr ≤ N fiber, per §1/§4 below).
W-3's charge: verify at §4.3 that every envelope consumed by the squeeze is
DEFINED as the complement of a DETECTED-at-N class (absorption definitional),
never as the complement of the semantic class (a real gap).

## 1. Site (i): CU-4 F4-S/F4-C — the §4 assembly display, leg by leg

The statements walked (CU_cluster_phaseB.md §4, verbatim): "(F4-S — soundness,
every N): Cert accepts (x_f, 𝐇) ⇒ 𝐇 ∈ Run_N(x_f) AND 𝐇 is verdict-carrying in
T_can(f). (F4-C — completeness at the decision level): if 𝐇 ∈ T_can(f) is
verdict-carrying and N ≥ N\*(𝐇), then Cert accepts (x_f, 𝐇)."

The assembly display (ibid., verbatim): "F4-S = record-only acceptance (O-1thr
§1.4) + CU-2 (the accepted history is Cons_f) + 2(B) (verdict-carrying). F4-C =
CU-1 (the verdict-carrying 𝐇 is realized on f; working-level form via Corollary
CU-1-LVL's one D-14 application) + CU-2t (the terminal record fires, forced) +
the TB-CAP window (it fires WITHIN the level budget). ... the composition of
these five supplies has not been walked end-to-end in any home package."
COUNTING NOTE: the display names SIX glue items from FIVE supply sources
(O-1thr §1.4, CU-2, O-2a 2(B), CU-1, CU-2t; TB-CAP is T-6's window bookkeeping
riding the composition). This walk covers all six displayed legs — a superset
of any five-way grouping, so no leg escapes on a counting convention.

* **S1 (F4-S ← O-1thr §1.4 record mechanics).** Consumed object: the acceptance
  record evaluated ON the accepted history at level N (IrrHalts ⟺ μ_last = 1;
  irrVerdict a pure record function; τ-hen certificates from mod-p data — §4
  supply bullet). The consumption is CONDITIONAL on acceptance, a level-N
  detected event; and the display itself keys the uniformity to the threshold:
  "at any box fibering a decided ns-free T, 'Cert accepts' is record-determined
  and uniform on the thr(T)-cylinder". No unrestricted decided class is
  quantified. thr-scoped: YES.
* **S2 (F4-S ← CU-2, Cons_f).** Consumed object: "the accepted history is
  Cons_f" — again FROM acceptance; only detected histories enter. YES.
* **S3 (F4-S ← O-2a Theorem 2(B)).** Consumed object: the semantic verdict tie
  "at the last continuing node, accE·accF = deg f_{t^{(k')}} ⟺ μ_{k'} = 1",
  applied (display: "through CU-2's Cons_f") to EMITTED, ACCEPTED saturated
  leaves. Only detected objects. YES.
* **C1 (F4-C ← CU-1 via Corollary CU-1-LVL).** F4-C's OWN hypothesis is
  "verdict-carrying and N ≥ N\*(𝐇)". N\* display (CU_cluster §0, standing,
  verbatim): "N\*(𝐇) = the D4R.4/L12 per-branch level with the TB-CAP
  verdict-window join; CEIL-UB retained one-directional"; and the majorancy
  direction is displayed at the D-14 application: "Applied over the witness's
  chain with N\*(𝐇) ≥ L bookkeeping (CEIL-UB direction)" — per-chain
  N\* ≥ L(H), so N ≥ N\*(𝐇) majorizes every chain ceiling, i.e. exactly the
  thr-majorant the blueprint expected. Boxes below a tree's threshold are
  simply OUTSIDE F4-C's hypothesis; the statement never claims them. YES.
* **C2 (F4-C ← CU-2t).** Consumed object: "the terminal record fires, forced" —
  an event of the run within the working level. YES.
* **C3 (F4-C ← TB-CAP window, T-6).** Consumed object (verbatim): "the
  certificate fires within its verdict window — the level bookkeeping that
  makes 'accepts AT N ≥ N\*' well-posed (N\*'s join clause)". Explicitly
  window-scoped; this leg carries D-12r's perimeter conditionality (its own
  §3.1 row), not (E-N). YES.
* **The Theorem-3 supply bullet, where (E-N) is displayed.** What CU-4 consumes
  from O-1thr Theorem 3 is "(F1) T's chains are ALL AND ONLY the realized pruned
  runs on f_x, and (F4) interior chains do not halt — both transported
  cylinder-exactly by Theorem 3(a)" — the FIBER clauses at the thr(T)-cylinder,
  NOT Theorem 3(c)'s count. Theorem 3(c) enters CU-4 only as the carried scope
  caveat (verbatim): "Scope caveat carried: (E-N) (can a level-N box fiber a
  thr > N tree?) is OPEN (O-1thr §6 rev-3 scoping) and touches F4-C's
  decision-level scoping through Theorem 3(c) — displayed, inherited, owned by
  O-1thr." That is PRICING (a condition displayed on the perimeter), not a
  consumption of the unrestricted count: F4-C's displayed statement is already
  confined to N ≥ N\*(𝐇) (leg C1), and 3(c)'s count is thr-scoped inside its
  own definition (§0). Dfloor supplies no proof content toward CU-4 (display:
  it is CU-4's fence-side CONSUMER) — no leg there.

**Site (i) finding:** every supply leg consumes acceptance events, run events,
or N ≥ N\*-scoped statements — detected objects all; the one appearance of
Theorem 3(c) is the displayed OPEN caveat itself. No leg consumes the
unrestricted reading.

## 2. Site (ii): the O3adj risk row R2, re-adjudicated

R2 (O3adj_adjudication.md §4, verbatim): "R2: the (E-N) caveat (can a level-N
box fiber a thr > N tree?) touches CU-4's decision-level completeness through
O-1thr Thm 3(c)'s scoping — displayed OPEN."

Re-adjudication against the walked display: R2 records exactly the touch walked
at §1's Theorem-3 supply bullet and names no OTHER consumer; as §1 shows, the
touch is a perimeter display on F4-C's scoping, while F4-C's displayed statement
is thr-scoped through its own N ≥ N\*(𝐇) hypothesis. R2 therefore stands as
what it says it is — a RISK row (evidence of pricing, exactly as the blueprint's
§3.2 hypothesis put it), not a consuming site. After the EN-U5 ROOT-row rewrite,
R2's wording may cite the rescoped reading; that rewrite is EN-U5's, not this
note's. thr-scoped: YES (no unrestricted consumer named).

## 3. Site (iii): Step 16's (UB-X)(a) transport at q ↦ q^δ

The ROOT (E-N) row (ROOT_ASSEMBLY_2026-08-02.md §3.1, verbatim): "OPEN, scoped,
touches CU-4 through Thm 3(c) (risk row R2 of the O3adj display) — AND enters
Step 16/clause (UB) through the (UB-X)(a)-transported dictionary/CU/drainage
layers, the SAME CU-4/Thm 3(c) content transported at q ↦ q^δ ... Beyond that
CU-4 touch and its clause-(UB) transport, NO other mandatory-path site consumes
it." Step 16's (a) (verbatim): "(a) the per-leaf O_δ re-base audit for the
leaves stated over ℚ_p (the dictionary/CU/drainage layers — the 'per-leaf scope
hygiene' of the D-3 collapse, declared but unwritten)".

Walk: the transported object is BY THE ROW'S OWN WORDS the same CU-4/Thm 3(c)
content with the base ring re-based to O_δ = W(F_{p^δ}). Transport changes the
base, not the level scoping: Theorem 3(c)'s display carries thr(T) ≤ N inside
D_σ(N)'s definition over either base, and F4-C's hypothesis N ≥ N\*(𝐇) rides
along verbatim. The (UB-X)(a) audit itself is declared-but-unwritten and is
PRICED as (H4b) on its own §3.1 row; its subject is the already-scoped ℚ_p
displays of §1. So the transport introduces no new consumption shape at δ > 1 —
it inherits §1's verdict. thr-scoped: YES (by inheritance).

## 4. Site (iv): the squeeze side

### 4.1 Input (vii)'s displayed sum — thr-scoped by definition

ASSEMBLY_PLAN_2026-07-26.md, (†-AGG) input (vii) (verbatim): "decided_σ(N) is
computed by the TREE-SHAPE sum

    decided_σ(N) = Σ_{T̂ : type(T̂) = σ, thr(T̂) ≤ N} C_T̂(q)·q^{nN−A(T̂)}

where T̂ ranges over complete finite tree SHAPES — 𝒯^fin shapes ONLY"; and
(†-AGG) instance (2): "decided_σ(N) itself — each decided f counted ONCE —
admissible ONLY via input (vii)'s tree-shape sum". The partition display (same
input): "the tree fibers {f : T_can^τ(f) = T} PARTITION the decided set
(T_can^τ choice-free)". The census-side brackets (same display): "the two-sided
SQUEEZE brackets (⌈(R_σ(p) − env(N))p^{nN}⌉ ≤ decided_σ(N) ≤ ⌊R_σ(p)p^{nN}⌋)".

Finding: the census-side counting object is DEFINED by the thr-scoped sum — the
protocol declares it "admissible ONLY" via that sum, so the unrestricted reading
cannot be consumed here: the object does not exist under it. thr-scoped: YES,
definitionally.

### 4.2 The (SQ) bracket — no tree object consumed at all

ROOT §1 (verbatim): "decided_τ(k) counts the residue classes mod p^k ALL of
whose monic lifts are separable of type τ; undec(k) is the measure of the
classes not decided for any type", and clause (SQ):

    decided_τ(k)/p^{nk} ≤ α(n, τ; p) ≤ decided_τ(k)/p^{nk} + undec(k),
    and undec(k) → 0 (drainage).

Attribution (ROOT §1, verbatim): "clause (SQ) — under this section's SEMANTIC
definitions of decided_τ(k) and undec(k) — rests on Step 1's bracket
(Corollaries BRACKET/SEM-DRAIN) + Step 13's semantic drainage layer, both
unconditional at every prime including wild: it consumes NO §3.1 row."

Finding: these definitions mention NO tree, threshold, or fiber predicate —
decided_τ(k) is the type-constancy predicate of the level-k class (O4T's c^sem)
and undec(k) its complement-of-any-type. The bracket is pure measure theory
over those class predicates. (E-N) cannot touch (SQ): there is no display in it
for either reading of the tree count. (The word "SEMANTIC" in the ROOT contrasts
these definitions with the CLASSIFIER-side counting — it does not mean the tree
predicate of §0's W-3 split; both (SQ) definitions are level-k class predicates.)
thr-scoped: N/A — no tree-count object consumed.

### 4.3 Duty W-3 — the drainage absorption, envelope definitions quoted

The absorption step under audit: "a decided box whose unique tree has thr > N
sits in the undecided-at-N envelope; drainage prices it to 0."

**Envelope definitions on file (both quoted verbatim):**
* O4T_phaseB_verifybrief_rev4.md §1: "A classifier c assigns to every level-N
  class a splitting type or ⊥, subject to stability ... It is sound if
  c_N(x) = σ ≠ ⊥ implies: every lift a ∈ x has f_a separable with σ(f_a) = σ.
  Undecided set and density:

      U^c_N := { a : c_N(a mod p^N) = ⊥ },   env^c(N) := μ(U^c_N)
      (= undec^c(N)/p^{nN} with undec^c(N) the number of undecided level-N
      classes)."

  This is the COMPLEMENT OF THE DETECTED-AT-N CLASS, by definition: U^c_N is
  defined through the classifier's level-N output, never through the tree
  predicate.
* ROOT §1 (quoted in full at §4.2): undec(k) = complement of any-type
  constancy — the c^sem instance of the same shape, again a level-k class
  predicate, not the tree predicate.

**Which envelope does the census-side bracket consume?** Step 13's Delivers
line (ROOT, verbatim): "The TRANSFER layer (the canonical classifier's own
termination + drainage: unconditional at n ≤ 3 by Theorem N3; conditional on
(AGR) (= CU-2 + CU-4 + Cor 4.19, all on file above) at general n) serves the
classifier-side counting reading consumed by Step 19's squeeze machinery inside
clause (R)'s conditional scope". So env(N) in §4.1's bracket is the OPERATIONAL
envelope env^can(N) = μ(U^can_N) — the O4T display above.

**Adjudication (the W-3 question).** The envelope is defined as the complement
of the detected-at-N class — the first horn of W-3, under which absorption is
definitional. Displayed, the absorption runs: a type-σ box x NOT counted by
§4.1's thr-scoped sum is (by input (vii)'s partition display, T_can^τ
choice-free) a box whose canonical tree has thr > N; such x lies in U^can_N
PROVIDED the connector

    (EN-W1)  c^can decides x at level N  ⇒  x's canonical tree has thr ≤ N

holds — and (EN-W1) is the certificate's own window bookkeeping, already
displayed at legs C1/C3 of §1 (detection = acceptance fires within verdict
windows joined into N\*(𝐇); per-chain N\* ≥ L(H) is the CEIL-UB direction
quoted at C1, so every certified chain ceiling, hence thr, is ≤ N) together
with F4-S soundness (an acceptance names a realized run of x's own canonical
tree, not some other tree). Membership in U^can_N is then definitional, and
drainage of env^can(N) is Step 13's transfer layer at its displayed price
(Theorem N3 unconditional at n ≤ 3; (AGR)-conditional at general n). Note the
DIRECTION of (EN-W1): detected ⇒ thr ≤ N. That is the OPPOSITE direction to
(E-N) (whose open question is about semantically decided boxes BELOW their
tree's threshold) — so the absorption consumes CU-4/CU-2t window bookkeeping at
its displayed conditionality, and does NOT consume (E-N) in either reading.
Had the envelope been defined semantically (complement of "fibers a decided
ns-free tree"), the thr > N boxes would sit OUTSIDE it and route (b) would fail
here; the quoted displays show it is not so defined. Absorption: DEFINITIONAL,
with the connector (EN-W1) named and priced where it already lives.

## 5. Per-site table (the deliverable)

| site | consumed object | thr-scoped? | display quoted |
|---|---|---|---|
| CU-4 S1: O-1thr §1.4 record mechanics | acceptance record at level N, uniform on the thr(T)-cylinder | YES (from acceptance) | §1 S1 |
| CU-4 S2: CU-2 | Cons_f membership of the ACCEPTED history | YES (from acceptance) | §1 S2 |
| CU-4 S3: O-2a 2(B) | verdict tie at accepted saturated leaves | YES (from acceptance) | §1 S3 |
| CU-4 C1: CU-1 + Cor CU-1-LVL | realization of verdict-carrying 𝐇 under hypothesis N ≥ N\*(𝐇); N\* ≥ L per chain (CEIL-UB) | YES (N ≥ N\* in the hypothesis) | §1 C1 |
| CU-4 C2: CU-2t | terminal record fires within the run | YES (run event) | §1 C2 |
| CU-4 C3: TB-CAP window (T-6) | certificate fires within its verdict window (N\* join); D-12r's own row prices the perimeter | YES (window-scoped) | §1 C3 |
| CU-4 ← O-1thr Thm 3 | fiber clauses (F1)/(F4) via Thm 3(a) at the thr(T)-cylinder; Thm 3(c) present only as the carried OPEN caveat | YES; the 3(c) touch is pricing, not count consumption | §1 bullet 7 |
| O3adj risk row R2 | the same CU-4/Thm 3(c) touch, recorded as a risk | YES (names no unrestricted consumer) | §2 |
| Step 16 (UB-X)(a) transport | the SAME CU-4/Thm 3(c) content re-based to O_δ at q ↦ q^δ; audit priced as (H4b) | YES (inherited; base changes, scoping does not) | §3 |
| Squeeze: input (vii) sum | decided_σ(N) := Σ_{T̂ : type(T̂)=σ, thr(T̂) ≤ N} C_T̂(q)·q^{nN−A(T̂)} | YES (by definition; "admissible ONLY" via this sum) | §4.1 |
| Squeeze: clause (SQ) bracket | §1 decided_τ(k)/undec(k) — level-k class predicates, no tree object | N/A ((E-N)-irrelevant: no tree count consumed) | §4.2 |
| Squeeze: drainage absorption | env^can(N) = μ(U^can_N), U^c_N := {a : c_N(a mod p^N) = ⊥} — complement of the DETECTED class | YES (absorption definitional given (EN-W1), which points the OPPOSITE direction to (E-N)) | §4.3 |

## 6. VERDICT: RESCOPE-CLEAN

(E-N)'s unrestricted reading is consumed NOWHERE on the walked perimeter: every
finite-N counting or acceptance object on the mandatory path is thr-scoped by
its displayed definition or hypothesis (table §5), the (SQ) bracket consumes no
tree object at all, and both envelope definitions on file are complements of
DETECTED-at-N classes, making the drainage absorption definitional (duty W-3,
first horn). Per the blueprint's discharge criterion, route (b)'s walk half is
COMPLETE; the ROOT (E-N) row rewrite ("OPEN, consumed nowhere unrestricted;
scoped count + drainage absorption displayed") is unit EN-U5's, through a VC
round — NOT executed here.

**HONEST RISKS (carried, not discharged):**
1. CU-4's own end-to-end walk is ITSELF unwalked and conditional on three
   pending passes — P(O-1thr r4), P(O-2a r5), P(CU-1 r2). This note walks the
   (E-N)-relevant faces ONLY and must not be cited as CU-4's full walk
   (blueprint §3.3 honest-risk clause, restated).
2. The absorption connector (EN-W1) (§4.3) is CU-4/CU-2t window bookkeeping
   consumed at its displayed conditionality (incl. D-12r's TB-CAP perimeter on
   leg C3 and (AGR) at general n). If a future CU-4 walk finds detection
   WITHOUT window containment, §4.3's absorption site re-opens; that would be a
   defect of the window bookkeeping, not a consumption of (E-N).
3. (E-N) itself remains TRUE AND OPEN as a caveat; RESCOPE is a display change
   (the caveat prices nothing on the mandatory path), exactly as the blueprint
   defines the retirement.
-/

import LeanUrat.Scaffold.Hypotheses

namespace LeanUrat.Scaffold.HDischarge.H3.EnWalk

/-! Compile-checked cross-reference pins (the H4-M7 convention): each `example`
pins a corpus name this walk cites, so the cross-references cannot silently rot.
No new mathematical declaration is made; nothing is discharged. -/

-- §0/§6: the (E-N) hypothesis row this walk rescopes (H3 leg 2), its (H3)
-- siblings touched at legs C3 (D-12r) and §3's transport ((UB-X)(a)).
example := @LeanUrat.Scaffold.RootHyps.h3_en
example := @LeanUrat.Scaffold.RootHyps.h3_d12r
example := @LeanUrat.Scaffold.RootHyps.h4b_rebase

end LeanUrat.Scaffold.HDischarge.H3.EnWalk
