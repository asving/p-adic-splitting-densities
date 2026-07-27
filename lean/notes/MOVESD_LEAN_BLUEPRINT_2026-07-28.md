# MOVESD LEAN BLUEPRINT — REV 8 (closing)

REV 8 (2026-07-28): the closing sweep — Fable#6 ACCEPT (0 crit / 2 one-line gaps;
certificate replicated in Python, two self-invented adversaries killed, the
UNCLAIMED A(P̂₀) = 14 cross-checked against the note) ∪ Codex FINAL#6 REJECT 3/3
(short, note-supported). Implemented:
(1) ShapeWF gains the RESIDUE-DEGREE laws `w0`/`wchain` (w₀ = 1; w_{r+1} = w_r·g_r
— L3's retained "residue degrees w_r" now chained; §D4-R.6: "F₁ := F_p[z]/(ψ) =
F_{p²}, w₁ = 2"); new adversary A-vi (root-only w = 2) FAILS the certificate.
(2) SW1 now DERIVES MonicTie's derivable clauses (monicTop → r = 0 via
hmonicRoot + root_iff; non-root reads' monicTop = false); the genuinely
underivable residue — the ROOT read's monicTop ↔ (s0+wSide = n) — is the named
encoding gap ENC-MONIC (§2 ledger), kept as SW1's weakest sufficient hypothesis
`hmt0` with the §D4-R.6 display quoted.
(3) The ∅ dispatch reaches E9/D3a/W3 through the F3/CD bridge: D4R2'/D4R2'_full
are restated on `Shape.CD` (C_∅ = 1 ≤ Mfac(∅)·p^{W(∅)} = 1 — the note's C_∅ = 1
arithmetic IS the theorem there); E9 gains `encTargetP_empty` (the
singleton-to-unit encoding display).
(4) Gaps: `strS` HOISTED to §3.0 group (1) (gamTie consumes it — the order now
elaborates); TreeModel gains L2's ALL-AND-ONLY law (`eligible` + `child_iff`,
typed OPEN); VerdictModel gains the uniform-cap teeth (`capBound`/`hcapU`/
`hcapB`/`hlevel` — `cellOf := id` now fails `cell_local`).
(5) Fable's one-liners: the §3.2 variable line completed; the Shape.NP ∅-routing
docstring sentence added (+ the elided word "value" restored).
Tables §9–§14 historical; §15 = REV 8. [Pre-REV-8 headers follow, audit trail:]

# MOVESD LEAN BLUEPRINT — REV 7 (certificate completion)

REV 7 (2026-07-28): completion sweep on the DUAL-CONFIRMED architecture — Codex
FINAL#5 REJECT 2/3 (`MOVESD_AUDIT_CODEX_FINAL5_2026-07-28.md`) ∪ Fable#5 REJECT
0 crit/2 gap (`MOVESD_AUDIT_FABLE5_2026-07-28.md`); both AFFIRM the domain-subtype
cure and the gate arithmetic. The union, implemented:
(1) ShapeWF COMPLETION (Codex c.1 — its h = 0 adversary stands): `ShapeRead` gains
`hh`/`hcop`/`hspecInc`/`hspecRec` (Node's "genuine polygon side: e, h ≥ 1, coprime"
+ the §C.0 species laws), `ShapeWF` gains the LATTICE ties `gamTie` (coherence's
γ-tie: γ = e·(STR·u*) + j*·h — L3 rev 9's "γ_r := e_r·u*_r + j*_r·h_r, §C's
DERIVED list") and `anchorTie` (Node.hAnchor at THE canonical Bézout coefficient
`bezT`, D.3(c)'s stride anchor). ALL adversaries re-run in §3.1: Fable's three +
Codex's h = 0 + a gcd violation (all FAIL the certificate); positives P̂*, P̂₀
(both PASS, every new clause checked).
(2) NP EMPTY-FAMILY CASE (Codex c.2): L12 QUOTED — "N(P̂) := 1 if Pref(P̂) = ∅" is
UNCONDITIONAL on the band, so the PIECEWISE form is required: `NP` is now
`if Nonempty (PrefIdx …) then NPband else 1` (`NPband` = the band-sup formula);
a nonempty shape with no realizable assignment gets NP = 1 exactly; the max-η
identification claim is SOFTENED to its corpus-consumed content (NP_stab + range).
(3) THE BINDING SWEEP (Fable g.1 = Codex g.3): §3.2/§3.4 signatures re-bound to
`Shape n` throughout (PrefIdx, PresentNorm, reprOf, CD → `Shape.CD`, PrefOpt,
Presented, D4R_CYL, ClassFiberWelldef) — the skeleton elaborates as displayed.
(4) SMALL ITEMS: stale TW sketch line purged (Fable g.2); hypothesis_fields now
list `hnorm` on D2a/F1/E9/D3a (Codex g.4); VerdictModel's `Cell` gains `hCellFin`
+ `cell_local` (the typed non-degeneracy tie, OPEN — Codex g.5); `rootHalt_iff`
gains the root-species filter (Fable OBS-1); NP docstring re-scoped (OBS-2);
§7 item 7 updated to "jet + hnorm" (OBS-3).
Tables §9–§13 historical; §14 = REV 7. [Pre-REV-7 headers follow, audit trail:]

# MOVESD LEAN BLUEPRINT — REV 6 (the domain-subtype ruling)

REV 6 (2026-07-28): the rev-5 verdicts split a fifth time — Fable#4 ACCEPT 0/0
(`MOVESD_AUDIT_FABLE4_2026-07-28.md`: gate recomputed on the Option carrier,
adversarial instances constructed and killed, L12 verbatim) vs Codex FINAL#4
REJECT 4/3 (`MOVESD_AUDIT_CODEX_FINAL4_2026-07-28.md`). ORCHESTRATOR DIAGNOSIS:
Codex's criticals 1–3 are ONE disease — the Lean `ShapePrefix` TYPE is bigger than
the note's universe (junk shapes ⟹ vacuous mass laws; pol-quantified units
trivialize on policy-voided domains; the M-bound needs a rider). THE RULING,
implemented here:
(1) the quantification domain becomes the note's universe BY TYPE:
`Shape n := {P : ShapePrefix // ShapeWF n P}` — the wf-certificate-in-the-type
pattern (the certificate variant of the L3 dictionary-image predicate, definable
from existing vocabulary; `MonicTie` is a COMPONENT of `ShapeWF`, §3.1). All
shape-quantified units re-bind `{P : Shape p F n}`→ mass laws hold UNCONDITIONALLY
over the note's shapes: no `Wellformed` riders (W2 unconditional over the
subtype), no junk-shape vacuity (a malformed monic encoding is NOT A SHAPE —
Codex#4 f.1's own words), W3 states BOTH displayed bounds. Gate preserved: §0.6's
subtype addendum shows P̂* ∈ Shape 3 and re-derives C_P̂*(2) = 3, mult ≡ 1 there.
(2) the five pol-standalone units (D2a, F1, E9, D3a, W3) gain
`hnorm : PresentNorm …` — normalized presentations, exactly the note's domain
(Codex#4 f.2).
(3) `Threshold.NP` is GONE as free data: `ShapePrefix.NP` is DEFINED by L12's
exact formula (1 + the largest constrained level; the max over η collapses by
shape-constancy — the note's own "identical for every η ∈ Pref(P̂*)"); `hstab`
and `NP ≤ Nshape` are DERIVED (unit NPu); D4R4_all covers ∀ N ≥ NP exactly —
no dropped range (Codex#4 f.4). Gate: NP(P̂*) = 1 + 4 = 5, the note's own
derivation reproduced.
(4) VerdictModel gains the root-(ns)-verdict and cell-exact-factorization TYPED
OPEN fields (Codex#4 f.5); §3.0 fixes declaration order normatively (f.6); every
"as rev 2" unit spec is INLINED in full (f.7).
Tables: §9–§12 historical; §13 = REV 6. [The pre-REV-6 header follows, kept for
the audit trail:]

# MOVESD LEAN BLUEPRINT — REV 5

Campaign unit-spec per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2. Writer: Fable.
REV 5 (2026-07-28): the rev-4 verdicts SPLIT maximally — Fable#3 ACCEPT 0/0
(`MOVESD_AUDIT_FABLE3_2026-07-28.md`: gate recomputed, all four pushbacks UPHELD)
vs Codex FINAL#3 REJECT 7/1 (`MOVESD_AUDIT_CODEX_FINAL3_2026-07-28.md`: all four
pushbacks rejected). ORCHESTRATOR ADJUDICATION: most disputes are two-readings-
both-right; REV 5 implements RECONCILING DESIGNS satisfying both (each pointed at
EXPLICITLY where the auditors looked; table §12):
(1) TreeModel is OPTION-ROOTED with the root's presence a LAW (`root_mem` — L2's
"its root is the empty chain ∅") while nonempty-chain inhabitation stays unforced
(L5's (ns) leaf case — Fable's computation stands);
(2) PRESENT-NORM is now the TYPED Prop `PresentNorm` — source set POLICY-FREE
(`PrefSetAny`), so a junk policy or a truncated normalization VIOLATES the field
`Presented.hnorm` (this also implements (6): CanonPolicy adequacy — L1 totality +
the L6-corollary "realizable ⟺ realized" — without pinning offset-P, still POL-PIN);
(3) the ∅ representation is a machine-checked BRIDGE THEOREM (F3 on the new
Option-level `PrefOpt`: literally `Pref(∅) = {∅}` + the CD correspondence);
(4) monicTop keeps the Boolean + guard (Fable's L11 reconstruction stands) PLUS the
definitional tie `MonicTie` (monicTop ↔ the root window's degree-n slot) as a
PrefSet clause — junk-monicTop shapes void their own PrefSet;
(5) D4R4_all is restated at the NOTE's threshold: `Threshold` structure with field
NP + its L12-visible defining properties; Nshape = the constructive witness
(`threshold_witness`); L12/D4R.4 quantifier quoted and matched;
(7) ClassFiberWelldef displayed as a Defs Prop and WIRED as D15's hypothesis;
(8) VerdictModel's cell tie stays the honest declared deferral.
REV-2 table §9, REV-3 §10, REV-4 §11, REV-5 reconciliation §12.

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

REV-6 SUBTYPE ADDENDUM (the gate lives in the note's universe — MANDATORY check):
P̂* satisfies `ShapeWF 3` clause by clause: species root-iff (read 0 root, read 1
recentering ✓); root_box 0+3 ≤ 3 ✓; window s0₁+wSide₁ = 1 ≤ μ₀ = 1 ✓; gmu
2·1 ≤ 3, 1·1 ≤ 1 ✓; edvd 1∣3, 1∣1 ✓; dchain D₀ = 1, D₁ = e₀g₀D₀ = 2 ✓ (the F_{p²}
block width); MonicTie read 0: monicTop ∧ 0+3 = 3 = n ✓, read 1: ¬monicTop ∧
0+1 ≠ 3 ✓. So P̂* ∈ Shape 3, and every count above is computed OVER THE SUBTYPE
unchanged: C_P̂*(2) = 3 ✓, C_P̂*(3) = 48 ✓, mult ≡ 1 ✓. The exact threshold formula
(§3.3; REV 7: the INHABITED branch of the piecewise NP — PrefIdx(P̂*) ≠ ∅):
NP(P̂*) = NPband = 1 + (largest constrained level = 4, at c₀'s level-4 band
coordinate) = 5 — the note's own "N(P̂*) = 1 + (largest pinned base level = 4, at
c₀) = 5" REPRODUCED BY THE DEFINITION (here NP = Nshape = 5; in general NP ≤
Nshape, unit NPu).

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
| `Matches.hmonic` + `ShapePrefix.MonicTie` (a `ShapeWF` COMPONENT) [REV 6] + **ENC-MONIC** (SW1's `hmt0`) [REV 8] | root monic lead digit = 1 (scoped, §0.5) + monicTop ⟺ the root window's degree-n slot; ENC-MONIC = the one underivable clause (root monicTop ↔ full span), an ENCODING-correctness duty | interface equalities; malformed encodings are NOT SHAPES; ENC-MONIC owned by the D4-n3 gate + menu-wave verification (each catalogued shape's bit checked against its displayed side) |
| `InBox n` (PrefSet clause) | the root side lies in the degree-n box | part of "§C history of the degree-n box" (the note's setting); consumed by W1 |
| `Presented.jet` + `Presented.hnorm` [REV 5] | per-class presentations (§C C.2) + the typed dictionary pin | HC-2 bridge — the corpus's two assumed structure fields; `Threshold.{hstab, jets}` packages them at the note's NP (reconciliation (5)) |
| `D4R_CYL S T` (pinned Prop, def) | L6's (D4R-CYL) | note-PROVED given kernel (a)+(b) (both dual-verified-discharged) + Thm C(a); Lean proof EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus; D15 consumes it as a named hypothesis |
| `TreeModel` data (`mem`, `child`) + laws | L2's T_can | interface data; laws are fields; uniqueness/eligibility semantics = kernel-(b) content, HC-2 |
| `VerdictModel` (whole) | D4R.0-K(c)/VP: alphabet V, emission, halt dichotomy, per-class cap law | **OPEN** — owned by §T-ASSEMBLY → MovesT; typed, consumed by nothing in MovesD |
| `hN : 1 ≤ N`, `hm : m = n*N` (D14a/D14b hyps) | L12's empty-case N(P̂) := 1 convention; the box shape | explicit theorem hypotheses (no jet available) |
| **PresentNorm** (TYPED Prop + the FIELD `Presented.hnorm`) [REV 5 ⇐ rev-4 prose pin] | the two-sided classes ↔ η dictionary: totality from the POLICY-FREE `PrefSetAny` (L1 kernel-(a) totality + L6-corollary realizable ⟺ realized + conjugation equivariance) ∧ Galois uniqueness (embedding rigidity) | HC-2 discharge; VIOLATED by truncated normalizations AND by history-voiding junk policies (reconciliations (2)+(6)); gate-checked §0.6 |
| **PRESENT-EXIST** (declared hyp) [REV 7: at the piecewise NP] | `∀ N ≥ P.NP pol, Nonempty (Presented …)` — presentability at every level of L12's exact range (§C C.2) | HC-2; sole consumer: `TW_threshold_witness` |
| **ClassFiberWelldef** (Defs Prop, §3.4) [REV 5: displayed AND wired] | representative independence: one η-class, one classifier locus (§C L4) | HC-2 (wave-4 tree corpus, with D4R_CYL); WIRED as D15's explicit hypothesis `hwd` (reconciliation (7)) |
| **POL-PIN** (future unit, named) [REV 4, Codex#2 f.4] | the instance `pol := the (S6b) offset-P policy` with its realizer laws | owned by HC-1/§B2-DEF corpus; until then all MovesD theorems are ∀-pol |

GONE at rev 3 (previously assumed): `henc` (→ PROVED, E1–E9), `hn : ℓ_r ≤ n`
(→ PROVED, W1), `complete`/`hist_inj`/`hshape`/`hcanon` (→ the construction, F1),
`offSlots_forced` (→ the scoped `hmonic`), `TreeModel.cyl` field (→ the pinned
deferred Prop `D4R_CYL`), bare `cap`/`hcap` (→ the typed cap law).

## 3. Defs skeleton — `lean/LeanUrat/MovesD/Defs.lean` (definitions only)

### 3.0 DECLARATION ORDER — NORMATIVE [REV 6, Codex#4 f.6: the file order IS the
spec; the §3.x display order below is thematic, the FILE follows THIS list]
  (1) `Box`, `topLocus`, `ShapeRead` (+ `d`/`len`/`mbar`/`childWidthS`),
      `ShapePrefix` (+ `W`/`Mfac`), `ShapePrefix.strS` (HOISTED here — REV 8,
      Codex#6 g.4: `ShapeWF.gamTie` consumes it), `MonicTie`, `bezT`, `ShapeWF`,
      `Shape` (the subtype);
  (2) the remaining shape replicas §3.3 — `lineS` … `bandS`, `A`, `Nshape`,
      `A'`, `NPband`, `Anet` (`strS`/`bezT` already in group (1));
  (3) `pool`, `fieldEnum`, `lexLt`, `RanchImage`, `ψImage`, `poolSubfield`,
      `EligibleImage`, `selRank`, `Node.sideDigit`;
  (4) `ShapeRead.Matches`, `MatchesHist`, `CanonPolicy`, `canonRoot`,
      `IsCanon`/`IsCanonPres`, `InBox`, `PrefSet`, `PrefSetAny`, `EtaData`,
      `etaData`, `EtaGalEq` (AFTER EtaData), `PrefIdx`, `Shape.NP` (AFTER
      PrefIdx — REV 7's piecewise form consumes it), `PresentNorm` (AFTER
      PrefIdx), `reprOf`, `Shape.CD`, `PrefOpt`, `etaDataO`, `emptyFiber`,
      `Presented`, `Threshold`;
  (5) `EncTargetP`, `History.snoc`, `History.IsPrefixOf`, `TreeModel`, `D4R_CYL`,
      `ClassFiberWelldef`, `VerdictModel`.
Every forward reference Codex#4 f.6 listed (EtaGalEq, PresentNorm, Threshold.hstab)
is resolved by this order; `Threshold` moreover no longer HAS an hstab field (§3.2).

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
  /-- [REV 7, Codex#5 c.1 — certificate completion, per-read part] Node's "the read
  side is a genuine polygon side: `e, h ≥ 1`, coprime (lowest terms)" (MovesC
  `Node.hh`/`Node.hcop`), and the §C.0 species laws (`Node.hspecInc`/`hspecRec`):
  an increment grows the stage, a recentering has e = 1, g = 1. Codex#5's h = 0
  adversary can no longer BUILD a ShapeRead. -/
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hspecInc : species = ReadSpecies.increment → 1 < e * g
  hspecRec : species = ReadSpecies.recentering → e = 1 ∧ g = 1
  /-- [REV 4, Codex#2 finding 1 — partial concession]: the monic lead exists only at
  the ROOT read (the box's top coefficient; deeper windows sit inside the box). -/
  hmonicRoot : monicTop = true → species = ReadSpecies.root

def ShapeRead.len (R : ShapeRead) : ℕ := R.wSide / R.e         -- ℓ_r = deg R_anch,r
/-- d_r (the tuple size). [REV 5, reconciliation (4) — Codex#3 finding 1]: the
Boolean is EXACT because at most ONE slot per read is off-box (the degree-n monic
slot, root only — Fable#3 C-1), AND `monicTop` is now SEMANTICALLY TIED by
`ShapePrefix.MonicTie` (a PrefSet clause, §3.2): monicTop = true ⟺ the read is the
root AND its top slot IS the degree-n coefficient position (s0 + wSide = n). A junk
shape faking (or omitting) monicTop violates MonicTie and voids its own PrefSet —
the "artificially smaller W" instance is unbuildable on C-carrying territory. -/
def ShapeRead.d (R : ShapeRead) : ℕ :=
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

/-- [REV 5, reconciliation (4)] **The monic-slot tie**: `monicTop` is true EXACTLY at
the root read whose side's top slot is the box's degree-n coefficient position
(root frame width 1: slot index = base index). Both directions: faking monicTop
(omitting a genuine digit, shrinking W) AND hiding it (inflating W past the box)
violate the tie. A PrefSet clause (§3.2), so violating shapes have empty PrefSet. -/
def ShapePrefix.MonicTie (P : ShapePrefix) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).monicTop = true ↔ (r = 0 ∧ (P.reads[r]'hr).s0 + (P.reads[r]'hr).wSide = n)

/-- [REV 7] THE canonical Bézout coefficient `t ∈ [0, e)` of a read side (rev 14's
`t^B`; MovesC `hbezCanon`: unique in the window, a FUNCTION of (e, h) — mirrored
shape-side; junk when gcd ≠ 1, excluded by `ShapeRead.hcop`). At e = 1: t = 0
(D.5's (P2) base — the γ-blind case that forced u*'s retention, L3 rev 9). -/
def bezT (e h : ℕ) : ℤ := (((Nat.xgcd e h).2 % (e : ℤ)) + (e : ℤ)) % (e : ℤ)

/-- [REV 6 — THE DOMAIN-SUBTYPE RULING; Codex#4 findings 1–3's one disease] **The
shape wf-certificate**: the L3-dictionary-image laws expressible on shape data —
what a note shape-prefix IS. A malformed encoding "is not a valid shape-prefix; it
cannot be converted into a valid shape having Pref(P̂) = ∅" (Codex#4 f.1, now the
design). The certificate variant is chosen over the literal ∃-Node-chain image to
stay non-circular and checkable; `ShapeWF_of_matches` (unit SW1) proves every
matched coherent in-box history's shape carries it — nothing of the note's universe
is lost. -/
structure ShapeWF (n : ℕ) (P : ShapePrefix) : Prop where
  species_iff : ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).species = ReadSpecies.root ↔ r = 0
  root_box : ∀ h0 : 0 < P.reads.length, (P.reads[0]'h0).s0 + (P.reads[0]'h0).wSide ≤ n
  window : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    (P.reads[r+1]'hr).s0 + (P.reads[r+1]'hr).wSide ≤ (P.reads[r]'(by omega)).μ
  gmu : ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).g * (P.reads[r]'hr).μ ≤ (P.reads[r]'hr).len
  edvd : ∀ (r : ℕ) (hr : r < P.reads.length), (P.reads[r]'hr).e ∣ (P.reads[r]'hr).wSide
  dchain0 : ∀ h0 : 0 < P.reads.length, (P.reads[0]'h0).Dwidth = 1
  dchain : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    (P.reads[r+1]'hr).Dwidth = (P.reads[r]'(by omega)).childWidthS
  monic : P.MonicTie n
  /-- [REV 8, Codex#6 c.1 — RESIDUE-DEGREE laws] L3 retains "residue degrees w_r";
  the tower chains them: the root pool is the BASE field (w₀ = 1 — §D4-R.6's root
  read: "Side digits (pool F_p)"), and F_{r+1} = F_r[z]/(ψ_r) with deg ψ = g gives
  w_{r+1} = w_r·g_r (recenterings: g = 1, unchanged — one uniform law; §D4-R.6:
  "F₁ := F_p[z]/(ψ) = F_{p²}, w₁ = 2"). The root-only w = 2 record is no longer a
  Shape. -/
  w0 : ∀ h0 : 0 < P.reads.length, (P.reads[0]'h0).w = 1
  wchain : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    (P.reads[r+1]'hr).w = (P.reads[r]'(by omega)).w * (P.reads[r]'(by omega)).g
  /-- [REV 7, Codex#5 c.1 — LATTICE COMPATIBILITY] the γ-tie, shape-side: L3 rev 9's
  "γ_r := e_r·u*_r + j*_r·h_r, §C's DERIVED list" at the chain stretch — mirrors
  `HistoryCoherent`'s γ-tie clause verbatim (γ's ℤ-typing IS on-lattice). -/
  gamTie : ∀ (r : ℕ) (hr : r < P.reads.length),
    (((P.reads[r]'hr).gam : ℤ) : ℚ)
      = ((P.reads[r]'hr).e : ℚ) * ((P.strS r : ℚ) * (P.reads[r]'hr).ustar)
        + ((((P.reads[r]'hr).s0 + (P.reads[r]'hr).wSide) : ℕ) : ℚ) * ((P.reads[r]'hr).h : ℚ)
  /-- [REV 7, c.1] the ANCHOR tie at THE canonical Bézout coefficient (`bezT` below;
  MovesC `hbezCanon`'s unique window representative): Node.hAnchor's
  "a = p_{s₀}(γ) = (s₀ − t·γ)/e", D.3(c/d), shape-side. -/
  anchorTie : ∀ (r : ℕ) (hr : r < P.reads.length),
    ((P.reads[r]'hr).e : ℤ) * (P.reads[r]'hr).a
      = ((P.reads[r]'hr).s0 : ℤ) - bezT (P.reads[r]'hr).e (P.reads[r]'hr).h * (P.reads[r]'hr).gam

/-- **THE NOTE'S SHAPE UNIVERSE, BY TYPE** [REV 6]: every shape-quantified unit
binds `{P : Shape p F n}` (coercion `↑P : ShapePrefix`; certificate `P.2`) — the
mass laws hold UNCONDITIONALLY over exactly the note's shapes ("always" verbatim);
junk data is not in the domain of quantification. -/
def Shape (n : ℕ) : Type := {P : ShapePrefix // ShapeWF n P}

/-- `Wellformed` is now a THEOREM over the subtype (rev-5's W1 argument gone
shape-internal — no member needed): ℓ₀ ≤ s0+wSide ≤ n (root_box), ℓ_{r+1} ≤
s0'+wSide' ≤ μ_r ≤ ℓ_r (window, gmu with g ≥ 1). Stated as unit W1′. -/

-- [REV 7 — THE ADVERSARY RE-RUN (Codex#5 c.1's demand; all five negatives, both
-- positives, against the COMPLETED certificate):
--  A-i  (Fable#5) root wSide = 10, n = 3            → fails root_box            ✗
--  A-ii (Fable#5) monicTop faker (s0+wSide = 2 ≠ 3) → fails MonicTie            ✗
--  A-iii(Fable#5) monicTop at depth 1               → fails hmonicRoot/species  ✗
--  A-iv (Codex#5) one-read root, h = 0              → fails ShapeRead.hh: the
--        record is UNBUILDABLE (was: a certificate-passing junk shape)          ✗
--  A-v  (new) (e, h) = (2, 4)                       → fails ShapeRead.hcop      ✗
--  A-vi (Codex#6, REV 8) root-only record, w = 2     → fails ShapeWF.w0          ✗
--  P̂* (n = 3): hh 1,3 ≥ 1 ✓; gcd(1,1) = gcd(1,3) = 1 ✓; species: read 1
--    recentering with e₁ = g₁ = 1 ✓; gamTie: γ₀ = 1·(1·0) + 3·1 = 3 ✓ (the
--    seal's γ₀), γ₁ = 1·(1·1) + 1·3 = 4 ✓; anchorTie: e = 1 ⟹ bezT = 0 ⟹
--    a = s0 = 0 ✓ both reads ((e,h,g,μ,a) = (·,·,·,·,0)); [REV 8] w0: w₀ = 1 ✓,
--    wchain: w₁ = w₀·g₀ = 1·2 = 2 ✓ (the note's "w₁ = 2"). P̂* ∈ Shape 3.       ✓
--  P̂₀ (n = 4, root-only (1,1,1,2,0), full span, u* = 0): hh/hcop ✓; gamTie
--    γ₀ = 0 + 4·1 = 4 ✓; anchorTie a = 0 = s0 ✓; [REV 8] w0: w₀ = 1 ✓ (root-only,
--    wchain vacuous). P̂₀ ∈ Shape 4; A(P̂₀) = 14 (Fable#6's unclaimed cross-check
--    against the note's "A(P̂₀) = 14"). ✓
-- Every REV-6 gate number is untouched (no new clause constrains the counted
-- digit/class data — they constrain SHAPE fields only).]
```

### 3.2 Canonical policy, PrefSet, η-classes, the constructed family (findings 1–3)

```lean
section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F} {P : Shape n}
-- [REV 8, Fable#6 G-1: the section's variable line completed — the fiber/event/
-- mult trio and every §3.2 def below elaborate as displayed; defs that bind their
-- own (n)/(pol)/(P) shadow these harmlessly.]

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
def PrefSet (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Set (History p F) :=
  {H | (P : ShapePrefix).MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧
       InBox n H ∧ pol.IsCanonPres H}
-- [REV 4] `IsCanon` → `IsCanonPres` (root-normalized presentation class, §0.6).
-- [REV 6, the ruling]: the domain is `Shape n` — MonicTie/wellformedness moved
-- INTO THE TYPE (ShapeWF); the rev-5 clause is deleted, not weakened. ALL
-- downstream defs/units re-bind `{P : Shape n}` (coercions elided below).
-- Defs-file order note: `RanchImage`/`ψImage`/`poolSubfield` (§3.4) precede this
-- section in the actual `Defs.lean` (canonRoot consumes ψImage).

/-- [REV 5, reconciliations (2)+(6) — Codex#3 findings 2/3; Fable#3 OBS-1's own
recommendation] The POLICY-FREE realizable prefix set: shape-matched, coherent,
realizable, in-box — NO canonicity clause of either kind. The reference set for the
typed dictionary pin `PresentNorm` below. -/
def PrefSetAny (n : ℕ) (P : Shape n) : Set (History p F) :=
  {H | (P : ShapePrefix).MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧ InBox n H}

/-- Coordinatewise field-automorphism action on η-class data (the Galois relation
between conjugate presentations — Fable#2 C1's witness action). -/
def EtaGalEq {P : ShapePrefix} (d d' : EtaData F P) : Prop :=
  ∃ φ : F ≃+* F, ∀ r : Fin P.reads.length,
    ((d' r).1 = fun k => φ ((d r).1 k)) ∧ ((d' r).2 = fun k => φ ((d r).2 k))

/-- **PRESENT-NORM, TYPED** [REV 5, reconciliation (2)+(6) — supersedes the rev-4
prose pin]: the two-sided dictionary between the note's η's and the normalized
classes. (i) TOTALITY (= L1's kernel-(a) totality + the L6-corollary "realizable ⟺
realized" + conjugation equivariance): every POLICY-FREE realizable prefix has a
normalized class-mate up to Galois — so BOTH a truncated normalization (empty
PrefIdx against nonempty PrefSetAny) AND a history-voiding junk policy VIOLATE this
Prop; (ii) UNIQUENESS (embedding rigidity): Galois-related normalized classes
coincide — classes never double-count an η. Math status: note-supported (L1
dual-verified-discharged; equivariance/rigidity per Fable#2 C1); Lean discharge =
HC-2. Carried as the FIELD `Presented.hnorm` — every consumer of a presented family
consumes it (the auditors' wiring demand). -/
def PresentNorm (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Prop :=
  (∀ H ∈ PrefSetAny n P, ∃ i : PrefIdx n pol P,
     EtaGalEq (etaData (P : ShapePrefix) H) (i : EtaData F (P : ShapePrefix))) ∧
  (∀ H H', H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') →
      etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H')

/-- [REV 5, reconciliation (3) — Codex#3 finding 5] The OPTION-LEVEL Pref: the
note's chain ontology with the empty prefix as a first-class member (`none` = the
empty chain ∅). F3 proves `Pref(∅) = {∅}` LITERALLY on this object, and the CD
correspondence — the representation deviation is machine-checked, not declared. -/
def PrefOpt (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) :
    Set (Option (History p F)) :=
  {c | match c with
       | none => (P : ShapePrefix).reads = []
       | some H => H ∈ PrefSet n pol P ∧ (P : ShapePrefix).reads ≠ []}

/-- Option-level class data (none ↦ none — the η = ∅ class). -/
noncomputable def etaDataO (P : ShapePrefix) :
    Option (History p F) → Option (EtaData F P)
  | none => none
  | some H => some (etaData P H)

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
def PrefIdx (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Type :=
  ↥(etaData (P : ShapePrefix) '' PrefSet n pol P)

/-- The classical representative section (a DEF, not a field — finding 3). -/
noncomputable def reprOf {n : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (i : PrefIdx n pol P) : History p F := i.2.choose

/-- The corpus C with the note's η = ∅ dispatch baked in at the note's own
definition level (Pref(∅) = {∅} — §D4-R L12/D4R.1: "present iff P̂ = ∅"). -/
noncomputable def Shape.CD {n : ℕ} (P : Shape n) (pol : CanonPolicy p F) : ℕ :=
  if (P : ShapePrefix).reads = [] then 1 else Nat.card (PrefIdx n pol P)

/-- S(∅,⊤) — §C C.0's EMPTY HISTORY clause at Z = ⊤ (the FULL BOX; never Thm C(b)). -/
def emptyFiber (p m : ℕ) : Set (Box p m) := Set.univ

/-- **The presented family** [REV 3, finding 3]: everything is CONSTRUCTED from
`PrefSet` except the two genuinely-open data — the HC-2 presentations and the typed
dictionary pin. [REV 5, reconciliation (2)+(6) — Codex#3 findings 2/3, Fable#3
OBS-1]: `hnorm` makes PRESENT-NORM a FIELD: a family over a truncated normalization
(empty `PrefIdx`, nonempty `PrefSetAny`) or over a history-voiding junk policy is
NOT `Presented` — the vacuity instances Codex exhibited violate `hnorm`, and every
mass-law unit consumes it through its `S` binder. -/
structure Presented (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : Shape n) where
  jet : (i : PrefIdx n pol P) → JetSetup (reprOf i) n N m
  hnorm : PresentNorm n pol P

/-- [REV 5, reconciliation (5) — Codex#3 finding 4] **The note's threshold, as
data with its L12-visible defining properties.** L12 QUOTED: "N(P̂) :=
max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅ … N(P̂) is finite, and for EVERY
N ≥ N(P̂): (D4R.4-SUM) … (D4R.4-EV)". [REV 6]: NP is now the DEFINED
`ShapePrefix.NP` (§3.3 — L12's exact formula; the max over η collapses by L9's
shape-constancy), so the ONLY field left is `jets` — presentations at EVERY level
≥ NP (§C C.2, HC-2). Stability from NP on is DERIVED (NPu); Nshape ≥ NP is DERIVED
(NPu); TW constructs `Threshold` from PRESENT-EXIST (jets on [Nshape,∞) suffice
only if NP = Nshape — in general TW needs presentations from NP on, so its
hypothesis is restated at NP; see the unit). The note does NOT quantify over
presentations (its counts are intrinsic); intrinsic-ness = ClassFiberWelldef. -/
structure Threshold (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) where
  jets : ∀ N : ℕ, P.NP pol ≤ N → Presented p F n N (n * N) pol P
-- [REV 6, Codex#4 f.4]: NP is no longer a FIELD — it is `Shape.NP`, L12's
-- exact PIECEWISE formula (§3.3/REV 7); `1 ≤ NP` holds on both branches; `hstab` is DERIVED
-- (unit NPu). The sole remaining datum is the HC-2 presentations at every
-- N ≥ NP — D4R4_all's range is exactly L12's, no dropped levels.

def Presented.fiber {P : Shape n} (S : Presented p F n N m pol P)
    (i : PrefIdx n pol P) : Set (Box p m) := (S.jet i).SHZ (topLocus p m)
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
open Classical in
/-- The GEOMETRIC threshold: 1 + the largest constrained (band) level. -/
noncomputable def ShapePrefix.NPband (P : ShapePrefix) (n : ℕ) : ℕ :=
  1 + ((Finset.range P.Nshape ×ˢ Finset.range n).filter
        (fun c => ∃ r < P.reads.length, P.bandS n r c)).sup (fun c => c.1)
open Classical in
/-- [REV 7, Codex#5 c.2 — the PIECEWISE form, L12 QUOTED VERBATIM: "N(P̂) :=
max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅, N(P̂) := 1 if Pref(P̂) = ∅" — the empty
clause is UNCONDITIONAL on the band, so a nonempty shape whose realizability
removes every value assignment (the note: "realizability can remove every value
assignment") gets NP = 1 exactly, even with band coordinates at positive levels.]
On the NONEMPTY branch, NPband's alignment with max_η N(η,⊤) is the DOCUMENTED
semantic reading (each N(η,⊤) = 1 + the largest constrained level, §C C.2; the
constrained set = the fresh band via mstar_eq/fresh_band, grid-read by D8/D4b; the
max collapses by shape-constancy — the note's "identical for every η"); the
corpus-CONSUMED content is only NP_stab + the range (NPu, D4R4_all) — nothing
stronger is claimed as a theorem [Codex#5 c.2's second half]. Note: `PrefIdx` is
pol-dependent, hence so is NP — as is L12's own Pref-conditional. Gate (inhabited):
NP(P̂*) = NPband = 1 + 4 = 5, the note's own derivation. [REV 8, Fable#6 G-2 —
the ∅-shape routing, displayed: the note's Pref(∅) = {∅} ≠ ∅ takes L12's MAX
branch with N(∅,⊤) = 1 (T(∅,⊤) has no equations); the Lean PrefIdx(∅) is empty
(History has no empty chain — F3's displayed deviation) and takes the ELSE
branch, value 1; NPband(∅) = 1 too — ALL routes give L12's N(∅) = 1,
value-exact.] -/
noncomputable def Shape.NP {n : ℕ} (P : Shape n) (pol : CanonPolicy p F) : ℕ :=
  if Nonempty (PrefIdx n pol P) then (P : ShapePrefix).NPband n else 1
-- [REV 7 order note: `NPband` stays in §3.0 group (2); `Shape.NP` DECLARES in
-- group (4) AFTER `PrefIdx` (it consumes it) — §3.0 list updated.]
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
  /-- [REV 5, reconciliation (1) — Codex#3 finding 6 ∧ Fable#3 C-8, BOTH satisfied]:
  the node carrier is `Option (History p F)` — `none` IS the empty chain ∅, a
  first-class tree node. -/
  mem : Option (History p F) → Box p m → Prop
  child : Option (History p F) → Node p F → Box p m → Prop
  /-- **THE ROOT'S PRESENCE IS A LAW** (L2: "its root is the empty chain ∅" — the
  root exists for EVERY input; Codex's reading). It may be a LEAF (no children —
  L5's (ns) case; Fable's computation), so NO nonempty-chain inhabitation is forced:
  both rev-4 readings hold on this carrier. -/
  root_mem : ∀ x : Box p m, mem none x
  mem_single : ∀ (ν : Node p F) (h1 : _) (x), mem (some ⟨[ν], h1.1, h1.2⟩) x ↔ child none ν x
  mem_snoc : ∀ (H ν hν x), mem (some (H.snoc ν hν)) x ↔ (mem (some H) x ∧ child (some H) ν x)
  mem_realizable : ∀ H x, mem (some H) x →
    HistoryCoherent H ∧ Realizable H ∧ pol.IsCanonPres H
  /-- [REV 8, Codex#6 g.5 — L2's ALL-AND-ONLY law, typed]: the tree's children are
  EXACTLY the eligible continuations — L2: "the children of a chain η ∈ T_can(f)
  … are ALL next-node data ν = (side s, its digit tuple, ψ, canonical lift) where
  s is an eligible side … and ψ ranges over the eligible factors". The SEMANTICS
  of `eligible` (side/ψ eligibility computed from the FIXED digit cell — "branch
  sets are cell data, not f-data", L5) is kernel-(b) content: OPEN, pinned by
  HC-2/MovesT; the law itself is no longer prose-only. -/
  eligible : Option (History p F) → Node p F → Box p m → Prop
  child_iff : ∀ (o : Option (History p F)) (ν : Node p F) (x : Box p m),
    mem o x → (child o ν x ↔ eligible o ν x)

/-- [REV 5, reconciliation (1) — superseding the rev-4 pushback display]: the
rev-4 dispute is RESOLVED on the Option carrier: Codex#3-f.6's "the empty root
always exists" is now the LAW `root_mem`; Fable#3-C-8's "nonempty chains need not
exist" (L5 (ns): ∅ can be a leaf) remains respected — no law forces `some`-chains;
and the old falsifying computation still guards consumers (`mem some· := False`
fails `D4R_CYL` against D0c's nonempty fibers). Exhaustive-children semantics stays
kernel-(b) content behind the D4R_CYL / ClassFiberWelldef pins. §12 row 1. -/

/-- L6's (D4R-CYL), as the PINNED Prop [REV 3, finding 7]: S(η,⊤) = {f : η ∈ T_can(f)}
for every enumerated class. Note-PROVED (kernel (a)+(b) dual-verified-discharged +
Thm C(a)); its LEAN proof is EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus.
D15 consumes it as a named hypothesis — it is NOT a TreeModel field. -/
def D4R_CYL {n N m : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (S : Presented p F n N m pol P) (T : TreeModel p F n N m pol) : Prop :=
  ∀ (i : PrefIdx n pol P) (x : Box p m), x ∈ S.fiber i ↔ T.mem (some (reprOf i)) x

/-- [REV 5, reconciliation (7) — Codex#3 finding 7: now DISPLAYED and WIRED (D15's
`hwd` hypothesis), no longer ledger-only] Representative independence: one η-class,
one classifier locus, over ALL representatives and ALL jets (§C L4's semantic
content). Deferred to the wave-4/HC-2 tree corpus together with `D4R_CYL`; the two
jointly restore L6's every-η/every-presentation reading. -/
def ClassFiberWelldef (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Prop :=
  ∀ (H H' : History p F), H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H' →
    ∀ (J : JetSetup H n N m) (J' : JetSetup H' n N m),
      J.SHZ (topLocus p m) = J'.SHZ (topLocus p m)

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
  halt_iff : ∀ H x, T.mem (some H) x →
    (vdict H x ≠ none ↔ ∀ (ν : Node p F) (hν : ν.species ≠ ReadSpecies.root),
      ¬ T.child (some H) ν x)
  -- [REV 5] vdict stays on NONEMPTY chains; the ∅-root's own (ns) verdict is
  -- MovesT's corner (VP-2's root clause), documented not modeled.
  /-- the box level of each digit coordinate (the presented charts' first component;
  MovesT pins it to the jets' `coordOf`). -/
  levelOf : Fin m → ℕ
  /-- [REV 4, Codex#2 finding 10] the chart-range consistency of `levelOf` (the full
  chart tie `levelOf = (coordOf ·).1` per presented jet is MovesT's, at consumption). -/
  levelOf_lt : ∀ c : Fin m, levelOf c < N
  cap : V → ℕ
  /-- [REV 8, Codex#6 g.6 — the UNIFORM-cap teeth]: the per-class caps are
  uniformly bounded (`capBound`) and the presented level EXCEEDS the envelope
  (`hcapB` — detection is finite-level data, the box is deeper), with the chart
  level-surjective (`hlevel`). Consequence: coordinates at levels ≥ capBound
  exist and sit OUTSIDE the cap envelope, so `cellOf := id` FAILS `cell_local`
  and `Cell := Box` is no longer a free instance. CROSS-LEVEL uniformity (the
  same `cap` at every presented N — the addendum's "UNIFORM per-class detection
  cap") is MovesT's VP packaging across its Threshold jets; typed here at each
  level, documented not silently claimed. Constant-verdict degenerate instances
  remain type-legal and are excluded only by the SEMANTIC pin (kernel (c)). -/
  capBound : ℕ
  hcapU : ∀ v : V, cap v ≤ capBound
  hcapB : capBound < N
  hlevel : ∀ ℓ : ℕ, ℓ < N → ∃ c : Fin m, levelOf c = ℓ
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
  /-- [REV 6, Codex#4 f.5 — TYPED OPEN fields completing the claimed (c) surface]
  the ∅-ROOT's verdict ((ns) at depth 0 — e.g. non-cluster inputs halt with no
  eligible side; L5 (ns) + L2's leaf clause at the root node): -/
  rootVdict : Box p m → Option V
  rootHalt_iff : ∀ x : Box p m,
    (rootVdict x ≠ none ↔ ∀ ν : Node p F, ν.species = ReadSpecies.root →
      ¬ T.child none ν x)
  -- [REV 7, Fable#5 OBS-1: the root-species filter — children of ∅ are ROOT
  -- reads (mem_single + History.root_iff); non-root ν at none is junk.]
  /-- CELL-EXACT FACTORIZATION, typed and OPEN: `cellOf` = the full next-outcome
  digit datum of L5 (its semantics — polygon + digit tuples per kernel-(b) — is
  the HC-2/MovesT pin); τ/vdict FACTORS THROUGH IT ("a function of CELL data
  alone, never of f", VP-2) at every node including the root. NOT discharged
  here; nothing in MovesD consumes it. -/
  Cell : Type
  cellOf : Option (History p F) → Box p m → Cell
  /-- [REV 7, Codex#5 g.5 — the typed NON-DEGENERACY ties, still OPEN]: cells are
  FINITE data determined by the capped digit prefix (VP-2's "a function of CELL
  data alone, never of f", typed at the same envelope as vdict) — the tautological
  `Cell := Box, cellOf := id` instance now fails `cell_local` whenever the cap
  envelope is proper, and `hCellFin` forces genuinely quotiented cell data. The
  SEMANTIC pin (cellOf = L5's full polygon/digit next-outcome datum with its
  exhaustive value-cell partition — kernel (b)) remains MovesT/HC-2's, typed here,
  never discharged. -/
  hCellFin : Finite Cell
  cell_local : ∀ (o : Option (History p F)) (x x' : Box p m),
    (∀ c : Fin m, (∃ v : V, levelOf c < cap v) → x c = x' c) → cellOf o x = cellOf o x'
  vdict_cell : ∀ (H : History p F) (x x' : Box p m),
    cellOf (some H) x = cellOf (some H) x' → vdict H x = vdict H x'
  rootVdict_cell : ∀ (x x' : Box p m),
    cellOf none x = cellOf none x' → rootVdict x = rootVdict x'
  -- [REV 7: `rootVdict_cell` + `cell_local` give the root the same uniform
  -- locality the nonempty chains get from `vdict_local` — Codex#5 g.5's root-cap
  -- remark answered at the same typed-OPEN level.]

end
end LeanUrat.MovesD
```

## 4. Unit specs (48 units [REV 4: +W3, +D4R4_all; REV 5: +F3; REV 6: +SW1, +NPu]; all in `lean/LeanUrat/MovesD/`)

Common binders (elided): `{p} [Fact p.Prime] {F} [Field F] [Finite F] {n N m : ℕ}
{pol : CanonPolicy p F} {P : Shape n}` [REV 6: THE SUBTYPE — every shape-quantified
statement reads the note's universe; `↑P` coercions elided]; `S : Presented p F n N
m pol P`; `top := topLocus p m`. AUX = no note display; informal statement given.

### D0a — topLocus_laws · `D0a_topLocus.lean`  [REV 6, Codex#4 f.7: INLINED]
statement:
  `theorem topLocus_sol : ∀ x : Box p m, (topLocus p m).IsSolution x`
  `theorem topLocus_numPinned : (topLocus p m).numPinned = 0`
  `theorem topLocus_admissible (Σf : Locus p m) : AdmissibleZ Σf (topLocus p m)`
moves_ref: "Z = ⊤: no constraint, vol(⊤) = 1" (L6). deps: MovesC.Defs.
sketch: `pinned ≡ false`; unfold + simp. easy. hypothesis_fields: none.

### D0b — thmC_top · `D0b_thmCtop.lean`  [REV 6, Codex#4 f.7: INLINED]
statement:
  `theorem totalPins_top {H : History p F} (J : JetSetup H n N m) : totalPins J (topLocus p m) = (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar)`
  `theorem thmC_top {H : History p F} (J : JetSetup H n N m) : Nat.card (J.SHZ (topLocus p m)) * p ^ totalPins J (topLocus p m) = p ^ (n * N)`
moves_ref: "Each NONEMPTY summand is Theorem C(b) with Z = ⊤ on the lift-carrying
history η: μ(S(η,⊤)) = ∏ᵢ vol(E_fresh(νᵢ))" (D4R.1 proof). deps: C6_thmC_b, D0a.
sketch: `C6_thmC_b J top (topLocus_admissible _)`; `boxMass = p^(n*N)` by `J.hm`;
`numPinned = 0`. easy. hypothesis_fields: none (J a binder; existence =
`Presented.jet`, HC-2).

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
statement:
  `theorem encIdx_inj (hnorm : PresentNorm n pol P) : Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F P)`  [REV 6: + hnorm]
  `theorem encTargetP_empty (hP : (P : ShapePrefix).reads = []) : Nat.card (EncTargetP p F (P : ShapePrefix)) = 1`  [REV 8, Codex#6 c.3 — the ∅ dispatch: L11's encoding at P̂ = ∅ is the SINGLETON-TO-UNIT map (Pref(∅) = {∅}, target = the empty product, card 1 = C_∅); routed with F3/CD, so the note's C_∅ = 1 arithmetic is a THEOREM here, not a 0-bound]
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
hypothesis_fields: `hnorm : PresentNorm n pol P` (REV 7, Codex#5 g.4).

### D2a — L8_finite_C · `D2a_finite.lean`
statement:
  `instance : Finite (PrefIdx n pol P)` — L8, structural (a subtype of the finite `EtaData`).
  `theorem CD_eq (hnorm : PresentNorm n pol P) (hne : (P : ShapePrefix).reads ≠ []) : P.CD pol = Nat.card (PrefIdx n pol P)`
  [REV 6, Codex#4 f.2: `hnorm` on the standalone units — the counts are the note's
  C over normalized presentations, never a policy-void artifact.]
moves_ref: "L8: Pref(P̂) is FINITE … Hence #Pref(P̂) ≤ M(P̂)·∏_r Q_r^{d_r} < ∞".
deps: Defs. sketch: EtaData is a Pi of finite types; `if_neg`. easy.
hypothesis_fields: `hnorm : PresentNorm n pol P` (on `CD_eq` — the open dictionary
pin, HC-2; §2 ledger) [REV 7, Codex#5 g.4]; the `Finite` instance itself is
hypothesis-free (the η-class construction).

### F1 — the constructed enumeration · `F1_enum.lean`
statement:
  `theorem reprOf_mem (i : PrefIdx n pol P) : reprOf i ∈ PrefSet n pol P`
  `theorem etaData_reprOf (i : PrefIdx n pol P) : etaData P (reprOf i) = (i : EtaData F P)`
  `theorem card_classes (hnorm : PresentNorm n pol P) : Nat.card (PrefIdx n pol P) = Nat.card (etaData P '' PrefSet n pol P)`  [REV 6: + hnorm, Codex#4 f.2]
moves_ref: "Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts }, C_P̂(p) :=
#Pref(P̂)" — the enumeration is CONSTRUCTED, completeness/injectivity are definitional
theorems (final-audit finding 3: nothing assumed). [REV 5, reconciliation (2) —
Codex#3 finding 3, ANSWERED WHERE IT LOOKED: "classes ↔ η's" is NO LONGER prose —
it is the TYPED Prop `PresentNorm n pol P` (§3.2: totality from the POLICY-FREE
`PrefSetAny` + Galois uniqueness), carried by every family as the FIELD
`Presented.hnorm`. The truncated-normalization instance (empty PrefIdx, nonempty
PrefSetAny) VIOLATES it. Gate-checked at §0.6 — C_P̂*(2) = 3, C_P̂*(3) = 48,
mult ≡ 1.]
deps: Defs. sketch: `Exists.choose_spec` twice; `Nat.card` of a subtype of a set
coerced. easy. hypothesis_fields: `hnorm : PresentNorm n pol P` on `card_classes`
(REV 7, Codex#5 g.4); `reprOf_mem`/`etaData_reprOf` are hypothesis-free.

### W1′ — wellformed_of_wf · `W1_wellformed.lean`  [REV 6: shape-internal — no
member needed; the rev-5 member-transport version is SUPERSEDED]
statement: `theorem wellformed_of_wf (P : Shape n) : (P : ShapePrefix).Wellformed n`
moves_ref: "COARSE CHAIN … deg R_anch,r ≤ n always" (L11) — over the note's shape
universe BY TYPE, unconditional.
deps: Defs. sketch: induction down the reads on the CERTIFICATE P.2: root —
ℓ₀ ≤ s0+wSide ≤ n (root_box); step — ℓ_{r+1} ≤ s0'+wSide' ≤ μ_r (window) ≤ ℓ_r
(gmu, g ≥ 1). easy-medium.

### SW1 — ShapeWF_of_matches · `SW1_shapeWF.lean`  [REV 6 — the universe-loss
guard; REV 8, Codex#6 c.2 — MonicTie now DERIVED except its one genuinely
encoding-level clause]
statement: `theorem ShapeWF_of_matches {Q : ShapePrefix} {H : History p F} (hM : Q.MatchesHist H) (hcoh : HistoryCoherent H) (hbox : InBox n H) (hmt0 : ∀ h0 : 0 < Q.reads.length, ((Q.reads[0]'h0).monicTop = true ↔ (Q.reads[0]'h0).s0 + (Q.reads[0]'h0).wSide = n)) : ShapeWF n Q`
moves_ref: (the L3 dictionary: every note-η's shape is dictionary-image — so the
subtype loses NOTHING of the note's universe). THE MONICTIE DERIVATION [REV 8]:
monicTop → r = 0 is DERIVED (`hmonicRoot` + `root_iff` via Matches), whence
non-root reads have monicTop = false; the RESIDUE — the root read's
monicTop ↔ (s0 + wSide = n) — is NOT derivable from Matches (its forcing clause
`monicTop → sideDigit ℓ = 1` speaks of the digit VALUE, not the slot POSITION,
and a full-span root can match a monicTop = false record): it is a property of
the shape's ENCODING, pinned at the gate by "slot 3 = the monic lead, digit 1"
(§D4-R.6). Kept as the WEAKEST SUFFICIENT hypothesis `hmt0`, named **ENC-MONIC**
(§2 ledger: encoding-correctness duty, owner = the D4-n3 gate + the menu wave —
each catalogued shape's monicTop bit is checked against its displayed side).
deps: E4, E5. sketch: transport each certificate clause from the matched history:
species_iff from `History.root_iff`; window/dchain from `HistoryCoherent`; gmu from
E5 (hOrd) + E4; edvd from `Node.hEdvd`; root_box from `InBox`; [REV 7] gamTie from
coherence's γ-tie clause + Matches (e/h/s0/wSide/ustar/gam) + D6a (strS); anchorTie
from `Node.hAnchor` + `hbezCanon`-uniqueness against `bezT` (the canonical window
representative is unique — small in-unit lemma). medium.

### W2 — Mfac_le · `W2_MfacLe.lean`  [REV 6, Codex#4 f.3: UNCONDITIONAL over the
subtype — the "smuggled" rider is GONE with the domain ruling]
statement: `theorem Mfac_le (P : Shape n) : (P : ShapePrefix).Mfac ≤ n ^ (P : ShapePrefix).reads.length`
moves_ref: "M(P̂) := ∏_r m̄_r ≤ ∏_r ⌊n/(g_rμ_r)⌋ ≤ n^{|P̂|} (m̄_r as above … coarse
chain displayed)" — for every shape-prefix of the degree-n classifier, verbatim.
deps: W1′. sketch: m̄_r ≤ ℓ_r ≤ n (W1′); List.prod ≤ pow. easy.
hypothesis_fields: NONE.

### W3 — D4R2'_full · `W3_coarseBound.lean`  [REV 6, Codex#4 f.3: BOTH displayed
bounds, over the subtype, no case analysis needed]
statement:
  `theorem D4R2'_full (hnorm : PresentNorm n pol P) : P.CD pol ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W ∧ (P : ShapePrefix).Mfac ≤ n ^ (P : ShapePrefix).reads.length`
  [REV 8: on `Shape.CD` — the ∅ case is 1 ≤ 1 ∧ 1 ≤ 1, the note's own C_∅
  arithmetic through the F3/CD bridge.]
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, M(P̂) ≤ n^{|P̂|} p-FREE (L11)" — the display
PAIR, verbatim, unconditional on the note's universe (`Shape n` + hnorm).
deps: D3a, W2. sketch: ⟨D4R2' hnorm, Mfac_le P⟩ — both components already
unconditional over the subtype. easy. hypothesis_fields: `hnorm` (Codex#4 f.2).

### D1c — encTargetP_card · `D1c_encCard.lean` (AUX)
statement: `theorem encTargetP_card (hp : 2 ≤ p) : Nat.card (EncTargetP p F P) ≤ P.Mfac * p ^ P.W`
moves_ref: (L11's codomain count ∏_r Q_r^{d_r}·m̄_r). deps: E2. sketch: Pi/product
cards; (card pool)^{d} ≤ (p^w)^d; regroup = p^W·Mfac. medium.

### D3a — D4R2' · `D3a_poolBound.lean`
statement: `theorem D4R2' (hnorm : PresentNorm n pol P) : P.CD pol ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W`
  [REV 8, Codex#6 c.3 — stated on `Shape.CD` (the F3/CD bridge): at P̂ = ∅ this IS
  the note's C_∅ = 1 ≤ Mfac(∅)·p^{W(∅)} = 1·p⁰ = 1 (empty product/sum); at
  nonempty shapes CD = Nat.card PrefIdx (CD_eq) — the former statement exactly.]
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}" (D4R.2′ display; the M ≤ n^{|P̂|} clause is W2).
deps: E9, D1c, D2a (CD_eq), F3. sketch: case split on `reads = []`: ∅ — CD = 1,
Mfac·p^W = 1 (empty product, W = 0); nonempty — CD_eq + `Nat.card_le_card_of_injective encIdx encIdx_inj` + D1c.
easy. hypothesis_fields: `hnorm : PresentNorm n pol P` (the open dictionary pin,
HC-2 — REV 7, Codex#5 g.4); the INJECTION itself is proved, nothing else assumed.

### D3b — D4R2_cor · `D3b_corD4R2.lean`
statement: `theorem D4R2_cor (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : Nat.card S.event * p ^ (P.A' n) ≤ P.Mfac * p ^ (P.W + n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} ≤ M(P̂)·p^{W(P̂)−A(P̂)} = M(P̂)·p^{−A_net(P̂)},
A_net(P̂) := A(P̂) − W(P̂)" (Corollary D4R.2), division-free (`Anet` records the named
exponent). deps: D12, D3a, D2a. sketch: chain D4R1_EV with D4R2' (via CD_eq);
pow_add. easy.

### THE L9 CHAIN (D4a–D9, L9s) — substance unchanged from rev 2 (no final-audit
finding hit it except D10's quantifier); one lemma per unit; specs abbreviated.

[REV 6, Codex#4 f.7: every "as rev 2" abbreviation below is INLINED in full;
`Q := (P : ShapePrefix)` inside statements for readability.]

### D4a — chart_bij · `D4a_chartBij.lean` (AUX)
informal: a JetSetup's ≺-sorted chart is a bijection onto the N×n grid.
statement: `theorem chart_bij {H : History p F} (J : JetSetup H n N m) : Function.Injective J.coordOf ∧ ∀ c ∈ Finset.range N ×ˢ Finset.range n, ∃ j : Fin m, J.coordOf j = c`
deps: MovesC.Defs. sketch: injectivity from `coordOf_sorted` + `CoordPrec`
irreflexivity; surjectivity from injective-into-a-grid-of-card-m (`J.hm`,
pigeonhole). medium.

### D4b — chart_count · `D4b_chartCount.lean` (AUX)
informal: pulled-back predicate counts over `Fin m` = grid filter counts.
statement: `theorem chart_count {H : History p F} (J : JetSetup H n N m) (φ : Coord → Prop) [DecidablePred φ] : Nat.card {c : Fin m // φ (J.coordOf c)} = ((Finset.range N ×ˢ Finset.range n).filter (fun c => φ c)).card`
deps: D4a. sketch: `Nat.card_congr` along D4a's bijection; `Finset.card_filter`
bridging. medium.

### D5a — Dwidth_pos · `D5a_dwidthPos.lean` (AUX)
informal: every read of a coherent history has positive frame width.
statement: `theorem Dwidth_pos {H : History p F} (hcoh : HistoryCoherent H) (r : ℕ) (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).Dwidth`
deps: MovesC.Defs. sketch: induction on r — root `deg Φ₀ = 1` + `hDwidth`; step
width chain `D_{r+1} = e·g·D_r`, e, g ≥ 1. medium.

### D6a — strFrame_shape · `D6a_strShape.lean`
statement: `theorem strFrame_shape {H : History p F} (hP : Q.MatchesHist H) : ∀ i, H.strFrame i = Q.strS i`
moves_ref: (L9's "SHAPE data" — STR_i = ∏_{m<i} e_m). deps: Defs.
sketch: List.take/map congruence from Matches' e-clause. easy.

### D5b — line_shape · `D5b_lineShape.lean`
statement: `theorem line_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : Q.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) : (H.nodes[r]'hr).line = Q.lineS r`
moves_ref: "each line is the slope −h_r/e_r line through (j*_r, u*_r), pinned only
WITH its height … A is a function of P̂ only because u*_r ∈ P̂" (L9 rev 9 — u*
enters HERE, through the intercept). deps: D5a, D6a. sketch: `Line` ext; slope from
coherence's slope law (e·STR·D ≠ 0 via he/D5a/strS ≥ 1); intercept solved from
`hLineU` at the matched right endpoint. medium.

### D6b — kappaH_shape · `D6b_kappaShape.lean`
statement: `theorem kappaH_shape {H : History p F} (hP : Q.MatchesHist H) : ∀ r, H.kappaH r = Q.kappaS r`
moves_ref: (L9 — κ_r = h_r/(e_r·STR_r) is shape data). deps: D6a.
sketch: getElem?-elim; Matches e/h + D6a. easy.

### D6c — innerslot_shape · `D6c_innerslotShape.lean`
statement: `theorem innerslot_shape {H : History p F} (hP : Q.MatchesHist H) : ∀ r b, H.innerslotH r b = Q.innerslotS r b`
moves_ref: (L9 — inner slots from the retained width chain). deps: Defs.
sketch: getElem?-elim; Matches e/g/Dwidth. easy.

### D6d — htH_shape · `D6d_htShape.lean`
statement: `theorem htH_shape {H : History p F} (hP : Q.MatchesHist H) : ∀ i c, H.htH i c = Q.htS i c`
moves_ref: "each alphabet cardinality a power of p determined by the history's
SHAPE data (§C C.3, verbatim)" (L9). deps: D6b, D6c. sketch: Finset.sum congruence
of the two K1-chain formulas. easy.

### D6e — prevRim_shape · `D6e_prevRimShape.lean`
statement: `theorem prevRim_shape {H : History p F} (hP : Q.MatchesHist H) : ∀ i, H.prevRim n i = Q.prevRimS n i`
moves_ref: (L9 — the rim thresholds μ_{i−1}·D_i are shape data). deps: Defs.
sketch: case split on i; getElem?-elim; Matches μ/e/g/Dwidth. easy.

### D7a — staircase_shape · `D7a_staircaseShape.lean`
statement: `theorem staircase_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : Q.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (hr' : r < Q.reads.length) : ∀ b, (H.nodes[r]'hr).staircase b = (Q.reads[r]'hr').staircaseS (Q.lineS r) b`
moves_ref: (L9 — the (ZC-a) staircases: line + μ + widths, all retained).
deps: D5b. sketch: unfold; rewrite line by D5b, μ/childWidth by Matches. easy.

### D7b — floorH_shape · `D7b_floorShape.lean`
statement: `theorem floorH_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : Q.MatchesHist H) : ∀ i b, H.floorH i b = Q.floorS i b`
moves_ref: "the fresh inventory's strip depths run between the recorded old/new
lines, each pinned only WITH its height" (L9 rev 9). deps: D7a.
sketch: fold congruence over the first-i staircases (List.take/map/range). medium.

### D7c — slotVal_shape · `D7c_slotValShape.lean`
statement: `theorem slotVal_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : Q.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (hr' : r < Q.reads.length) : ∀ b, (H.nodes[r]'hr).slotVal ((H.nodes[r]'hr).fineSlot b) = (Q.lineS r).at ((b / (Q.reads[r]'hr').Dwidth) * (Q.reads[r]'hr').Dwidth)`
moves_ref: (L9 — the band's fine-slot upper edge `new(j) = line.at(j·Dwidth)`,
MovesC ROUND 6's boundary). deps: D5b. sketch: unfold slotVal/fineSlot; D5b +
Matches Dwidth. easy.

### D8 — band_shape · `D8_bandShape.lean`
statement: `theorem band_shape {H : History p F} {J : JetSetup H n N m} (hP : Q.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (c : Fin m) : (inFreshBand H n J.coordOf r (H.nodes[r]'hr) c ↔ Q.bandS n r (J.coordOf c))`
moves_ref: (L9's per-read exponent — `inFreshBand` is §C C.1(ii)'s inventory; all
three conjuncts shape formulas). deps: D6d, D6e, D7b, D7c (coherence via
`J.coherent`). sketch: conjunct-wise transfer. medium.
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

### NPu — the exact-threshold lemmas · `NPu_threshold.lean`  [REV 6, Codex#4 f.4]
statement:
  `theorem NP_pos : 1 ≤ P.NP pol` (both branches)
  `theorem NP_le_Nshape : P.NP pol ≤ (P : ShapePrefix).Nshape` (sup < Nshape; 1 ≤ Nshape)
  `theorem NP_stab [Nonempty (PrefIdx n pol P)] : ∀ N, P.NP pol ≤ N → (P : ShapePrefix).A n N = (P : ShapePrefix).A' n`
  [REV 7: NP_stab is stated on the INHABITED branch (NP = NPband); the empty
  branch never consumes stability — D4R4_all's proof case-splits: empty ⟹ both
  sides 0 at EVERY N ≥ 1 = L12's empty clause at full strength.]
moves_ref: L12: "N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅, N(P̂) := 1 if
Pref(P̂) = ∅ … N(P̂) is finite" — NP is the DEFINED formula (§3.3; the max collapses
by shape-constancy; the empty convention falls out of the sup). `hstab` is now
DERIVED, not assumed (the rev-5 field deleted).
deps: Defs, L9s. sketch: NP_stab — every band coordinate has level ≤ NP − 1 (the
filter's sup), so the level-range extension beyond NP adds nothing; combine with
L9s at Nshape via NP_le_Nshape. medium.

### THE MASS LAWS (final-audit finding 5: the uniform quantifier ∀ N ≥ N(P̂))

### D10 — D4R1_SUM · `D10_sumLaw.lean`
statement: `theorem D4R1_SUM (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : (∑ᶠ i : PrefIdx n pol P, Nat.card (S.fiber i)) * p ^ (P.A' n) = Nat.card (PrefIdx n pol P) * p ^ (n * N)`
moves_ref: "Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (D4R.1-SUM)" ≡ "N(P̂) is
finite, and for EVERY N ≥ N(P̂): Σ_η #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)}
(D4R.4-SUM)". THE QUANTIFIER [REV 5]: N and S universally bound at every
level where the ledger has stabilized — `hA : P.A n N = P.A' n`, DISCHARGED by L9s
whenever `Nshape ≤ N` and by `Threshold.hstab` from the note's own NP on (so
D4R4_all covers [N(P̂), Nshape) too); C and A′ are N-FREE, so all levels share their
constants — D4R.4's content. The uniform-threshold packaging is D4R4_all.
deps: D0b, D9, L9s, D2a (Fintype from Finite for ∑ᶠ). sketch: per summand
thmC_top + D9 + A_stable; sum the constant. NO disjointness consumed. medium.
hypothesis_fields: `S.jet` only.

### D11a — mult_sum · `D11a_multSum.lean` — as rev 2 on the new types:
`∑ x, S.mult x = ∑ᶠ i, Nat.card (S.fiber i)` (double counting). medium.
### D11b — event_iff_mult · `D11b_eventMult.lean` — `x ∈ S.event ↔ 1 ≤ S.mult x`.
easy.

### D12 — D4R1_EV · `D12_evBound.lean`
statement: `theorem D4R1_EV (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : Nat.card S.event * p ^ (P.A' n) ≤ Nat.card (PrefIdx n pol P) * p ^ (n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡ "(D4R.4-EV) …
the union bound within the level-N box", at every N ≥ N(P̂) (same quantifier note as
D10). deps: D10, D11a, D11b. sketch: card event = #{mult ≥ 1} ≤ Σ mult. medium.

### D13 — D4R1_EV_iff · `D13_evIff.lean`
statement: `theorem D4R1_EV_iff (hne : P.reads ≠ []) (N : ℕ) (hA : P.A n N = P.A' n) (S : Presented p F n N m pol P) : (Nat.card S.event * p ^ (P.A' n) = Nat.card (PrefIdx n pol P) * p ^ (n * N)) ↔ (∀ x ∈ S.event, S.mult x = 1)`
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … count-equality ⟺ …
mult_P̂ ≡ 1 POINTWISE on the event — the finite-level statement carries no
measure-zero exception" (D4R.1/L12). deps: D10, D11a, D11b. sketch: cancel p^{A′}
(p ≥ 2); Finset double counting, pointwise. medium-hard.

[REV 4, Codex#2 finding 6, second half — CONCEDED: D10/D12/D13/D3b now carry
`hne : P.reads ≠ []`, so with `CD_eq` their constant IS the corpus C (`P.CD`) on
their whole domain, and the P̂ = ∅ display is carried ONLY by D14a — the note's own
two-mechanism proof ("The EMPTY prefix η = ∅ … is dispatched FIRST, separately from
Theorem C(b)"). First half PUSHED BACK — §11 row 6.]

### D4R4_all — the law at the NOTE's threshold · `D4R4all_wrapper.lean`
[REV 5, reconciliation (5) — Codex#3 finding 4; restated on `Threshold`]
statement:
  `theorem D4R4_all (hne : (P : ShapePrefix).reads ≠ []) (T : Threshold p F n pol P) : ∀ N, P.NP pol ≤ N → (((∑ᶠ i, Nat.card ((T.jets N ‹_›).fiber i)) * p ^ ((P : ShapePrefix).A' n) = P.CD pol * p ^ (n * N)) ∧ (Nat.card (T.jets N ‹_›).event * p ^ ((P : ShapePrefix).A' n) ≤ P.CD pol * p ^ (n * N)))`
  `theorem TW_threshold_witness (hex : ∀ N, P.NP pol ≤ N → Nonempty (Presented p F n N (n*N) pol P)) : Nonempty (Threshold p F n pol P)`  [REV 6: hex restated AT NP — PRESENT-EXIST's ledger row updated to match; no dropped range]
moves_ref: L12 QUOTED VERBATIM: "N(P̂) is finite, and for EVERY N ≥ N(P̂):
Σ_{η ∈ Pref(P̂)} #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN − A(P̂)} (D4R.4-SUM) …
#{f mod p^N ∈ S(P̂,⊤)} ≤ C_P̂(p)·p^{nN − A(P̂)} (D4R.4-EV)". MATCH: ∀ N ≥ NP (the
threshold DATA with its L12-visible properties), the SUM equality ∧ the EV bound,
constants CD and A′ N-free. The note quantifies over LEVELS only (its counts are
intrinsic — no ∃-over-presentations remains in the conclusion; presentation-
intrinsic-ness = ClassFiberWelldef, declared). `TW` [REV 7 — the stale rev-5
construction line PURGED, Fable#5 g.2]: `Threshold` has had NO NP/hstab fields
since rev 6 — TW builds the sole field `jets` from `hex` by choice on L12's exact
piecewise range; PRESENT-EXIST (§2) is consumed HERE and only here.
deps: D10, D12, D2a (CD_eq), NPu; NP_stab bridges A n N to A′ on the inhabited
branch; the empty branch is the 0 = 0 case split (L12's empty clause, every N ≥ 1).
sketch: apply D10/D12 at T.jets N with hA := NP_stab N. easy-medium.
hypothesis_fields: `T : Threshold` (sole field: jets — the L12 presentations,
HC-2); `hex` (PRESENT-EXIST, restated at NP) only in TW. Non-vacuity: T.jets carry
`hnorm`, so truncated/junk-policy instantiations violate the field.

### F3 — the ∅-representation BRIDGE · `F3_emptyBridge.lean`
[REV 5, reconciliation (3) — Codex#3 finding 5 ∧ Fable#3 C-6: the deviation is now
a THEOREM on the Option-level object, not a prose declaration]
statement:
  `theorem PrefOpt_empty (hP : P.reads = []) : PrefOpt n pol P = {Option.none}`
  `theorem PrefOpt_nonempty (hne : P.reads ≠ []) : PrefOpt n pol P = Option.some '' PrefSet n pol P`
  `theorem CD_correspondence : P.CD pol = Nat.card (etaDataO P '' PrefOpt n pol P)`
moves_ref: "Pref(∅) = {∅}" (L12/D4R.1's dispatch) — now LITERAL: the Option-level
Pref of the empty shape IS the singleton of the empty chain, and the corpus C (`CD`)
equals the class count of `PrefOpt` UNIFORMLY (both branches machine-checked: ∅ —
image = {none}, card 1; nonempty — etaDataO ∘ some classes = the PrefIdx classes).
The consumed arithmetic (D14a's law, D10's constant via CD_eq) is thereby EQUIVALENT
to the note's ontology by theorem.
deps: Defs, D2a, F1. sketch: set ext + match unfolding; `Option.some` injective for
the card transport. easy.

### D14a — emptyShape_law · `D14a_emptyShape.lean` (final-audit finding 6)
[REV 5: `Pref_empty_shape`'s History-level display now sits UNDER the F3 bridge —
the Option-level `PrefOpt_empty` carries the note's "Pref(∅) = {∅}" literally; this
unit keeps the History-level honesty display + the mass law.]
statement:
  `theorem Pref_empty_shape (hP : P.reads = []) : PrefSet n pol P = ∅ ∧ P.CD pol = 1`
  `theorem A'_nil (hP : P.reads = []) : ∀ n, P.A' n = 0`
  `theorem emptyShape_law (hm : m = n * N) (hN : 1 ≤ N) (hP : P.reads = []) : Nat.card (emptyFiber p m) * p ^ (P.A' n) = P.CD pol * p ^ (n * N)`
moves_ref: "Pref(∅) = {∅} … its fiber is the FULL BOX, level-N count p^{nN} =
C_∅·p^{nN − A(∅)} (C_∅ = 1, A(∅) = 0), by L5's normalized full-box display — NOT by
Theorem C(b)". CONNECTED IN CORPUS VOCABULARY: `emptyFiber` IS the defined S(∅,⊤),
`P.CD` IS the corpus C (its `if` branch is the note's own definition-level dispatch
Pref(∅) = {∅} — the History type has no empty chain, which is WHY CD carries the
dispatch; `Pref_empty_shape` displays that the History-level set is empty, so 1 is
the η = ∅ class and nothing else), `P.A'` IS the corpus A. deps: Defs. sketch:
if_pos; card univ = p^m; empty sum. easy. hypothesis_fields: `hm`, `hN` explicit.

### D14b — D4R4_emptyPref · `D14b_emptyPref.lean`
statement: `theorem D4R4_emptyPref (hne : P.reads ≠ []) (hemp : IsEmpty (PrefIdx n pol P)) (hN : 1 ≤ N) (hm : m = n * N) (S : Presented p F n N m pol P) : S.event = ∅ ∧ P.CD pol = 0 ∧ Nat.card S.event * p ^ (P.A' n) = P.CD pol * p ^ (n * N)`
moves_ref: "If Pref(P̂) = ∅ then S(P̂,⊤) = … = ∅ and C_P̂(p) = 0, so for EVERY N ≥ 1:
#{f mod p^N ∈ ∅} = 0 = C_P̂(p)·p^{nN − A(P̂)}" (L12). deps: Defs, D2a. sketch: empty
iUnion over an empty index; CD_eq + Nat.card of an empty type. easy.
hypothesis_fields: `hN`, `hm` explicit (L12's N(P̂) := 1 convention).

### THE TREE UNITS (final-audit finding 7 + gap 8)

### T1a — tree_prefix_closed · `T1a_prefixClosed.lean`
statement: `theorem tree_prefix_closed (T : TreeModel p F n N m pol) : ∀ H H' x, H.IsPrefixOf H' → T.mem (some H') x → T.mem (some H) x` — plus the base `∀ H x, T.mem (some H) x → T.mem none x` (immediate from `root_mem`). [REV 5: Option carrier.]
moves_ref: "T_can(f) is prefix-closed — a tree" (L2) — now a THEOREM from the
generation laws, not a field. deps: Defs. sketch: downward induction along
`mem_snoc` (peel the last node; a prefix of a snoc is the history or a prefix of it).
medium.

### D15 — tree_bridge · `D15_tree.lean`
statement:
  `theorem mult_eq_tree (S) (T : TreeModel p F n N m pol) (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P) (x : Box p m) : S.mult x = Nat.card {i : PrefIdx n pol P // T.mem (some (reprOf i)) x}`
  `theorem event_iff_tree (S) (T) (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P) (x : Box p m) : x ∈ S.event ↔ ∃ i : PrefIdx n pol P, T.mem (some (reprOf i)) x`
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
4. The EV criterion pointwise-on-the-event; the level quantifier via
   `hA : P.A n N = P.A' n` (discharged by L9s at N ≥ Nshape, by `Threshold.hstab`
   at N ≥ NP) and the note-threshold form at D4R4_all — present on
   D10/D12/D13 with N-free C and A′.
5. `ShapePrefix.A`/`A'`/`CD` are DEFINITIONS; `CD`'s if-branch is the note's own
   Pref(∅) = {∅} dispatch — reject any unit weakening it to a hypothesis.
6. The encoding chain E1–E9 must consume ONLY MovesC node Props + Matches — any new
   assumption there is a statement-fence breach.
7. `Presented.{jet, hnorm}` are the ONLY assumed structure fields in the corpus
   (REV 7, Fable#5 OBS-3; hnorm = the typed PresentNorm pin, §2).

## 8. MANIFEST stub

corpus: MovesD · source: §D4-R rev 9 (DUAL-ACCEPTED 2026-07-27) · consumes: MovesC ·
units: 48 (D0a–c; E1–E9; D1c; D2a; F1; F3; SW1; W1′–W3; NPu; D3a–b; D4a–b; D5a–b;
D6a–e; D7a–c; D8; D9; L9s; D10; D4R4_all(+TW); D11a–b; D12; D13; D14a–b; T1a; D15;
13 AUX) · domain: `Shape n` (the subtype — REV 6 ruling) · defs: 1 file ·
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

Unit count at rev 4: 45; at rev 5: 46 (+F3). AUX still 13. Gate acceptance test
(per the triage protocol): §0.6 — C_P̂*(2) = 3 ✓, C_P̂*(3) = 48 ✓, mult_P̂* ≡ 1 ✓,
Nshape(P̂*) = 5 ✓, A(P̂*) = 11 ✓, W = 7 ✓, M = 1 ✓.

## 12. REV 5 reconciliation table (Fable#3 ACCEPT 0/0 vs Codex FINAL#3 REJECT 7/1 — orchestrator-adjudicated designs)

| # | dispute (who held what) | the reconciling design (both readings satisfied) |
|---|---|---|
| 1 | TreeModel root: Codex f.6 "the empty root ALWAYS exists" (L2: "its root is the empty chain ∅") vs Fable C-8 upheld "root-inhabitation on nonempty History would be unfaithful (L5 (ns): ∅ can be a leaf)" — BOTH RIGHT | node carrier = `Option (History)`: `root_mem : ∀ x, mem none x` is a LAW (Codex's reading); NO law forces `some`-chains (Fable's (ns) computation stands); `mem_single`/`mem_snoc`/`D4R_CYL`/T1a/D15 requantified on `some`; VerdictModel stays on nonempty chains (∅-verdict = MovesT's VP-2 root corner, documented) |
| 2 | PresentNorm: Codex f.3 "prose pin, PrefIdx may truncate Pref" vs Fable OBS-1 (same recommendation, non-blocking) | `PresentNorm n pol P` TYPED (§3.2): totality from the POLICY-FREE `PrefSetAny` + Galois uniqueness; carried as the FIELD `Presented.hnorm` — the empty-PrefIdx-vs-nonempty-Pref instance VIOLATES it, and every mass unit consumes it through S |
| 3 | ∅ representation: Codex f.5 "Pref_empty_shape states the wrong set" vs Fable C-6 upheld "the History type has no empty chain; CD's if-branch IS the note's dispatch" | the deviation is now a THEOREM (F3, on the new Option-level `PrefOpt`): `PrefOpt_empty : PrefOpt = {none}` = the note's "Pref(∅) = {∅}" LITERALLY; `CD_correspondence` machine-checks the consumed arithmetic equivalence; D14a keeps the History-level honesty display |
| 4 | monicTop: Codex f.1 "Boolean unfaithful to L3's slot sets; junk root shapes shrink W" vs Fable C-1 upheld (L11 reconstruction + at most one off-box slot + gate d-counts) | Boolean + root guard STAND (Fable), PLUS the definitional tie `ShapePrefix.MonicTie` (monicTop ⟺ root ∧ s0+wSide = n) as a PrefSet clause — faking/hiding monicTop voids the shape's PrefSet (Codex's instance unbuildable on C-carrying territory) |
| 5 | D4R4_all: Codex f.4 "starts at Nshape not N(P̂); ∃-S conclusion; hex trivially satisfiable" vs Fable §5 PASS (documented boundary, note licenses the shape bound) | `Threshold` structure = the note's NP with its L12-VISIBLE properties (`hstab`, `jets`); D4R4_all restated ∀ N ≥ NP with NO ∃-over-presentations in the conclusion (L12 quantifies over LEVELS only — quoted verbatim in the spec); D10/D12/D13/D3b generalized to `hA : P.A n N = P.A' n` (covers [N(P̂), Nshape)); `TW_threshold_witness`: Nshape = the constructive witness under PRESENT-EXIST; hnorm kills the trivial-hex instance |
| 6 | CanonPolicy: Codex f.2 "junk pol can void the corpus; POL-PIN not a hypothesis" vs Fable C-4 upheld (L1 verbatim; ∀-pol sound; DAG ownership) | parameter design STANDS (Fable) + the note-supported adequacy is now INSIDE `PresentNorm`'s totality clause (source set = policy-FREE `PrefSetAny`): a history-voiding policy violates `Presented.hnorm` — vacuity killed WITHOUT pinning offset-P (POL-PIN stays HC-1) |
| 7 | ClassFiberWelldef: Codex f.7 "not shown, not a hypothesis" | displayed as a Defs Prop (§3.4) and WIRED: D15's two theorems carry `hwd : ClassFiberWelldef …` explicitly |
| 8 | VerdictModel cells: Codex f.8 (GAP) "no digit-cell factorization" — acknowledged by both as the declared MovesT boundary | stays the honest deferral: `vdict_local`/`levelOf_lt`/`cap_law` are the interface-expressible shadow; the cell-exact tie is VP-2/MovesT's, stated in the structure docstring — no silent claim |

Gate acceptance (unchanged from §0.6, re-affirmed by BOTH rev-4 verdicts'
independent recomputations): C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1, Nshape = 5,
A = 11, W = 7, M = 1.

## 13. REV 6 table (the domain-subtype ruling; Fable#4 ACCEPT 0/0 vs Codex FINAL#4 REJECT 4/3)

| # | Codex#4 finding | REV-6 repair (the ruling) |
|---|---|---|
| 1 | `MonicTie` as a PrefSet clause = the prohibited degenerate-instance escape (malformed shapes should not BE shapes) | AGREED — the ruling adopts Codex's own words: `Shape n := {P // ShapeWF n P}` with `MonicTie` a ShapeWF COMPONENT; the malformed encoding is NOT A SHAPE; the PrefSet clause is deleted (moved into the type, not weakened); SW1 proves the note's shapes all carry the certificate (no universe loss); the gate shape's certificate checked clause-by-clause (§0.6 addendum) |
| 2 | pol-standalone units (D2a, F1, E9, D3a, W3) trivialize on policy-voided domains | all five gain `hnorm : PresentNorm n pol P` — normalized presentations, the note's domain; with hnorm, PrefIdx-emptiness ⟺ the note's Pref = ∅, never a policy artifact |
| 3 | W2's `Wellformed` rider smuggled; W3 bounds C but not M | over the subtype BOTH are unconditional: W1′ proves `Wellformed` from the CERTIFICATE (no member needed), W2 drops the rider, W3 = `D4R2'_full` states the display PAIR (C ≤ M·p^W ∧ M ≤ n^{|P̂|}) verbatim |
| 4 | `Threshold.NP` not definitionally L12's N(P̂); range [N(P̂), NP) dropped | `ShapePrefix.NP` DEFINED = 1 + the largest constrained (band) level — L12's formula with the max-over-η collapsed by shape-constancy (the note's own "identical for every η"); the empty convention NP = 1 falls out of the sup; `hstab`/`NP ≤ Nshape` DERIVED (NPu); Threshold's sole field = jets at every N ≥ NP; D4R4_all/TW/PRESENT-EXIST restated at NP — exact range. Gate: NP(P̂*) = 1+4 = 5 = the note's derivation |
| 5 | VerdictModel missing root-(ns) verdict + cell factorization | TYPED OPEN fields added: `rootVdict`/`rootHalt_iff` ((ns) at the ∅-root) and `Cell`/`cellOf`/`vdict_cell`/`rootVdict_cell` (τ factors through L5's digit cell — VP-2, typed not discharged) |
| 6 | Defs skeleton not order-correct Lean | §3.0 NORMATIVE declaration order (file order is the spec); EtaGalEq after EtaData, PresentNorm after PrefIdx, A/A′/NP before Threshold; Threshold no longer has an hstab field at all |
| 7 | "as rev 2" unit specs unauditable | ALL inlined in full: D0a, D0b, D4a, D4b, D5a, D6a–e, D7a–c (+ D5b, D8 restated) — the blueprint is self-contained |

Unit count at rev 6: 48 (+SW1, +NPu). Gate acceptance UNCHANGED over the subtype
(§0.6 addendum): P̂* ∈ Shape 3 clause-by-clause; C_P̂*(2) = 3, C_P̂*(3) = 48,
mult ≡ 1, NP = 5 (= the note's N(P̂*), by the DEFINED formula), Nshape = 5, A = 11,
W = 7, M = 1.

## 14. REV 7 table (certificate completion; Codex FINAL#5 2/3 ∪ Fable#5 0/2 — both confirm the architecture)

| # | finding (who) | REV-7 repair |
|---|---|---|
| 1 | ShapeWF incomplete — h = 0 adversary passes; gcd/species/lattice clauses missing (Codex c.1; not in Fable's adversary set, STANDS) | `ShapeRead` gains `hh`/`hcop` (Node's "genuine polygon side: e, h ≥ 1, coprime (lowest terms)") + `hspecInc`/`hspecRec` (§C.0 species laws); `ShapeWF` gains `gamTie` (the γ-tie at the chain stretch — L3 rev 9's derived γ, coherence's clause verbatim) + `anchorTie` (Node.hAnchor at `bezT`, THE canonical Bézout coefficient, new def). ADVERSARIES re-run (§3.1): Fable's three ✗ + h = 0 ✗ (unbuildable record) + gcd(2,4) ✗; positives P̂* ∈ Shape 3 and P̂₀ ∈ Shape 4 re-checked including the new clauses (γ₀ = 3, γ₁ = 4 = the seal's; a = s0 at e = 1). Gate numbers untouched (new clauses constrain shape fields only) |
| 2 | NP not L12's piecewise threshold — Pref-empty shapes with nonempty band get NP > 1 (Codex c.2; half-echoed by Fable OBS-2) | L12 QUOTED ("N(P̂) := 1 if Pref(P̂) = ∅" — unconditional on the band): `Shape.NP pol := if Nonempty (PrefIdx …) then NPband else 1` — PIECEWISE, pol-dependent exactly as L12's own Pref-conditional; NPu's NP_stab scoped to the inhabited branch; D4R4_all case-splits (empty: 0 = 0 at every N ≥ 1 — L12's empty clause at full strength); the max-η identification SOFTENED to its corpus-consumed content (NP_stab + range), documented not claimed |
| 3 | binding sweep — §3.2/§3.4 still bound `P : ShapePrefix` into subtype-taking defs (Codex g.3 = Fable g.1) | ALL re-bound to `Shape n`: PrefIdx, PresentNorm, reprOf, `Shape.CD` (renamed from ShapePrefix.CD), PrefOpt, Presented, D4R_CYL, ClassFiberWelldef, the fiber/event/mult section variables; raw-type utilities (EtaData/etaData/EtaGalEq/etaDataO/NPband) stay on ShapePrefix and are consumed through explicit coercions; §3.0 order updated (`Shape.NP` in group (4) after PrefIdx) |
| 4 | stale rev-5 TW construction line (Fable g.2) | purged; TW's text now matches the rev-6+ Threshold (sole field `jets`, built from hex by choice on the exact piecewise range) |
| 5 | hypothesis_fields omit `hnorm` where statements use it (Codex g.4) | D2a (CD_eq), F1 (card_classes), E9, D3a all list `hnorm : PresentNorm n pol P` as the open dictionary pin (HC-2); W3 already did |
| 6 | VerdictModel's Cell/cellOf tautologically satisfiable; root lacks cap/locality (Codex g.5) | typed non-degeneracy OPEN ties: `hCellFin` + `cell_local` (cells = finite data of the capped digit prefix — kills `cellOf := id` under a proper envelope) + the root gets the same locality (`rootVdict_cell` + `cell_local` at `none`); the L5 semantic pin stays MovesT/HC-2, typed never discharged |
| 7 | rootHalt_iff unfiltered ν; NP docstring overreach; §7 stale "ONLY field" (Fable OBS-1/2/3) | root-species filter added; NP docstring re-scoped to the piecewise form with the softened identification; §7 item 7 now "jet + hnorm" |

Unit count: 48 (unchanged; ShapeWF/VerdictModel grew fields, no new units — SW1's
sketch extends to the new clauses: gamTie/anchorTie from coherence's γ-tie +
hAnchor + hbezCanon-uniqueness against `bezT`). Gate acceptance UNCHANGED (§0.6 +
the §3.1 adversary block): P̂* ∈ Shape 3 under the COMPLETED certificate;
C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1, NP = 5 (inhabited branch), Nshape = 5,
A = 11, W = 7, M = 1.

## 15. REV 8 table (closing; Fable#6 ACCEPT 0/2 ∪ Codex FINAL#6 REJECT 3/3)

| # | finding (who) | REV-8 repair |
|---|---|---|
| 1 | ShapeWF admits residue-degree-impossible shapes (root-only w = 2) — Codex c.1 | `ShapeWF.w0` (w₀ = 1: the root pool is F_p — §D4-R.6 "Side digits (pool F_p)") + `ShapeWF.wchain` (w_{r+1} = w_r·g_r: F_{r+1} = F_r[z]/(ψ_r); recenterings g = 1 unchanged — one law; §D4-R.6 "F₁ := F_p[z]/(ψ) = F_{p²}, w₁ = 2"); adversary A-vi (root-only w = 2) fails w0 ✗ |
| 2 | SW1 assumes MonicTie, a certificate component — Codex c.2 | MonicTie's derivable clauses now DERIVED in SW1 (monicTop → r = 0 via hmonicRoot + root_iff; non-root monicTop = false); the underivable residue (root monicTop ↔ s0+wSide = n — Matches' clause speaks of the digit VALUE, not the slot POSITION) is the NAMED encoding gap **ENC-MONIC**, SW1's weakest sufficient hypothesis `hmt0`, §D4-R.6 quoted, owner = D4-n3 gate + menu-wave verification (§2 ledger) |
| 3 | E9/D3a/W3 lose the empty prefix (0-bounds where the note has C_∅ = 1) — Codex c.3 | routed through the F3/CD bridge: D4R2'/D4R2'_full restated on `Shape.CD` — at P̂ = ∅ the theorem IS C_∅ = 1 ≤ Mfac(∅)·p^{W(∅)} = 1 (empty product); E9 gains `encTargetP_empty` (the singleton-to-unit encoding, card 1 = C_∅); D3a's proof is the explicit ∅/nonempty case split |
| 4 | declaration order: gamTie consumes strS declared later — Codex g.4 | `strS` HOISTED to §3.0 group (1) before ShapeWF; group (2) re-scoped — the order elaborates |
| 5 | TreeModel lacks L2's exhaustive-child law — Codex g.5 | typed OPEN fields `eligible` + `child_iff` (mem o x → (child o ν x ↔ eligible o ν x)) — L2's "ALL next-node data … where s is an eligible side and ψ ranges over the eligible factors"; eligible's cell-data semantics = kernel-(b), HC-2/MovesT — the dependency is a named field, not prose |
| 6 | VerdictModel cure degenerate (Cell := Box, cap > N); no uniform cap — Codex g.6 | `capBound`/`hcapU` (per-class caps uniformly bounded) + `hcapB : capBound < N` (the box exceeds the envelope) + `hlevel` (chart level-surjectivity): coordinates outside the envelope exist, so `cellOf := id` fails `cell_local`; cross-level uniformity documented as MovesT's VP packaging; constant-verdict instances excluded only by the semantic pin (stated) |
| 7 | §3.2 variable line incomplete; NP ∅-routing gloss; "every [value] assignment" — Fable G-1/G-2/OBS-A | variable line completed (`{n N m pol P}`); the Shape.NP docstring displays the ∅-shape routing (note: MAX branch with N(∅,⊤) = 1; Lean: else-branch, value 1; NPband(∅) = 1 — all routes value-exact, deviation = F3's) ; the elided word restored |

FULL ADVERSARY BLOCK (re-run, §3.1): A-i root_box ✗ · A-ii MonicTie ✗ · A-iii
hmonicRoot/species ✗ · A-iv h = 0 unbuildable ✗ · A-v gcd(2,4) ✗ · A-vi root-only
w = 2 ✗ (NEW). Positives: P̂* ∈ Shape 3 (now incl. w₀ = 1, w₁ = 2 — the note's
"w₁ = 2") ✓ · P̂₀ ∈ Shape 4 (w₀ = 1; A(P̂₀) = 14, Fable#6's unclaimed cross-check) ✓.
GATE (unchanged, both auditors' recomputations + §0.6): C_P̂*(2) = 3, C_P̂*(3) = 48,
mult ≡ 1, NP = 5 (inhabited branch = the note's own derivation), Nshape = 5,
A = 11, W = 7, M = 1; the ∅ arithmetic now THEOREMS on E9/D3a/W3 (C_∅ = 1 ≤ 1).
Unit count: 48 (unchanged; fields grew, statements restated).
