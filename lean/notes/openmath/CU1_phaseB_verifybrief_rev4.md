# CU-1 (K-RUN-C composition, unit NM) — no-missing + interior adequacy + state binding — verify brief, REV 4 (Fable, 2026-08-02)

(Companion record: `CU1_phaseB_attempt_rev3.md` (unchanged at rev 4).
This is REVISION 4 — the LIGHT repair round after PASS 2 of 2. The
lineage: rev 2 was the STRUCTURAL repair of V27 (rev 1 UNSOUND; table §0);
rev 3 repaired V29's consumption-accounting findings on rev 2 (table
§0-R3). The PASS-2 hostile verification of rev 3
(`CU1_pass2_fable_verify.md`, Fable, fresh context, 2026-07-31; verdict
SOUND-WITH-GAPS, 0 critical / 7 justification gaps F-1..F-7) CONFIRMED
the whole rev-2/3 mathematical structure yet again — genuinely N-free
induction, exhaustive-disjoint split on its stated domain, creation-first
record match, D-14 fired exactly once, pins declared where consumed, and
the two rev-3 consumption DROPS verified correct — but found §5's
exactness claim STILL false at named points (unmapped load-bearing
inputs: Lemma CEIL/L(H); (C4)/Cons_f; Θ; the rows-7/17/18 O-1thr
coverage overstatement), one unrouted boundary case (depth-0 a₀ = 1),
and two pin-display defects ((FR≡)'s frame clause consumed as an
assertion while displayed only as antecedent text; π's (FR≡) citation
outside the pin's trigger). REV 4 REPAIRS EXACTLY THOSE SEVEN (disposition
table: §0-R4). The §§1–3 statements and proofs and §4's constructions are
byte-identical to rev 2/3; the ONLY text edits outside §§0-R4/5/8 and this
preamble are: the §0′ (FR≡) display gains its second clause as displayed
pin content (F-6), the §0′ π paragraph is re-cited to §1.2 (F-7), §4's
split gains the depth-0 hen-leaf routing bullet (F-5), and CU-1-SURJ's
dependency row-list is corrected (F-1). NO new mathematics and NO new
input anywhere: rows 30–33 display inputs the text already consumed, and
the (FR≡) second clause displays content rev 2 already declared as the
pin's (its consumption sites were already on row 21) — same owner (R-6),
same order-1 PROVED instance, same §7.2 gate shadow. The primary gate
(depth-3 falsifier, §7) ran before rev 1 and SURVIVED; rev 4 adds no
mechanism and no input, so no new gate is owed — §7.4 carries.)

**Unit spec:** `O3adj_adjudication.md` §3.1 CU-1 (ACCEPTED plan), cross-read
with `SYNTHESIS_PASS4_2026-08-01.md` §2.3. CU-1 is the K-RUN-C composition's
ONE new proof obligation: an ordinary induction on chain length whose step is
entirely per-site lemmas already stated (and partly proved) elsewhere.

**What this brief claims:** Theorem CU-1 (§2) and its three corollaries,
PROVED as a conditional composition — every named input is either (a) proved
in its home brief at a displayed grade, or (b) an EXACT open lemma / declared
pin listed in §5, consumed by citation with no strengthening beyond what is
flagged in §0's churn column. NO new per-site mathematics is introduced.
**What it does NOT claim:** no box-keyed universal statement (everything is
per-f); no global adequacy object or tree isomorphism; no leaf-coverage
claim (routed to O5triple Theorem B — the §4 split); no claim that the base
packages are verified beyond their displayed grades.

## 0-R4. Rev-4 changelog (pass-2 findings F-1..F-7 → dispositions; accounting + display only)

| P2 finding | disposition (repair site) | churn class |
|---|---|---|
| F-1. Lemma CEIL / the L(H) read-ceiling: consumed (§1's MAX display; CU-1-LVL's "one application suffices"; SURJ's walk clause) but NO row; CEIL ungraded; SURJ's row list also omits row 17 | NEW row 30: L(H) + Lemmas NAT/CEIL, with all three site groups and the home grade (PROVED, O-1thr §3 displayed proofs). SURJ's dependency sentence corrected: rows 7–11, 15–18, 22, 30 (row 17 added — (M4) is consumed inside D-14's application, as row 17's own location column already said) | row ADDED (input already consumed) + one accounting sentence |
| F-2. (C4)/Cons_f consumed at ≥ 7 sites (two load-bearing: the step preamble's per-level prefix restriction = the IH's legality; ADEQ's two-sided converse reading) with NO row; Θ consumed in clause (ii)'s statement with NO row | NEW row 31: (C4)/Cons_f — every site listed, incl. the two load-bearing facts with their home warrant ((C4)'s own per-level quantifier shape, O-2a rev 5 §2). NEW row 32: Θ = (C3). The exhaustiveness paragraph's coverage list now names (C4) and Θ | rows ADDED (inputs already consumed; (C4) remains hypothesis vocabulary — the row makes its consumption auditable, adds no dependence) |
| F-3. Exhaustiveness paragraph overstates rows 7/17/18's O-1thr coverage: (N1)–(N3)-at-harvest, §1.2 AUX prefix closure, the §1.1 recursion, §1.3 READ/REALIZED, and the base-k=0 sites trace to no row | NEW row 33: the O-1thr §§1.1–1.3 definitional bundle (frame recursion; node fields + laws + AUX prefix closure + the home-displayed (N1)–(N3)-at-harvest fact; READ/REALIZED definitions), all sites. Row 18's location column gains base k = 0 (track/root-state existence, §1.4 root initialization). Exhaustiveness paragraph rewritten to the corrected row assignment | row ADDED + location fix |
| F-4. Row 6's "ONLY" is inexact: §4's terminal bullet cites Lemma R's displayed non-claim as the warrant for the terminal routing — a third site | row 6 location column: the terminal-bullet site RECORDED (consumption of the displayed NON-claim; still produces and identifies nothing) | location fix (one clause) |
| F-5. The depth-0 boundary (a₀ = 1: root-level simple factor, complete at depth 0) is routed by no sentence — every displayed route hypothesizes a₀ ≥ 2 | §4 split: NEW displayed bullet routing the a₀ = 1 case — it is a HEN LEAF of O5triple's tree (Definition 𝒯(g), §3 there: root child at multiplicity 1), covered by the SAME routing target (Theorem B through the hen slots of leafslots(T) = hen ⊎ irr, via (I-1)(b)'s hen clause; Theorem D(b)) at the same conditionality; CU-1 consumes nothing from it. The split's coverage claim is thereby displayed as: per children of non-complete types PLUS the hen-leaf routing | routing sentence ADDED (display; no proof touched, no input consumed) |
| F-6. (FR≡)'s "frame clause" is consumed as an ASSERTION (clause (ii): base 6, step 5) but displayed only as the unpacked ANTECEDENT of the read-object clause | §0′ (FR≡) display: explicit SECOND clause (FR≡-frame) displayed as assertible pin content — machine §1.1-recursion frame data over matched records (with (P-KEY) keys) = the [F.0] stage frame data over (f, Θ(𝐇)). Same pin, same owner (R-6), same order-1 PROVED instance, same §7.2 shadow; row 21 annotated | pin display completed (content rev 2 already declared and row 21 already carried; no new dependence) |
| F-7. Row 21 omits the §0′ (π) site; worse, π's definition cites (FR≡) at arbitrary machine histories, outside the pin's frame-equality trigger | §0′ π paragraph RE-CITED (the pass-2 report's own cheap repair): field presence on every record is §1.2 content (row 33); the (FR≡) citation belongs to the stage-record MATCH (base item 4, step 3(d)), where clause (ii) supplies the hypothesis — π's definition now consumes NO pin. Row 21 annotated with the re-cite | citation fix (strict weakening: one pin consumption site DELETED) |
| Minor notes (no findings): ADEQ's W1 e = 1 case is vacuous under μ ≥ 2 (the displayed argument proves the vacuous case — harmless); ADEQ's W4 has a silent y/z variable renaming (order-1 vs order-(i+1) residual variable); §1's "(N\*-MAJ) holds by construction" is a sketch, not the R-4 discharge | DISPOSITIONED HERE, text unchanged (cores byte-stable): W1 — the argument is sound and covers the case whether or not it can arise; W4 — the identification is (L3)'s own variable convention (row 25's home block); (N\*-MAJ) — row 22 consumes only the displayed inequality, discharge stays R-4 | none (recorded) |

## 0-R3. Rev-3 changelog (V29 findings → dispositions; consumption accounting only)

| V29 finding | disposition (repair site) | churn class |
|---|---|---|
| 1. Interior/terminal split — PASS, with the scope caveat that the μ = 1 leg is conditional routing (O5triple (I-1)–(I-3)), "explicitly admitted, not a hidden overclaim" | NO CHANGE OWED — the caveat is already the §4 routing display's own text | none |
| 2. Dressing construction — PASS ("Lemma R … appears only after construction as a recovery/canonicity observation") | NO CHANGE OWED | none |
| 3. Read-back — global quantification PASSES, but "its dependencies are exactly ∀-instances of Theorem CU-1 and Corollary CU-1-ADEQ" is FALSE AS WRITTEN: the walk-on-f_N clause requires CU-1-LVL, hence D-14, REAL≡, the decode facts, and the machine-interface bundle | §4 CU-1-SURJ: the dependency sentence now SPLITS the accounting — chain construction + realization on f = ∀-instances of CU-1 + ADEQ; the walk clause = the ∀-instance of CU-1-LVL, consuming LVL's displayed bundle (rows 7–11, 15, 16, 18, 22). The corollary's STATEMENT is unchanged. §8 item 9 updated to match | accounting fix (one sentence) |
| 4a. Map row 2 lists "FULL OL-2 (a)–(d)" but clause (a) is not visibly consumed — only (b), (c), (d) are | row 2 REBUILT: consumed clauses = (b)/(c)/(d) ONLY; clause (a) displayed as consumed by NO sentence of this brief | consumption DROP (strict weakening) |
| 4b. ADEQ's W4 check consumes the nonzero-constant-term fact "via (L3)/the OL-3 note", but row 3 locates OL-3 only in steps 2 and 3(d) | row 3 REBUILT: the ADEQ W4 site is recorded, with its classification displayed — the consumed fact is (L3)'s y ∤ R_λ(f) (row 25), the OL-3 note being its DISPLAY SITE at home; no OPEN content of OL-3 enters §4 | location fix + classification |
| 4c. ADEQ explicitly invokes (L2), (L3), Def. 2.21, (C1), and the W-laws; rows 7/17/18 (principally O-1thr machine inputs) cannot carry them | NEW rows 24–28: (L2); (L3); Def 2.21; the (C1) carrier; the W-laws (W1)–(W5) — each with its consumption sites and home status. The §5 exhaustiveness paragraph is rewritten to assign O-1thr vocabulary to rows 7/17/18 and O-2a vocabulary to rows 24–29 | rows ADDED (the inputs were already consumed in the text; the map now says so — no new dependence) |
| 4d. [F.2] is repeatedly cited independently in the record match yet has no standalone map entry; subsuming it under FR≡ is inconsistent with the prose | NEW row 29: [F.2] standalone (the stage-side tower / emitted-field-list display), sites §0′ (π), step 2, step 3(d); its machine-side instantiation at orders ≥ 2 still rides (FR≡) (row 21) | row ADDED |
| 4e. O-2a Theorem 2(A) is listed as consumed in ADEQ, but no indispensable use of (A) is displayed | (A) DROPPED from row 5 (the "drop the unconsumed listing" option): no sentence of §§2–4 uses it — §4's split consumes only (B)'s biconditional. §0's trailing paragraph annotated in place | consumption DROP (strict weakening) |

Nothing else is touched: §§1–3 (statements, proofs, the induction), §4's
constructions and split displays, §§6–7 are byte-identical to rev 2; the
only §4 edit is finding 3's one dependency sentence, and the only edits
outside §§0-R3/4/5/8 are this preamble and the closing line.

## 0. Rev-2 changelog (V27 findings → dispositions; churn classification)

| V27 finding | disposition (repair site) | churn class |
|---|---|---|
| 1. Window-width tie GAP: (M6c)(ii)/WGEO + OL-2a-2-min do not put the semantic side inside the finite window; the proof silently strengthens OL-2-min or omits a width-coverage input | §3 step 2: the tie is now FULL OL-2 clause (b) (stage window polygon = N_{k+1}(f) as subsets of ℝ², vertex for vertex) + WGEO(c) (machine-side: the principal part of the FULL polygon coincides with the window hull). No width-indexed clause is invented | RESCOPE, sanctioned: O-2a rev 5 §4 advertises full OL-2 (a)–(d) to exactly this consumer ("the O-3 design seam"); CU-1 IS that seam. The min-core citation of rev 1 was wrong-direction — repaired by consuming the full form, which is on record at home |
| 2a. Record match invalid: "both are functions of (f, Θ(𝐇′))" does not imply equality; Lemma R's hypotheses never established for the harvested chain | §3 step 3: the construction now comes FIRST (the harvested record, via (M6a) + the (FR≡) pin), and the match is FIELDWISE — each 𝔈-field displayed with its named source (OL-2(c)/(d), OL-3, [F.2], the inc law). Lemma R is demoted to a canonicity remark; it is nowhere used to produce or identify the record | structural repair (the V27-suggested fieldwise route, executed) |
| 2b. OL-2a-6(b) invoked "at level k+2" where no (k+2)-nd emitted record exists | DELETED. Clause (ii) at k+1 is re-founded on (R4)/(M4) + the displayed policy pin (P-KEY) (§0′). OL-6 is no longer consumed anywhere in this unit (its consumer remains O-2a Theorem 2(D) = CU-2) | rescope vs the O3adj spec (which listed OL-6 in the step); the state-level pins (FR≡)/(P-KEY) are the content OL-6's stage-birth proof route supplies, declared instead — flagged for the orchestrator in the attempt record |
| 3a. Base k = 0 incomplete: REALIZED asserted at the empty history; ROOT-M unmapped | §2/§3: REALIZED is NOT asserted at k = 0 (O-1thr defines it only at H·ν); the k = 0 clause is restated as the displayed root clause. ROOT-M has map row 12 | display repair |
| 3b. Base k = 1: root-prefix non-saturation not displayed | §3 base: displayed route — the root state has no last record, saturation halts are record-only at a LAST record, and a₀ ≥ 2 excludes the (τ-hen) certification | display repair |
| 3c–d. Step 2/3 gaps (width tie; M6c(ii) non-halting use off-map; saturation relation + width equality undisplayed) | step 2 as finding 1; step 3(a): non-saturation is now the RECORD-ONLY route (IrrHalts ⟺ μ_last = 1 via the key-degree identity, O-1thr §1.4) — the rev-1 Theorem 2(B) detour is dropped (strictly weaker consumption); step 3(b): non-ns-halting is definitional once step 2 exhibits the principal face (¬NsHalts := no principal face); map rows audited | display + one consumption DROP |
| 3e/5. Step 4 invalid IH use: N ≥ N\*(𝐇) not derivable from N ≥ N\*(𝐇′); prefix monotonicity not assumed; (N\*-MAJ) insufficient for the stated induction | STRUCTURAL: the induction is now N-FREE — realization is proved on f itself (clauses (i)/(ii) mention no working level). The level transfer is ONE D-14 application at the top site, in the separate Corollary CU-1-LVL; L(M) majorizes every prefix ceiling BY ITS OWN DEFINITION (a max over reads), so no monotonicity of N\* is used anywhere. (N\*-MAJ) restated as the single top-site inequality (§1) | structural repair |
| 3f. Hidden decode input: level-N decode's legitimacy and its REALIZED never established before REAL≡ | Corollary CU-1-LVL displays: f_N := the decode of f's level-N box is MONIC of degree n by O-1thr §1's box definition (integer lift, digits ≥ N zeroed, leading coefficient 1) with f ≡ f_N (mod p^N) by construction; "the canonical run at working level N" is DEFINED as the execution walk on f_N; D-14 establishes REALIZED(f_N, M) BEFORE REAL≡ fires on f_N | display repair |
| 3g. Step 5: OL-6(b) unlicensed; record identity inherited | as 2b; the record identity is now step 3's fieldwise match | covered above |
| 4. The 16-row map false as exhaustive (ROOT-M, M4 missing; rows 6/10 mislocated; SPAN listed without use; decode/root-initialization/machine-rule inputs unmapped) | §5 rebuilt: rows added (ROOT-M; (M4); the §1.4 definitional bundle + key-degree identity; the decode display; the three pins); SPAN deleted (rev 1 listed it without a use — V27 was right); every row's locations re-audited against the §3 text | display repair + one row DELETION |
| 6a. Corollary ADEQ overclaims: complete/terminal children not realizable by CU-1 | §4: ADEQ rescoped to INTERIOR children (μ ≥ 2); complete children (μ = 1 — leaves, by O-2a Theorem 2(B)'s displayed biconditional) are routed to O5triple Theorem B / Theorem D(b) (= D-7b), whose counting-forced coverage consumes NO no-missing clause; the split is displayed with its no-gap/no-overlap check. Terminal machine records (sel = ⊥) are not GMN children at all — CU-2t's seam | RESCOPE per the adjudicated directive |
| 6b. "dressing recovered per Lemma R" creates nothing | §4: the node is now CONSTRUCTED by displayed formulas (the same formulas as Lemma R's recovery map, used as definitions); Cons_f and well-formedness are then CHECKED clause by clause. Lemma R appears only as the canonicity remark | structural repair |
| 6c. Read-back "per site" is globally quantified in substance | §4 Corollary CU-1-SURJ: stated GLOBALLY, with the display that its dependencies are exactly ∀-instances of Theorem CU-1 + ADEQ (no new input), and with the explicit non-claims (no leaves, no boxes, no tree object) | honesty repair (option "state it globally with its true dependencies") |

Also at rev 2, TWO consumption DROPS (no finding demanded them; both are
strict weakenings, listed for the no-silent-churn rule): OL-5 is no longer
cited (the order-1 base now runs on O-2a Theorem 1 (D3), which is PROVED,
plus the O-1thr root kernel — rev 1's "converse-transport direction" gloss
of OL-5 was itself a silent strengthening of an emission-direction lemma);
O-2a Theorem 2(B) is no longer cited in the step (saturation is record-only,
finding 3c); 2(A)/(B) remain cited at the base and in §4's split. [Rev-3
annotation (V29 finding 4e): that last clause OVERSTATED — the base cites
neither (A) nor (B), and §4's split consumes only (B)'s biconditional; (A)
is dropped entirely at rev 3 (row 5).]

## 0′. Standing setting (imports, grades, and the three displayed pins)

f ∈ ℤ_p[x] monic of degree n ≥ 2 with disc f ≠ 0 (the tree §2.4 standing
preconditions ride the cluster and are not re-litigated here). Residue field
F_q = 𝔽_p (O = ℤ_p). Vocabularies imported VERBATIM (restated below only
where a clause is consumed; the home briefs are normative):

* **O-1thr machine** (`O1thr_phaseB_verifybrief_rev4.md`): §1 boxes and
  decodes (a level-M box is the tuple of the n non-leading coefficients mod
  p^M; its decode f_x is the integer-lift polynomial, digits ≥ M set to 0 —
  so f_x is MONIC of degree n, and f ≡ f_{x} (mod p^M) for x = f's own
  level-M box); §1.1 frames (Φ_i, w_i, K_i), stretches E_i, key heights γ̂_i,
  sheared heights u^{(i)}_j, policies 𝒫; §1.2 nodes (fields e, h, s0, wSide,
  γ, pat, ψ, μ, (vhtx, vtx), produced key, species), laws (N1)–(N4), history
  coherence, LAWFUL = CORE ∧ AUX (AUX prefix-closed, box-free); §1.3 READ
  (R1)–(R5) and **REALIZED(f, H·ν)** := READ ∧ LAWFUL ∧ no-proper-prefix-
  saturated — defined at NONEMPTY histories H·ν only; §1.4 states, the
  development polygon at a state (sheared points u_j = w_o(B_j) + j·γ̂_o over
  ALL slots), window width W_o (= m at a root state of reduction factor
  φ̄^m; = μ_ν at H·ν), the window hull, candidate children, harvesting,
  halts — **IrrHalts(H)** ⟺ μ_{last} = 1 via the displayed key-degree
  identity accE·accF = Dwidth (record-only), **NsHalts(o, f)** := REALIZED
  non-saturated o whose window has no principal face; interface (M1)–(M6):
  **(M4)** frame data are record functions; **(M6a)** harvest totality
  (definitional); **(M6b)** (i) vertex nonzero [PROVED via Corollary VTX at
  the displayed slice], (ii) the (N4) band [upper: VTX; lower: residue],
  (iii) AUX at harvest [residue]; **(M6c)** window-harvest completeness
  (rev-4 requantification, no halting hypothesis); Lemmas ROOT-M, VAL1/KEY1/
  DIV1, **WGEO** (window geometry — (c): the principal part of the FULL
  polygon coincides with the window hull; (d): beyond-window points lie
  strictly above every window face's line), Corollary VTX, **Lemma REAL≡**
  (walk visits H·ν ⟺ REALIZED(f, H·ν), given (M6a)+(M6b)+(M6c)); §3 the
  read ceiling L(H) := 1 + max_{i<k} ⌈I_i/E_i⌉ (a MAX over the chain's
  reads; Lemmas NAT/CEIL); §4 **Theorem 1 = D-14** (lawful-site read
  locality: for LAWFUL (H, ν), L := L(H·ν), f ≡ f′ (mod p^L) monic degree-n
  ⟹ REALIZED(f, H·ν) ⟺ REALIZED(f′, H·ν); PROVED OUTRIGHT machine-side,
  pass 4 pending).
* **O-2a dictionary** (`O2a_phaseB_verifybrief_rev5.md` — REV 5 is now the
  normative home; rev 1 of this brief cited rev 4, and rev 1's "OL-2a-N"
  names are the home's OL-N): carriers 𝔈 (dressed histories; W1–W5) and 𝔗
  (formal chains), Θ, ι, Lift ((C1)–(C3)); **(C4)/Cons_f** ((c0), (c1) side
  + INTRINSIC positional clause, (c2) exact multiplicity); **Lemma R**
  (recovery: on all-continuing Cons_f chains, 𝐇 is a function of (f, Θ(𝐇)),
  by the DISPLAYED recovery map); Theorem 1 (order ≤ 1, PROVED — in
  particular **(D3)**: the displayed development/hull/positional/residual
  formulas ARE (L2)/(L3)'s order-1 data); Theorem 2 (A)/(B)/(C)/(D); the six
  open lemmas **OL-1..OL-6**, including the FULL **OL-2** (a) valuation tie
  u_{i+1} = v_{i+1}, (b) stage window polygon = N_{i+1}(f) as subsets of ℝ²
  vertex for vertex, (c) emitted (e, h, ℓ) = the side's lowest-terms slope
  pair and degree d(S), (d) emitted (s, u) = the side's initial point in the
  order-(i+1) INTEGER frame; and the FULL **OL-3** (R^nrm = c·R_{λ}(f),
  c ∈ F_{i+1}^×, equal monic-irreducible factor multisets with equal
  multiplicities, both constant terms nonzero); the stage interface
  [F.0]–[F.2] (in particular [F.2]: the stage residue field IS the
  constructed F_{i+1} of (C1), and the EMITTED node record has exactly the
  𝔈-node fields (e, h, ℓ, s, u, sel, inc) + dressing).
* **O5triple** (`O5triple_phaseB_verifybrief_rev3.md`): Theorem B (β_g
  bijective onto leaves(𝒯(g)), surjectivity counting-forced) and Theorem
  D(b) (= D-7b), conditional on its interface (I-1)–(I-3) — consumed ONLY
  as the ROUTING target of §4's split, not as an input to any proof here.

**Grades displayed verbatim (no "proved base"):** O-1thr rev 4 =
PROVED-UNVERIFIED modulo its displayed residue ((M6b)(ii)-lower/(iii),
(V1)/(V2) beyond the proved slice), pass 4 pending. O-2a rev 5 = the
thrice-confirmed core lineage; V25 on rev 4 was SOUND-WITH-GAPS (0 critical,
1 minimality gap, repaired at rev 5); required pass 2 pending. O5triple
rev 3 = its own displayed conditional grade. CU-1's grade can never exceed
the meet of these.

**The three pins (DECLARED cross-artifact inputs, displayed here so nothing
is smuggled).** The O-1thr machine and the O-2a stage flow are two
abstractions of the ONE project engine (MOVES §B2-DEF; Lean `MovesX`). Each
brief consumes the engine only through its own interface; composing them
requires the following identifications, which rev 1 consumed silently and
rev 2 declares:

> **(P-ROOT)** The fixed policy 𝒫's root lift is O-2a's Lift₀: the
> coefficientwise canonical lift of φ̄ (so Φ₀ = Lift₀(ψ̂₀) at the track of
> ψ̂₀). [O-2a (C2) pins Lift₀ to exactly this; O-1thr's policy assigns "a
> monic lift prescribed from f̄" — the pin selects the same one.]
>
> **(P-KEY)** 𝒫's produced key at a node depends only on the FORMAL chain
> datum (the slopes and dressings up to that node), and equals Lift on it:
> the produced key of a node with formal datum extending c to c′ is
> Lift_{i+1}(c′). [O-2a (C2) pins Lift_{i≥1} to "the project engine's
> standard lift", a function of the length-(i+1) formal datum; (R4)/(M4)
> make the machine's produced key a function of records + policy. The pin
> asserts these are the SAME function — definitional under the shared-source
> reading, declared because it is cross-brief.]
>
> **(FR≡)** (frame/read identification). At any state o on f whose frame
> equals the [F.0] stage frame over (f, c) — key Φ_o = Lift(c), valuation
> w_o and shear γ̂_o the §1.1 recursion over the same key tower, residue
> tower K_• = the constructed F_• of (C1) — the state's development polygon
> (the sheared points u_j over ALL slots), its per-face residual polynomials
> read through the recorded unit normalization, and its per-(face, factor)
> harvested records ARE the stage read's window polygon [F.0], normalized
> residuals R^nrm [F.1]/[F.2], and emitted node records, at parameters
> (f, c). **Second clause (FR≡-frame) — the frame clause, displayed as
> assertible pin content at rev 4 (P2 F-6):** for a machine history M on f
> whose records match an 𝔈-chain 𝐇 fieldwise (π(M) = 𝐇) and whose produced
> keys are Lift on the formal data ((P-KEY)), the §1.1 frame recursion over
> M's records and 𝒫 — key, valuation, shear, residue tower — yields EXACTLY
> the [F.0] stage frame data over (f, Θ(𝐇)), level by level. [This is the
> clause that clause (ii) (base 6, step 5) consumes under the name "(FR≡)'s
> frame clause"; rev 3 displayed its content only inside the FIRST clause's
> unpacked antecedent — hypothesis text doing assertion work, P2 F-6. Its
> consumption sites were already on row 21; nothing new is consumed. Given
> (FR≡-frame) at the matched records, the first clause's antecedent (frame
> equality) is SUPPLIED at the state — which is exactly how clause (ii) at
> level k triggers the read-object clause at level k + 1.]
> **Status (both clauses):** at order 1 (root states under (P-ROOT)) this is
> checkable by inspection — the machine's root read objects are literally
> the displayed formulas of O-2a's (D3), which is PROVED ("the displayed
> formulas ARE (L2)/(L3)'s order-1 data"; Gauss heights, zero shear, no
> twist). At orders ≥ 2 it is a DECLARED PIN (the state-level content that
> OL-6's stage-birth proof route supplies), OPEN, owned by the MOVES
> §B2-DEF transcription / GD campaign (§6, R-6). Its order-2 refutable
> content is exactly what the §7 gate probes: a slot-fresh reading of its
> residual clause is REFUTED 1,818 times by the depth-3 harness (§7.2), and
> the surviving coherent convention is the pin's content.

**Machine dressings and the projection π.** A **machine history on f** is an
O-1thr history M = [ν̂₁, …, ν̂_k] (full record fields). Its **𝔈-projection**
π(M) is the dressed 𝔈-history whose i-th node is the [F.1]/[F.2] emitted
record of ν̂_i's harvest — explicitly: e := ê, h := ĥ, ℓ := ŵSide/ê (the
side degree: the number of e-strides, = deg of the residual polynomial),
(s, u) := the emitted initial-point pair, sel := (deg ψ̂, μ̂), inc := 1 iff
the species is increment (⟺ ê·deg ψ̂ ≥ 2, the §1.2 species law = W2's
value), dressing := ψ̂ — fields all present on EVERY node record by the
§1.2 field list (row 33). [Rev-4 re-cite, P2 F-7: π is defined for an
ARBITRARY machine history M on f, at whose states (FR≡)'s frame-equality
hypothesis need not hold, so π's definition consumes NO pin — rev 3's
"via (FR≡)'s emitted-record clause" invoked the pin outside its trigger.
(FR≡) fires at the LATER claim that π(M_𝐇)'s records match the STAGE's
emitted records (base item 4, step 3(d)), where clause (ii) supplies the
frame hypothesis — row 21's sites, unchanged.] Theorem CU-1 produces, for
each admissible 𝔈-chain 𝐇, a CONSTRUCTED machine history M_𝐇 with
π(M_𝐇) = 𝐇.

## 1. The decision level N\*(𝐇) — the single consumed property

For a dressed history, N\* is the per-branch decision level (the D4R.4/L12
join with the TB-CAP verdict window; rev-1 (O5′), uncontested at V21). This
brief consumes exactly ONE property of it, restated at rev 2 as a SINGLE
top-site inequality (V27 findings 3e/5: rev 1's per-prefix form tempted an
invalid IH use; the induction below is N-free, so the majorant is consumed
exactly once, in Corollary CU-1-LVL):

> **(N\*-MAJ)** For the f-pinned machine dressing M_𝐇 of a realized chain
> (§2): N\*(𝐇) ≥ L(M_𝐇).

Since L(M) = 1 + max_{i<k} ⌈I_i/E_i⌉ is a MAX over the chain's reads,
(N\*-MAJ) is equivalent to majorizing every prefix ceiling
(L(M_{𝐇,≤j}) ≤ L(M_𝐇) for every j — a max over a subset); no prefix
monotonicity of N\* itself is used anywhere in this brief. (N\*-MAJ) holds
for the D4R.4/L12 join by construction (it is a max over the branch's nodes
of per-site band levels joined with the verdict window). Any level function
satisfying (N\*-MAJ) may be substituted. [Seam: the cluster spec owns the
exact N\* definition; (N\*-MAJ) is displayed so CU-1 cannot silently
strengthen it — residue R-4.]

## 2. Theorem CU-1 (statement) and Corollary CU-1-LVL

**Theorem CU-1 (N-free realization + state binding).** Let
𝐇 = (ρ₀; ν₁, …, ν_k) ∈ 𝔈, k ≥ 0, be well-formed with Cons_f(𝐇), a₀ ≥ 2,
ALL nodes continuing, and EVERY node non-complete: μ_i ≥ 2 for all
1 ≤ i ≤ k. (For i < k this is W3; at i = k it is CU-1's INTERIOR scoping —
complete last nodes, μ_k = 1, are the leaf seam, routed in §4's split; the
theorem quantifies over interior chains exactly.) Then there is a machine
history M_𝐇 = [ν̂₁, …, ν̂_k] on f, on the track of ψ̂₀, constructed
level-by-level by harvesting (the construction is displayed in the proof and
is choice-free: each ν̂_i is THE harvest of one identified candidate pair),
such that:

* **(i) (realization on f, no working level.)** π(M_𝐇) = 𝐇 field by field,
  and — for k ≥ 1 — REALIZED(f, M_𝐇), in O-1thr's single displayed sense.
  At k = 0 the clause reads (REALIZED is not defined at the empty history —
  V27 finding 3a): the track root state o_𝐇 of ψ̂₀ exists on f, i.e.
  ord_{ψ̂₀}(f̄) = a₀ ≥ 2, with reduction factor ψ̂₀^{a₀}.
* **(ii) (state binding — the old F5, carried as a clause.)** The state
  o_𝐇 (the root state at k = 0; the state of M_𝐇 at k ≥ 1) has frame equal
  to the [F.0] stage frame over (f, Θ(𝐇)): its key is Φ_{o_𝐇} =
  Lift_k(Θ(𝐇)); its valuation, shear, and residue tower are the §1.1
  recursion over M_𝐇's records and 𝒫 ((M4)), which under (P-KEY)/(FR≡) are
  the stage's [F.0] data over Θ(𝐇); and its window width is W_{o_𝐇} = a₀
  (k = 0) resp. μ_k (k ≥ 1) — §1.4's definition instantiated at the
  matched records.

**Corollary CU-1-LVL (working-level transfer; the only clause where N
appears).** Let 𝐇 be as above with k ≥ 1, and let N ≥ L(M_𝐇) — in
particular any N ≥ N\*(𝐇), by (N\*-MAJ). Let x be f's own level-N box and
f_N its decode. Then f_N is MONIC of degree n (the §1 box display: the
decode lifts the n non-leading coefficients and restores the leading 1) with
f ≡ f_N (mod p^N) by construction; REALIZED(f_N, M_𝐇) holds; and the
execution walk on f_N — this is the DEFINITION of "the canonical run of the
machine on f at working level N" — visits o_𝐇. At k = 0 (any N ≥ 1): the
walk on f_N starts at the root states of all tracks of f̄_N = f̄, among them
o_𝐇.

*Proof of CU-1-LVL from CU-1.* k ≥ 1: (H, ν) := (M_{𝐇,≤k−1}, ν̂_k) is a
LAWFUL site (clause (i) gives LAWFUL(M_𝐇)) with L(M_𝐇) ≤ N, and f, f_N are
monic degree-n with f ≡ f_N (mod p^N), hence (mod p^{L(M_𝐇)}). O-1thr
Theorem 1 (D-14), applied ONCE at this top site, transfers REALIZED(f, M_𝐇)
to REALIZED(f_N, M_𝐇). (One application suffices: REALIZED at the top site
already quantifies over every prefix read, and L(M_𝐇) is the max of all the
per-read ceilings — Lemma CEIL's audit is over all i < k.) Lemma REAL≡ (⟸)
[(M6a)+(M6b)+(M6c), at their displayed grades] applied to f_N — with
REALIZED(f_N, M_𝐇) established FIRST (V27 finding 3f) — gives the walk's
visit. k = 0: the walk starts at root states of every track of f̄_N; N ≥ 1
gives f̄_N = f̄, and clause (i) gives the track. ∎

*Scope notes.* (1) Everything is per-f: no clause quantifies over lifts of
a box; the box enters only through CU-1-LVL's single D-14 application
(per-site), and cylinder/box-level lift uniformity lives at D-15. (2)
Terminal machine records (sel = ⊥) do not occur in 𝐇 (all nodes continuing)
and correspond to no GMN child (Cons_f constrains no terminal field);
verdict-carrying terminal seams are CU-2t's business. Complete last nodes
(μ_k = 1) are EXCLUDED by the interior scoping and routed in §4. (3) M_𝐇 is
canonical: by Lemma R, 𝐇 itself is a function of (f, Θ(𝐇)), and the
construction of M_𝐇 is deterministic in (f, 𝐇) — no choice enters. (Lemma R
is consumed ONLY in this remark and in §4's canonicity remark; it produces
nothing — V27 findings 2a/6b.)

## 3. Proof of Theorem CU-1 (ordinary induction on k; no working level)

**Base k = 0.** Cons_f((ρ₀)) is (c0): ord_{ψ̂₀}(f̄) = a₀, and a₀ ≥ 2 by
hypothesis. Machine-side, f̄ has the repeated irreducible factor ψ̂₀^{a₀}
(a₀ ≥ 2), so the track of ψ̂₀ exists with root state o_𝐇, reduction factor
ψ̂₀^{a₀} — clause (i) at k = 0. Clause (ii): the root frame is
(Φ₀, w₀, K₀) = (𝒫's root lift of ψ̂₀, Gauss, 𝔽_p[z]/(ψ̂₀)) with γ̂ = 0 and
window width a₀ (§1.4 root initialization, displayed definitions); by
(P-ROOT), Φ₀ = Lift₀(ψ̂₀), which is the [F.0] key of the level-1 stage over
Θ((ρ₀)) = (ψ̂₀); Gauss valuation and zero shear are the order-1 [F.0] data
by (D3)'s displayed formulas ((FR≡) at order 1 — checkable by inspection);
width a₀ = ord_{ψ̂₀}(f̄) is (c0). No REALIZED claim is made ((i)'s k = 0
reading). [Consumed: (c0); ROOT-M is NOT yet needed here; §1.4 root
definitions; (P-ROOT); (D3).]

**Base k = 1.** Let 𝐇 = (ρ₀; ν₁), ν₁ continuing with μ₁ ≥ 2 (the interior
scoping; W3 gives a₀ ≥ 2).

1. *The order-1 objects coincide.* By (P-ROOT), the machine's root
   development polygon — points (j, w₀(B_j)), zero shear — is the polygon of
   the φ₁-adic development of f with φ₁ = Lift₀(ψ̂₀) in the plain coefficient
   valuation: literally the (L2) order-1 polygon N₁(f) of O-2a's (D3)
   (PROVED). Likewise the stride digits and face residuals (unit-part
   classes, no twist at order 1) are (L3)'s residual coefficients — (D3)
   again. [This is (FR≡)'s order-1 instance; no pin is consumed, only the
   PROVED (D3) plus inspection of O-1thr's §1.1 order-0 display.]
2. *The semantic pair is on the menu.* Cons_f(𝐇) (c1) gives the side S₁ of
   N₁^−(f) of slope −h₁/e₁ with d(S₁) = ℓ₁ and the recorded initial point;
   (c2) gives ord_{ψ̂₁}(R_{λ₁}(f)) = μ₁. By step 1, S₁ is a principal face
   of the machine's root polygon; by Lemma ROOT-M (a₀ ≥ 2), every principal
   face lies in slots [0, a₀] and every beyond-window point lies strictly
   above its extended line — so the hull over [0, a₀] of all points equals
   the window hull there, and S₁ is a face of the WINDOW hull. Its machine
   residual is R_{λ₁}(f) up to the (D3) identification, so ψ̂₁ (an
   irreducible in F₁[z] = K₀[z], the same quotient) is a factor of the
   face's machine residual with exact multiplicity μ₁: (S₁, ψ̂₁) is a
   candidate pair at o_ρ₀.
3. *Root non-saturation and harvest.* The root state has NO last record, and
   both halt conditions are conditions on records/faces: IrrHalts is the
   recorded identity AT THE LAST NODE (none exists), and the (τ-hen)
   certification concerns simple factors only — excluded by a₀ ≥ 2 (V27
   finding 3b's requested display). Not ns-halted: step 2 exhibited a
   principal window face, and NsHalts means the window has none. So the root
   state is non-halted, and (M6a) (harvest totality) harvests ALL candidate
   pairs there, among them (S₁, ψ̂₁). Set ν̂₁ := its harvested record and
   M_𝐇 := [ν̂₁].
4. *Fieldwise match π(ν̂₁) = ν₁.* Each 𝔈-field, with its source: (e, h) =
   S₁'s primitive slope pair (coprimality pins it) = (e₁, h₁) [(c1)];
   ℓ = the side degree of S₁ = ℓ₁ [(c1), d(S₁) = ℓ₁]; (s, u) = S₁'s initial
   point in the order-1 integer frame — the harvest reads it off the same
   hull in the same frame (zero shear; (D3)'s positional formula IS (c1)'s
   positional clause) = (s₁, u₁); sel = (deg ψ̂₁, ord(R)) = (g₁, μ₁) [(c2) +
   the (D3) residual identification]; inc = [e₁g₁ ≥ 2] on both sides (§1.2
   species law / W2); dressing = ψ̂₁ by the choice of pair. No recovery
   lemma is invoked.
5. *REALIZED(f, M_𝐇).* READ: window-slot (R1)/(R2) and (R3)/(R4) by the
   harvest construction ((M6a)); (R1) beyond the window by (M6c)(i) at the
   root = Lemma ROOT-M; (R5) well-defined with the (N4)-upper by Corollary
   VTX [PROVED outright at root states over degree-1 root keys under the
   standard first key; modulo (V1)/(V2) for root keys of degree ≥ 2 —
   displayed grade, row 11]. LAWFUL: (N1)–(N3) displayed at harvest;
   (N4)-lower and AUX by (M6b)(ii−)/(iii) [residue R-2]. Prefix
   non-saturation: the only proper prefix is the root state, non-saturated
   by item 3. So REALIZED(f, [ν̂₁]).
6. *Clause (ii) at k = 1.* The state key is ν̂₁'s produced key ((R4), (M4)),
   which by (P-KEY) equals Lift₁(Θ(𝐇)) (the formal datum (ψ̂₀; λ₁, ψ̂₁) —
   fields matched in item 4). Valuation/shear/tower: the §1.1 recursion over
   the matched records ((M4)), = the level-2 stage's [F.0] data over Θ(𝐇)
   under (FR≡)'s frame clause. Window width = μ₁ (§1.4). ∎(base)

**Step (k → k + 1, k ≥ 1).** Let 𝐇′ = (𝐇; ν_{k+1}) satisfy the hypotheses
at length k + 1. Cons_f and the interior scoping restrict to the prefix 𝐇
((C4) is per-level; μ_i ≥ 2 for i ≤ k holds in 𝐇′ already), so the IH
applies to 𝐇: M_𝐇 exists with π(M_𝐇) = 𝐇, REALIZED(f, M_𝐇), and clause
(ii) at k. NOTHING about N is assumed or used (V27 findings 3e/5: the
induction carries no working level).

1. **Frames and GMN objects.** By IH (ii), o_𝐇's frame is the [F.0] stage
   frame over c := Θ(𝐇), with key Φ̂_{k+1} = Lift_k(c). OL-1 (cumulative
   reading) grants the GMN interpretation: ι(c) = t^{(k)} is a genuine type
   chain with representative φ_{k+1} = Lift_k(c), so N_{k+1}(f) and the
   residuals R_λ(f) — the objects (c1)/(c2) speak of — are well-defined
   w.r.t. exactly the state key. By (FR≡) at o_𝐇 (its frame clause holds by
   IH (ii)), the state's development polygon, face residuals, and harvested
   records ARE the level-(k+1) stage read's objects over (f, c).
2. **The semantic pair is on the menu (the width tie, repaired).**
   Cons_f(𝐇′) (c1) gives the side S_{k+1} of N_{k+1}^−(f) of slope
   −h_{k+1}/e_{k+1} < 0 with d(S_{k+1}) = ℓ_{k+1} and the recorded initial
   point; (c2) gives ord_{ψ̂_{k+1}}(R_{λ_{k+1}}(f)) = μ_{k+1}. By FULL OL-2
   clause (b) at the stage read over (f, c) [c is Cons_f-consistent of order
   k ≥ 1 — its setting; OL-1 for well-definedness], the stage window polygon
   of f EQUALS N_{k+1}(f) as subsets of ℝ², vertex for vertex and side for
   side; by (FR≡) the machine's full development polygon at o_𝐇 is that
   stage polygon. So S_{k+1} is a face of the machine's FULL polygon with
   strictly negative slope — a principal face. By Lemma WGEO(c) at o_𝐇
   [hypothesis: the creating read ν̂_k satisfies (R1) at all slots and (R2)
   at its strides on f — supplied by REALIZED(f, M_𝐇), "every REALIZED
   state qualifies"; status: modulo (V1)/(V2) beyond the proved slice], the
   principal part of the full polygon COINCIDES with the window hull (slots
   ≤ W_{o_𝐇} = μ_k, the width by IH (ii)) — so S_{k+1} is a face of the
   WINDOW hull. No width-indexed dictionary clause is invented: the tie is
   the home-stated whole-polygon identity OL-2(b) (advertised by O-2a rev 5
   to exactly this consumer) plus the machine-side WGEO(c) (V27 finding 1).
   Residual: by FULL OL-3 at the same stage read, R^nrm = c′·R_{λ_{k+1}}(f)
   (c′ ∈ F_{k+1}^×) with equal factor multisets and multiplicities; by
   (FR≡)/[F.2] the machine residual of the face S_{k+1} is that R^nrm over
   the SAME constructed tower F_{k+1}. Hence ψ̂_{k+1} is a monic irreducible
   factor of the face's machine residual with exact multiplicity μ_{k+1}:
   (S_{k+1}, ψ̂_{k+1}) is a candidate pair at o_𝐇.
3. **Non-halting, harvest, and the FIELDWISE record match.**
   (a) o_𝐇 is NON-SATURATED by the record-only route: IrrHalts(M_𝐇) ⟺
   μ̂_k = 1 (§1.4's displayed equivalence via the key-degree identity), and
   μ̂_k = μ_k ≥ 2 by the IH's fieldwise projection plus W3 in 𝐇′. (No
   semantic saturation display is consumed — the rev-1 Theorem 2(B) detour
   is dropped; V27 finding 3d.)
   (b) o_𝐇 is NOT NS-HALTED, definitionally: step 2 exhibited a principal
   window face, and NsHalts(o_𝐇, f) says there is none. ((M6c)(ii) is NOT
   consumed for this — V27's row-10 mislocation is moot.)
   (c) o_𝐇 is REALIZED (IH) and non-halted, so (M6a) harvests ALL candidate
   pairs, among them (S_{k+1}, ψ̂_{k+1}). Set ν̂_{k+1} := its harvested
   record, M_{𝐇′} := M_𝐇·ν̂_{k+1}. The harvested window data are read off
   f by construction; the vertex pair is well-defined with the (N4)-upper by
   Corollary VTX [(V1)/(V2) at order ≥ 1 — displayed grade].
   (d) FIELDWISE match π(ν̂_{k+1}) = ν_{k+1} — the construction precedes any
   recovery talk, and each 𝔈-field is matched with a named source (V27
   finding 2a's requested display). Via (FR≡), ν̂_{k+1}'s emitted record IS
   the stage read's emitted record at the side S_{k+1} with selected factor
   ψ̂_{k+1}; a polygon has at most one side of a given slope, so "the
   corresponding side" in OL-2's clauses is S_{k+1} itself. Then: (e, h, ℓ)
   = S_{k+1}'s lowest-terms slope pair and degree [OL-2(c)] =
   (e_{k+1}, h_{k+1}, ℓ_{k+1}) [(c1)]; (s, u) = S_{k+1}'s initial point in
   the order-(k+1) INTEGER frame [OL-2(d), the positional transport] =
   (s_{k+1}, u_{k+1}) [(c1)'s intrinsic positional clause]; sel: the factor
   is ψ̂_{k+1} by the choice of pair (same tower, [F.2]), with machine
   multiplicity = ord_{ψ̂_{k+1}}(R^nrm) = ord_{ψ̂_{k+1}}(R_{λ_{k+1}}(f)) =
   μ_{k+1} [OL-3's scalar preserves multiplicities + (c2)], and g = deg
   ψ̂_{k+1} = g_{k+1}; inc = [e·g ≥ 2] on both sides (species law / W2);
   dressing equal by choice. Every field of the 𝔈-node is covered; Lemma R
   is NOWHERE invoked in this match.
4. **REALIZED(f, M_{𝐇′}).** READ: the prefix reads by IH; the new read's
   window clauses by the harvest construction ((M6a)); (R1) beyond the
   window by (M6c)(i) at o_𝐇 [= WGEO(d) at non-root states; displayed
   grade]; (R5) by (M6b)(i)/Corollary VTX. LAWFUL: (N1)–(N3) displayed at
   harvest; (N4)-upper VTX; (N4)-lower and AUX by (M6b)(ii−)/(iii) [residue
   R-2]; AUX prefix closure (§1.2). Prefix non-saturation: the IH's prefixes
   plus step 3(a) at o_𝐇. So REALIZED(f, M_{𝐇′}), and π(M_{𝐇′}) = 𝐇′ by
   IH + step 3(d) — clause (i) at k + 1.
5. **Clause (ii) at k + 1.** The state o_{𝐇′}'s key is ν̂_{k+1}'s produced
   key ((R4), (M4)); by (P-KEY) and step 3(d)'s formal fields it equals
   Lift_{k+1}(Θ(𝐇′)). Valuation/shear/tower: the §1.1 recursion over
   M_{𝐇′}'s records ((M4)) — the [F.0] stage data over Θ(𝐇′) under (FR≡)'s
   frame clause. Window width = μ_{k+1} (§1.4's definition at the last
   read's multiplicity, = the matched μ_{k+1}). NO run-decomposition lemma
   is consumed: OL-6 appears nowhere (V27 finding 2b — rev 1's "OL-2a-6(b)
   at level k + 2" is deleted, not relocated). ∎

## 4. Interior adequacy, the leaf split, and the global read-back

**Corollary CU-1-ADEQ (interior adequacy; per step, rescoped — V27 finding
6a).** Let 𝐇_{≤i} (i ≥ 0) be a well-formed all-continuing Cons_f prefix with
a₀ ≥ 2 and every node non-complete, and let (S, ψ) be a GMN child of
t^{(i)} = ι(Θ(𝐇_{≤i})) in t_{i+1}(f) — a (side of N_{i+1}^−(f),
monic irreducible factor of R_λ(f)) refinement, λ := the side's slope — that
is INTERIOR: μ := ord_ψ(R_λ(f)) ≥ 2. CONSTRUCT the node ν(S, ψ) by the
displayed formulas (these are Lemma R's recovery formulas USED AS
DEFINITIONS — the construction precedes and replaces any appeal to recovery,
V27 finding 6b):

    (e, h) := the lowest-terms pair of −λ;   ℓ := d(S);
    (s, u) := the initial point of S in the order-(i+1) integer frame;
    sel := (deg ψ, μ);   inc := 1 iff e·deg ψ ≥ 2;   dressing ψ̂ := ψ.

Then (𝐇_{≤i}; ν(S, ψ)) is a well-formed all-continuing Cons_f chain with
every node non-complete, and Theorem CU-1 realizes it (M exists, REALIZED on
f); for N ≥ L(M), CU-1-LVL makes the walk on f_N visit its state. Checks,
clause by clause: Cons_f — (c1) at level i + 1 asks exactly that S be a side
of N_{i+1}^−(f) with the recorded slope/degree/initial point, and (c2) that
ord_{ψ̂}(R_λ(f)) = μ: both hold by construction (the hypothesis IS the
data). Well-formedness — domains: s, u ∈ ℤ_{≥0} ((L2)-nonnegativity of v_i
on integral polynomials, the (C1) note); μ·g ≤ ℓ since μ·deg ψ ≤
deg R_λ(f) = d(S) = ℓ ((L3)/Def 2.21: the residual's degree is the side
degree, cf. (D3)'s "d = ℓ"); W1: if ℓ = 1, e ≥ 2 then e·g ≥ 2 forces
inc = 1 by the construction; if ℓ = 1, e = 1 then μg ≤ 1 with μ ≥ 1 forces
g = 1, so inc = 0; W2 by construction; W3: interior nodes of the extension
are 𝐇_{≤i}'s (given non-complete) — ν is last; W4: ψ̂ = ψ is monic
irreducible, and ψ ≠ z because R_λ(f) is never divisible by y ((L3), as
displayed in O-2a's OL-3 note); W5: ν is continuing. Non-completeness of the
last node is the hypothesis μ ≥ 2. Conversely, every all-continuing Cons_f
extension of 𝐇_{≤i} by one node arises this way from its own (S, ψ) —
(C4) is definitionally two-sided once OL-1 grants well-definedness (a
polygon has at most one side per slope, so the side is pinned; the fields
are then forced by (c1)/(c2) + W2). Canonicity remark (the ONLY Lemma R
use): the constructed chain is recoverable from (f, Θ), so nothing here
depends on a choice. ∎

**The split (no gap, no overlap — displayed).** Every GMN child (S, ψ) of a
non-complete t^{(i)} has μ = ord_ψ(R_λ(f)) ≥ 1. Exactly one of:

* **μ ≥ 2 (interior child):** covered by CU-1-ADEQ above — realized as an
  interior state of the walk.
* **μ = 1 (complete child = LEAF):** by O-2a Theorem 2(B)'s displayed
  biconditional (accE·accF = deg f_{t} ⟺ μ = 1; and at μ = 1 the cluster
  factor is irreducible), the child type is COMPLETE — a leaf of the
  semantic tree, singling out one irreducible factor of f. CU-1 claims
  NOTHING about it. Its coverage is counting-forced at the leaf level:
  O5triple Theorem B (β_g : leafslots(T) → leaves(𝒯(g)) is a bijection —
  injectivity (I-2), surjectivity forced by the two checksums; that brief's
  headline sharpening: "D-7b consumes NO no-missing clause") and Theorem
  D(b) (= D-7b), at their own displayed conditionality ((I-1)–(I-3)). This
  is a ROUTING statement — the two results are not merged, and CU-1 consumes
  nothing from O5triple; jointly the two theorems cover ALL GMN children:
  the cases μ ≥ 2 / μ = 1 are exhaustive (μ ≥ 1 always) and disjoint.
* Terminal machine records (sel = ⊥) correspond to NO GMN child — Cons_f
  constrains no terminal field (Lemma R's displayed non-claim); the
  verdict-carrying terminal seam is CU-2t's unit, not CU-1's.
* **Depth-0 boundary (a₀ = 1 — routed at rev 4, P2 F-5):** a root-level
  SIMPLE irreducible factor ψ̄ of f̄ (multiplicity a₀ = ord_{ψ̄}(f̄) = 1)
  is complete at depth 0: it heads NO track and is a child of NO type, so
  it lies outside this split's domain (children of a non-complete t^{(i)})
  and outside every CU-1 route (all displayed routes hypothesize a₀ ≥ 2 —
  the theorem, ADEQ, SURJ). Its coverage is the SAME routing target at its
  HEN slot: in O5triple's semantic tree (Definition 𝒯(g), §3 there) the
  root child at a multiplicity-1 factor is a **hen leaf**; the slot domain
  leafslots(T) = hen slots ⊎ irr slots includes the hen slots, (I-1)(b)'s
  first clause transports "hen slot at ψ̄ ↦ the hen leaf at ψ̄", and
  Theorem B's bijection + Theorem D(b) cover these leaves with all others,
  at the same conditionality ((I-1)–(I-3)). CU-1 consumes nothing from
  this routing. (Machine-side, the a₀ = 1 factor is exactly the (τ-hen)
  certification that base item 3 excludes at a₀ ≥ 2; downstream, Dfloor's
  (C2) (τ-hen) convention consumes its verdict δ_{(1, deg ψ̄)} — the
  density layer, not this coverage claim.) The split's coverage claim thus
  reads, displayed: over children of non-complete types, μ ≥ 2 / μ = 1 is
  exhaustive and disjoint; jointly with the hen-leaf routing, every
  irreducible-factor slot of f — depth-0 hen leaves included — is covered
  by exactly one of CU-1-ADEQ (interior) or O5triple's Theorems B/D(b)
  (leaf: μ = 1 children AND a₀ = 1 hen leaves).

**Corollary CU-1-SURJ (read-back — stated GLOBALLY, V27 finding 6c).**
Quantifying over ALL interior refinement paths of f simultaneously: for
every k ≥ 0 and every path ρ₀ → (S₁, ψ₁) → ⋯ → (S_k, ψ_k) of GMN children
with a₀ = ord_{ψ̂₀}(f̄) ≥ 2 and every step interior (each μ_j ≥ 2), the
chain built by iterating CU-1-ADEQ's construction is a well-formed
all-continuing non-complete Cons_f chain, Theorem CU-1 realizes it on f, and
the walk on f_N visits its state whenever N ≥ L(M). This IS a global
quantification over the chains of f at once — rev 1 called it "per site",
which understated it. Its dependencies, split by clause (V29: rev 2 said
"exactly CU-1 + ADEQ", which understated the walk clause): the chain
construction and the realization on f are exactly ∀-instances of Theorem
CU-1 and Corollary CU-1-ADEQ (induction on path length; no input beyond
theirs); the walk clause is the ∀-instance of Corollary CU-1-LVL, and so
additionally consumes LVL's whole displayed bundle — D-14, Lemma REAL≡ with
(M6a)–(M6c) at their grades, the §1 box/decode display, (N\*-MAJ)
whenever the level is taken from N\*, and the L(H)/NAT/CEIL ceiling facts
(rows 7–11, 15–18, 22, 30 — row 17 because (M4) is consumed inside D-14's
application, row 30 = L(H)/NAT/CEIL; corrected at rev 4, P2 F-1; nothing
beyond LVL's own proof). Non-claims, displayed: no leaf statement (the split above), no
statement across lifts or boxes (D-15 owns cylinders; the only box object
anywhere is CU-1-LVL's f_N), no canonical tree object and no tree
isomorphism (the V21-5 object stays deleted). ∎

## 5. The consumption map (every input, its clause, its status)

| # | input | consumed at | status (home) |
|---|---|---|---|
| 1 | OL-1 (GD-1) | step 1 (ι, representative well-definedness); ADEQ converse | OPEN (O-2a rev 5 §4; cumulative reading) |
| 2 | **OL-2 clauses (b)/(c)/(d)** (of the FULL OL-2 (a)–(d), GD-2) | step 2 ((b): whole-polygon identity — the width tie's semantic half); step 3(d) ((c)/(d): emitted side fields + positional transport). Clause (a) (the valuation tie u_{i+1} = v_{i+1}) is consumed by NO sentence of this brief — dropped from this row at rev 3 (V29 finding 4a); it stays part of the home lemma, whose full-form advertisement this unit still cites | OPEN; the full form is advertised at home to exactly this consumer (rev-5 §4 "the O-3 design seam") — rev 1 under-cited OL-2-min (repaired at rev 2); rev 2 over-listed (a) (repaired at rev 3) |
| 3 | **FULL OL-3** (GD-3) | steps 2, 3(d) (residual identity ⟹ factor/multiplicity transport). ALSO cited at ADEQ's W4 check (rev-3 location record, V29 finding 4b) — but there ONLY as the home DISPLAY SITE of (L3)'s GMN-side fact y ∤ R_λ(f) ("as displayed in O-2a's OL-3 note"); the consumed fact is row 25's, and no OPEN content of OL-3 enters §4 | OPEN; same advertisement (shared with the O-9 leaf) |
| 4 | O-2a Thm 1 — (c0), cases, **(D3)** | base k = 0, k = 1 (the order-1 objects/formulas; (FR≡)'s PROVED order-1 instance) | PROVED (O-2a, confirmed lineage) |
| 5 | O-2a Thm 2(B) | §4 split ONLY ((B)'s biconditional: complete ⟺ μ = 1, for the leaf routing). NOT consumed in the step (rev-2 drop). Thm 2(A) DROPPED ENTIRELY at rev 3 (V29 finding 4e: rev 2 listed it for "placement/non-completeness vocabulary" but no sentence of §§2–4 uses it — the placement content those sentences do use is OL-1's well-definedness grant (row 1) plus (C4)'s own clauses, which are the theorem's HYPOTHESIS vocabulary (§0′), not a consumed result) | conditional [Cons_f + OL-1], displayed |
| 6 | Lemma R | §2 scope note (3) + §4 canonicity remark + §4 split's terminal bullet (the displayed NON-claim "Cons_f constrains no terminal field", cited as the warrant for the terminal routing — third site recorded at rev 4, P2 F-4) — produces and identifies NOTHING | PROVED (O-2a) |
| 7 | (M6a) harvest totality | base 3/5; steps 3(c), 4 | definitional (O-1thr §2.4) |
| 8 | (M6b)(i) + (ii)-upper via Corollary VTX | base 5; steps 3(c), 4 ((R5) well-defined, (N4)-upper) | PROVED at the root/degree-1 slice; modulo (V1)/(V2) beyond |
| 9 | (M6b)(ii)-lower + (iii) AUX | base 5; step 4 (LAWFUL); CU-1-LVL (inside REAL≡'s bundle) | OPEN (interface residue R-2) |
| 10 | (M6c)(i) | base 5 (= ROOT-M at the root); step 4 (= WGEO(d)) | PROVED at the displayed slice; modulo (V1)/(V2) beyond |
| 11 | (M6c)(ii) | CU-1-LVL ONLY (inside REAL≡'s hypothesis bundle) — NOT consumed for non-halting (rev-2 relocation per V27) | same status |
| 12 | Lemma ROOT-M | base k = 1 items 2, 5 (window confinement; beyond-window (R1)) | PROVED (O-1thr, displayed proof) |
| 13 | Lemma WGEO (c)/(d) | step 2 ((c): principal part = window hull — the width tie's machine half); step 4 ((d) via (M6c)(i)) | PROVED at the degree-1 slice; modulo (V1)/(V2) beyond |
| 14 | (V1)/(V2) key compliance | inside rows 8, 10, 11, 13 at order ≥ 1 | OPEN (named assumption; gated at order 2 by §7's T-G — SURVIVED) |
| 15 | Lemma REAL≡ | CU-1-LVL only (⟸ direction, on f_N) | PROVED conditional on (M6a)+(M6b)+(M6c) |
| 16 | O-1thr Thm 1 (D-14) | CU-1-LVL only — ONE application at the top site | PROVED OUTRIGHT machine-side (rev 4; pass 4 pending) |
| 17 | (M4) frame/record functionality | clause (ii) (base 6, step 5); step 1; inside D-14 | definitional (O-1thr §2.4) |
| 18 | O-1thr §1.4 definitional bundle: state/window-width defs, IrrHalts ⟺ μ_last = 1 (via the key-degree identity), NsHalts, candidate pairs, species law; §1 box/decode display | base k = 0 (track/root-state existence + §1.4 root initialization — site added at rev 4, P2 F-3); base 3 (root non-saturation, a₀ ≥ 2 vs τ-hen); step 3(a)/(b); clause (ii) widths; π's fields; CU-1-LVL's f_N | displayed definitions + the PROVED key-degree identity |
| 19 | **(P-ROOT)** | base k = 0, k = 1 item 1 | DECLARED pin (§0′); definitional under the shared-source reading |
| 20 | **(P-KEY)** | base 6; step 5 (clause (ii) key binding) | DECLARED pin (§0′); OPEN as a transcription obligation (R-6) |
| 21 | **(FR≡)** (both displayed clauses) | step 1, 2, 3(d) (polygon/residual/record identification — incl. base item 4/step 3(d)'s stage-record match, where the rev-4 π re-cite relocated the load, P2 F-7); clause (ii) frame clause (= the SECOND displayed clause (FR≡-frame), §0′ — displayed as assertible pin content at rev 4, P2 F-6). §0′ (π)'s DEFINITION no longer cites (FR≡) at all (field presence is §1.2, row 33 — one pin site DELETED at rev 4) | order 1: PROVED ( = (D3) by inspection, both clauses); order ≥ 2: DECLARED pin, OPEN (R-6); slot-fresh reading REFUTED by §7.2 |
| 22 | (N\*-MAJ) | CU-1-LVL's "in particular" ONLY | displayed hypothesis (§1); holds for the D4R.4/L12 join by construction (R-4) |
| 23 | O5triple Thm B / Thm D(b) | §4 split — ROUTING target only; no clause of any proof here consumes it | its own displayed conditional grade |
| 24 | **(L2)** (GMN Def 2.5/Prop 2.6, O-2a §1's transcription): order-r valuations v_r extend v, values on O[x]∖{0} nonnegative integers | ADEQ well-formedness (domains: s, u ∈ ℤ_{≥0} from (L2)-nonnegativity, with (C1)'s consistency note — row 27). Its order-1 vocabulary appearance at base item 1 rides row 4's PROVED (D3) | literature transcription (GMN arXiv:0807.2620v2), byte-stable at O-2a rev 5, unchallenged V10/V14/V20/P2/V25; cross-package load-bearing (O5triple (L5b′) seam note) |
| 25 | **(L3)** (GMN Defs 2.3, 2.19–2.21, same transcription block): order-r polygon/residual; R_λ(P) never divisible by y | ADEQ: the W4 check (ψ ≠ z since y ∤ R_λ(f) — the fact whose home display site is the OL-3 note, row 3) and, with row 26, the μ·g ≤ ℓ degree bound. Order-1 appearances at base item 1 ride row 4's (D3) | literature transcription, same block/status as row 24 |
| 26 | **Def 2.21** (GMN, inside (L3)'s transcription): the residual polynomial has degree d = d(S) (side degree) | ADEQ: μ·g ≤ ℓ via μ·deg ψ ≤ deg R_λ(f) = d(S) = ℓ (cf. (D3)'s "d = ℓ") | literature transcription (carried inside row 25's block; listed separately per V29 — ADEQ cites it by name) |
| 27 | **(C1)** — the 𝔈-carrier definition: field domains (incl. sel's μg ≤ ℓ constraint), the constructed tower F₁ = F_q[y]/(ψ̂₀), F_{i+1} = F_i[z]/(ψ̂_i), prefix closure, the (s, u)-nonnegativity note | ADEQ well-formedness (the domain checks ARE (C1)'s clauses; the note); the tower cited by [F.2] (row 29) and (FR≡) (row 21); §0′'s π targets its field list | definitional (O-2a §2, rev-2 domain declaration) |
| 28 | **W-laws (W1)–(W5)** (inside (C1)) | theorem statement + step (W3: the interior scoping "for i < k this is W3", the prefix restriction, step 3(a)); π's inc field / base item 4 / step 3(d) (W2 = the §1.2 species-law tie); ADEQ's clause-by-clause checks (W1, W2, W3, W4, W5) | definitional (O-2a (C1) well-formedness laws) |
| 29 | **[F.2]** (stage interface, standalone at rev 3 — V29 finding 4d): the anchor normalization lands R^nrm in F[z] with F IDENTIFIED with (C1)'s constructed F_{i+1}, and the emitted node record carries exactly the 𝔈-node fields | §0′ (π's emitted-record field list); step 2 ("that R^nrm over the SAME constructed tower F_{k+1}"); step 3(d) ("same tower, [F.2]") | displayed stage-interface definition (O-2a [F.0]–[F.2]); consumed independently where the TOWER/field-list identification is the content — its machine-side instantiation at orders ≥ 2 rides (FR≡) (row 21), at order 1 rides (D3) (row 4) |
| 30 | **L(H) + Lemmas NAT/CEIL** (O-1thr §3, NEW row at rev 4 — P2 F-1): L(H) := 1 + max_{i<k} ⌈I_i/E_i⌉; NAT (L(H) ∈ ℕ, ≥ 2 at nonempty H — the modulus p^L well-formed); CEIL (every f-dependent constraint of read i lies at height ≤ I_i, i.e. below level L(H) — the audit is over ALL i < k) | §1 (the displayed MAX form; the prefix-ceiling remark L(M_{𝐇,≤j}) ≤ L(M_𝐇) — a max over a subset); CU-1-LVL (statement's N ≥ L(M_𝐇); proof's "one application suffices" — the single-D-14 argument load-bears on CEIL exactly here); SURJ's walk clause (inside LVL's bundle) | PROVED (O-1thr §3, displayed one-line proofs; carried inside rev 4's PROVED-UNVERIFIED grade, pass 4 pending — not part of its OPEN residue) |
| 31 | **(C4)/Cons_f** — clauses (c0), (c1) (side + intrinsic positional), (c2) (exact multiplicity) (NEW row at rev 4 — P2 F-2; hypothesis vocabulary of the theorem, mapped because the text consumes its structural FACTS) | theorem statement (§2 hypothesis); base k = 0 ((c0)); base items 2, 4 ((c1)/(c2) data); step preamble — THE LOAD-BEARING FACT: (C4) restricts to prefixes (the legality of the IH), which holds by the home definition's own quantifier shape (O-2a rev 5 §2: Cons_f = (c0) ∧ per-i clauses (c1)/(c2) over 1 ≤ i ≤ k′ — a conjunction of per-level clauses, so prefix restriction is verbatim); steps 2, 3(d) ((c1)/(c2) at level k + 1); ADEQ's clause-by-clause checks AND its converse — the second load-bearing fact: (C4) is definitionally two-sided given OL-1's well-definedness grant ((c1)/(c2) at level i + 1 ARE the constructed node's data); §4 split's terminal bullet (Cons_f constrains no terminal field — the home definition's displayed non-constraint line, shared with row 6's non-claim) | definitional (O-2a rev 5 §2 (C4)); the per-level display is the home definition's own shape, NOT a new lemma — no dependence added |
| 32 | **Θ = (C3)** (the dictionary; NEW row at rev 4 — P2 F-2): total, truncation-compatible re-indexing of the continuing part | clause (ii)'s statement (Lift_k(Θ(𝐇))); §2 scope note (3) + §4 canonicity remark ((f, Θ(𝐇)) recovery vocabulary); step 1 (c := Θ(𝐇)); base 6 / step 5 (Θ(𝐇), Θ(𝐇′) as Lift arguments); ADEQ (ι(Θ(𝐇_{≤i}))); §0′ (FR≡-frame)'s (f, Θ(𝐇)) | definitional (O-2a rev 5 §2 (C3); truncation-compatibility is the displayed home property that makes the step's prefix use legitimate). Lift itself rides rows 19/20's (C2)-pinned displays |
| 33 | **O-1thr §§1.1–1.3 definitional bundle** (NEW row at rev 4 — P2 F-3): §1.1 the frame recursion (Φ_i, w_i, K_i over records + policy); §1.2 the node-record field list, node laws (N1)–(N4), AUX prefix closure, and the home-DISPLAYED fact that harvested records satisfy (N1)–(N3) (inside O-1thr's (M6b) display: (N1) read off the face, (N2)/(N3) via Lemma POS — NOT part of the (M6b)(ii)-lower/(iii) OPEN residue); §1.3 READ (R1)–(R5), LAWFUL = CORE ∧ AUX, REALIZED | §0′ (π's field presence — the rev-4 re-cite, P2 F-7); §2 statement (REALIZED's displayed sense); base 5 / step 4 ((N1)–(N3) at harvest; AUX prefix closure; the (R1)–(R5)/LAWFUL unpacking); base 6 / step 5 + clause (ii) (the §1.1 recursion over the matched records); CU-1-LVL (REALIZED's definition at the top site) | displayed definitions (O-1thr §§1.1–1.3) + the home-displayed harvest facts; the OPEN parts of the (M6b) block stay on row 9 — nothing OPEN rides this row |

Exhaustiveness claim (precise form, V27 finding 4; row set rebuilt at rev 3
per V29 finding 4 and completed at rev 4 per P2 F-1/F-2/F-3): every input
consumed by any sentence of §§2–4 appears in a row above, and §0′'s π
definition (pulled into scope by clause (i)) is covered by rows 27, 29, 33.
The O-1thr side, with the corrected assignment (P2 F-3): row 33 carries the
§§1.1–1.3 bundle (the frame recursion, the node field list + laws +
AUX prefix closure + the (N1)–(N3)-at-harvest display, READ/REALIZED); row
18 carries the §1.4 bundle (states, windows, halts, candidate pairs,
species law — now including the base-k=0 root sites) + the §1 box/decode
display + the PROVED key-degree identity; row 30 carries §3's ceiling
(L(H), NAT, CEIL); rows 7–11, 13, 15–17 the interface and lemma citations.
The O-2a side: rows 24–29 (rev 3) cover (L2)/(L3)/Def 2.21, the (C1)
carrier with its W-laws, [F.2]; rows 31–32 (rev 4) cover (C4)/Cons_f and
Θ — the theorem's own hypothesis vocabulary, mapped because the text
consumes its structural facts (prefix restriction; two-sidedness; the
terminal non-constraint). The remaining rows are the substantive
citations, each with its locations audited against the text. In
particular: OL-2 is consumed ONLY at clauses (b)/(c)/(d) (row 2 — clause
(a) is consumed NOWHERE); O-2a Thm 2(A) is consumed NOWHERE (dropped at
rev 3 — row 5); NO OL-4, OL-5, OL-6 (dropped at rev 2 — §0); NO
SPAN; NO O-2b/OB1/F6′ face; NO cross-polynomial statement; NO global
adequacy; NO mutual induction (Theorem 2(D)'s induction lives inside O-2a =
CU-2 and is not consumed here at all); and π's definition consumes NO pin
(the rev-4 re-cite — (FR≡) fires only at row 21's sites, where clause (ii)
supplies its hypothesis).

## 6. Honesty ledger (what CU-1's acceptance would and would not mean)

**Proved here:** the N-free induction of §3 and the three corollaries — i.e.
that the DISPLAYED inputs of §5 compose, with no unbound chain parameter, no
halting-guard circle, no box-keyed quantifier, no global adequacy object,
and no working-level leakage into the induction. That is the whole claim.

**Open residue (owners named; deltas vs rev 1 flagged):**

* **R-1 (dictionary):** OL-1 + FULL OL-2 + FULL OL-3 — the GD campaign owns
  them (GD-1/2/3). DELTA vs rev 1: the full forms replace the min cores
  (findings 1/2a); this is the consumption O-2a rev 5 already advertises to
  this seam, so the RESIDUE these lemmas represent is unchanged at home —
  but CU-1's conditionality is now on the stronger, home-stated forms.
* **R-2 (machine interface):** (M6b)(ii)-lower, (M6b)(iii) AUX, (V1)/(V2)
  beyond the proved slice — O-1thr's displayed residue, unchanged.
* **R-3 (verification states):** O-1thr rev-4 pass 4; O-2a rev-5 pass 2;
  D-14 r2 — CU-1's grade rises only as those land.
* **R-4 (cluster seams):** the exact N\* definition and (N\*-MAJ)'s
  discharge (D4R.4/L12/TB-CAP), consumed only via §1's displayed inequality.
* **R-5 (scope):** complete-child/leaf coverage = O5triple Theorem B (§4
  split); terminal seams = CU-2t; box-level lift uniformity = D-15. CU-1
  neither states nor needs them.
* **R-6 (NEW at rev 2 — the declared pins):** (P-KEY) and (FR≡) at orders
  ≥ 2 (with (P-ROOT), definitional). These are cross-artifact identification
  clauses between the two abstractions of the ONE engine — the state-level
  content of OL-6's stage-birth route, declared instead of the run-level
  OL-6 (finding 2b). Owner: the MOVES §B2-DEF transcription / GD-6 family.
  They are NOT new mathematics about polygons or residuals; their refutable
  order-2 content is pinned and gated by §7 (the coherent-convention
  finding), and rev 1 consumed the same content SILENTLY — rev 2's honesty
  delta is the declaration, not the dependence.

## 7. Falsifier record (run FIRST, before rev 1; carried unchanged)

### 7.1 The primary gate: T-G at depth 3 (order-2 states) — SURVIVES

`verification/openmath/o1thr_depth3_check.py` (full spec in its docstring),
extending the T-F depth-2 harness to ORDER-2 STATES: root read (depth-1
site) + window-hull read (depth-2 site, residual over K₁ = 𝔽_p[z]/ψ(z)) +
the order-2 frame w₂ = MacLane composite, the standard level-2 key Φ₂ built
from the harvested ψ₁, and the FULL Φ₂-development geometry — exactly the
per-site kernel CU-1's step consumes where it is weakest ((V1)/(V2) at
level ≥ 1; O3adj §3.4's charge). Checks T-G.0–T-G.6 cover: (R1)-support,
WGEO(a) display, (V2b) at f, the WGEO(b) vertex law (first attainment at
μ₁ + the VTX pin), (M6c)(i)/(ii) at o₂, the VTX chain with (V2b)-at-level-1,
DIRECT (V1) multiplicativity probes on product pairs, and DIRECT (V2b)
development-identity probes.

Run 2026-07-31, this machine, exact integer arithmetic (tracked record:
`verification/openmath/results/o1thr_depth3_run_20260731.txt`; raw log
`logs/o1thr_depth3_run_20260731_151242.log`), configs (p, n, M) =
(2,4,4), (3,4,3), (2,6,3), (3,3,4), (2,6,4), (2,8,3):

    470,736 order-2 instances — ZERO violations of all nine checks.
    Coverage: 122,577 with beyond-window slots (the (M6c) content is
    non-vacuous); 10,935 growth steps (e₁g₁ ≥ 2); 16,472 extension-field
    parents (g ≥ 2, residuals over 𝔽_{p^g}); 2,091 children with g₁ ≥ 2;
    saturated parents included (laws are state-hypothesis-free at rev 4).

**Verdict: the gate SURVIVES; CU-1's spec dispatch is licensed (O3adj §3.5
step order).**

### 7.2 The gate's own countermodel finding (independent value, GD-3)

The checker's FIRST version normalized level-1 residues per-slot
("fresh-t₀", no coherent monomial march). Under that reading the vertex law
FAILS: first countermodel f = X³+3X²+3X, p = 3, depth-1 site
(e, h, ψ, μ) = (2, 1, z+1, 1), face (0,4)–(1,3) — naive selects ψ₁ = z′+2
whose standard lift X²+6X+3 is a NON-improving recentering (v(Φ₂(θ)) = 3/2,
no gain), while the coherent (anchored-march) convention selects ψ₁ = z′+1
whose lift X²+3X+3 is the TRUE ℚ₃-factor. Final tally: 1,827 instances
where the readings differ, 1,818 naive vertex-law refutations — ALL at
p = 3 with g = 1 in these configs, i.e. exactly where ȳ ≠ 1 (at p = 2,
g = 1 the twist unit ȳ = 1 makes the two readings coincide — the naive
reading is INVISIBLE there). Consequences: (a) the pinned convention for
order-2 residual reads must carry the coherent slot normalization (the
"recorded unit normalization" of (R2)/(R5) made concrete — the machine
countermodel that shapes GD-3's slot-twist/z-power clause); (b) any
GD-3/OL-3 statement or Lean transcription that normalizes residues
slot-fresh is REFUTED at order 2. Also reported: the naive mixed-units
order-2 (N4)-lower comparison w₁(D_{μ₁}) ≥ u_{k₁} fails in 470,057 of
470,736 instances — the order-2 lower band must NOT be stated that way
(statement-shaping datum for (M6b)(ii) at depth).

### 7.3 Standing suites (unchanged, still green)

T-A..T-D, T-E, T-F re-run unchanged earlier this cycle (O-1thr rev-4
record): ALL PASS. G-EMIT/U6 remain OL-6's falsifiers (O-2a rev-4/5 note);
CU-1 rev 2 no longer consumes OL-6, so no obligation moves.

### 7.4 Rev-2 falsifier accounting (why no new gate is owed)

Rev 2's changes are quantifier plumbing (the N-free restructure; the
fieldwise match; the ADEQ split and SURJ restatement) plus two kinds of
input change: (a) widened citations — full OL-2/OL-3 in place of the min
cores; their order-2 refutable content (polygon identity geometry, residual
normalization, vertex/attainment laws) is what T-G.1–T-G.6 already probe on
the machine side, and their GMN-side identities are GD-2/GD-3's open
content, unchanged in kind; (b) the DECLARED pins (P-ROOT)/(P-KEY)/(FR≡) —
(FR≡)'s residual clause is exactly the convention the §7.2 finding forced
and the checker pins (the slot-fresh alternative is refuted 1,818 times),
so the pins' checkable order-2 shadow is already exercised and adversarially
shaped by the existing harness. No new per-site law is introduced anywhere;
the falsifier-first obligation for rev 2 is discharged by the standing
suites plus this mapping.

## 8. Verification checklist (where to press hardest)

1. **N-freeness of §3:** does any sentence of the base or step consume a
   working level, a box, or a decode? (The rev-2 structural claim; V27
   finding 3e's cure. CU-1-LVL should be the ONLY consumer of D-14, REAL≡,
   f_N, and (N\*-MAJ).)
2. **The width tie:** step 2's chain is OL-2(b) [stage polygon = N_{k+1}(f),
   whole polygon] + (FR≡) [machine polygon = stage polygon] + WGEO(c)
   [principal part = window hull]. Check no residual width clause is
   consumed beyond these, and that WGEO's hypothesis is supplied by the IH
   as claimed.
3. **The fieldwise match (step 3(d), base item 4):** is every 𝔈-field
   covered with a correct source, and does any field secretly need Lemma R
   or an unstated uniqueness? (The side-per-slope uniqueness used is the
   displayed polygon fact.)
4. **The pins:** are (P-ROOT)/(P-KEY)/(FR≡) consumed anywhere BEYOND their
   §0′ displays (especially: does anything use (FR≡) at a state whose frame
   equality is not first supplied by clause (ii))? Is the order-1 "= (D3) by
   inspection" claim actually inspection-grade against O-1thr §1.1 and O-2a
   §3?
5. **Full OL-2/OL-3 consumption:** check the consumed clauses against O-2a
   rev 5 §4 verbatim — no clause wider than (a)–(d) resp. the displayed
   residual identity; and check the home advertisement ("consumer: the O-3
   design seam") matches this unit's role.
6. **Saturation/halting routes:** step 3(a)'s record-only route (key-degree
   identity ⟹ IrrHalts ⟺ μ_last = 1) and base item 3's root display —
   any leftover semantic saturation dependence?
7. **CU-1-LVL:** is ONE D-14 application at the top site really sufficient
   (does REALIZED at the top site quantify over all prefix reads, and is
   L(M) ≥ every per-read ceiling by Lemma CEIL — now mapped, row 30)? Is
   f_N's monicity/degree display faithful to O-1thr §1?
8. **The ADEQ split:** exhaustive and disjoint (μ ≥ 2 / μ = 1 / sel = ⊥)?
   Does the well-formedness check of the constructed node really need no
   OL-4 (each W-law is discharged by a displayed argument)? Is the μ = 1
   routing honest about O5triple's conditionality?
9. **CU-1-SURJ:** is the global statement really the displayed ∀-composition
   — CU-1 + ADEQ for construction/realization, CU-1-LVL (with its bundle,
   rows 7–11, 15–18, 22, 30) for the walk clause, and NOTHING more (no
   hidden tree object, no leaf claim, no box object beyond LVL's f_N)?
10. **Quantifier audit of §2:** any secretly box-keyed or ∀-lift clause?
    (The V16/V21 kill class; §6 and the scope notes claim not.)
11. **Gate adequacy:** does §7.4's mapping of the rev-2 deltas onto T-G
    hold up — in particular, is (FR≡)'s order-2 content really the pinned
    convention the harness tests? Named residue: T-G probes the
    standard-lift policy on the degree-1 root slice; general-d₀ root keys
    and non-standard compliant policies remain outside the numeric
    perimeter (as at T-E/T-F).

— CU-1 rev 4 complete. PROVED-UNVERIFIED (conditional composition, §5
grades) until hostile passes accept it. Verification lineage: V27 on rev 1
= UNSOUND (structural repair → rev 2); V29 on rev 2 = SOUND-WITH-GAPS
(consumption accounting → rev 3); PASS 2 on rev 3
(`CU1_pass2_fable_verify.md`) = SOUND-WITH-GAPS, 0 critical / 7 gaps, all
consumption-accounting/display class, repaired above (§0-R4) — per the
ledger's 2026-08-02 CORRECTION entry
(`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`), CU-1's status is
ZERO-CRITICAL-PASS-2 WITH GAP DEBTS until a gap-check pass accepts these
rev-4 repairs; VERIFIED is NOT claimed. Primary gate SURVIVED (§7,
carried); falsifier accounting §7.4 carries (rev 4, like rev 3, adds no
input and no mechanism — rows 30–33 and the two §0′ display repairs
expose inputs and pin content the text already consumed).
