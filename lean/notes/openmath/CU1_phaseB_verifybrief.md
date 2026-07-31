# CU-1 (K-RUN-C composition, unit NM) — no-missing + interior adequacy + state binding — verify brief, rev 1 (Fable, 2026-07-31)

**Unit spec:** `O3adj_adjudication.md` §3.1 CU-1 (ACCEPTED plan; ledger
dbccbc1), cross-read with `SYNTHESIS_PASS4_2026-08-01.md` §2.3 (F2′ as
assembly over the proved O-1thr layer). CU-1 is the K-RUN-C composition's
ONE new proof obligation: an ordinary induction on chain length whose step
is entirely per-site lemmas already stated (and partly proved) elsewhere.
**The primary gate ran FIRST and SURVIVED** (§7: the depth-3 falsifier
`verification/openmath/o1thr_depth3_check.py`, order-2 states, where
(V1)/(V2) are genuinely consumed; plus a checker-convention finding of
independent value, §7.2).

**What this brief claims:** Theorem CU-1 below, PROVED as a conditional
composition — every named input is either (a) proved in its home brief at a
displayed grade, or (b) one of the EXACT open lemmas of the O-2a/O-1thr
residue, consumed by citation with no strengthening. NO new per-site
mathematics is introduced; the unit's content is the induction's quantifier
discipline and the consumption map. **What it does NOT claim:** no box-keyed
universal statement (the V21-1/2 class is structurally avoided: everything
is per-f); no global ADEQ unit (deleted per O3adj — interior adequacy is a
per-step corollary here); no claim that the base packages are verified
beyond their displayed grades.

## 0. Standing setting

f ∈ ℤ_p[x] monic of degree n ≥ 2 with disc f ≠ 0 (the tree §2.4 standing
preconditions — ns-free carriers, pinned F_rep — ride the cluster and are
not re-litigated here); ONE fixed policy 𝒫, standard at degree-1 root nodes
and (V1)/(V2)-key-compliant in the O-1thr rev-4 sense (§5, residue R-2).
Vocabularies imported VERBATIM (statements restated below only where a
clause is consumed; the home briefs are normative):

* **O-1thr machine** (`O1thr_phaseB_verifybrief_rev4.md`): frames w_i /
  keys Φ_i / sheared heights u^{(i)}_j (§1.1); nodes, sites, LAWFUL =
  CORE ∧ AUX with AUX prefix-closed and box-free (§1.2); READ (R1)–(R5)
  and **REALIZED** := READ ∧ LAWFUL ∧ no-proper-prefix-saturated (§1.3);
  states, windows, candidate children, halts (§1.4); interface (M1)–(M6):
  (M4) frame data are record functions; (M6a) harvest totality; (M6b)
  kernel/(iii); **(M6c)** window-harvest completeness (rev-4
  requantification: NO halting hypothesis); Lemmas ROOT-M/VAL1/KEY1/DIV1/
  WGEO, Corollary VTX, Lemma SPAN, **Lemma REAL≡** (execution walk visits
  H·ν ⟺ REALIZED(f, H·ν), given (M6a)+(M6b)+(M6c)); ceiling L(H) (§3);
  **Theorem 1 = the D-14 statement** (lawful-site read locality below
  p^{L(H·ν)}, PROVED OUTRIGHT machine-side at rev 4, pass 4 pending).
* **O-2a dictionary** (`O2a_phaseB_verifybrief_rev4.md`): carriers 𝔈
  (dressed histories) and 𝔗 (formal chains), Θ total and formal, ι the GMN
  interpretation ((C1)–(C3)); **Cons_f** ((C4): per level, the interpreted
  type t^{(i−1)} = ι(Θ(𝐇_{≤i−1})) has a side S_i of slope −h_i/e_i on
  N_i(f) and ψ_i is an irreducible factor of the residual with the recorded
  exact multiplicity); **Lemma R** (on all-continuing Cons_f chains, 𝐇 is a
  function of (f, Θ(𝐇)) — the dressing is PINNED by the formal chain);
  Theorem 1 (order ≤ 1); Theorem 2 (A)/(B)/(C)/(D); the SIX open lemmas
  OL-2a-1..6, in particular **OL-2a-6** (run decomposition + chain binding
  at every level: the j-th emitted record IS the stage read on f over
  c = Θ(𝐇_{≤j−1}), key Lift(c)).

**Grades displayed verbatim (V21-6 discipline; no "proved base"):** O-1thr
rev 4 = PROVED-UNVERIFIED, pass 4 pending; Theorems 2(b)/3 and the §2.5
kernel modulo the displayed residue ((M6b)(iii), lower (N4), (V1)/(V2)
compliance beyond the proved slice). O-2a rev 4 = core thrice-confirmed
(V14/V20/P2) SOUND-WITH-GAPS lineage, pass 2 of the required 2 pending;
Theorem 2(D) conditional on OL-2a-1..6. D-14 pass-1 substantively clean,
r2 pending. CU-1's own grade can never exceed the meet of these.

## 1. The decision level N*(𝐇) — the single consumed property

For a dressed history 𝐇, N*(𝐇) is the per-branch decision level (the
D4R.4/L12 join with the TB-CAP verdict window; rev-1 (O5′), uncontested at
V21). This brief consumes exactly ONE property of it:

> **(N\*-MAJ)** For every prefix site of 𝐇 (each 𝐇_{≤j−1}·ν_j, 1 ≤ j ≤ k):
> N*(𝐇) ≥ L(𝐇_{≤j}) — N* majorizes every prefix read ceiling.

This is the thr-style majorant reading (O-1thr §1.4's "any majorant works");
(N\*-MAJ) holds for the D4R.4/L12 join by construction (it is a max over
the branch's nodes of per-site band levels joined with the verdict window).
Any level function satisfying (N\*-MAJ) may be substituted. [Seam: the
cluster spec owns the exact N\* definition; (N\*-MAJ) is displayed here so
CU-1 cannot silently strengthen it.]

## 2. Theorem CU-1 (statement)

**Theorem CU-1.** Let 𝐇 = (ρ₀; ν₁, …, ν_k) ∈ 𝔈 be well-formed with
Cons_f(𝐇) and ALL nodes continuing, and let N ≥ N*(𝐇). Then:

* **(i) (no-missing / realization.)** REALIZED(f, 𝐇) holds — in O-1thr's
  single displayed sense (§1.3) — and the canonical run of the machine on f
  at working level N visits the state of 𝐇 (execution reading, via Lemma
  REAL≡). Here "𝐇" carries its f-pinned dressing: by Lemma R the
  non-formal fields of a Cons_f all-continuing chain are functions of
  (f, Θ(𝐇)), and clause (i) asserts realization of exactly that dressing.
* **(ii) (state binding — the old F5, carried as a clause.)** The engine's
  frame state after the realized prefix 𝐇 equals the stage data of Θ(𝐇):
  the state key is Lift_k(Θ(𝐇)), the state valuation and key height are
  the record functions of 𝐇's records ((M4)), and the window width is μ_k
  — i.e. the state the run stands at IS the stage read's parameter frame
  over the formal chain of what was emitted (the OL-2a-6 binding,
  instantiated at the realized run and carried inductively).

**Corollary CU-1-ADEQ (interior adequacy; per-step, no global unit).**
For every 0 ≤ i < k and every GMN child of t^{(i)} = ι(Θ(𝐇_{≤i})) in
t_{i+1}(f) — i.e. every (side, irreducible residual factor) refinement —
there is a node ν with Cons_f(𝐇_{≤i}; ν): the Cons_f-extensions of a
consistent prefix are EXACTLY the GMN children ((C4) is definitionally
two-sided once OL-2a-1 grants well-definedness), and by Theorem CU-1 each
such extension with ceiling below N is realized. Hence every t_•(f) node
whose chain's N* is ≤ N arises from a realized Cons_f chain — read-back
surjectivity per site, with NO global tree-isomorphism statement (the
V21-5 object is deleted, per O3adj Arg-4).

*Scope notes.* (1) Everything is per-f ("selected-f"): no clause
quantifies over lifts of a box; the cylinder/lift content lives at D-14
(per-site, proved) and D-15 (the cluster's box node) — O3adj Arg-4. (2)
Terminal/saturated LAST nodes are excluded by "all nodes continuing";
verdict-carrying terminal seams are CU-2t's business, not CU-1's. (3) At
k = 0, (i) reads: the track's root state is visited and (ρ₀)'s record data
are f's (ord_{φ̄}(f̄) = a₀); (ii) reads: the root frame is (Φ₀, w₀) with
window width a₀.

## 3. Proof (ordinary induction on the chain length k)

**Base (k = 0, and the first read k = 1).** k = 0: Cons_f((ρ₀)) says
t^{(0)} ∈ t₀(f) with ω = a₀ ≥ 2 (O-2a Theorem 1 case (i)); machine-side,
the track's root state exists with reduction factor φ̄^{a₀} and its READ
content is level-1 box data (O-1thr §1.1 order 0; Lemma ROOT-M gives the
root window's confinement). The run starts at root states of all tracks:
visited. Clause (ii) at k = 0 is definitional (Φ₀ = 𝒫(φ̄), w₀ = Gauss,
γ̂ = 0, width a₀ = ord_{φ̄}(f̄), which Cons_f pins). k = 1: Cons_f gives
the side S₁ on N₁(f) and ψ₁ | R_{S₁}(f) exactly (O-2a Theorem 1 case
(iii)'s objects); OL-2a-5-min (b′)+(c′) states that the engine's base read
over ρ₀ emits verbatim (c1)/(c2) — consumed here in the converse-transport
direction: the (R1)/(R2) clauses of ν₁ on f hold iff the GMN side data are
present, which Cons_f asserts. OL-2a-6(a) binds the run's first emitted
record to that base read. Realization at working level N: (N\*-MAJ) gives
N ≥ L(𝐇_{≤1}), so O-1thr Theorem 1 (D-14) transfers the exact read to the
level-N run (f and its level-N decode agree below p^N ≥ p^{L}). LAWFUL and
prefix-non-saturation: (N1)–(N3) hold of harvested/base-read records
(displayed laws; O-1thr §1.2), (N4)-upper by Corollary VTX at the root
(PROVED slice), (N4)-lower and AUX by (M6b)(ii−)/(iii) [residue R-2];
there is no proper prefix beyond the root record. REAL≡ (⟸) turns
REALIZED into the visit. [Base grades: O-2a Theorem 1 at its displayed
grade; the O-1thr root kernel PROVED.]

**Step (k → k + 1, k ≥ 1).** Let 𝐇′ = (𝐇; ν_{k+1}) with Cons_f(𝐇′), all
continuing, N ≥ N*(𝐇′). Cons_f and N\*-MAJ restrict to prefixes
(immediately from (C4)'s per-level form and §1), so the IH applies to 𝐇:
REALIZED(f, 𝐇), the run visits o_𝐇, and (ii) holds at k.

1. **State identification.** By IH (ii), o_𝐇's frame is the stage frame
   over c := Θ(𝐇): key Φ̂_{k+1} = Lift_k(c), which by OL-2a-1 is a GMN
   representative of t^{(k)} = ι(c) — and t^{(k)} ∈ t_k(f), non-complete,
   by O-2a Theorem 2(A) at 𝐇 [Cons_f + OL-2a-1].
2. **The semantic next read is on the menu (the old SEM-LAWFUL).**
   Cons_f(𝐇′) gives: N_{k+1}(f) (the polygon w.r.t. Φ̂_{k+1} in the GMN
   frame) has the side S_{k+1} of slope −h_{k+1}/e_{k+1}, and ψ_{k+1} is a
   monic irreducible factor of R_{S_{k+1}}(f) of exact multiplicity
   μ_{k+1}. By OL-2a-2-min (the stage window polygon = N_{k+1}(f)
   vertex-for-vertex, emitted-record typing) the side is a face of the
   MACHINE's window hull at o_𝐇 — it lies inside the window (slots ≤ μ_k)
   because the window hull IS the full polygon's principal part there:
   (M6c)(ii)/WGEO(c) at o_𝐇 [(V1)/(V2) compliance beyond the proved
   slice]. By OL-2a-3 (min core: ord_{ψ̂_hom}(in f) = ord_ψ(R) — the
   residual dictionary) ψ_{k+1} appears as an irreducible factor of the
   face's MACHINE residual with the same exact multiplicity. So
   (S_{k+1}, ψ_{k+1}) is a candidate pair at o_𝐇 in the §1.4 sense.
3. **Harvest and record match.** o_𝐇 is non-saturated (𝐇′ continues
   through it: Cons_f(𝐇′) has t^{(k)} non-complete, and Theorem 2(B)'s
   saturation display ties completeness ⟺ μ_k = 1, so μ_k ≥ 2) and not
   ns-halted (step 2 exhibited a principal window face — the requantified
   (M6c)(ii) discipline: non-halting is CONCLUDED, never presupposed). By
   (M6a) the walk standing at the REALIZED non-halted o_𝐇 harvests ALL
   candidate pairs, among them (S_{k+1}, ψ_{k+1}); the harvested record's
   fields are read off f by construction, its vertex pair well-defined
   with the (N4)-upper by Corollary VTX [(V1)/(V2) at level ≥ 1], LAWFUL
   modulo (M6b)(ii−)/(iii) [residue R-2]. The harvested record EQUALS
   ν_{k+1}: both are functions of (f, Θ(𝐇′)) — the harvest by
   OL-2a-2-min(d′)/OL-2a-3 (the emitted record is verbatim the GMN datum
   (c1)/(c2) of the stage read over c), ν_{k+1} by Lemma R's recovery
   (Cons_f pins the dressing from (f, Θ(𝐇′))). [This is the P2-1 lesson
   consumed correctly: the citation fires at the stage read OL-2a-6(b)
   binds, whose chain parameter the IH's clause (ii) carries — no unbound
   c.]
4. **Realization at working level N.** REALIZED(f, 𝐇′) now holds: READ =
   prefix reads (IH) + the new read (harvest construction (M6a) window
   clauses, (M6c)(i) beyond-window at o_𝐇, VTX for (R5)); LAWFUL as in
   step 3 plus AUX prefix closure; prefix-non-saturation = IH's plus
   step 3's μ_k ≥ 2. By (N\*-MAJ), N ≥ L(𝐇′_{≤j}) for every j, so O-1thr
   Theorem 1 (D-14) applied at each prefix site transfers every read to
   the level-N decode: the canonical run at working level N performs the
   same reads. Lemma REAL≡ (⟸) [(M6a)+(M6b)+(M6c)] converts REALIZED
   into the walk's visit of o_{𝐇′}.
5. **Clause (ii) at k + 1.** The engine, having emitted ν_{k+1}, births
   the next stage from it: OL-2a-6(b) at level k + 2 binds the next
   read's chain parameter to Θ(𝐇′), and its key to Lift_{k+1}(Θ(𝐇′)) —
   which is the harvested record's produced key by (R4) (policy-pinned,
   (M4)). The state valuation/key height after ν_{k+1} are record
   functions of 𝐇′'s records ((M4), machine-proved), and the new window
   width is μ_{k+1} (§1.4). So the state o_{𝐇′} carries exactly the
   stage data of Θ(𝐇′). ∎

**Proof of Corollary CU-1-ADEQ.** Fix i < k (or any consistent prefix) and
a GMN child (S, ψ) of t^{(i)} in t_{i+1}(f). By definition (C4), the chain
(𝐇_{≤i}; ν) with ν's formal fields (e, h from S's slope, ψ) and dressing
recovered per Lemma R satisfies Cons_f — (C4) at level i + 1 asks exactly
that S be a side of N_{i+1}(f) and ψ a factor of its residual, which is
the hypothesis. Well-formedness of ν: the recovered record is the stage
read's emitted record over Θ(𝐇_{≤i}) (OL-2a-2-min/3 as in step 3), and
emitted records are well-formed [OL-2a-4]. Theorem CU-1 then realizes it
whenever N ≥ N* of the extended chain. NO other object is constructed: in
particular no global T_can and no tree isomorphism. ∎

## 4. The consumption map (every input, its clause, its status)

| # | input | consumed at | status (home brief) |
|---|---|---|---|
| 1 | OL-2a-1 (GD-1) | step 1 (representative), step 3 via (R4) | OPEN |
| 2 | OL-2a-2-min (GD-2) | steps 2, 3 (window = polygon; (c1) verbatim) | OPEN |
| 3 | OL-2a-3 min core (GD-3) | steps 2, 3 ((c2); exact multiplicity) | OPEN |
| 4 | OL-2a-4 | Corollary (well-formedness of emitted records) | OPEN |
| 5 | OL-2a-5-min | base k = 1 (base-read conformance) | OPEN (GD-5: closes by composition per SYNTH4 §1) |
| 6 | OL-2a-6 (GD-6a) | base (a); step 5 (b) — the binding IH clause (ii) carries | OPEN |
| 7 | O-2a Thm 1 / Thm 2(A)(B) | base; steps 1, 3 (placement; saturation tie) | conditional, core thrice-confirmed; pass 2 pending |
| 8 | Lemma R | statement (i); step 3; Corollary | PROVED (O-2a, confirmed) |
| 9 | (M6a) | steps 3, 4 | machine-proved by construction (O-1thr §2.4) |
| 10 | (M6c)(i)/(ii) + WGEO/SPAN geometry | steps 2, 4 | PROVED at root/degree-1-first-transition slice; modulo (V1)/(V2) beyond |
| 11 | Corollary VTX | base; steps 3, 4 ((R5) well-defined, (N4)-upper) | PROVED at root slice; modulo (V1)/(V2) at order ≥ 1 |
| 12 | (M6b)(ii)-lower + (iii) | base; steps 3, 4 (LAWFUL) | OPEN (interface residue) |
| 13 | (V1)/(V2) key compliance | inside 10, 11 at order ≥ 1 | OPEN (named assumption; **gated at order 2 by §7's T-G — SURVIVED**) |
| 14 | Lemma REAL≡ | base; step 4 | PROVED conditional on (M6a)+(M6b)+(M6c) |
| 15 | O-1thr Thm 1 (D-14) | base; step 4 (level-N transfer) | PROVED OUTRIGHT machine-side (rev 4; pass 4 pending); D-14 node r2 pending |
| 16 | (N\*-MAJ) | base; step 4 | displayed hypothesis (§1); holds for the D4R.4/L12 join by construction |

Nothing else is consumed. In particular: NO O-2b/OB1/F6′ face, NO
cross-polynomial statement, NO global adequacy, NO mutual induction — the
two inductions of the K-RUN-C composition (this one, and Theorem 2(D)'s
inside O-2a) couple only through the FIXED per-site lemmas above (O3adj
§2, Arg-3/4).

## 5. Honesty ledger (what CU-1's acceptance would and would not mean)

**Proved here:** the induction of §3 — i.e. that the DISPLAYED inputs of §4
compose, with no unbound chain parameter (the P2-1 class), no halting-guard
circle (the V24-C1 class), no box-keyed quantifier (the V16/V21 class), and
no global adequacy object (V21-5). That is the whole claim of the unit.

**Open residue (owners named; nothing new added by this unit):**

* **R-1 (dictionary):** OL-2a-1..6 — O-2a's declared residue, = GD-1..GD-6
  in SYNTH4's merge; the GD campaign owns them (SYNTH4 §3.2 step 3).
* **R-2 (machine interface):** (M6b)(ii)-lower, (M6b)(iii) AUX, and
  (V1)/(V2) key compliance beyond the proved slice — O-1thr's displayed
  residue; GD-2/GD-3/GD-4's territory.
* **R-3 (verification states):** O-1thr rev-4 pass 4; O-2a rev-4 pass 2;
  D-14 r2 — CU-1's grade rises only as those land.
* **R-4 (cluster seams):** the exact N\* definition and (N\*-MAJ)'s
  discharge live in the cluster spec (D4R.4/L12/TB-CAP); CU-1 consumes the
  displayed majorant property only.
* **R-5 (scope):** terminal seams (CU-2t), leaf coverage counting (CU-4 /
  O5triple Theorem B), box-level lift uniformity (D-15) are OTHER units of
  the K-RUN-C composition; CU-1 neither states nor needs them.

## 6. Why this induction is not the rejected design (the V16/V21 audit)

(P1) box-keyed quantifier: CU-1 has none — both clauses are per-f, and the
box appears only through D-14's level transfer, which is per-SITE. Two
lifts of one box never meet in any statement. (P2) global T_can/ADEQ: CU-1
defines no canonical tree; the semantic side enters only as Cons_f (a
per-chain predicate) and t_•(f) (GMN's own object); adequacy is the
per-step Corollary. The mutual-induction coupling V16-6 worried about is
gone: Theorem 2(D)'s induction lives inside O-2a and is consumed as a
finished conditional statement (through Lemma R and the record match of
step 3), not re-run here. F3′/F4/F6′ faces: absent (other units / deferred
tier). This section exists so the verifier can kill the unit quickly if
any of these re-entered through a citation.

## 7. Falsifier record (run FIRST, per the dispatch)

### 7.1 The primary gate: T-G at depth 3 (order-2 states) — SURVIVES

`verification/openmath/o1thr_depth3_check.py` (new; full spec in its
docstring), extending the T-F depth-2 harness to ORDER-2 STATES: root read
(depth-1 site) + window-hull read (depth-2 site, residual over
K₁ = 𝔽_p[z]/ψ(z)) + the order-2 frame w₂ = MacLane composite, the
standard level-2 key Φ₂ built from the harvested ψ₁, and the FULL
Φ₂-development geometry — exactly the per-site kernel CU-1's step consumes
where it is weakest ((V1)/(V2) at level ≥ 1; O3adj §3.4's charge). Checks
T-G.0–T-G.6 cover: (R1)-support, WGEO(a) display, (V2b) at f, the WGEO(b)
vertex law (first attainment at μ₁ + the VTX pin), (M6c)(i)/(ii) at o₂,
the VTX chain with (V2b)-at-level-1, DIRECT (V1) multiplicativity probes
on product pairs, and DIRECT (V2b) development-identity probes.

Run 2026-07-31, this machine, exact integer arithmetic (tracked record:
`verification/openmath/results/o1thr_depth3_run_20260731.txt`; raw log
`logs/o1thr_depth3_run_20260731_151242.log`), configs (p, n, M) =
(2,4,4), (3,4,3), (2,6,3), (3,3,4), (2,6,4), (2,8,3):

    470,736 order-2 instances — ZERO violations of all nine checks.
    Coverage: 122,577 with beyond-window slots (the (M6c) content is
    non-vacuous); 10,935 growth steps (e₁g₁ ≥ 2); 16,472 extension-field
    parents (g ≥ 2, residuals over 𝔽_{p^g}); 2,091 children with g₁ ≥ 2;
    saturated parents included (laws are state-hypothesis-free at rev 4).

**Verdict: the gate SURVIVES; CU-1's spec dispatch is licensed (O3adj
§3.5 step order).** A kill here would have reopened the per-site kernel,
not the composition's shape (O3adj R1) — neither happened.

### 7.2 The gate's own countermodel finding (independent value, GD-3)

The checker's FIRST version normalized level-1 residues per-slot
("fresh-t₀", no coherent monomial march). Under that reading the vertex
law FAILS: first countermodel f = X³+3X²+3X, p = 3, depth-1 site
(e, h, ψ, μ) = (2, 1, z+1, 1), face (0,4)–(1,3) — naive selects
ψ₁ = z′+2 whose standard lift X²+6X+3 is a NON-improving recentering
(v(Φ₂(θ)) = 3/2, no gain), while the coherent (anchored-march) convention
selects ψ₁ = z′+1 whose lift X²+3X+3 is the TRUE ℚ₃-factor. Final tally:
1,827 instances where the readings differ, 1,818 naive vertex-law
refutations — ALL at p = 3 with g = 1 in these configs, i.e. exactly where
ȳ ≠ 1 (at p = 2, g = 1 the twist unit ȳ = 1 makes the two readings
coincide — the naive reading is INVISIBLE there). Consequences: (a) the
pinned convention for order-2 residual reads must carry the coherent slot
normalization (the "recorded unit normalization" of (R2)/(R5) made
concrete — the machine countermodel that shapes GD-3's slot-twist/z-power
clause, the depth-3 sibling of rev 3's sloped-vs-plain pin); (b) any
GD-3/OL-2a-3 statement or Lean transcription that normalizes residues
slot-fresh is REFUTED at order 2. Also reported: the naive mixed-units
order-2 (N4)-lower comparison w₁(D_{μ₁}) ≥ u_{k₁} fails in 470,057 of
470,736 instances — the order-2 lower band must NOT be stated that way
(statement-shaping datum for (M6b)(ii) at depth; the band's order-2 form
remains open with the rest of R-2).

### 7.3 Standing suites (unchanged, still green)

T-A..T-D, T-E, T-F re-run unchanged earlier this cycle (O-1thr rev-4
record): ALL PASS. G-EMIT/U6 remain OL-2a-6's falsifiers (O-2a rev-4 §4
note); CU-1 adds no new obligation there but its step 5 consumes exactly
the law G-EMIT tests.

## 8. Verification checklist (where to press hardest)

1. **Quantifier audit of §2:** is any clause secretly box-keyed or
   ∀-lift? (The V16/V21 kill class; §6 claims not.)
2. **The IH package:** does step 2 use anything at o_𝐇 beyond clause (ii)
   + the cited OL-2a-1/2-min/3? In particular, does "the side lies inside
   the window" really follow from (M6c)(ii)/WGEO(c) at o_𝐇 plus
   OL-2a-2-min's vertex-for-vertex tie, or does it need the window-width
   tie W_{o_𝐇} = μ_k as an EXTRA dictionary clause? (The brief takes the
   width from §1.4's definition + clause (ii); check this is not a silent
   OL-2a-2 strengthening.)
3. **Record match (step 3):** Lemma R recovers 𝐇′ from (f, Θ(𝐇′)) — but
   Lemma R is proved on Cons_f chains; the harvested record is shown
   Cons_f-consistent only through OL-2a-2-min/3. Is the match argument
   circular-free as displayed (both sides functions of (f, Θ(𝐇′)) through
   INDEPENDENT routes)?
4. **D-14 consumption (step 4):** Theorem 1 transfers site reads between
   f ≡ f′ (mod p^L); the brief applies it to f vs its level-N decode.
   Check the decode is a legitimate f′ (monic, degree n) and that
   "canonical run at working level N" is consumed ONLY through this
   transfer + REAL≡ (no hidden appeal to the source machine's leveled
   execution semantics).
5. **(N\*-MAJ):** is the majorant property as displayed sufficient
   everywhere N appears (base, step 4), and is prefix-monotonicity of N\*
   used silently anywhere (it is NOT assumed)?
6. **Saturation tie (step 3):** the μ_k ≥ 2 argument routes through
   Theorem 2(B)'s saturation display, which is [Cons_f + OL-1]-conditional
   and asserted for k′ ≥ 1 only. Check the k = 1 corner (prefix of length
   1) and the k′ = 0 vacuity note.
7. **Corollary CU-1-ADEQ:** "(C4) is definitionally two-sided" — verify
   against O-2a's (C4) text that Cons_f-extensions = GMN (side, factor)
   children EXACTLY (no extra Cons_f clause constrains ν beyond side +
   factor + exact multiplicity + dressing recovery).
8. **No-strengthening sweep (the dedup-audit rule):** every OL citation in
   §3/§4 against its home statement — is any consumed CLAUSE wider than
   declared there (esp. OL-2a-2-min's (c′)(d′) vs the retired full OL-2,
   and OL-2a-3's min core vs full form — V25's trim)?
9. **Gate adequacy:** does §7.1's T-G really exercise every step-2/3
   ingredient (per O3adj: "every per-site ingredient of the new
   induction's step")? Named residue: T-G probes the standard-lift policy
   on the degree-1 root slice; general-d₀ root keys and non-standard
   compliant policies are outside the numeric perimeter (as at T-E/T-F).

— CU-1 rev 1 complete. PROVED-UNVERIFIED (conditional composition, §4
grades) until hostile passes accept it; primary gate SURVIVED and is on
record above.
