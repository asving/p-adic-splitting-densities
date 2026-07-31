# CU-1 rev 3 — hostile verification, PASS 2 of 2 (Fable, fresh context, 2026-07-31)

Charge: standalone read of `CU1_phaseB_verifybrief_rev3.md` ONLY (no other
project file, no prior verifier reports consulted). Quote-and-classify;
fix nothing. Audit axes ordered per the charge: (A) the chain-length
induction against the 29-row consumption map — anything consumed and not
mapped is a finding; (B) the interior/terminal split and its boundary
cases; (C) the constructed machine history, creation vs recovery; (D) the
N-free structure and the single top-site D-14 application; (E) the
declared pins.

**VERDICT: SOUND-WITH-GAPS** — 0 critical errors, 7 justification gaps.
The rev-2 structure (confirmed at V29) survives my independent read: the
induction is genuinely N-free, the split is exhaustive-disjoint on its
stated domain, the record match is creation-first, D-14 fires exactly
once, and the pins are declared where consumed. Every finding below is in
the consumption-accounting / display class — the same class rev 3 claims
to have closed, which is why several of them matter: the §5 exactness
claim fails at named points that survived the rev-3 repair.

---

## A. The induction vs the 29-row map

I traced every named consumption of §§2–3 to a row. Base k = 0: (c0)
[row 4], §1.4 root init [row 18, but see F-3], (P-ROOT) [19], (D3) [4] —
clean. Base k = 1 items 1–6: (P-ROOT) [19], (D3) [4], ROOT-M [12],
§1.4 halts [18], W2/species [28], (M6a) [7], (M6c)(i) [10], VTX [8],
(M6b)(ii−)/(iii) [9], (R4)/(M4) [17], (P-KEY) [20], (FR≡) [21] — clean
except as below. Step items 1–5: OL-1 [1], OL-2(b)/(c)/(d) [2], OL-3 [3],
(FR≡) [21], WGEO(c)/(d) [13], (V1)/(V2) [14], (M6a) [7], VTX [8],
(M6b) [9], (M6c)(i) [10], [F.2] [29], W2/W3 [28], (M4) [17], (P-KEY)
[20], §1.4 [18] — clean except as below. The dropped consumptions check
out: OL-2(a) is indeed used by no sentence; Thm 2(A) is indeed used by no
sentence (the split consumes only (B)'s biconditional); OL-4/5/6, SPAN,
Thm 2(D) appear nowhere. The following do NOT trace.

### F-1 (JUSTIFICATION GAP — unmapped input, load-bearing): Lemma CEIL / the L(H) read-ceiling has NO row

Quote (§2, proof of CU-1-LVL): "One application suffices: REALIZED at the
top site already quantifies over every prefix read, and L(M_𝐇) is the max
of all the per-read ceilings — **Lemma CEIL's audit is over all i < k**."
Also §1: "Since **L(M) = 1 + max_{i<k} ⌈I_i/E_i⌉** is a MAX over the
chain's reads…" (the O-1thr §3 definition, with Lemmas NAT/CEIL listed in
§0′'s import display).

No row of §5 carries L(H), Lemma CEIL, or Lemma NAT: row 18 is the §1.4
bundle plus the §1 box/decode display; rows 15/16/22 are REAL≡/D-14/
(N\*-MAJ). CU-1-LVL is §2, so §5's exhaustiveness claim ("every input
consumed by any sentence of §§2–4 appears in a row above") is FALSE at
this point — and the input is load-bearing: the "one application at the
top site suffices" argument (checklist item 7, the D-14 single-shot
structure) rests exactly on CEIL. Downstream, Corollary CU-1-SURJ's
dependency sentence enumerates LVL's bundle as "rows 7–11, 15, 16, 18,
22" — a list that cannot carry CEIL (no row exists), and that also omits
row 17 even though row 17's own location column says (M4) is consumed
"inside D-14" (row 16, which IS listed). Home status of CEIL is not
graded anywhere in the brief (§0′ lists "Lemmas NAT/CEIL" without a
grade). Not critical — the chain is not broken, the input plainly exists
at home — but it is precisely the V29 class, surviving rev 3.

### F-2 (JUSTIFICATION GAP — unmapped input, load-bearing): (C4)/Cons_f has NO row

The map never assigns (C4)/Cons_f a row, yet the text consumes it by name
at at least seven sites, two of them load-bearing facts rather than
hypothesis vocabulary:

* Step preamble: "Cons_f and the interior scoping restrict to the prefix
  (**(C4) is per-level**; μ_i ≥ 2 for i ≤ k holds in 𝐇′ already), so the
  IH applies" — the per-level/prefix-stability of Cons_f is the LEGALITY
  OF THE INDUCTION HYPOTHESIS. If Cons_f were not prefix-stable, §3
  collapses. This fact is asserted parenthetically with no row and no
  home citation beyond §0′'s vocabulary line.
* ADEQ converse: "**(C4) is definitionally two-sided** once OL-1 grants
  well-definedness" — a consumed biconditional reading of the definition.
* Plus (c0) at base k = 0; (c1)/(c2) at base item 2, step 2, step 3(d),
  ADEQ's checks; and the split's terminal bullet ("**Cons_f constrains no
  terminal field**").

Row 5's rev-3 annotation explicitly classifies (C4)'s clauses as "the
theorem's HYPOTHESIS vocabulary (§0′), not a consumed result" — but the
rev-3 standard that created rows 27–28 for (C1) and the W-laws (equally
definitional O-2a vocabulary, added because "ADEQ explicitly invokes"
them) applies a fortiori to (C4), which the step preamble invokes to run
the induction at all. The exhaustiveness paragraph's coverage list
("(L2)/(L3)/Def 2.21, the (C1) carrier with its W-laws, [F.2]") omits
(C4). Same omission for Θ, consumed by name in clause (ii)'s statement
(Lift_k(Θ(𝐇))) with no row (Lift itself plausibly rides rows 19/20's
(C2)-pinned displays; Θ rides nothing).

### F-3 (JUSTIFICATION GAP — exhaustiveness paragraph overstates rows 7/17/18's O-1thr coverage)

Quote (§5): "Rows 7, 17, 18 cover O-1thr's definitional vocabulary
(states, windows, halts, READ/REALIZED, harvesting, π's machine side)."
But the text consumes, by name, O-1thr content in NO row's input column:

* "(N1)–(N3) displayed at harvest" (base item 5, step 4) — the display
  that harvested records satisfy the first three node laws. Rows 7/9
  carry (M6a) and (M6b)(ii−)/(iii); (N1)–(N3)-at-harvest is neither.
* "AUX prefix closure (§1.2)" (step 4) — §1.2 content; row 18's bundle
  is §1.4 + the §1 box/decode display, and no row names §1.2.
* "the §1.1 recursion over the matched records" (clause (ii): base 6,
  step 5; also §2's statement) — the frame recursion itself is §1.1
  definitional content; row 17 carries only (M4) ("frame data are record
  functions"), not the recursion display.
* §1.3's READ/REALIZED definitions (base 5, step 4 unpack (R1)–(R5),
  LAWFUL = CORE ∧ AUX) — claimed covered, but no row names §1.3.
* Base k = 0's track/root-state existence display ("the track of ψ̂₀
  exists with root state o_𝐇") — row 18's location column lists base 3
  but not base k = 0.

Each item is definitional and surely true at home; the defect is that the
rebuilt exhaustiveness paragraph claims a coverage the rows do not carry
— the V29 finding-4c class, on the O-1thr side this time.

### F-4 (JUSTIFICATION GAP — row 6's "ONLY" is inexact)

Row 6: Lemma R consumed at "§2 scope note (3) + §4 canonicity remark
ONLY — produces and identifies NOTHING." But §4's terminal bullet reads:
"Terminal machine records (sel = ⊥) correspond to NO GMN child — Cons_f
constrains no terminal field (**Lemma R's displayed non-claim**)" — a
third citation site. Citing a NON-claim is arguably not consumption, but
the row asserts "ONLY", and the parenthetical is doing justificatory work
(it is the named warrant for the terminal routing). One-word-class fix;
still a map-exactness miss under the brief's own bar.

---

## B. The interior/terminal split (boundary cases)

The displayed split — μ ≥ 2 (interior, CU-1-ADEQ) / μ = 1 (leaf, routed
to O5triple B + D(b) at their own conditionality) / sel = ⊥ (no GMN
child, CU-2t) — is exhaustive and disjoint ON ITS STATED DOMAIN: children
(S, ψ) of a non-complete t^{(i)} reached by an all-continuing,
non-complete Cons_f chain with a₀ ≥ 2. μ ≥ 1 always, so the two μ-cases
partition; terminal records are correctly excluded from the child set
rather than treated as a third child class. The μ = 1 leg is honest about
O5triple's (I-1)–(I-3) conditionality and consumes nothing from it
(routing only). ADEQ's i = 0 case (children of the root) is explicitly in
scope. Checked.

### F-5 (JUSTIFICATION GAP — the depth-0 boundary is routed by no sentence)

Every displayed route hypothesizes a₀ = ord_{ψ̂₀}(f̄) ≥ 2: Theorem CU-1,
ADEQ ("with a₀ ≥ 2"), SURJ ("with a₀ = ord_{ψ̂₀}(f̄) ≥ 2"), and the split
quantifies only over children of non-complete types along such chains. A
track with a₀ = 1 (a simple irreducible factor of f̄) is complete at
depth 0 — a root-level leaf — and NO sentence of §4 routes it: the split's
μ = 1 bullet covers complete CHILDREN of non-complete parents, not
complete ROOTS. Presumably O5triple's leaves(𝒯(g)) include depth-0 leaves
and the same routing extends, but the "no gap, no overlap — displayed"
claim does not display it. If the split's coverage claim is meant per
track-with-a₀ ≥ 2, say so; if it is meant for all GMN children of f, the
depth-0 complete track needs one routing sentence.

Minor note, same section (no separate finding): ADEQ's W1 check argues
the ℓ = 1, e = 1 case via "μg ≤ 1 with μ ≥ 1 forces g = 1" — under ADEQ's
interior hypothesis μ ≥ 2 that case is vacuous (μg ≤ 1 is impossible);
the displayed argument is harmless but proves the vacuous case rather
than noting it cannot arise.

Minor note 2: ADEQ's W4 check equates "ψ ≠ z" with "y ∤ R_λ(f)" ((L3),
row 25) without displaying the y/z variable identification (order-1 vs
order-(i+1) residual variable). Standalone, the inference has a silent
renaming step. Display nit.

---

## C. The constructed machine history: creation vs recovery

Confirmed repaired, independently of V29's identical verdict. In §3 the
record is CREATED by harvest — step 3(c) sets ν̂_{k+1} := the harvested
record of the candidate pair (S_{k+1}, ψ̂_{k+1}), whose candidacy is
established from (c1)/(c2) + OL-2(b) + (FR≡) + WGEO(c) + OL-3 BEFORE any
recovery vocabulary appears — and step 3(d) matches π(ν̂_{k+1}) = ν_{k+1}
fieldwise, each 𝔈-field with a named source: (e, h, ℓ) [OL-2(c)],
(s, u) [OL-2(d)], sel-factor [choice of pair + [F.2] tower], sel-
multiplicity [OL-3 scalar + (c2)], g [same field], inc [W2 = species
law], dressing [choice]. The side-per-slope uniqueness that pins "the
corresponding side" is the displayed elementary polygon fact. Every field
of §0′'s π list is covered; Lemma R appears in the match nowhere. In §4,
ADEQ's node is constructed by displayed formulas and checked clause by
clause; Lemma R survives only in the two canonicity remarks (plus the
F-4 parenthetical). No creation-by-recovery anywhere. PASS.

---

## D. N-freeness and the single top-site D-14 application

Scanned every sentence of §3 for a working level, box, decode, D-14,
REAL≡, f_N, or N\*: NONE occurs — the base and step consume no level
object, and the step's IH invocation ("NOTHING about N is assumed or
used") is accurate as written. CU-1-LVL is the sole consumer of D-14
(one application, at the top site (M_{𝐇,≤k−1}, ν̂_k)), REAL≡ (⟸ only, on
f_N, with REALIZED(f_N, M_𝐇) established first), the box/decode display,
and (N\*-MAJ) (the single "in particular"). The D-14 hypotheses are
discharged in-text: LAWFUL from clause (i)'s REALIZED (REALIZED := READ ∧
LAWFUL ∧ no-proper-prefix-saturated, §0′), L(M_𝐇) ≤ N, f ≡ f_N
(mod p^N) ⟹ (mod p^{L(M_𝐇)}), both monic degree n (the decode display).
The sufficiency of ONE application is coherent — REALIZED at the top site
quantifies over the whole history's reads and L is the max of the per-
read ceilings — but that step load-bears on Lemma CEIL, which is F-1's
unmapped input. §1's prefix-ceiling remark (L(M_{𝐇,≤j}) ≤ L(M_𝐇), max
over a subset) is correct provided prefix reads are read off the same
records, which they are (records are history data). The k = 0 clause's
f̄_N = f̄ at N ≥ 1 is right. Saturation is handled record-only (IrrHalts ⟺
μ_last = 1), so prefix non-saturation transfers with the records —
consistent. PASS, modulo F-1's accounting.

(N\*-MAJ) hygiene: consumed exactly once, displayed as a hypothesis, with
the discharge deferred to R-4. The §1 aside "(N\*-MAJ) holds for the
D4R.4/L12 join by construction" is an unproved one-line sketch sitting
next to a deferral — tolerable since the map (row 22) consumes only the
displayed inequality, but the sketch should not be mistaken for the R-4
discharge. No separate finding.

---

## E. The declared pins

(P-ROOT): consumed at base k = 0 and base item 1, mapped (row 19),
definitional under the shared-source reading — fine. (P-KEY): consumed at
base 6 / step 5 only, mapped (row 20), OPEN R-6, admitted — fine. (FR≡):
order-1 uses (base items 1) are explicitly routed through the PROVED (D3)
with "no pin is consumed" — consistent with row 21. Order ≥ 2 uses
(step 1, 2, 3(d); clause (ii)) are admitted pin consumptions, and in the
step the frame-equality trigger is supplied by IH (ii) before each use —
the checklist-4 circularity is absent. The §7.2 countermodel record gives
the pin's residual clause genuine refutable content (slot-fresh reading
killed 1,818 times); I cannot re-run the harness standalone, but the
brief's use of it is as a falsifier record, not a proof — legitimate.

### F-6 (JUSTIFICATION GAP — (FR≡)'s "frame clause" is hypothesis text used as an assertion)

§0′ displays (FR≡) as a conditional: "At any state o on f WHOSE FRAME
EQUALS the [F.0] stage frame over (f, c) — key Φ_o = Lift(c), valuation
w_o and shear γ̂_o the §1.1 recursion over the same key tower, residue
tower K_• = the constructed F_• of (C1) — the state's [read objects] ARE
the stage read's [objects]." The em-dash content unpacks the ANTECEDENT.
But clause (ii)'s proofs (base 6, step 5) cite "(FR≡)'s frame clause" as
the warrant for an identification: "the §1.1 recursion over the matched
records ((M4)), = the level-(k+1) stage's [F.0] data over Θ(𝐇′) under
(FR≡)'s frame clause." That consumes an ASSERTED identity — machine
§1.1-recursion frame data = O-2a's [F.0] stage frame data over the
matched formal datum — which the displayed conditional does not assert
anywhere; on the displayed reading, (FR≡) outputs read-object identities
only, given frame equality. The intended content is clearly part of the
pin (row 21 lists "clause (ii) frame clause" as a consumption site, so
the map is honest about the dependence), but the §0′ display does not
contain the clause being consumed: the pin statement needs an explicit
second clause (frame-data identification), or clause (ii)'s wording needs
to derive frame equality from (P-KEY) + (M4) + the definition of the
stage frame. As displayed, hypothesis text is doing assertion work.

### F-7 (JUSTIFICATION GAP — row 21 omits the §0′ π-display site; π's (FR≡) citation lacks its hypothesis)

§0′'s π definition: "fields all present on the harvested record via
(FR≡)'s emitted-record clause." Row 21's location column ("step 1, 2,
3(d) …; clause (ii) frame clause") does not list §0′ (π) — inconsistent
with rows 27 and 29, which DO record §0′ (π) as a consumption site of
(C1) and [F.2]. (§0′ is outside the literal "§§2–4" exhaustiveness scope,
but π is consumed by §2's clause (i), pulling its inputs into scope; and
the map's own practice at rows 27/29 concedes the point.) Substantively:
π is defined for an ARBITRARY machine history M on f, at whose states
(FR≡)'s frame-equality hypothesis is not supplied — the citation as
written invokes the pin outside its trigger. The cheap repair is visible
in the brief itself: §0′'s §1.2 node display already lists the fields
(e, h, s0, wSide, γ, pat, ψ, μ, …) on EVERY record, so π's formulas need
only §1.2, and the (FR≡) citation belongs to the later claim that π(M_𝐇)
matches the STAGE's emitted record, where the hypothesis is supplied.

---

## Verdict and what it rests on

**SOUND-WITH-GAPS.** Zero critical errors: no forall-by-example (the
order-1 (FR≡) instance rides the PROVED (D3), the §7 harness is used
strictly as a falsifier, and every ∀-claim in §§2–4 is proved by
induction or displayed construction); no broken step in the induction; no
N-leak; no creation-by-recovery; no undeclared pin use; the two rev-3
consumption DROPS (OL-2(a), Thm 2(A)) verified correct against the text.
All seven findings are justification gaps of the consumption-accounting /
display class: F-1 (Lemma CEIL/L(H) unmapped — load-bearing for the
single-D-14 argument; SURJ's row list also omits row 17), F-2 ((C4)/
Cons_f and Θ unmapped — the per-level prefix restriction is the IH's
legality), F-3 (rows 7/17/18 don't carry the claimed O-1thr coverage:
(N1)–(N3)-at-harvest, §1.2 AUX closure, the §1.1 recursion, §1.3
READ/REALIZED, base-k=0 sites), F-4 (row 6's "ONLY" vs the terminal
bullet), F-5 (depth-0 a₀ = 1 track unrouted by the split display), F-6
((FR≡)'s frame clause consumed but not displayed as assertible content),
F-7 (row 21's missing §0′ (π) site; π's citation outside the pin's
trigger). §5's exactness claim is therefore still false at F-1/F-2/F-3
after the rev-3 repair — the map bar the brief set for itself is not yet
met, though the mathematics it maps is, at the displayed conditional
grades, coherently composed.

Standalone caveats: I could not and did not check any home brief, the
O3adj spec, the V27/V29 reports, or the §7 run records; all "PROVED at
home" grades, the gate record, and the home-advertisement claims (OL-2/
OL-3 "advertised to exactly this consumer") are taken as citations, per
the brief's own conditional-composition framing.

— Pass 2 (Fable, fresh context). 0 CRITICAL / 7 GAPS. SOUND-WITH-GAPS.
