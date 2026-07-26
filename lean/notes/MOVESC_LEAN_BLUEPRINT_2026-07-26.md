# MOVES §C — Lean formalization blueprint (composition theorem, 2026-07-26)

*Blueprint-architect deliverable for the §C-Lean campaign. Formalizes the ACCEPTED **§C REV 2**
(the composition theorem, passes 12+13 CLEAN) of `lean/notes/MOVES_2026-07-24.md`, with the two
fresh-context derivations `C10B_DERIVATION_2026-07-26.md` (window kernel) and
`C15_DERIVATION_2026-07-26.md` (the Route-B counting mechanism). Read with
`lean/LeanUrat/MovesC/Defs.lean` (the shared vocabulary, COMPILES green under `lake env lean`, no
`sorry`/axiom) and `lean/LeanUrat/MovesC/MANIFEST.json` (31 units, verbatim Lean statements — all
elaboration-tested, §5). Written Protocol-L (agent-facing): verbatim names, statements re-bound at
use, explicit claim DAG.*

Discipline (parent CLAUDE.md): **NO new axioms**; anything not (yet) provable stays `sorry`.
`sorry`-free ≠ non-vacuous. The statement-fence holds — do not weaken a statement to prove it. Every
interface predicate is the trust boundary and is flagged for the semantic guardian (§4).

---

## 0. What §C is, and the one architectural split

§C composes the §B2-DEF per-move ledger along a whole **read history** `H = (ν₀,…,ν_k)` (root read,
then increments/recenterings in any interleaving) and proves **Theorem C**: for every realizable
lift-carrying history and admissible terminal system `Z`,
> `#{ f mod p^N ∈ S(H,Z) } = p^{nN} · ∏_{i≤k} vol(E_fresh(ν_i)) · vol(Z)`  for all `N ≥ N(H,Z)`.

Each `vol(E_fresh(ν_i)) = p^{−m*(ν_i)}` (a product of per-base-digit factors `p⁻¹`, the BLOCK
CONVENTION). So the theorem is, combinatorially, a **mass recursion**: the state cylinder `Σ_i`'s
mass multiplies by `p^{−m*}` at each read (C.1.5′(1)), initialized at the root, giving the product.

**The split that makes this formalizable now.** The proof factors into
- a **combinatorial counting core** — digit-system order/count/intersection/transport, the mass
  recursion, Theorem C's product — which is PROVABLE over the existing `DigitSystem` (DefsT); and
- a **geometric+graded bridge** — the identification of the K1-chain valuation `w` with a literal
  zero-downset on base-digit coordinates (KEY OBS 1), and the piece maps `R_δ` of the typed initial
  form (TYP) — which needs the **UNBUILT graded ring** (the §B2-DEF campaign's standing boundary,
  round-4 gap R4.5 items 1&3: graded pieces `gr^Ĉ_δ` and the global jet-coordinate system
  D.3(e)(ii)). This enters ONLY as flagged interface hypotheses (`LstData`, a coordinate-height
  presentation, `TypObject`, `JetSetup`), never approximated. This is exactly the pattern
  `L6.measureExact` already uses (it takes `codeN`/`ΘN`/`hcylN` as named hypotheses).

---

## 1. Design decisions (the concrete model), with justification

**M1 — ≺-sorted coordinates.** §C's base coordinates are `c = (ℓ, i)` (`ℓ` = p-adic level, `i` =
coefficient index) under the GLOBAL ORDER `(ℓ,i) ≺ (ℓ',i')` iff `ℓ<ℓ'`, or `ℓ=ℓ'` and `i>i'`
(`CoordPrec`; Fact A's elimination order). The note ALWAYS "solves in ≺-order", so we work
throughout in **≺-sorted coordinates**: a box of `m = nN` base digits is `Fin m` with the `Fin`
`<` STANDING FOR `≺`. `Coord`/`CoordPrec` are kept for faithfulness and to state the sorting
bijection (`C0.coordSort`, a finite-linear-order fact; `C0.coordPrec_trichotomy`/`_trans` witness
that `≺` is a strict linear order). This dodges a heavy order-iso layer with zero loss — the note's
own idiom.

**M2 — Loci ARE unitriangular digit systems.** `Locus p m := DigitSystem m (ZMod p)` (the accepted
`LeanUrat.Moves.DigitSystem`, DefsT). The BLOCK CONVENTION (§C.0): an `F`-digit of residue degree
`d` is its `d` base equations, each over `ZMod p`, each factor `p⁻¹` — so the alphabet is uniformly
`ZMod p` and mass is `Nat.card` of the solution set (`Locus.mass`). By the count law
(`C0.digitSystemMass`, specializing the accepted `L2.P6ii`) `mass = p^{m − numPinned}`; codimension
`K` ⟺ `numPinned = K`. **This is the "existing DigitSystem + Nat.card pattern" the charge asked
for.** PIN-WELLDEF (`C0.pinWelldef`) makes "number of pins" a locus statistic (equal solution sets
⟹ equal `numPinned`), so §C's "codimension"/"|Π_i|" language is never a set of addresses.

**M3 — Histories/nodes over the existing `Stage` vocabulary.** `ReadSpecies` = `root | increment |
recentering`. A `Node` carries its FRAME `σ : Stage p F` (the stage it reads in), the read index
`(e,h)`, descend degree `g`, ψ-order `μ`, anchor `a`, side `[s0, s0+wSide]`, block width `Dwidth`,
its read-side `line : Line` (absolute scale), the recorded `lift`, and the fixed side-pattern
`pat`/its key `ψ`/anchored residual `Ranch : Polynomial ↥σ.K` (pattern-only). `Node.vtxPoly :=
(Ranch /ₘ ψ^μ) %ₘ ψ` is the polynomial factor of the transported vertex value — **pattern-only, so
`vtx` is a predicate on node data alone** (rev 8's (HV) fix). A `History` is a node list whose head
is `root`; `HistoryCoherent` links consecutive frames by the ACCEPTED `TransitionCoreL` (D.7,
increments) / `IsRecenteringCore` (D.10, recenterings) — the provenance interface tying §C to the
tower. `Realizable` encodes the two data-only side conditions: **(NA)** `new(μ_i) < old(μ_i)` at a
non-adjacent read; **(HV)** pattern lead `= vtx(ν_i)` at an adjacent read.

**M4 — Masses are `Nat.card`; the product formula is stated in pin-arithmetic.** `ℕ` has no `p⁻¹`,
so Theorem C(b) is stated as `Dfin.mass · p^{totalPins} = boxMass p m` (= `p^m`), with `totalPins =
Σ_{i≤k} m*(ν_i) + |pins Z|`. This is exactly `mass · p^K = p^{nN}` — the product formula, division-
free and level-independent (the pin count is fixed once `N ≥ N(H,Z)`; larger `N` only enlarges the
free box).

**M5 — The (ZC) invariant as a `Type`-bundle `ZCData D`.** Carries the rim threshold `rimStart :
Fin m` and the cumulative fresh count `freshSum`, with (ZC-a)+(ZC-b) as `pin_dichotomy` (every
pinned coordinate is a rim lead OR a literal zero — the zero-downset core vs. `DIG_i` leads-at-rim)
and (ZC-c) as `zc_c : numPinned = freshSum`. `JetSetup H m` bundles the DEFERRED presentation: the
per-prefix `Σ_i` with its `ZCData`, the per-step `FreshData`, the moves `Θ_i` (unitriangular), and
the defining RECURSION `Σ_{i+1} = Θ_i(Σ_i ∩ E_fresh(ν_i))` (§C.1.5′'s `(R)` two-sidedness).

**M6 — Boundary-deferred graded interfaces (never approximated).** `LstData σ ht lines i` (LST: the
scale `ht(ℓ,b)=ℓ+off(b)`, floor constancy, and the SELECTION property — level set above floor);
`TypObject s α` (TYP: a SURJECTIVE additive hom from the weight-γ′ level-set assignments onto the
digit alphabet — the piece map `R_δ`); a coordinate-height presentation `htc : Fin m → ℚ`
(KEY OBS 1: `w`-clauses as literal zero downsets). These encode the unbuilt graded ring; the units
that consume them are PROVABLE-FROM-INTERFACE and flagged (§4).

---

## 2. Which accepted §B2-DEF objects §C consumes

§C imports `Moves.{Defs,DefsT,DefsCore,DefsL}` (all four Defs layers; oleans present). It reuses:

| accepted object | file | §C use |
|---|---|---|
| `DigitSystem`/`IsSolution`/`numPinned` | DefsT | `Locus`, mass, PIN-WELLDEF, all counting |
| `Stage` | Defs | the frame of each `Node` (M3) |
| `TransitionCoreL` (D.7) | DefsL | `HistoryCoherent` increment link |
| `IsRecenteringCore` (D.10) | DefsCore | `HistoryCoherent` recentering link |
| `StageCoreL` / `LandingCylinderL` (D.8) | DefsL | supplies each read's stratum → the root init (`C1.zcInit`) and step re-presentation (`C4.zcPersist` cites `L5.landTwoSided`) |
| `OrdPsiPoly` / `%ₘ`,`/ₘ` at monic ψ | Defs / mathlib | `Node.vtxPoly` (the transported vertex value) |
| `L2.P6ii` (the `|α|^{n−k}` count) | Moves MANIFEST | `C0.digitSystemMass` |

§C adds NO new axiom and touches NO existing statement. The only new trust surface is the six
`MovesC/Defs` interface predicates (§4).

---

## 3. The DAG — 7 layers, 31 units (8/4/5/4/4/2/4)

Each unit is one file `lean/LeanUrat/MovesC/<id>.lean` importing `MovesC.Defs` + its `deps`.
Verbatim statements + per-unit sketches in `MANIFEST.json`; below is the skeleton and the
load-bearing edges. **PROV** = provable outright; **PROV/IF** = provable from a deferred interface
(§4); **AFF** = pure affine/ℚ arithmetic.

**C0 — digit systems / global order / transport corollary (C.0, C.0.5) [8].**
`coordPrec_trichotomy`, `coordPrec_trans` (AFF, `≺` a strict linear order); `coordSort` (PROV, the
≺-sorted enumeration `Fin n×Fin N ≃ Fin (nN)`); `digitSystemMass` (PROV via `L2.P6ii`,
`mass=p^{m−k}`); `pinWelldef` (PROV, PIN-WELLDEF); `unitriBij` (PROV, invert in ≺-order);
`moveMass` (PROV, bijection ⟹ equal `Nat.card`); **`pinTransport`** (PROV, hard — the C.0.5
pin-transport corollary: `Θ*(E)` has the same pins/vol).

**C1 — the (ZC) state cylinder (C.1.5) [4].**
`zcMass` (PROV, `mass=p^{m−freshSum}`); `zcInit` (PROV, root init `freshSum₀=m*₀` — base of the
recursion, consumes the root `LandingCylinderL`); `valClauseDownset` (**PROV/IF** — KEY OBS 1: a
`w≥β` clause = literal zero downset, via the deferred height presentation `htc`); `rimLeads` (PROV,
hard — (ZC-b′) leads-at-rim persist under `Θ`-pushforward, via `pinTransport`).

**C2 — DOM / TYP / LST — the geometric+graded interface (C.1) [5].**
**`DOM`** (AFF — interior floor domination, the displayed affine induction from `steeper`+`vertex_
entry`); `DOM_floorForm` (PROV — floor `=` current line on the interior, `sup'`); `LST_selection`
(**PROV/IF** via `LstData` — level set above floor); `LST_typing` (**PROV/IF** via `LstData` — the
scale `ht=ℓ+off`); `TYP_fiberCount` (PROV — a surjective `AddMonoidHom` has equal fibers, so a value
clause cuts `|α|⁻¹`; the `TypObject` itself is deferred).

**C3 — the species inventory + E_fresh selection (C.1) [4].**
`crossing` (AFF — §C.1(i)(α), single crossing `j×`, convex interpolation); `crossing_reverse` (AFF —
(γ) right of `j×`, weaker bound); `EInh_implied` (**PROV/IF** — E_inh at/below floor is implied on
`Σ_i`); `freshFree` (**PROV/IF** — E_fresh constrains only FREE coordinates strictly above the
floor).

**C4 — C.1.5′ the per-step conditional exactness lemma [4].**
`stripCount` (PROV — fresh strip zeros are free, each cuts `p⁻¹`); `valueCount` (PROV — a value
clause cuts `|α|⁻¹`, via `TYP_fiberCount`); **`conditionalMass`** (PROV, hard — §C.1.5′(1):
`numPinned(Σ_i ∩ stratum) = numPinned(Σ_i)+m*`); **`zcPersist`** (PROV, hard — §C.1.5′(2): (ZC) for
`Σ_{i+1}`, via `conditionalMass`+`rimLeads`+`L5.landTwoSided`).

**C5 — the mass recursion (C.2) [2].**
**`massRec`** (PROV — induction: `numPinned(Σ_k)=Σ_{i≤k} m*(ν_i)`, from `zcInit`+`zcPersist`);
`numPinnedCodim` (PROV — `mass(Σ_k)=p^{nN−Σm*}`, level-independent).

**C6 — Theorem C (C.2) [4].**
`transportedAdmissible` (PROV — admissible `Z` cuts exactly `p^{−|pins Z|}`); `psiBij` (PROV —
`Ψ_H` a global digit-level bijection); **`thmC_b`** (PROV, hard — Theorem C(b), the product formula
in pin-arithmetic); **`thmC_a`** (PROV, hard — Theorem C(a): `S(H,Z)=Ψ_H⁻¹(Σ_k∩locus Z)` carried
bijectively, equal pin count via PIN-WELLDEF).

**Load-bearing cross-layer edges (acyclic — verified by construction, no back-edges):**
`digitSystemMass → {zcMass, numPinnedCodim, thmC_b}`; `pinWelldef → {pinTransport, thmC_a}`;
`unitriBij → {moveMass, pinTransport, psiBij}`; `pinTransport → {rimLeads, zcPersist}`;
`TYP_fiberCount → valueCount → conditionalMass`; `{zcInit, zcPersist} → massRec →
{numPinnedCodim, thmC_b}`; `DOM → DOM_floorForm → LST_selection`. The mathematical induction is:
root init (`zcInit`) → [`conditionalMass` → `zcPersist`] repeated along the history → `massRec` →
Theorem C; the file DAG unrolls one step and the history is closed by the parametric `JetSetup`
quantification.

---

## 4. Honest gaps — the boundary-deferred graded ring (for the semantic audit)

All five deferrals are ONE object: the **unbuilt graded ring** — the §B2-DEF campaign's standing
boundary since round 1 (blueprint `MOVES_LEAN_BLUEPRINT_2026-07-26.md` §R5.3), specifically its
round-4 gap R4.5 items **1** (graded pieces `gr^Ĉ_δ` and the piece map `R_δ`) and **3** (the global
jet-coordinate system: Fact A applied down the WHOLE tower, giving literal digit coordinates on
every coefficient space — "§C territory", R4.5 item 3 explicitly names this). §C consumes it through
FOUR flagged interface predicates in `MovesC/Defs`. Each is faithful (non-vacuous content, verified
by hand) and the consuming units are provable FROM it — the deferral is that the interface is
ASSUMED, not built, exactly as `L6.measureExact` assumes `codeN`/`ΘN`/`hcylN`.

- **G1 — `LstData` (LST typing + selection).** Carries `ht(ℓ,b)=ℓ+off(b)` (`ht_scale`), floor
  constancy (`floor_const`), and SELECTION (`selection`). **Deferred half:** that `off` equals the
  genuine `κ_r = h_r/(e_r·STR_r)` combination = the K1-chain weight of the coordinate's basis
  monomial `p^ℓ·∏ Φ̂_r^{innerslot}`. Needs the graded piece structure (item 1) + the jet coordinates
  (item 3). Consumed by `LST_selection`, `LST_typing`, and (via the crossing) `freshFree`.
  **FLAG:** the identification `ht = K1-chain weight`.

- **G2 — the coordinate-height presentation `htc : Fin m → ℚ`.** KEY OBS 1: a valuation clause
  `w(B)≥β`, since `w` is the iterated K1 slot-minimum, is LITERALLY the zero downset
  `{y_c=0 : ht(c)<β}`. Stating this in `Fin m` coordinates needs `htc` = the height of each base
  digit = the jet-coordinate system (item 3). Consumed by `valClauseDownset`, `EInh_implied`,
  `freshFree`. **FLAG:** that `htc` is realized by the K1 chain (no carries in valuation content).

- **G3 — `TypObject` (the piece map `R_δ`).** TYP: the weight-γ′ initial form lives in `gr^Ĉ_δ`
  (`δ=str·γ′`) and its fresh value clause is a SURJECTIVE additive hom onto the digit alphabet
  (image = the additive span of the slot images, D.3(e)(i)). Its combinatorial CONSEQUENCE (equal
  fibers ⟹ cuts `|α|⁻¹`) is PROVEN (`TYP_fiberCount`); the OBJECT — that the real fresh value clause
  IS such a surjection — is the graded piece (item 1). Consumed by `valueCount`→`conditionalMass`.
  **FLAG:** that the fresh value digit is graded/level-set-supported/carry-free.

- **G4 — `JetSetup` (the global presentation of a history).** Bundles, per prefix, the presented
  `Σ_i` (a `Locus`), its `ZCData`, the `FreshData`, the unitriangular moves `Θ_i` (C.0.5's
  unitriangularity — Fact A down the tower, item 3), and the RECURSION
  `Σ_{i+1}=Θ_i(Σ_i∩E_fresh)`. This is the whole jet-coordinate presentation of `S(H,Z)`; the
  counting theorems (C4/C5/C6) are provable from it. **FLAG:** that a real classifier history is
  presented by such a `JetSetup` (the §C analogue of `L6.measureExact`'s `codeN`/`hcylN`).

Additional honest notes, NOT silent weakenings:
- **C.0.5 unitriangularity itself** ("move maps are unitriangular by Fact A's division accounting")
  is supplied by `JetSetup.Theta_uni` (G4), NOT proven as a standalone §C unit — the divisions live
  in the tower/Fact A. The pin-transport COROLLARY (`pinTransport`) IS proven.
- **`Node.vtxPoly` well-definedness** ("`(R_anch/ψ^μ) mod ψ` is pattern-only, independent of the
  lift") is stated at the polynomial level; the z̄-power scalar and residue-field arithmetic of the
  full `vtx ∈ F_{i+1}ˣ` are folded into `Realizable`'s (HV) clause, not reproven. FLAG.
- **`N(H,Z)` finiteness / level-independence** is not a separate unit: it is built into M4's
  pin-arithmetic form (the pin count is fixed once `N ≥ N(H,Z)`; each unit is stated per-`N`).
- **Aggregation over histories / shape-menu finiteness / depth resummation** — §C.3 explicitly does
  NOT claim these (assembly-note burden); no §C unit touches them.

---

## 5. Elaboration-test record

`MovesC/Defs.lean` compiles green: `lake env lean LeanUrat/MovesC/Defs.lean` exit 0, no output; no
`sorry`, no `axiom`; 333 lines; olean built via `lake env lean -o` (never `lake build`, per repo
README). It imports and rests on `Moves.{Defs,DefsT,DefsCore,DefsL}` (oleans present).

**All 31 `MANIFEST.json` statements were elaboration-tested** (`:= sorry` against the
`Defs`+`DefsT`+`DefsCore`+`DefsL`+`MovesC.Defs` preamble with the section binder
`{p:ℕ}[Fact p.Prime]{F:Type*}[Field F][Finite F]`; `lake env lean`, exit 0, exactly 31 `sorry`
warnings, zero errors, split across two scratch files of 18 + 13). Coverage spans every layer:
C0×8, C1×4, C2×5, C3×4, C4×4, C5×2, C6×4. Difficulty split 6 easy / 18 medium / 7 hard; 5 units are
boundary-deferred (G1–G4 interfaces): `valClauseDownset`, `LST_selection`, `LST_typing`,
`EInh_implied`, `freshFree` (`TYP_fiberCount` is PROVEN — only the `TypObject` it consumes is
deferred).

**Convention for the fan-out.** Build per file with `lake env lean LeanUrat/MovesC/<file>.lean`;
end each file with `#print axioms` (Lean-core only; `sorryAx` acceptable this campaign but flag in
the docstring). Search-before-prove ladder as the repo standard. Do NOT edit `MovesC/Defs.lean`
without re-running the §5 elaboration sample; new shared defs go in a `MovesC/Defs2.lean`.

---

# ROUND 2 (2026-07-26) — rebuild after the STOP-THE-LINE audit

*The round-1 manifest above is RETIRED (do not fan out from it). The audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_2026-07-26.md` found 5 structural failures, 13 FAITHLESS
units and 3 outright-false statements. `MovesC/Defs.lean` was OVERWRITTEN (round 2, 399 lines,
compiles green under `lake env lean`, no `sorry`/axiom) and `MANIFEST.json` rebuilt: 34 units,
all statements elaboration-tested twice, the second time generated verbatim FROM the manifest
JSON. This section answers each audit objection at its own address.*

## R2.A — answers to the definitions audit (audit §a)

**A1. "`Node` stores many appropriately named fields, but does not enforce their §C meanings."**
Point by point, all now `Prop` FIELDS of `Node`:
- *`Ranch` untied to `pat`/stride/anchor* → `hRanch : Ranch = Σ_{k ≤ wSide/e} C (pat k)·X^k`
  (D.3(c)'s stride positions collapse to CONSECUTIVE powers past the anchor because consecutive
  on-lattice slots differ in z-position by `e·s + h·t = 1`; the anchor `a` locates the absolute
  position `a + k` and enters `vtx` as `z̄^{a−μm̂}`), plus the polygon-convention endpoints
  `hpat0 : pat 0 ≠ 0`, `hpatTop : pat (wSide/e) ≠ 0`.
- *`ψ` unconstrained* → `hψmonic`, `hψdeg : ψ.natDegree = g`, and `hOrd : OrdPsiPoly ψ Ranch μ`
  (`ψ^μ ∥ Ranch` EXACTLY — the reused accepted predicate).
- *`e, h, g, μ, Dwidth, line`, stage mutually unrelated* → `he/hh/hcop` (lowest-terms side),
  `hg/hμ` (genuine descend), `hEdvd : e ∣ wSide`, `hDwidth : Dwidth = σ.Φ.natDegree` (frame
  link), and in `HistoryCoherent`: the width chain `Dwidth_{i+1} = e_i·g_i·Dwidth_i`
  (`Node.childWidth`), the (I-aug) slope chain `slope_i < slope_{i+1}`, and the absolute-scale
  slope law `slope_i·(e_i·STR_i·D_i) = h_i` with `STR_i = History.strFrame i = Π_{m<i} e_m`.
  NOT enforced (honest): the line's INTERCEPT tie to the pinned vertex — that is D.8 geometry,
  still entering through `DomData.vertex_entry` as a hypothesis.
- *species constraints absent* → `hspecInc : increment → 1 < e·g`,
  `hspecRec : recentering → e = 1 ∧ g = 1`, `hspecRecCenter : recentering → ψ = X − C center ∧
  z̄ = center` (D.10's consumed linear factor at the recorded center).
- *recentering witness existential, untied to the recorded lift* → `HistoryCoherent` now states
  `IsRecenteringCore σ_i σ_{i+1} center_i lift_i` AT the parent node's RECORDED `center`/`lift`;
  no existential anywhere in the coherence predicate.
- *increment transition used child-Stage fields, not the node's recorded read data* → the
  increment/root clause is `IsStandardLift σ_i ψ_i g_i (σ_{i+1}.Φ) ∧ TransitionCoreL σ_i σ_{i+1}
  (σ_{i+1}.Φ) e_i h_i z̄_i` — the recorded `ψ, g, e, h, zbar` of the PARENT node, keyed on the
  PARENT's species (the read that produces the next frame), with the lifted key pinned to the
  child frame's actual key.
- *"a later node may have species root"* → `History.root_iff : species = root ↔ index = 0`, and
  the coherence transition clause is TOTAL over species (recentering vs. not-recentering).
- *`HistoryCoherent`/`Realizable` unconsumed* → both are FIELDS of `JetSetup`
  (`coherent`/`realizable`), so every C4/C5/C6 theorem consumes them by construction;
  `C3.steeperChain` additionally consumes coherence directly (it supplies `DomData.steeper`).
- *(HV) vacuous (`∃ lead, vtxPoly = lead`)* → `Realizable`'s adjacent clause is now the data
  IDENTITY `(pat_{ν_{i+1}} (wSide/e) : F) = vtx(ν_i)` where `Node.vtx := z̄^{a−μ·m̂} ·
  ((Ranch/ψ^μ) mod ψ)(z̄) ∈ F` — the FULL transported vertex value with its scalar factors
  (`m̂ = −t·h·g`, `Node.mhat`), valued in the ambient field containing `F_{i+1} = K(z̄)`;
  `z̄` is required to be a genuine root of `ψ` (`hzbarRoot`). Nothing is trivially witnessable.
- *(NA) typing (line evaluated at a slot index)* → (NA) now compares both lines at the BASE
  index `μ_i·childWidth_i` (= `μ_i·D_{i+1}`).

**A2. "Locus and mass: locally faithful, globally incomplete."**
- *`m` never tied to `n·N`* → `JetSetup.hm : m = n·N`, with `n N` explicit parameters.
- *no `N(H,Z)` hypothesis* → recorded honestly as an EXISTENCE condition on the presentation
  (the `JetSetup` docstring): a jet presentation exists at every `N ≥ N(H,Z)`; each unit is
  stated per presented box. `N` largeness is not internalized as arithmetic — flagged in R2.C.
- *`coordSort` cardinal-only; flattening unlinked* → two repairs: the theorem `C0.coordSort` now
  produces the SORTED enumeration (`j < j' ↔ CoordPrec (f j) (f j')`, range in the box), and —
  the load-bearing one — `JetSetup` carries the chart `coordOf : Fin m → Coord` with
  `coordOf_sorted : j < j' ↔ CoordPrec (coordOf j) (coordOf j')` and `coordOf_lt` (levels `< N`,
  indices `< n`), so every downstream height/floor/rim statement reads through the genuine
  `(level, index)` pair rather than a bare `Fin m`.

**A3. "`ZCData` materially weaker than (ZC)."** Rebuilt (parameters: `coordOf`, `ht`, `floor`,
`rimIdx`):
- *floor downset not exact* → `downset_exact : pinned j = true ↔ ht(coordOf j) ≤ floor(index)`
  at interior indices — BOTH directions (the round-1 `pin_dichotomy` allowed under-pinning);
  *literal zeros* → `interior_zero : interior pins solve to 0`.
- *no floor or height map; not node-dependent* → the floor parameter is pinned by `JetSetup.zc`
  to `History.floorH (i+1)` — the max of the recorded nodes' `Node.staircase` step functions
  (line value at the left block edge on the factor interior `[0, μ·childWidth)`, `⊥` outside) —
  and the rim threshold to the RECORDED `μ_i·childWidth_i`.
- *rim not a ≺-suffix; `rimStart := 0` vacuity; `m = 0` uninhabited* → the rim condition is now
  a BASE-INDEX region (`(coordOf j).2 < rimIdx`), exactly §C's `≥ μ_i·D_{i+1}`; `rimIdx : ℕ` is
  node-supplied (not a free `Fin m` datum), so the vacuity move and the `m = 0` failure are gone.
- *DIG solving for whole rim LEVEL SETS* → NOT encoded (honest): `DigitSystem` pins are
  per-base-digit; the counting consumes only rim-ness of the non-zero pins (C15 S4c). Flagged.

**A4. "`FreshData` contradicts accepted Route B (pin addresses)."** The round-1
`coords : Finset (Fin m)` + `pinTo` model is DELETED. A fresh clause is now a `LevelClause`:
`support` (strip region / weight-γ′ level set) + `codim` + a constraint `sat` with `dep` (reads
only the support) and `count` — the division-free EXACT-FIBER law `#{supported y | sat y}·
p^codim = p^{|support|}`. A fresh value clause is an additive function of an entire level set,
entering ONLY through `C1.TYP_toClause` (so `C4.conditionalMass` now genuinely consumes TYP —
the audit's "bypasses TYP" is structurally impossible); strip zeros are the singleton case
(`C1.stripClause`). `FreshData = clauses + pairwise-disjoint supports`; freeness on `Σ_i` is the
THEOREM `C2.freshFree` (from the exact downset + the above-floor/interior links), not a field.
The `count` field is self-policing: an unsatisfiable or inexact clause admits no instance.

**A5. "Pin arithmetic sound, but `thmC_b` disconnected and false in general."** The final
statements are now Theorem C: `C6.thmC_a/b` are stated about the ACTUAL final joint locus
`{x | Σ_len x ∧ Z x}` and its image `S(H,Z)` under the RECORDED composite `JetSetup.Psi`
(`Ψ_H`), with `AdmissibleZ` against the FINAL state `Sigma H.nodes.length`, `m = n·N`, and
coherence/realizability consumed through `J`. No existential `Dfin` remains anywhere.

## R2.B — the audit's per-unit dispositions

FAITHLESS/IMPRECISE round-1 units and their fates: `C0.coordSort` → re-stated with the order
property; `C0.pinWelldef`/`C0.pinTransport` → upgraded to per-coordinate STATUS (`C0.pinStatus`
new; `pinTransport` returns the same pinned FUNCTION); `C1.zcInit` → deleted (initialization is
`JetSetup.init`: `Sigma 0` IS the full box — nothing left to assume-as-conclusion);
`C1.valClauseDownset` → deleted (the K1-downset realization is presentation content inside the
deferred `Sigma`; no synthetic `htc` unit survives); `C1.rimLeads` → deleted (rim persistence
is `JetSetup.zc` at every prefix — interface content, honestly deferred, no longer fake-proved);
`C2.LST_selection`/`C2.LST_typing` → deleted with `LstData`; their genuine content became the
`JetSetup` links `fresh_above` (LST(iii) selection) + `zc` floor exactness, consumed by
`C2.freshFree`; the ht-=-K1-weight identification stays flagged on the bare `ht` field;
`C3.EInh_implied` → re-stated as FORCED ZEROS on the locus from the exact downset (derives,
not restates); `C3.freshFree` → `C2.freshFree` (no rim alternative in the conclusion: fresh
supports are interior by `fresh_interior`); `C4.conditionalMass` → re-stated address-free over
`LevelClause`s (consumes TYP via the clause bridge); `C4.zcPersist` → deleted as a theorem
((ZC) persistence is interface content; the numeric residue it carried is `C4.numPinnedStep`,
proved from masses); `C5.massRec`/`C5.numPinnedCodim` → re-indexed (`Sigma 0` = full box; sum
over `range k`; `k ≤ len`) — the audit's k = 0 countermodel is unbuildable since `init` forces
`numPinned (Sigma 0) = 0` and `fresh 0` sits between `Sigma 0` and `Sigma 1`; `C6.psiBij` →
about the recorded composite `JetSetup.Psi` (with `C6.transportedSystem` supplying the
history-composition content); `C6.thmC_a/b` → see R2.A5. FLAGGED-OK units (14) are carried
over verbatim or strengthened.

## R2.C — honest gaps after round 2 (the deferred boundary, restated)

1. **`JetSetup` existence for a real classifier history** — the unbuilt graded ring / global
   jet-coordinate system (R4.5 items 1&3). Includes: the presentation of each `Σ_i` as a digit
   system; `Theta_uni` (Fact A's division accounting); the `recursion` field, which ABSORBS
   C.1(i)'s inherited-clause implication (the crossing analysis) into the presentation; the
   (ZC) invariant `zc` at every prefix (persistence, C15 S4c); `fresh_above`/`fresh_interior`
   (LST(iii) + rim domination). These are §C's PROVED steps — deferred here only because their
   Lean form needs the jet coordinates; the interface records their exact statements.
2. **`ht` = the K1-chain weight** (LST(i)): `ht` is bare data; its identification with
   `l + Σ innerslot_r·κ_r` at CURRENT κ is deferred.
3. **`TypObject` existence** for each real fresh value digit (graded piece `gr^Ĉ_{δ'}`, piece
   map `R_δ'` additive/injective/image = alphabet).
4. **`N ≥ N(H,Z)`** is an existence condition on the presentation, not internal arithmetic.
5. **(ZC-b) level-set grouping** of DIG equations not encoded (rim-ness of pins only).
6. **`vtx ≠ 0`** (hence `∈ Fˣ`) is not claimed: needs ψ-irreducibility/residue-iso content;
   the polynomial factor's nonvanishing IS proved (`C3.vtxPolyNe`).
7. **`DomData.vertex_entry`** (D.8's box geometry) remains a per-instance hypothesis; only the
   `steeper` half is derived from coherence (`C3.steeperChain`).
8. **`m*(ν_i)` = the D.11 species inventory**: `mstar` is the presented clauses' codim sum; its
   equality with the inventory computed from node data (α/β/γ strips + value digits) is
   presentation content.
9. **Line intercept tie** (the read line passes through the pinned vertex) not enforced (A1).

## R2.D — elaboration record (round 2)

`MovesC/Defs.lean`: 399 lines, `lake env lean` exit 0, no output, no `sorry`/`axiom`; olean
rebuilt. All 34 manifest statements elaborated with `:= sorry` against the standard preamble —
TWICE: hand-assembled scratch (12+12+10, zero errors), then REGENERATED VERBATIM from
`MANIFEST.json` by script and re-run (12+12+10, zero errors, two runs). Scratch files removed.
Layer counts 10/4/6/4/3/2/5 = 34; difficulty 6 easy / 22 medium / 6 hard; 12 units carry a
deferred-interface hypothesis (`JetSetup`/`TypObject`).
