# verdict_SPB — UNIT SPB: the carrier→calculus spine bridge — the wiring laws dissected at the wired-read genre; the keystone site half fires through the spine route (2026-08-31)

**Status: COMPLETE.**
`leanfinal/Uniformity/ChapI/I10SpineBridge.lean` (NEW, ~530 lines, namespace
`Uniformity.Density.DeepExport`) — 0 errors, 0 warnings, **0 `sorry`**; all **18**
printed footprints exactly `[propext, Classical.choice, Quot.sound]` (machine-tallied,
non-core set = NONE).  Verified per-file (`timeout 580 ~/.elan/bin/lake env lean
Uniformity/ChapI/I10SpineBridge.lean`, exit 0, 12 s), per-target
(`lake build Uniformity.ChapI.I10SpineBridge` — Build completed successfully, 8983
jobs), and the chapter aggregator `Uniformity/ChapI.lean` re-verified exit 0 after the
one standing import-line edit.  Cite ledger: **empty** — Lean core over the landed
corpus.  `maxHeartbeats` at the corpus-standard 800000 (see repair log — no raise was
ultimately needed).  No git operations.

## CHARGE 1 ANSWERED — do the wiring laws FIRE at the keystone from the completed packs?

**YES they fire — and the kernel-agreement is NOT `rfl`/defeq.**  The adjudication of
the charge's hypothesis ("the keystone realization was BUILT from this tower, so
kernel-agreement may be rfl/defeq"):

* The keystone export was NOT wired to the tower's pack reads: it was wired at
  construction to the CONSTANT `1` (IFC4's P3 licence, GCW-6-mandated at depth ≥ 4;
  `C136c0.s2Four_towerReadFamily_live`).
* The tower's own reads — the R4K packs' reads (`s2Rung2Pack`/`s2Rung3Pack`/
  `s2Rung4Pack`, host `(s2DepthTwo).fld 2`) and the site calculus's `Rgr` — agree with
  the export **VALUEWISE, through the card-2 collapse**: each is NONZERO on its lawful
  domain (the packs' `exact_ne`; the bank's B-1 `Rgr_ne_zero` rows — the same FGMN
  `graded_scalar_nonzero` mechanism), and every nonzero value of a 2-element field is
  `1`.  One `c0`-collapse per law; no new structure; no type-level hom between the pack
  host and the realization's `Kt` exists or is needed (none is landed; the agreement is
  by shared value).  Machine pins: ★ `s2Rung2_read_eq_one` / `s2Rung3_read_eq_one` /
  `s2Rung4_read_eq_one` — the pack reads are constantly `1` on their exact-grade
  domains below the key fence, i.e. the exports and the tower's own reads take the SAME
  value everywhere both are lawful (§6, consuming the packs' own `exact_ne`).

**The fire** (all at every depth-4 keystone witness, conditionality exactly the
keystone's; universes `.{0, 0, uL}`):

* ★ `s2Four_bankWiredAt` — `BankWiredAt` NAMED at the standalone bank
  (`s2FourSiteBank`), proved through the SPINE route (genre pin + card-2 + the bank's
  own B-1 nonvanishing) — **no `GC13Wiring` instance consumed** (the landed direct
  route `s2Four_gc13Wiring` is not cited in the proof).
* `s2FourBankFamily` (def) + ★★ `s2Four_bankWiringSupply` — **the first named
  `BankWiringSupply` instance** (SCS's per-realization residue, closed).
* Coherence examples: `SiteCalculusSupply`, `CarrierReadSupply`, ★★ `WiredSiteSupply`
  (the deepTwist SITE HALF), and `GentowPerWitnessExporter`, each re-derived at the
  keystone through the spine route alone — agreeing with the landed direct instances
  (`s2Four_siteCalculusSupply`, `s2Four_carrierReadSupply`, `s2Four_wiredSiteSupply`,
  `s2Four_gentowPerWitnessExporter`) on the wired genre.  (Named duplicates avoided:
  where a named instance already exists in the corpus, this unit lands an `example`.)

## CHARGE 2 — the generic/keystone dissection (the TWD/WSS pattern), PROVED

Genre pin `ReadOneAt X j` (NEW STATEMENT, review): the exported read at level `j` is
constantly `1` — what EVERY wired-genre witness (IFC4 `s2SplitNodeWired`, depth-four
`s2SplitNodeFour`, any thresholds/payload) exports by construction.  At the genre the
three wiring laws dissect EXACTLY — iffs, uniform in `q`, the frame, the tower, the
bank, the realization:

| wiring law | at `ReadOneAt`, EXACTLY (iff) | card-2 discharge (generic constructor) |
|---|---|---|
| `BankWiredAt` (GC-13 read law) | `φ(Rgr(e'·(s·u'), chainNormBelow(s·u'))) = 1` per window `1 ≤ s ≤ f'` — ★ `bankWiredAt_iff_of_read_one` | ★ `bankWiredAt_of_read_one_card`: the bank's OWN B-1 nonvanishing + receiver injectivity (fields) + collapse |
| `CarrierReadLaw.read_ker_pow` (kernel-agreement + power law) | `res k = 1` for every height-kernel element — ★ `carrierReadLaw_iff_of_read_one` | ★ `carrierReadLaw_of_read_one_card`: trivial unit group |
| `CarrierReadLaw.tie` (peel) | `peelUnit = 1` (same iff) | same collapse |

Plus `read_mult_of_read_one` — the constant read trivially realizes the `read_mul`
multiplicativity shape the packs export (RL3 §7's "multiplicativity half"), i.e. the
`hmul` input of LRS's `carrierReadLaw_of_mult_agree`; a coherence example fires that
coarse route too.  **Keystone-specific inputs are exactly three**: the genre pin
(`s2Four_towerReadFamily_live` → `s2Four_readOneAt`), the terminal-field cardinality
(`s2R7Fld_card`), and the bank (`s2FourSiteBank`, `(h2, hq)` alone).  At a GENERAL-`q`
wired-constant witness the iffs show the residue does NOT vanish (`res ≡ 1` and
`peelUnit = 1` are genuinely false in general) — beyond card 2 the wired genre must
wire the read NON-constantly to the receiver image of the bank's reads (GC-13's formula
as the construction).  No machine refutation is constructible from the landed corpus
(the only landed realization genre is card-2) — flagged honestly, as in LRS.

★★ **THE GENRE THEOREM** — `wiredSiteSupply_of_bankFamily_read_one_card`: at ANY
arising realization of the wired card-2 genre, the deepTwist SITE HALF (WSS's
`WiredSiteSupply` = `SiteCalculusSupply` ∧ `LadderReadSupply`) reduces to the
**TOWER-SIDE BANK FAMILY ALONE** — the per-realization wiring residue VANISHES at this
genre.  Chain corollary `gentowPerWitnessExporter_of_read_one_card`.  Supply-level
routes are SUFFICIENT-ONLY (no converse claimed); the per-law dissections are exact
iffs.

## CHARGE 3 — the deepTwist boundary after SPB (post-O-TAU form)

Per the landed iff (`deepTwistField_iff_universalPerWitness`) the boundary is UNCHANGED
in strength.  The sufficient surface:

    deepTwist ⟸ UniversalTauWordDescentSupply    [tau half — OUT OF THIS UNIT'S
                                                   TERRITORY: per TAU2, the lattice/
                                                   kernel-span route is REFUTED and the
                                                   pinning guard awaits the O-TAU owner
                                                   amendment; the guarded route
                                                   universalPinnedTauSupply_of_descent
                                                   is landed]
               ∧ UniversalSiteCalculusSupply      [= universal bank family ⊗ wiring, SCS iff]
               ∧ UniversalLadderReadSupply        [⟸ CarrierReadSupply, LRS]

The SITE HALF after SPB, stratified per arising realization:

| witness stratum | per-realization residue | tower-side residue |
|---|---|---|
| wired card-2 genre (every keystone witness) | **EMPTY** (the genre theorem) | a `LevelSiteBank` family — at the keystone, LANDED (`s2FourBankFamily`, `(h2,hq)` only) |
| wired general-`q` genre | exactly the unit equations of the iffs (`φ(Rgr…) = 1` per window; `res ≡ 1`; `peelUnit = 1`) — false in general, so the read must be wired non-constantly | same bank family |
| arbitrary realizations | `BankWiringSupply` + `LadderReadSupply` (SCS/LRS's named remainder, verbatim) | same |

The remaining open MATHEMATICS of the site half is therefore concentrated tower-side:
the `LevelSiteBank` family at general frames — and within the L2E program, note the
CARRIER side is now closed generically at `f' = 1` and completely at the keystone
(RL3/W3P/R4K); the open leg is the carrier→CALCULUS transcription (producing
`FGMNCalculus` operators + B-1 grades from `RungPack` data), plus the `PrevGrade` leg
at `f' ≥ 2`.  That is the exact successor charge for the spine program.

## New statements flagged for the standing review

`ReadOneAt` (the genre pin — the one genuinely new interface Prop);
`bankWiredAt_iff_of_read_one`, `bankWiredAt_of_read_one_card`,
`carrierReadLaw_iff_of_read_one`, `carrierReadLaw_of_read_one_card`,
`read_mult_of_read_one`, `bankWiringSupply_of_read_one_card`,
`siteCalculusSupply_of_bankFamily_read_one_card`, `carrierReadSupply_of_read_one_card`,
`wiredSiteSupply_of_bankFamily_read_one_card`,
`gentowPerWitnessExporter_of_read_one_card`, `s2Four_readOneAt`, `s2Four_bankWiredAt`,
`s2FourBankFamily`, `s2Four_bankWiringSupply`, `s2Rung2_read_eq_one`,
`s2Rung3_read_eq_one`, `s2Rung4_read_eq_one` — all supplier-side below the signed
surface; `BankWiredAt`/`CarrierReadLaw`/`BankWiringSupply`/`SiteCalculusSupply`/
`WiredSiteSupply` consumed verbatim on conclusion sides; nothing weakened.  Local twins
flagged for the standing dedup: `spb_eq_one_of_ne_zero` (card-2 collapse, 5th+ corpus
repetition, here universe-polymorphic `Type*`) and `spb_unit_eq_one` (unit-group
collapse, twin of `C136r4.s2FourUnit_eq_one`'s mechanism, generic).

## Repair log (one real round + one PERFORMANCE GOTCHA worth the corpus's attention)

1. (mechanical) `simp`/`rw` cannot see through the `ReadOneAt` def — fixed by binding
   the unfolded ∀-equation (`have hR : ∀ g, towerReadFamily X j g = 1 := hread`) before
   rewriting; and `set_option … in`/`omit … in` must precede the docstring.
2. **THE META-CORE BLOWUP (new gotcha, generalizing WSS's D3AD trunc-boundary note).**
   Keystone term applications of the generic lemmas with the realized input passed as
   `_` (`bankWiredAt_of_read_one_card _ hj (s2FourSiteBank h2 hq) …`) left `core` a
   METAVARIABLE while `hj : DeepLive 4 3` and the bank argument unified — the unifier
   then ground `?core.T.trunc … =?= (s2DepthFour …).trunc …` field-wise through the
   mega structure literals (whose fields carry `decide`/`norm_num` proof terms):
   >9.5 min for ONE declaration at `maxHeartbeats 40000000`, surfacing at lower caps as
   a FAKE "Application type mismatch" (heartbeat exhaustion mid-defeq, with the error
   pretty-printer itself timing out).  Diagnosis by bisection (`#exit` markers +
   statement-with-`sorry` split: statement 7 s, proof >400 s).  **Fix: pass the
   realized input EXPLICITLY** so `core` is assigned before the dependent arguments
   unify — the same declaration then elaborates in ~1 s and the whole file in 12 s at
   the standard 800000 cap.  Rule of thumb for keystone-genre term assembly: never
   leave the `RealizedInput` argument as `_` in applications whose other arguments
   mention `core.r`/`core.T`.

## Verification, footprint

* Per-increment `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10SpineBridge.lean`
  throughout; FINAL: exit 0, 0 errors, 0 warnings, `grep -c sorry` = 0; AxChk **18/18**
  Lean-core; `lake build Uniformity.ChapI.I10SpineBridge` — Build completed successfully
  (8983 jobs); aggregator `Uniformity/ChapI.lean` exit 0 after the one import line.
* Footprint: `leanfinal/Uniformity/ChapI/I10SpineBridge.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  Scratch probes
  removed.  No landed file edited; no git operations.
