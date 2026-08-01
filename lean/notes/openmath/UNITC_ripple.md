# UNIT C — NsFree keying repair: ripple enumeration (pre-edit record)

Executed 2026-08-01 (machine clock) per the 2026-08-05-dated dispatch;
sign-off of record: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md:1709`
("sign-off granted on the NsFree repair!", Asvin, verbatim). Governing specs:
`M02-count-tie_fable.md` §2 (minimal repair) + `R11_REPAIR_DESIGN_V5_2026-08-04.md`
(NSF-KEY-RET) R-0..R-5. This file is the R-1 "ripple scope, CLOSED" enumeration
(round-5 finding 5): the declarations referencing `bridgeTree`, from
`rg -n 'bridgeTree' LeanUrat/` (41 matches, 8 .lean files + 1 MANIFEST record),
each classified before editing.

## The one definition change (R-1)

* `MovesU/BridgeD3_treeCarrier.lean:94` — `def bridgeTree` gains the third
  conjunct `∧ MovesT.NsFree V` (`MovesT.NsFree`, MovesT/Defs.lean:1534 —
  existing HEAD predicate). Docstring + header (†5) display updated to match
  (comment-truth duty).

## Compile-affected ripple (destructuring of the carrier's `.2`)

* `MovesU/BridgeD4_vtLaws.lean:68` — `bridgeVt_realizedSelf := T.2.2` must
  become `T.2.2.1` (the property is now a 3-conjunct chain). ONLY such site
  in the corpus.
* `MovesU/BridgeD4_vtLaws.lean` — NEW projection `bridgeVt_nsFree := T.2.2.2`
  (the mechanical read-off of the new clause, exactly parallel to
  `bridgeVt_typemult`/`bridgeVt_realizedSelf`; it IS the compiled record that
  no ns-marked tree — in particular M02 §2's exact-square poison V₀ — is
  carried; R-3(3)'s V₀-dead artifact).

## Referencing declarations verified UNAFFECTED (no `.2` destructuring, no
## carrier-element construction)

* `BridgeD3_treeCarrier.lean:100,105-107` — DecidableEq instance
  (Classical.decEq), `bridgeTree.lvl` (reads `T.1` only).
* `BridgeD4_vtLaws.lean:39,50,56,61` — `bridgeVt := T.1`, `bridgeThr`,
  `bridgeVt_typemult := T.2.1` (unchanged position), `bridgeVt_thr` (rfl).
* `BridgeD6_fiberUniq.lean:44,55,68-69` — †7u uniqueness trio: all through
  `bridgeVt`/`bridgeVt_typemult`/`vtree_eq_of_fiberAt`; M02's effects list
  ("never used the ns clause") confirmed.
* `BridgeD7_canonical.lean:60,85,92,103` — `bridgeCanonical` + pin: the ∃
  quantifies over the carrier; adding a clause re-scopes the classifier
  AUTOMATICALLY (this is the repair's intended mechanism: exact squares now
  fiber no carried tree ⇒ drain to `none`/env). No destructuring.
* `BridgeD17_treeOf.lean` (7 sites) — `bridgeTreeOf`/`thr_le`/`treeOf_pin`:
  choice on the pin's ∃; carrier-generic.
* `BridgeD18_treePin.lean:46` — parametric assembly (all fields binders);
  types re-elaborate over the guarded carrier unchanged.
* `BridgeKernels.lean:183-185` — `bridge_slice_finite`: injects via `T.1`
  into the finite realized family; the guarded carrier's slice is a SUBSET
  of the old one — `Set.Finite.subset` shape unchanged (proof injective on
  values, indifferent to the extra clause).
* `BridgeMk.lean:47-60` — intended-wiring comments only.
* `MovesD/MANIFEST.json:707` — historical footprint record; not code.

## Statements re-typed THROUGH the carrier (R-2: texts byte-identical)

1. `TreeSeam.count_tie` (DefsLedger.lean:241) — at the wired instance
   `F.Tree σ := bridgeTree n p σ` its ∀ T now ranges over ns-free carried
   trees = the hdet-guarded corpus (`MovesT.treeN`'s `hdet` clause,
   E11_treeN.lean:50, = `MovesT.NsFree` unfolded). TEXT UNTOUCHED.
2. `ClassifierSpec.canonical_stable` (Defs.lean:65) — at
   `canonical := bridgeCanonical` over the guarded carrier. TEXT UNTOUCHED;
   validation = BridgeD8's `bridgeCanonical_stable` re-compiles green.
3. `VPSound` (Defs.lean:72) — TEXT UNTOUCHED; remains the open kernel
   (ledger field `cl10_vpsound`); retirement artifact = V₀-dead record
   (`bridgeVt_nsFree`) + consuming wiring re-compiled. NO proof promised
   (R-3(3), the round-4 de-overpromise).

## Known de-syncs recorded (OUT of the closed ripple scope — no edit)

* `BridgeD16_vtSurj.lean` — never names `bridgeTree` (inlined 2-clause
  anonymous subtype); its header's "IB-D3's `Tree σ` is definitionally this
  subtype" becomes STALE after the repair, and the repackaging of
  `bridge_vt_surj` into `TreePin.vt_surj` at the guarded instance now owes
  an ns-free scope (M02 §2 poison V₀ is realized-but-not-carried, so the
  as-typed vt_surj obligation at the instance is refutable at the intended
  semantics — same flagged `ReadsOf` caveat, no compiled countermodel while
  `canPolicy` is designer-sorried). This is the (†5)-completeness face of
  the SAME per-site repair family M02 §4-5 already prices; it is an OPEN
  OBLIGATION on the vt_surj supplier, NOT on this repair, and it was
  already unprovable-at-instance at HEAD (binder-only). Recorded for the
  Phase-B queue; sanction fence forbids touching it here.
* Compiled V₀-style negation witnesses: NONE exist at HEAD (grep
  `M02|exact.?square|nsPoison|V0` over LeanUrat/ — no compiled countermodel
  was possible, M02's flagged step), so nothing to re-point or fail.
