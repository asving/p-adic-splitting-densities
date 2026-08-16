import Uniformity
import Leanspec.ChapG
import Leanspec.ChapB
-- Wired at chapter H's 0e RETIREMENT (2026-08-15): now that every ChapH stub is an `example`
-- against a landed declaration, the roll-up import turns those 253 type diffs into a STANDING gate
-- on `lake build Leanspec` — a later `leanfinal` edit that drifts from a signed chapter-H type
-- breaks this build. (It was deliberately unwired while the H stub gate was open, per ChapH's
-- FILE LAYOUT note, so concurrent stub-gate agents could not collide on this file.)
import Leanspec.ChapH
-- **Chapter I is DELIBERATELY NOT WIRED (2026-08-16, its 0e stub gate) — wiring it would break
-- this build, and that is a `leanfinal` defect, not a chapter-I one.** `Uniformity.Density.Gauge.Wle`
-- and `…VarthetaWConjunct` are each DECLARED TWICE in `leanfinal` — `Uniformity/ChapD/D55.lean:103`
-- + `D63.lean:144` versus `Uniformity/ChapD/D62w.lean:369` + `:412` — so the two module branches
-- cannot coexist in one environment. `Uniformity` (line 1 above) carries the D62w branch;
-- `Leanspec.ChapI` must reach the chapter-E Display-A carriers (E.24/E.61/E.62/E.63), which import
-- D63 → D55. Adding the import below yields, machine-checked at the gate:
--   `import Uniformity.ChapD.D55 failed, environment already contains
--    'Uniformity.Density.Gauge.Wle' from Uniformity.ChapD.D62w`
-- Chapter I's stub file therefore hand-picks its own import set (`Uniformity.lean`'s list minus
-- `Uniformity.ChapD`, plus E24/E63) and is built with `lake build Leanspec.ChapI`, GREEN.
-- Uncomment the line below the moment D62w's two duplicate `def`s are deleted in favour of
-- importing D55/D63 — that one edit restores the standing gate here AND unblocks landing chapter I
-- in `leanfinal` at all (defect I-D1 in `Leanspec/ChapI.lean`'s header).
-- import Leanspec.ChapI
/-!
# leanspec — the isolated interface environment (design stage 0e)

Theorem interfaces land here as exact `axiom` stubs in topological order,
per chapter, BEFORE that chapter's fleet fires; definitions come from the
real `Uniformity` package (imported). NEVER imported by leanfinal or
leancheck. After a real declaration lands in leanfinal, its normalized
type is diffed against the stub here. Stubs are per-chapter files
(Leanspec/ChapG.lean, ...), added as the blueprints freeze.

## The stub lifecycle (0e-G, 2026-08-15)

Because every chapter stub file `import`s `Uniformity` (the real `leanfinal` package) at its
top, EVERY blueprint node signature it carries has a two-state lifecycle keyed on whether that
node has landed in `leanfinal` yet:

* **UNLANDED — `axiom <name> : <type>`.** The elaboration gate: declaring the axiom checks the
  SIGNATURE type-checks (references real, already-landed dependencies correctly) without
  requiring a proof. This is the state a theorem-shaped node is signed in, from the moment its
  blueprint entry freezes until its fleet lands it.
* **LANDED — `example : <type> := <name>`.** The retirement form. Once `leanfinal` carries a real
  declaration of the same name, the stub's own `axiom` (or local definitional body, see below)
  would collide with it — both are visible simultaneously, since the stub imports `Uniformity`
  wholesale — so the stub declaration is replaced by a bodyless `example` that (i) does not
  introduce a competing name (curing the collision) and (ii) applies the now-landed real
  constant at the EXACT type the stub originally signed, so a divergence between the signed
  interface and the landed declaration's actual type is a hard Lean error on this file's build,
  not a silent drift. This is automatic on every `leanspec` build: no separate diff tool, no
  manual step.

  Reapply every parameter by NAME (`name (arg₁ := arg₁) (arg₂ := arg₂) ... := realName (a := a)
  ...`), not positionally: a parameter that is implicit and unconstrained by the others (e.g. an
  index that appears in no other hypothesis or in the conclusion) leaves an unassigned
  metavariable under positional application, and Lean errors with "don't know how to synthesize
  implicit argument" — named application binds every slot unambiguously regardless of
  implicit/explicit status or whether it is otherwise determined. Conversely, an
  instance-implicit that the stub's own header never carried (because auto-inclusion runs off
  what a bodyless `axiom`'s TYPE mentions, and the landed theorem's PROOF alone may pull in an
  extra instance the stub's axiom never needed to state — the chapter-G defect log calls this
  D4) does not need to be reapplied or restated: Lean auto-synthesizes a missing
  instance-implicit from the ambient section `variable`s exactly as at any ordinary call site, so
  the retirement-form `example` still type-checks even though its header is one instance short of
  the landed theorem's. Confirmed empirically (2026-08-15) against four such D4 nodes
  (`card_dvdSet`, `card_exactSet_add`, `tendsto_geom_partial`, `card_species3`); zero of the 33
  nodes landed as of the 0e-G unit needed their header widened to retire cleanly.

**Definitional stubs are the exception to the UNLANDED state, not to the lifecycle.** A `def`,
`structure`, or `inductive` carries no proof obligation, so stage-0e rule 1 lands its REAL BODY
in the stub directly (never an `axiom`) from the start — the two-state split above is only
literally axiom-vs-example for theorem-shaped nodes. Once such a node lands in `leanfinal`, the
same collision arises (the stub's local body and the real one share a name), and the same cure
applies: delete the local body and add a retirement-form check.
* `def`s convert exactly like theorems: `example : <type> := <name>` (mark `noncomputable` if the
  landed def is).
* `structure`s and `inductive`s do not, because their OWN type-former is nearly always
  uninformative to assert (every structure/inductive former ends in some `Sort`, so checking
  ITS type checks nothing about the fields'/constructors' own types — the actual shape that
  could silently drift). Assert instead a representative FIELD projection's type (structures) or
  EVERY constructor's type (inductives — cheap, and each constructor is an independent unit of
  the shape, e.g. `CubicFamilyIndex`'s five constructors fix five different `Fin` arities). Where
  even that is unnatural, a `#check @<name>` line with a `-- 0e-diff` comment documents the
  retirement without asserting a type.
-/
