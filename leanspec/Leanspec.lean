import Uniformity
/-!
# leanspec — the isolated interface environment (design stage 0e)

Theorem interfaces land here as exact `axiom` stubs in topological order,
per chapter, BEFORE that chapter's fleet fires; definitions come from the
real `Uniformity` package (imported). NEVER imported by leanfinal or
leancheck. After a real declaration lands in leanfinal, its normalized
type is diffed against the stub here. Stubs are per-chapter files
(Leanspec/ChapG.lean, ...), added as the blueprints freeze.
-/
