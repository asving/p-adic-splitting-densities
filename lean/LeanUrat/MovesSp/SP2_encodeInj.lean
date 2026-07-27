/-
Unit Sp.encodeInj — moves_ref: "Every species tuple is determined by an integer
vector with all entries in {0, 1, …, n+1} … Total length ≤ 1 + 3 + 5 + (n+1) + n²
+ 2 + 2n = n² + 3n + 12, each entry taking ≤ n + 2 values".
deps: Sp.compEncode, Sp.lamEncode. sketch: field-by-field recovery: scalar entries
in range by (B5) (d ≤ n+1 the widened entry); λ via lamMatrix; sel via the
reserved (0,0) pair (WellTyped parts ≥ 1 keep it disjoint); flanks via compCuts +
spans s0 / W − s0 − w′ recovered from scalar entries; slots redundant ("kept for
crudeness"). difficulty: medium-hard (split candidate: scalar-block recovery vs
flank/λ blocks if > ~40 lines). Needs `hn : 1 ≤ n` ("n + 2 ≥ 3 for every n ≥ 1" —
the tag entry).
-/
import LeanUrat.MovesSp.Defs
-- deps Sp.compEncode / Sp.lamEncode: proof-level only (P-phase adds the imports);
-- corpus convention = unit files import the def layer alone.

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- the SP-FIN encoding (blueprint: body = P-phase work; entries in the note's
order — tag 1; D w W 3; e ℓ a s₀′ d 5; slot indicator n+1; λ-matrix n²; sel 2;
flank cut-set indicators 2n). -/
def encode (n : ℕ) (hn : 1 ≤ n) (s : Species) : Code n := sorry

theorem encode_inj {n hn} {s s' : Species} (hs : Coherent s ∧ Budget n s)
    (hs' : Coherent s' ∧ Budget n s') (h : encode n hn s = encode n hn s') :
    s = s' := sorry

end LeanUrat.MovesSp
