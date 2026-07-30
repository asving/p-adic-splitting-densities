import LeanUrat.MovesSp.DefsEnum
open LeanUrat.MovesSp
def enumD (n : ℕ) : List Species := (speciesEnum n).eraseDups
partial def closureFrom (n : ℕ) (cur : List Species) : List Species :=
  let next := (enumD n).filter (fun s' =>
    !(cur.contains s') && cur.any (fun s => succStepB n s s'))
  if next.isEmpty then cur else closureFrom n (cur ++ next)
def catN (n : ℕ) : List Species := closureFrom n ((enumD n).filter (rootAdmissibleB n))
#eval (catN 1).length
#eval (catN 1).map (fun s => (s.D, s.w, s.W, s.e, s.ell, s.sel.isNone))
