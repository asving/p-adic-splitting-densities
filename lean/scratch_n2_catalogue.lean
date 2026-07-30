/- Scratch: compute the degree-2 species catalogue 𝒮₂^raw with the corpus's own
   enumeration + Bool laws (speciesEnum / rootAdmissibleB / succStepB), for the
   public paper's Step-2 section. NOT part of the build. -/
import LeanUrat.MovesSp.DefsEnum

open LeanUrat.MovesSp

def tagStr : Tag → String
  | .root => "root" | .postInc => "postInc" | .postRec => "postRec"

def lamStr (m : Multiset (ℕ × ℕ)) : String :=
  -- print as counts of each (g,μ) with g,μ ≤ 3 (enough for n ≤ 3)
  String.intercalate " " <| (List.range 3).flatMap fun g0 =>
    (List.range 3).flatMap fun m0 =>
      let c := m.count (g0+1, m0+1)
      if c = 0 then [] else [s!"({g0+1},{m0+1})x{c}"]

def showSp (s : Species) : String :=
  s!"tag={tagStr s.tag} D={s.D} w={s.w} W={s.W} e={s.e} s0={s.s0} ell={s.ell} " ++
  s!"a={s.a} d={s.d} lam=[{lamStr s.lam}] sel={s.sel} lf={s.lflank} rf={s.rflank}"

def enumD (n : ℕ) : List Species := (speciesEnum n).eraseDups

partial def closureFrom (n : ℕ) (cur : List Species) : List Species :=
  let next := (enumD n).filter (fun s' =>
    !(cur.contains s') && cur.any (fun s => succStepB n s s'))
  if next.isEmpty then cur else closureFrom n (cur ++ next)

def catN (n : ℕ) : List Species :=
  closureFrom n ((enumD n).filter (rootAdmissibleB n))

-- validation: the sealed n=3 count is 53 (SP6_card53); root group is 21
#eval ((enumD 3).filter (rootAdmissibleB 3)).length  -- expect 21
#eval (catN 3).length                                 -- expect 53

-- the degree-2 catalogue
#eval ((enumD 2).filter (rootAdmissibleB 2)).length
#eval (catN 2).length
#eval (catN 2).map showSp
-- transition matrix: row s → columns s', does succStepB 2 fire?
#eval (catN 2).map (fun s => (catN 2).map (fun s' => succStepB 2 s s'))
-- terminal letters (sel = ⊥): the read halts with a verdict
#eval (catN 2).map (fun s => s.sel.isNone)
-- self-loops
#eval (catN 2).map (fun s => succStepB 2 s s)

-- degree-1: the catalogue is a single terminal root letter
#eval (catN 1).length
#eval (catN 1).map (fun s => (s.D, s.w, s.W, s.e, s.ell, s.sel.isNone))
