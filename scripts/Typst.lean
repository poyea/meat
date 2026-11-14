import Lean

open Lean Meta

namespace Typst

structure Out where
  text : String
  prec : Nat := 100
  tuple : Option String := none

structure Tmpl where
  text : String
  prec : Nat := 100
  args : List Nat := []

def preamble : String :=
  "#let given = math.class(\"relation\", sym.bar.v)\n"

def table : Std.HashMap Name Tmpl := .ofList [
  (``HAdd.hAdd, { text := "#1 + #2", prec := 65, args := [65, 66] }),
  (``HSub.hSub, { text := "#1 - #2", prec := 65, args := [65, 66] }),
  (``HMul.hMul, { text := "#1 #2", prec := 70, args := [70, 71] }),
  (``HDiv.hDiv, { text := "#1 / #2", prec := 70, args := [100, 100] }),
  (``HPow.hPow, { text := "#1^(#2)", prec := 75, args := [100, 0] }),
  (``Neg.neg, { text := "-#1", prec := 75, args := [75] }),
  (``Eq, { text := "#1 = #2", prec := 50, args := [51, 51] }),
  (``Ne, { text := "#1 != #2", prec := 50, args := [51, 51] }),
  (``LE.le, { text := "#1 <= #2", prec := 50, args := [51, 51] }),
  (``LT.lt, { text := "#1 < #2", prec := 50, args := [51, 51] }),
  (``GE.ge, { text := "#1 >= #2", prec := 50, args := [51, 51] }),
  (``GT.gt, { text := "#1 > #2", prec := 50, args := [51, 51] }),
  (``Iff, { text := "#1 <=> #2", prec := 20, args := [21, 21] }),
  (``And, { text := "#1 and #2", prec := 35, args := [36, 35] }),
  (``Or, { text := "#1 or #2", prec := 30, args := [31, 30] }),
  (``Not, { text := "not #1", prec := 40, args := [40] }),
  (``Membership.mem, { text := "#2 in #1", prec := 50, args := [51, 51] }),
  (``HasSubset.Subset, { text := "#1 subset.eq #2", prec := 50, args := [51, 51] }),
  (``Function.comp, { text := "#1 compose #2", prec := 90, args := [91, 90] }),
  (`closure, { text := "overline(#1)" }),
  (`Set.Icc, { text := "[#1, #2]" }),
  (``Singleton.singleton, { text := "{#1}" }),
  (``OfNat.ofNat, { text := "#1" }),
  (``Nat.cast, { text := "#1" }),
  (`NNReal.toReal, { text := "#1" }),
  (`ENNReal.toReal, { text := "#1" }),
  (`Fintype.card, { text := "|#1|" }),
  (`Real.log, { text := "log #1", prec := 80, args := [100] }),
  (`Real.pi, { text := "pi" }),
  (`Real.negMulLog, { text := "eta(#1)" }),
  (`MeasureTheory.Measure.map, { text := "#1_* #2", args := [100, 100] }),
  (`MeasureTheory.Measure.real, { text := "#1(#2)", args := [100, 0] }),
  (`MeasureTheory.Measure.rnDeriv, { text := "(dif #1) / (dif #2) (#3)" }),
  (`MeasureTheory.MeasureSpace.volume, { text := "lambda" }),
  (`ProbabilityTheory.gaussianReal, { text := "cal(N)(#1, #2)" }),
  (`Meat.measureEntropy, { text := "H(#1)" }),
  (`Meat.entropy, { text := "H(#*1)" }),
  (`Meat.condEntropy, { text := "H(#1 given #2)" }),
  (`Meat.mutualInfo, { text := "I(#1; #2)" }),
  (`Meat.condMutualInfo, { text := "I(#1; #2 given #3)" }),
  (`Meat.natsToBits, { text := "beta(#1)" }),
  (`Meat.bitsToNats, { text := "gamma(#1)" }),
  (`Meat.entropyBits, { text := "H_2(#*1)" }),
  (`Meat.condEntropyBits, { text := "H_2(#1 given #2)" }),
  (`Meat.mutualInfoBits, { text := "I_2(#1; #2)" }),
  (`Meat.condMutualInfoBits, { text := "I_2(#1; #2 given #3)" }),
  (`Meat.measureDiffEntropy, { text := "h(#1)" }),
  (`Meat.diffEntropy, { text := "h(#*1)" }),
  (`Meat.awgnCapacity, { text := "C(#1, #2)" }),
  (`Meat.DMC.capacity, { text := "C(#1)" }),
  (`Meat.DMC.Achievable, { text := "#2 \" achievable for \" #1", prec := 50, args := [51, 51] }),
  (`Meat.SlepianWolf.achievableRegion, { text := "cal(A)(#1)" }),
  (`Meat.SlepianWolf.rateRegion, { text := "cal(R)(#1)" }),
  (`Meat.MAC.achievableRegion, { text := "cal(A)(#1)" }),
  (`Meat.MAC.capacityRegion, { text := "cal(C)(#1)" }),
  (`Meat.BC.achievableRegion, { text := "cal(A)(#1)" }),
  (`Meat.BC.superpositionRegion, { text := "cal(S)(#2, #3)" }),
  (`Meat.Network.minCut, { text := "op(\"mincut\")(#2, #3)" }),
  (`Meat.Network.Code.Decodes, { text := "#2 \" decodes \" #1", prec := 50, args := [51, 51] })]

def predicates : Std.HashMap Name String := .ofList [
  (`Fintype, "finite"),
  (``Nonempty, "nonempty"),
  (`Measurable, "measurable"),
  (`MeasureTheory.IsProbabilityMeasure, "a probability measure"),
  (`Meat.Network.IsAcyclic, "acyclic")]

def wrap (o : Out) (p : Nat) : String :=
  if o.prec < p then "(" ++ o.text ++ ")" else o.text

def fill (t : Tmpl) (outs : Array Out) : String := Id.run do
  let cs := t.text.toList.toArray
  let mut res := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '#' && i + 1 < cs.size then
      let star := cs[i + 1]! == '*'
      let j := if star then i + 2 else i + 1
      if j < cs.size && cs[j]!.isDigit then
        let k := cs[j]!.toNat - '0'.toNat - 1
        let o := outs.getD k { text := "\"?\"" }
        let p := t.args.getD k 0
        res := res ++ (if star then o.tuple.getD (wrap o p) else wrap o p)
        i := j + 1
        continue
    res := res.push cs[i]!
    i := i + 1
  return res

def subDigit (c : Char) : Option Char :=
  if '₀' ≤ c && c ≤ '₉' then some (Char.ofNat ('0'.toNat + (c.toNat - '₀'.toNat))) else none

def ident (s : String) : String :=
  let cs := s.toList
  let base := cs.takeWhile (subDigit · |>.isNone)
  let subs := (cs.dropWhile (subDigit · |>.isNone)).filterMap subDigit
  let b := match base with
    | [c] => c.toString
    | c :: rest =>
      if c.isLower && rest.all Char.isUpper then s!"{c}_{String.ofList rest}"
      else s!"\"{String.ofList base}\""
    | [] => "x"
  if subs.isEmpty then b else s!"{b}_{String.ofList subs}"

abbrev R := StateT NameSet MetaM

def fvarName (x : Expr) : MetaM String := do
  return ident (← x.fvarId!.getDecl).userName.eraseMacroScopes.toString

def explicitArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let info ← getFunInfoNArgs fn args.size
  let mut out := #[]
  for h : i in [:args.size] do
    let explicit :=
      if h' : i < info.paramInfo.size then info.paramInfo[i].binderInfo.isExplicit else true
    if explicit then out := out.push args[i]
  return out

partial def onlyApplied (x e : Expr) : Bool :=
  if !e.containsFVar x.fvarId! then true
  else match e with
    | .app f a =>
      if a == x then f.getAppFn.isFVar && onlyApplied x f else onlyApplied x f && onlyApplied x a
    | .mdata _ b => onlyApplied x b
    | .lam _ t b _ => onlyApplied x t && onlyApplied x b
    | .forallE _ t b _ => onlyApplied x t && onlyApplied x b
    | _ => false

mutual

partial def render (supp : List FVarId) (e : Expr) : R Out := do
  match e with
  | .mdata _ b => render supp b
  | .lit (.natVal n) => return { text := toString n }
  | .lit (.strVal s) => return { text := s!"\"{s}\"" }
  | .fvar _ => return { text := ← fvarName e }
  | .lam n ty b bi =>
    withLocalDecl n bi ty fun x => do
      let body := b.instantiate1 x
      if onlyApplied x body then
        render (x.fvarId! :: supp) body
      else
        let o ← render supp body
        return { text := s!"{← fvarName x} |-> {wrap o 11}", prec := 10 }
  | .forallE n ty b bi =>
    if !b.hasLooseBVars && (← isProp ty) then
      let l ← render supp ty
      let r ← render supp b
      return { text := s!"{wrap l 26} => {wrap r 25}", prec := 25 }
    else
      withLocalDecl n bi ty fun x => do
        let body := b.instantiate1 x
        let v ← fvarName x
        if let .forallE _ hyp rest _ := body then
          if !rest.hasLooseBVars && hyp.isAppOfArity ``Membership.mem 5
              && hyp.appArg! == x then
            let s ← render supp hyp.appFn!.appArg!
            let r ← render supp rest
            return { text := s!"forall {v} in {wrap s 51}: {wrap r 11}", prec := 10 }
        let r ← render supp body
        return { text := s!"forall {v}: {wrap r 11}", prec := 10 }
  | .letE _ _ v b _ => render supp (b.instantiate1 v)
  | .app .. | .const .. => renderApp supp e
  | .proj _ i s => do
    let o ← render supp s
    return { text := s!"{wrap o 100}.{i + 1}" }
  | _ => return { text := "\"?\"" }

partial def binder (supp : List FVarId) (f : Expr) (k : String → Out → R Out) : R Out := do
  match f with
  | .lam n ty b bi =>
    withLocalDecl n bi ty fun x => do
      k (← fvarName x) (← render supp (b.instantiate1 x))
  | _ => do
    let o ← render supp f
    k "x" { text := s!"{wrap o 100}(x)" }

partial def renderSpecial (supp : List FVarId) (name : Name) (fn : Expr) (args : Array Expr) :
    R (Option Out) := do
  let ex ← explicitArgs fn args
  match name, ex.size with
  | ``Prod.mk, 2 =>
    let a ← render supp ex[0]!
    let b ← render supp ex[1]!
    let inner := s!"{a.text}, {b.text}"
    return some { text := s!"({inner})", tuple := some inner }
  | `setOf, 1 | `Set.ofPred, 1 =>
    some <$> binder supp ex[0]! fun v o => return { text := "{" ++ v ++ " : " ++ o.text ++ "}" }
  | `Finset.sum, 2 | `Finset.prod, 2 =>
    let op := if name == `Finset.sum then "sum" else "product"
    let s := ex[0]!
    let dom ← if s.isAppOf `Finset.univ then pure none else some <$> render supp s
    some <$> binder supp ex[1]! fun v o =>
      let sub := match dom with
        | none => v
        | some d => s!"{v} in {d.text}"
      return { text := s!"{op}_({sub}) {wrap o 66}", prec := 60 }
  | `iSup, 1 | `iInf, 1 =>
    let op := if name == `iSup then "sup" else "inf"
    some <$> binder supp ex[0]! fun v o =>
      return { text := s!"{op}_({v}) {wrap o 66}", prec := 60 }
  | ``Exists, 1 =>
    some <$> binder supp ex[0]! fun v o =>
      return { text := s!"exists {v}: {wrap o 11}", prec := 10 }
  | `MeasureTheory.integral, 2 =>
    let μ := ex[0]!
    let vol := μ.isAppOf `MeasureTheory.MeasureSpace.volume
    let m ← render supp μ
    some <$> binder supp ex[1]! fun v o =>
      let d := if vol then s!"dif {v}" else s!"dif {wrap m 100}({v})"
      return { text := s!"integral {wrap o 66} {d}", prec := 60 }
  | ``LE.le, 2 =>
    if (← inferType ex[0]!).isAppOf `Set then
      let a ← render supp ex[0]!
      let b ← render supp ex[1]!
      return some { text := s!"{wrap a 51} subset.eq {wrap b 51}", prec := 50 }
    return none
  | ``Not, 1 =>
    let p := ex[0]!
    if p.isAppOfArity ``Membership.mem 5 then
      let s ← render supp p.appFn!.appArg!
      let a ← render supp p.appArg!
      return some { text := s!"{wrap a 51} in.not {wrap s 51}", prec := 50 }
    return none
  | `Real.exp, 1 =>
    let o ← render supp ex[0]!
    return some { text := if o.text == "1" then "e" else s!"e^({o.text})" }
  | _, _ => return none

partial def renderApp (supp : List FVarId) (e : Expr) : R Out := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if h : args.size > 0 then
    let last := args[args.size - 1]
    if last.isFVar && supp.contains last.fvarId! then
      return ← render supp (mkAppN fn args.pop)
  match fn with
  | .const name _ =>
    if let some o ← renderSpecial supp name fn args then return o
    let ex ← explicitArgs fn args
    match table[name]? with
    | some t =>
      if t.text == "#1" && ex.size == 1 then return ← render supp ex[0]!
      let outs ← ex.mapM (render supp)
      return { text := fill t outs, prec := t.prec }
    | none =>
      modify (·.insert name)
      let outs ← ex.mapM (render supp)
      let head := s!"#raw(\"{name}\");"
      if outs.isEmpty then return { text := head }
      return { text := head ++ "(" ++ ", ".intercalate (outs.map (·.text)).toList ++ ")" }
  | _ =>
    let h ← render supp fn
    let outs ← args.mapM (render supp)
    return { text := wrap h 100 ++ "(" ++ ", ".intercalate (outs.map (·.text)).toList ++ ")" }

end

structure Statement where
  hyps : Array String
  body : String
  unmapped : Array Name

def predicate? (ty : Expr) : MetaM (Option (String × Expr)) := do
  let some n := ty.getAppFn.constName? | return none
  let some p := predicates[n]? | return none
  let ex ← explicitArgs ty.getAppFn ty.getAppArgs
  if ex.isEmpty then return none
  return some (p, ex[ex.size - 1]!)

def statement (type : Expr) : MetaM Statement := do
  let ((hyps, body), unmapped) ← go.run {}
  return { hyps, body, unmapped := unmapped.toArray.qsort Name.lt }
where
  go : R (Array String × String) := forallTelescope type fun xs body => do
    let mut groups : Array (String × Array String) := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let relevant := d.binderInfo.isInstImplicit || (d.binderInfo.isExplicit && (← isProp d.type))
      unless relevant do continue
      if let some (p, subj) ← predicate? d.type then
        let s := s!"${(← render [] subj).text}$"
        if let some (q, ss) := groups.back? then
          if q == p then
            groups := groups.pop.push (q, ss.push s)
            continue
        groups := groups.push (p, #[s])
      else if d.binderInfo.isExplicit then
        groups := groups.push ("", #[s!"${(← render [] d.type).text}$"])
    let hyps := groups.map fun (p, ss) =>
      if p.isEmpty then ss[0]! else ", ".intercalate ss.toList ++ " " ++ p
    let b ← render [] body
    return (hyps, b.text)

end Typst
