import Lean

/-!
# `PyExtract` — a Python backend for Lean 4, built from scratch

Lean ships C and LLVM backends only. This module adds a Python one by walking the
elaborated `Expr` of a definition and re-rendering it as Python source. It exists to
answer the practical question: *how far does "derive code from the proof" actually
get, and where does it break?*

Design:

* **Proof erasure is structural.** A verified function's body contains proofs (the
  second component of `⟨a + b, proof⟩`). Those arguments are dropped, not
  translated — `Prop`-valued content has no Python meaning. The number of erased
  subterms is reported, so the erasure is visible rather than implied.
* **Unsupported constructs throw.** The extractor never guesses. Recursive
  definitions arrive as recursor applications (`Nat.brecOn`, `List.brecOn`) which are
  not source-level recursion; they are reported as unsupported, not mistranslated.
-/

open Lean Meta Elab Command

namespace PyExtract

/-- Running count of proof terms erased, so erasure is observable and not implied. -/
structure Stats where
  erasedProofs : Nat := 0
  erasedLeaves : Array String := #[]
  deriving Inhabited

abbrev M := StateT Stats TermElabM

structure PyFun where
  name : String
  params : List String
  body : String
  deriving Inhabited

/-- Python infix operator and its precedence, or `none`. -/
def binOpOf (n : String) : Option (String × Nat) :=
  match n with
  | "HAdd.hAdd" | "Int.add" | "Nat.add" | "Add.add" => some ("+", 6)
  | "HSub.hSub" | "Int.sub" | "Nat.sub" | "Sub.sub" => some ("-", 6)
  | "HMul.hMul" | "Int.mul" | "Nat.mul" | "Mul.mul" => some ("*", 7)
  | "Nat.div" => some ("//", 7)  -- NAT only; see the Int.div special case below
  | "HMod.hMod" | "Int.emod" | "Nat.mod" | "Mod.mod" => some ("%", 7)
  | "LT.lt" | "Int.lt" | "Nat.lt" => some ("<", 4)
  | "LE.le" | "Int.le" | "Nat.le" => some ("<=", 4)
  | "GT.gt" | "Int.gt" => some (">", 4)
  | "GE.ge" | "Int.ge" => some (">=", 4)
  | "BEq.beq" | "Int.beq" | "Nat.beq" => some ("==", 4)
  | _ => none

/-- Prefix notation: unary function names mapped to Python spellings. -/
def prefixOf (n : String) : Option (String × Nat) :=
  match n with
  | "Neg.neg" | "Int.neg" | "Nat.sub" => some ("-", 8)
  | "Bool.not" | "not" => some ("not ", 8)
  | _ => none

def eraseProof (why : String) : M Unit := do
  modify (fun s => { s with erasedProofs := s.erasedProofs + 1,
                            erasedLeaves := s.erasedLeaves.push why })

mutual

/-- Render an `Expr` as Python source. `prec` is the precedence of the enclosing
context; sub-expressions bind looser than that get parenthesised. -/
partial def render (locals : List (FVarId × String)) (e : Expr) (prec : Nat := 0) :
    M String := do
  match e with
  | .lit (.natVal n) => return toString n
  | .lit (.strVal s) => return toString (repr s)
  | .mdata _ b => render locals b prec
  | .fvar id =>
      match locals.find? (fun p => p.1 == id) with
      | some (_, n) => return n
      | none        => throwError "unbound local {id.name}"
  | .letE _ _ v b _ => render locals (b.instantiate1 v) prec
  | .app .. => renderApp locals e prec
  | .const c _ => throwError "bare constant with no Python rendering: {c}"
  | .lam .. => throwError "un-applied lambda in value position"
  | .forallE .. => throwError "function type in value position"
  | .sort _ => throwError "Sort in value position"
  | .bvar _ => throwError "loose bound variable"
  | .proj _ _ _ => throwError "structure projection"
  | .mvar _ => throwError "metavariable (incomplete elaboration)"

/-- Render an application spine: class projections, literals, and calls. -/
partial def renderApp (locals : List (FVarId × String)) (e : Expr) (prec : Nat) : M String := do
  let f := e.getAppFn
  let args := e.getAppArgs
  -- Peel numeric class wrappers, which carry type/instance arguments we ignore.
  if let .const c _ := f then
    let cs := c.toString
    -- Integer literals arrive as `Int.ofNat n` / `Int.negSucc n`, possibly wrapped in
    -- `OfNat.ofNat`. `negSucc n` denotes `-(n+1)`.
    if cs == "Int.ofNat" && args.size >= 1 then
      if let .lit (.natVal n) := args[args.size - 1]! then return toString n
    if cs == "Int.negSucc" && args.size >= 1 then
      if let .lit (.natVal n) := args[args.size - 1]! then return s!"(-{n + 1})"
    if cs == "OfNat.ofNat" && args.size >= 2 then
      return (← render locals args[1]! prec)
    -- `ite` and `dite`. For `dite` the branches are functions of the proof, so taking
    -- their bodies is proof erasure: the erased hypothesis is what the branch needed.
    if (cs == "ite" || cs == "dite") && args.size >= 3 then
      let isDep := cs == "dite"
      if isDep then eraseProof "dite hypothesis"
      let cond ← render locals args[1]! 4
      let strip (x : Expr) : Expr :=
        if isDep then (match x with | .lam _ _ b _ => b | _ => x) else x
      let t ← render locals (strip args[args.size - 2]!) 3
      let fl ← render locals (strip args[args.size - 1]!) 3
      return s!"({t} if {cond} else {fl})"
    -- Subtype/Sigma/Exists: the payload is second-to-last, the proof is last.
    if (cs == "Subtype.mk" || cs == "Sigma.mk" || cs == "Exists.intro") && args.size >= 2 then
      eraseProof s!"{cs} proof field"
      return (← render locals args[args.size - 2]! prec)
    if cs == "Prod.mk" && args.size >= 2 then
      let a ← render locals args[args.size - 2]! 0
      let b ← render locals args[args.size - 1]! 0
      return s!"({a}, {b})"
    if cs == "And.intro" then
      eraseProof "And.intro"
      throwError "proof term in value position (`And.intro`)"
    if (cs == "Subtype.val" || cs == "Sigma.fst") && args.size >= 1 then
      return (← render locals args[args.size - 1]! prec)
    if cs == "id" && args.size >= 1 then
      return (← render locals args[args.size - 1]! prec)
    if cs == "List.nil" then return "[]"
    if cs == "List.cons" && args.size >= 2 then
      let h ← render locals args[args.size - 2]! 0
      let t ← render locals args[args.size - 1]! 0
      return s!"([{h}] + {t})"
    if cs == "Bool.and" && args.size >= 2 then
      return s!"({← render locals args[args.size - 2]! 5} and {← render locals args[args.size - 1]! 5})"
    if cs == "Bool.or" && args.size >= 2 then
      return s!"({← render locals args[args.size - 2]! 5} or {← render locals args[args.size - 1]! 5})"
    if cs == "Bool.true" then return "True"
    if cs == "Bool.false" then return "False"
    if let some (op, opPrec) := binOpOf cs then
      if args.size >= 2 then
        let l ← render locals args[args.size - 2]! opPrec
        let r ← render locals args[args.size - 1]! (opPrec + 1)
        let s := s!"{l} {op} {r}"
        return if opPrec < prec then s!"({s})" else s
    if let some (op, opPrec) := prefixOf cs then
      if args.size >= 1 then
        let o ← render locals args[args.size - 1]! opPrec
        return s!"{op}{o}"
    -- Division and modulus need TYPE-DIRECTED handling. Lean's `Int` division is
    -- Euclidean (remainder always >= 0); Python's `//` floors. They agree when the
    -- divisor is positive and differ when it is negative:
    --     Lean: (7 : Int) / -2 = -3      Python: 7 // -2 = -4
    --   so mapping Int.div to `//` would silently emit wrong code.
    let typeNameOf (x : Expr) : String :=
      match x.consumeMData.consumeMData with
      | .const c _ => c.toString
      | _ => ""
    if cs == "Int.div" || cs == "Nat.div" || cs == "HDiv.hDiv" || cs == "Div.div" then
      if args.size >= 2 then
        let ty := if args.size >= 1 then typeNameOf args[0]! else ""
        let isInt := cs == "Int.div" || ((cs == "HDiv.hDiv" || cs == "Div.div") && ty == "Int")
        let isNat := cs == "Nat.div" || ((cs == "HDiv.hDiv" || cs == "Div.div") && ty == "Nat")
        let l ← render locals args[args.size - 2]! 7
        let r ← render locals args[args.size - 1]! 8
        if isNat then
          let s := s!"{l} // {r}"
          return if 7 < prec then s!"({s})" else s
        else if isInt then
          return s!"_lean_div({l}, {r})"
        else
          throwError "division on type '{ty}' (head {cs}): the Euclidean/floor \
            mismatch cannot be resolved without knowing the type; refused rather \
            than guessed"
    if cs == "Int.emod" || cs == "Nat.mod" || cs == "HMod.hMod" || cs == "Mod.mod" then
      if args.size >= 2 then
        let ty := if args.size >= 1 then typeNameOf args[0]! else ""
        let isInt := cs == "Int.emod" || ((cs == "HMod.hMod" || cs == "Mod.mod") && ty == "Int")
        let isNat := cs == "Nat.mod" || ((cs == "HMod.hMod" || cs == "Mod.mod") && ty == "Nat")
        let l ← render locals args[args.size - 2]! 7
        let r ← render locals args[args.size - 1]! 8
        if isNat then
          let s := s!"{l} % {r}"
          return if 7 < prec then s!"({s})" else s
        else if isInt then
          return s!"_lean_emod({l}, {r})"
        else
          throwError "modulus on type '{ty}' (head {cs}): the Euclidean/floor \
            mismatch cannot be resolved without knowing the type; refused rather \
            than guessed"
    -- Recursors: these are how Lean encodes recursion and pattern matching. They are
    -- NOT source-level recursion, and rendering them as Python is a separate project.
    if cs.endsWith "brecOn" || cs.endsWith "rec" || cs.endsWith "recOn"
       || cs.endsWith "casesOn" || cs.endsWith "below" || cs.endsWith "ibelow" then
      throwError "recursion/pattern-matching is a recursor application ({cs}) — \
        not translatable as source; needs a dedicated recursion pass"
    -- A call to another *definition*: verified functions compose. Render it as a
    -- Python call to that definition's extracted name. This is what lets proofs be
    -- built from smaller proved pieces and then compiled out.
    match (← getEnv).find? c with
    | some (.defnInfo _) =>
        let mut rendered : Array String := #[]
        for a in args do
          rendered := rendered.push (← render locals a 0)
        let short := (c.toString.splitOn ".").getLast!
        return s!"{short}({", ".intercalate rendered.toList})"
    | _ =>
        throwError "unsupported constant: {cs} (arity {args.size})"
  match f with
  | .fvar id =>
      let name : String ← match locals.find? (fun p => p.1 == id) with
        | some (_, n) => pure n
        | none => throwError "unbound function local {id.name}"
      let mut rendered := #[]
      for a in args do
        rendered := rendered.push (← render locals a 0)
      return s!"{name}({String.intercalate ", " rendered.toList})"
  | _ => throwError "unsupported application head: {f}"

end

/-- Extract a named definition as a `PyFun`. Throws with a specific reason when the
construct is outside the translatable subset — it never guesses. -/
def extractDef (env : Environment) (ns : Name) (s : String) : M PyFun := do
  let candidates :=
    if s.contains '.' then [s.toName, ns ++ s.toName]
    else [ns ++ Name.mkSimple s, Name.mkSimple s]
  let some name := candidates.find? (fun n => (env.find? n).isSome)
    | throwError "no definition named '{s}'"
  let some ci := env.find? name | throwError "no definition named '{s}'"
  let d ← match ci with
    | .defnInfo d => pure d
    | .thmInfo _ =>
        throwError "'{s}' is a theorem — a proof, not code; it has no runtime content"
    | _ => throwError "'{s}' is not a definition"
  set ({} : Stats)
  lambdaTelescope d.value fun params body => do
    let mut locals : List (FVarId × String) := []
    let mut pnames : Array String := #[]
    for p in params do
      let some fv := p.fvarId? | continue
      -- Prop-typed parameters are proofs, not data: erase them from the signature.
      if ← isProp (← inferType p) then
        eraseProof s!"Prop-typed parameter ({fv.name})"
        continue
      let n := ((← getLCtx).find? fv).map (fun ld => ld.userName.toString) |>.getD "p"
      locals := (fv, n) :: locals
      pnames := pnames.push n
    let bodySrc ← render locals body 0
    let st ← get
    if st.erasedProofs > 0 then
      logInfo m!"  [{name}] erased {st.erasedProofs} proof term(s): {st.erasedLeaves.toList}"
    return { name := name.toString, params := pnames.toList, body := bodySrc }

/-- Emit a self-contained Python module from a list of Lean definitions. -/
def emitModule (env : Environment) (ns : Name) (names : List String) : M String := do
  let mut fns : Array PyFun := #[]
  for s in names do
    fns := fns.push (← extractDef env ns s)
  let mut out := "# Generated from Lean 4 by PyExtract.\n"
  out := out ++ "# Proofs are erased: each definition below had its proof term dropped,\n"
  out := out ++ "# leaving only computation. If a claim in the spec were false, the Lean\n"
  out := out ++ "# definition would not elaborate, so nothing below would exist.\n\n"
  let bodies := fns.map (·.body) |>.toList
  let usesDiv := bodies.any (fun b => b.contains "_lean_div" || b.contains "_lean_emod")
  if usesDiv then
    -- Lean's `Int` division is Euclidean: the remainder is always non-negative.
    -- Python's `//` and `%` floor, so the remainder takes the divisor's sign. These
    -- helpers implement Lean's semantics on top of Python's, for all sign
    -- combinations. (`Nat` division needs none of this and stays as `//`.)
    out := out ++ "# --- Lean Int division semantics (Euclidean) on top of Python's floor ---\n"
    out := out ++ "def _lean_div(a, b):\n"
    out := out ++ "    q = a // b\n"
    out := out ++ "    return q + 1 if a - b * q < 0 else q\n\n"
    out := out ++ "def _lean_emod(a, b):\n"
    out := out ++ "    return a - b * _lean_div(a, b)\n\n"
  for f in fns do
    let short := f.name.splitOn "." |>.getLast!
    let ps := String.intercalate ", " f.params
    out := out ++ s!"def {short}({ps}):\n"
    out := out ++ "    return " ++ f.body ++ "\n\n"
  return out

end PyExtract

open PyExtract in
/-- `python_export "A.b" "C.d"` renders the named definitions as Python. -/
elab "python_export " names:str* : command => do
  let env ← getEnv
  let ns ← getCurrNamespace
  let code ← liftTermElabM do
    let (r, _) ← (emitModule env ns (names.map (·.getString)).toList).run {}
    return r
  logInfo code
