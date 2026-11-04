/- Audit helper (included by scripts/audit.py into the file it generates), version 0.20, 2026-11-04
(0.10 + no kind label is a banned word of the token scan).
For one row it reports, from the elaborated declaration only:
  (1) the published facts `Robinson.Fact…` and computer checks `Robinson.Check…` that occur in its type, following
      project definitions and opaques (type and value) and project inductive types (constructor types);
  (2) its leading binders whose type is exactly one constant of type `Prop` (a named hypothesis), in order;
  (3) the rows `Robinson.Paper.…` that its proof term mentions directly.
Proof bodies are read only for (3). Nothing is assumed. -/
namespace RobinsonAudit
open Lean Elab Command

/-- A published fact `Robinson.Fact…` or a computer check `Robinson.Check…` (by name; audit.py checks the registry). -/
def isTagged : Name → Bool
  | .str (.str .anonymous "Robinson") s => s.startsWith "Fact" || s.startsWith "Check"
  | _ => false

/-- (1): facts and checks reachable from `e`. Each project constant is followed once (a work list, no recursion). -/
def tagsIn (env : Environment) (e : Expr) : NameSet := Id.run do
  let mut found : NameSet := {}
  let mut seen : NameSet := {}
  let mut pending : Array Expr := #[e]
  while pending.size > 0 do
    let next := pending.back!
    pending := pending.pop
    for n in next.getUsedConstants do
      if isTagged n then
        found := found.insert n
      else if (`Robinson).isPrefixOf n && !seen.contains n then
        seen := seen.insert n
        match env.find? n with
        | some (.defnInfo info) => pending := (pending.push info.type).push info.value
        | some (.opaqueInfo info) => pending := (pending.push info.type).push info.value
        | some (.inductInfo info) =>
          for ctor in info.ctors do
            if let some ci := env.find? ctor then
              pending := pending.push ci.type
        | _ => pure ()
  return found

/-- (2): the leading binders of `type` whose type is a single constant `n` with `n : Prop`. -/
def namedPropBinders (env : Environment) (type : Expr) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut t := type.consumeMData
  while t.isForall do
    if let .const n _ := t.bindingDomain!.consumeMData then
      if let some info := env.find? n then
        if info.type.consumeMData.isProp then
          out := out.push n
    t := t.bindingBody!.consumeMData
  return out

/-- (3): the rows used directly by a proof term. -/
def rowsUsed (value : Expr) : NameSet := Id.run do
  let mut out : NameSet := {}
  for n in value.getUsedConstants do
    if (`Robinson.Paper).isPrefixOf n then
      out := out.insert n
  return out

def namesCSV (names : NameSet) : String :=
  String.intercalate "," ((names.toList.map Name.toString).mergeSort (· ≤ ·))

def arrayCSV (names : Array Name) : String :=
  String.intercalate "," (names.toList.map Name.toString)

/-- One line per row: RBROW|label|facts and checks in the type|named binders|rows used|kind|END. -/
def inspect (name : Name) (label : String) : CommandElabM Unit := do
  let env ← getEnv
  let info ← getConstInfo name
  let (kind, used) := match info with
    | .thmInfo ti => ("theorem", rowsUsed ti.value)
    | _ => ("other", ({} : NameSet))
  logInfo m!"RBROW|{label}|{namesCSV (tagsIn env info.type)}|{arrayCSV (namedPropBinders env info.type)}|{namesCSV used}|{kind}|END"

/-- One line per registered fact or check: RBREG|name|kind|is its type Prop|END. -/
def inspectRegistered (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  let kind := match info with
    | .defnInfo _ => "def"
    | .axiomInfo _ => "axiomInfo"   -- label only; audit.py accepts only "def"
    | .opaqueInfo _ => "opaque"
    | .thmInfo _ => "theorem"
    | _ => "other"
  logInfo m!"RBREG|{name.toString}|{kind}|{toString info.type.consumeMData.isProp}|END"
end RobinsonAudit
