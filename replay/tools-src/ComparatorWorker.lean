import Lean
import Comparator.Compare

/- The pinned Comparator library supplies comparison and axiom traversal.
   Rust supplies process isolation, immutable exports, deadlines and attribution.
   This executable neither builds candidates nor spawns other checkers. -/
open Lean

@[extern "lean_internal_set_max_memory"]
opaque setReplayMaxMemory (max : USize) : BaseIO Unit

structure ReductionComponent where
  exportPath : String
  theoremName : String
  deriving FromJson, Inhabited

structure ReplayRequest where
  mode : Option String := none
  referenceExport : String := ""
  candidateExport : String := ""
  theoremName : String := ""
  memoryMiB : Nat
  -- Parent first, then the exact ordered premises. These are controller inputs.
  reductionComponents : Option (Array ReductionComponent) := none
  reductionBaseExport : Option String := none
  reductionWitnessExport : Option String := none
  reductionWitnessTheoremName : Option String := none
  deriving FromJson

def ReplayRequest.components (request : ReplayRequest) : Array ReductionComponent :=
  request.reductionComponents.getD #[]

-- Keep these in agreement with the pinned Comparator Main.lean. Export both
-- environments with all these roots so kernel primitives cannot change meaning.
def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce]

def legalAxioms : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]

def readExport (path : String) : IO Export.ExportedEnv := do
  let handle ← IO.FS.Handle.mk path .read
  Export.parseStream (IO.FS.Stream.ofHandle handle)

def closedMonomorphic (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLooseBVars && !e.hasLevelParam && !e.hasSorry

def componentType (env : Export.ExportedEnv) (name : Name) : IO Expr := do
  let some (.thmInfo info) := env.constMap[name]? |
    throw <| IO.userError s!"reduction component is not a theorem: {name}"
  unless info.levelParams.isEmpty && closedMonomorphic info.type do
    throw <| IO.userError s!"reduction requires a closed monomorphic type: {name}"
  return info.type

def readComponents (parts : Array ReductionComponent) : IO (Array (Export.ExportedEnv × Expr)) := do
  unless 2 ≤ parts.size && parts.size ≤ 9 do
    throw <| IO.userError "reduction requires a parent and one to eight premises"
  parts.mapM fun part => do
    let env ← readExport part.exportPath
    return (env, ← componentType env part.theoremName.toName)

-- Compare complete declarations, including transitive definitions. No theorem
-- or definition holes are exempted, and every pair gets fresh traversal state.
def compareClosure (reference candidate : Export.ExportedEnv) (roots : Array Name) : IO Unit := do
  IO.ofExcept <| Comparator.Compare.loop.run
    { challenge := reference, solution := candidate, definitionTargets := {}, theoremTargets := {} }
    |>.run' { worklist := roots ++ primitiveTargets, checked := {} }

def compareComponent (reference : Export.ExportedEnv) (expected : Expr)
    (candidate : Export.ExportedEnv) (actual : Expr) : IO Unit := do
  unless closedMonomorphic actual && expected == actual do
    throw <| IO.userError "reduction component expression mismatch"
  compareClosure reference candidate expected.getUsedConstants

def reductionRoots (parts : Array (Export.ExportedEnv × Expr)) : IO (Array String) := do
  let mut names : Array Name := #[``Eq, ``And, ``True]
  for (_, type) in parts do
    for name in type.getUsedConstants do
      if !names.contains name then names := names.push name
  unless names.size ≤ 1024 do
    throw <| IO.userError "reduction base export root limit"
  names.mapM fun name => do
    let text := name.toString
    unless text.toName == name && text.utf8ByteSize ≤ 4096 do
      throw <| IO.userError "reduction base root cannot round-trip through exporter CLI"
    return text

def checkReduction (request : ReplayRequest) (candidate : Export.ExportedEnv) : IO Json := do
  let parts ← readComponents request.components
  let some basePath := request.reductionBaseExport |
    throw <| IO.userError "missing immutable reduction base export"
  let some witnessPath := request.reductionWitnessExport |
    throw <| IO.userError "missing reduction typing witness export"
  let some witnessName := request.reductionWitnessTheoremName |
    throw <| IO.userError "missing reduction typing witness theorem"
  let base ← readExport basePath
  let witness ← readExport witnessPath
  let mut residual ← componentType candidate request.theoremName.toName
  for (reference, type) in parts do
    compareClosure base reference type.getUsedConstants
  -- Exactly the explicit premise binders; the parent's own quantifiers remain.
  for index in [1:parts.size] do
    let (reference, expected) := parts[index]!
    let .forallE _ domain body .default := residual |
      throw <| IO.userError "reduction premise is not an explicit arrow"
    unless !body.hasLooseBVars do
      throw <| IO.userError "reduction premise binder is dependent"
    compareComponent reference expected candidate domain
    residual := body
  compareComponent parts[0]!.1 parts[0]!.2 candidate residual
  -- A separately kernel-replayed conjunction of Eq.{1} Prop P P witnesses
  -- establishes proposition typing. Merely parsing a thmInfo is insufficient.
  compareClosure base witness #[``Eq, ``And, ``True]
  let mut witnessType ← componentType witness witnessName.toName
  for (reference, expected) in parts do
    let .app (.app (.const ``And []) identity) tail := witnessType |
      throw <| IO.userError "reduction typing witness conjunction mismatch"
    let .app (.app (.app (.const ``Eq [.succ .zero]) (.sort .zero)) left) right := identity |
      throw <| IO.userError "reduction typing witness must assert equality in Prop"
    compareComponent reference expected witness left
    compareComponent reference expected witness right
    witnessType := tail
  unless witnessType == mkConst ``True do
    throw <| IO.userError "reduction typing witness has an unexpected tail"
  return Json.mkObj [
    ("schema", toJson "jocelyn.reduction-binding-diagnostics.v1"),
    ("parent_theorem", toJson request.components[0]!.theoremName),
    ("premise_theorems", toJson (request.components.extract 1 request.components.size |>.map (·.theoremName))),
    ("typing_witness_theorem", toJson witnessName),
    ("exact_component_expressions", toJson true), ("nondependent_premise_arrows", toJson true),
    ("frozen_base_definitions", toJson true), ("typing_witness_shape", toJson true),
    ("independent_typing_replay_required", toJson true), ("proof_accepted", toJson false)]

unsafe def main (args : List String) : IO UInt32 := do
  let [requestPath] := args | throw <| IO.userError "expected one replay request"
  let request ← IO.ofExcept <| Json.parse (← IO.FS.readFile requestPath)
  let request ← IO.ofExcept <| fromJson? (α := ReplayRequest) request
  unless request.memoryMiB ≥ 256 && request.memoryMiB ≤ 6144 do
    throw <| IO.userError "invalid comparator memory bound"
  setReplayMaxMemory (request.memoryMiB.toUSize * 1024 * 1024)
  if request.mode.getD "comparison" == "reduction-roots" then
    let roots ← reductionRoots (← readComponents request.components)
    IO.println <| (Json.mkObj [
      ("schema", toJson "jocelyn.reduction-export-roots.v1"),
      ("roots", toJson roots), ("proof_accepted", toJson false)]).compress
    return 0
  unless request.mode.getD "comparison" == "comparison" do
    throw <| IO.userError "unknown comparator mode"
  if request.components.isEmpty &&
      (request.reductionBaseExport.isSome || request.reductionWitnessExport.isSome ||
       request.reductionWitnessTheoremName.isSome) then
    throw <| IO.userError "reduction exports require component bindings"
  let reference ← readExport request.referenceExport
  let candidate ← readExport request.candidateExport
  let target := request.theoremName.toName
  IO.ofExcept <| Comparator.compareAt reference candidate (#[target] ++ legalAxioms)
    #[] primitiveTargets
  IO.ofExcept <| Comparator.checkAxioms candidate #[target] #[] legalAxioms
  let reduction ← if request.components.isEmpty then pure [] else do
    pure [("reduction_binding", ← checkReduction request candidate)]
  IO.println <| (Json.mkObj ([
    ("schema", toJson "jocelyn.comparator-diagnostics.v1"),
    ("comparator_source_commit", toJson "14b5039e0b6a5171afa160920984e521817d4138"),
    ("export_parser_source_commit", toJson "411dce7db58a3afc60ecab2d211acd1042b593dc"),
    ("lean_version", toJson Lean.versionString), ("lean_githash", toJson Lean.githash),
    ("theorem_name", toJson request.theoremName),
    ("statement_comparison", toJson true), ("axiom_audit", toJson true),
    ("builtin_kernel_replay", toJson false),
    ("declarations", toJson candidate.constOrder.size), ("proof_accepted", toJson false)] ++ reduction)).compress
  return 0
