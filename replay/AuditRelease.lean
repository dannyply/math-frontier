import JocelynWorkspace

/-!
# Release axiom and statement audit

Elaborated with `lake env lean replay/AuditRelease.lean` by `scripts/audit.py` and
`replay/replay.py`. It is not part of the `JocelynWorkspace` library.

Input: `REPLAY_DECLS_FILE`, a file with one fully qualified declaration name per line
(normally the names in `release/manifest.json`).
Output: one JSON object per declaration on stdout, prefixed with `REPLAY-AUDIT `.
Each object gives the name, kind, defining module, `Lean.collectAxioms` result, the
`pp.all` rendering of the type with no step limit (hashed into `statement_sha256`; the
field `pp_truncated` is true if the rendering still contains an elision `⋯`, and the
audit then fails), the default rendering of
the type at width 100 (the human-readable statement), and the repository constants that
occur in the type (the statement surface). Every axiom name appears twice. `axioms` holds
the display form (`Name.toString`). `axioms_raw` holds the component-joined form that
lean4export/Nanoda use, which keeps macro scopes such as `_@`/`_hyg`.
-/

open Lean Elab Command Meta

/-- Options of the statement fingerprint: `pp.all` with no limit on pretty-printer steps.
The default `pp.maxSteps` elides large terms as `⋯`, which can make different statements
print identically. `scripts/test_fingerprint.py` checks that this file uses these options. -/
def fingerprintOptions (o : Options) : Options :=
  (o.setBool `pp.all true).set `pp.maxSteps (1000000000 : Nat)

/-- Components joined by `.`, with numeric components printed as digits. This matches
Nanoda's `name_to_string` for names read from a lean4export file. -/
def replayRawName (n : Name) : String :=
  ".".intercalate <| n.components.map fun
    | .str _ s => s
    | .num _ k => toString k
    | .anonymous => ""

def replayKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def replayModuleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => toString (env.header.moduleNames[idx.toNat]!)
  | none => "<current>"

run_cmd do
  let some path ← IO.getEnv "REPLAY_DECLS_FILE"
    | throwError "REPLAY_DECLS_FILE is not set"
  let lines ← IO.FS.lines path
  let env ← getEnv
  for line in lines do
    let text := line.trimAscii.toString
    if text.isEmpty then continue
    let n := text.toName
    match env.find? n with
    | none =>
      IO.println ("REPLAY-AUDIT " ++ (Json.mkObj [("name", toJson text), ("found", toJson false)]).compress)
    | some ci =>
      let axs ← liftCoreM (Lean.collectAxioms n)
      let modName := replayModuleOf env n
      let ppAll ← liftTermElabM <| withOptions fingerprintOptions do
        return (← ppExpr ci.type).pretty 100000
      let ppDefault ← liftTermElabM <| do
        return (← ppExpr ci.type).pretty 100
      let surface := ci.type.getUsedConstants.toList.filterMap fun c =>
        let m := replayModuleOf env c
        if m.startsWith "JocelynWorkspace" then
          some (Json.mkObj [("name", toJson c.toString), ("module", toJson m)])
        else none
      IO.println ("REPLAY-AUDIT " ++ (Json.mkObj [
        ("name", toJson text),
        ("found", toJson true),
        ("kind", toJson (replayKind ci)),
        ("module", toJson modName),
        ("level_params", toJson (ci.levelParams.map toString)),
        ("axioms", toJson (axs.map toString)),
        ("axioms_raw", toJson (axs.map replayRawName)),
        ("statement_constants", Json.arr surface.toArray),
        ("type_pp_all", toJson ppAll),
        ("pp_truncated", toJson (decide ((ppAll.splitOn "⋯").length > 1))),
        ("type_pp", toJson ppDefault)]).compress)
