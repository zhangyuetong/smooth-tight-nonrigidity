import TightVer401.VisibleConnectorFinalSmoothingGerms
import Lean

open Lean Elab Command in
elab "#final_smoothing_audit" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if !(name.toString.startsWith "TightVer401." || name.toString.startsWith "OAI." ||
        name.toString.startsWith "Schoenflies." ||
        name == `ite_eq_left || name == `dite_eq_left ||
        name == `ite_eq_left_decidable || name == `ite_eq_right_decidable ||
        name == `dite_eq_left_decidable || name == `dite_eq_right_decidable) then
      continue
    let axioms ← collectAxioms name
    if axioms.any (fun a => !allowed.contains a) then
      throwError "Unapproved transitive axiom in {name}: {axioms}"
    if info.type.hasSorry || (info.value? true).any Expr.hasSorry then
      throwError "Admission in {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | _ => "generated"
    if kind == "axiom" then throwError "Custom axiom is prohibited: {name}"
    let typeText ← liftTermElabM <| PrettyPrinter.ppExpr info.type
    let row := Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson kind),
      ("type", toJson typeText.pretty),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"VER401_AUDIT {row.compress}"
    count := count + 1
  if count == 0 then throwError "No project declarations found"
  logInfo m!"VER401_AUDIT_COUNT {count}"

#final_smoothing_audit


