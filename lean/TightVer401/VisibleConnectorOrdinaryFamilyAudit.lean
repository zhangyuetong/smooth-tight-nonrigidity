import TightVer401.VisibleConnectorOrdinaryFamilyTerminalJets
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedCoefficients
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedTopology
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedRawPotential
import TightVer401.VisibleConnectorOrdinaryFamilyBandCarrier
import TightVer401.VisibleConnectorOrdinaryFamilyRawPotential
import TightVer401.VisibleConnectorOrdinaryFamilyCoefficientContinuity
import TightVer401.VisibleConnectorOrdinaryFamilySourceEnclosure
import TightVer401.VisibleConnectorOrdinaryFamilySourceChart
import TightVer401.VisibleConnectorOrdinaryFamilySourceSeparation
import TightVer401.VisibleConnectorOrdinaryFamilyGradientEnclosure
import TightVer401.VisibleConnectorOrdinaryFamilyTerminalEscape
import TightVer401.VisibleConnectorOrdinaryFamilyLowerDelta
import Lean

open Lean Elab Command in
elab "#ordinary_family_audit" : command => do
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
    logInfo m!"ORDINARY_FAMILY_AUDIT {row.compress}"
    count := count + 1
  if count == 0 then throwError "No project declarations found"
  logInfo m!"ORDINARY_FAMILY_AUDIT_COUNT {count}"

#ordinary_family_audit
