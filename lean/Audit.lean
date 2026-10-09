import TightVer401
import Lean

open Lean Elab Command in
elab "#ver401_audit" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  -- Printed types can contain depth omissions. Check the full expression with
  -- the kernel instead: the conditional helper's result inhabits EXACTLY the
  -- canonical type, and the latter starts with an existential, not premises.
  let pairChecked ← liftTermElabM do
    let canonicalType ← Meta.inferType
      (mkConst ``TightVer401.exists_noncongruent_isometric_tight_tori_pair)
    unless canonicalType.consumeMData.getAppFn.isConstOf ``Exists do
      throwError "Canonical pair type must start with an existential"
    let supplied := mkApp
      (mkConst ``TightVer401.exists_noncongruent_isometric_tight_tori_pair_of_classical)
      (mkConst ``TightVer401.classicalPositiveGaussTightness_proved)
    let identity := mkLambda `pairResult BinderInfo.default canonicalType (mkBVar 0)
    Meta.checkWithKernel (mkApp identity supplied)
    return true
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
    let pairEvidence := if name == ``TightVer401.exists_noncongruent_isometric_tight_tori_pair
      then [("unconditional_pair_conclusion_checked", toJson pairChecked)] else []
    let row := Json.mkObj ([
      ("name", toJson name.toString), ("kind", toJson kind),
      ("type", toJson typeText.pretty),
      ("axioms", toJson (axioms.map Name.toString))] ++ pairEvidence)
    logInfo m!"VER401_AUDIT {row.compress}"
    count := count + 1
  if count == 0 then throwError "No project declarations found"
  logInfo m!"VER401_AUDIT_COUNT {count}"

#ver401_audit
