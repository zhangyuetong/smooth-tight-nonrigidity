import TightVer401.PositiveExitConstructionSelectedHomotopy
import Mathlib.Topology.Path

/-! Concatenate literal selected-source homotopies inside the SAME domain.
The paths take values in actual closed loops whose entire images lie in U. -/
namespace TightVer401
noncomputable section
open Set Function
open scoped Topology

/-- Join two actual closed-loop families without losing their literal domain. -/
theorem positiveExit_actual_loop_homotopy_trans
    {U : Set ℂ} (H1 H2 : C(unitInterval, C(unitInterval, ℂ)))
    (he : H1 1 = H2 0)
    (hc1 : ∀ a, H1 a 1 = H1 a 0) (hc2 : ∀ a, H2 a 1 = H2 a 0)
    (hU1 : ∀ a t, H1 a t ∈ U) (hU2 : ∀ a t, H2 a t ∈ U) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      H 0 = H1 0 ∧ H 1 = H2 1 ∧
      (∀ a, H a 1 = H a 0) ∧ ∀ a t, H a t ∈ U := by
  let K : Set C(unitInterval, ℂ) := {c | c 1 = c 0 ∧ ∀ t, c t ∈ U}
  let x : K := ⟨H1 0, hc1 0, hU1 0⟩
  let y : K := ⟨H1 1, hc1 1, hU1 1⟩
  let z : K := ⟨H2 1, hc2 1, hU2 1⟩
  let p : Path x y := {
    toFun := fun a => ⟨H1 a, hc1 a, hU1 a⟩
    continuous_toFun := H1.continuous.subtype_mk _
    source' := rfl
    target' := rfl }
  let q : Path y z := {
    toFun := fun a => ⟨H2 a, hc2 a, hU2 a⟩
    continuous_toFun := H2.continuous.subtype_mk _
    source' := Subtype.ext he.symm
    target' := rfl }
  let pq := p.trans q
  let H : C(unitInterval, C(unitInterval, ℂ)) :=
    ⟨fun a => (pq a).val, continuous_subtype_val.comp pq.continuous⟩
  refine ⟨H, ?_, ?_, fun a => (pq a).property.1, fun a => (pq a).property.2⟩
  · exact congrArg Subtype.val pq.source
  · exact congrArg Subtype.val pq.target

/-- Reverse an actual family while retaining closedness and the SAME domain. -/
theorem positiveExit_actual_loop_homotopy_symm
    {U : Set ℂ} (H0 : C(unitInterval, C(unitInterval, ℂ)))
    (hc : ∀ a, H0 a 1 = H0 a 0) (hU : ∀ a t, H0 a t ∈ U) :
    ∃ H : C(unitInterval, C(unitInterval, ℂ)),
      H 0 = H0 1 ∧ H 1 = H0 0 ∧
      (∀ a, H a 1 = H a 0) ∧ ∀ a t, H a t ∈ U := by
  let K : Set C(unitInterval, ℂ) := {c | c 1 = c 0 ∧ ∀ t, c t ∈ U}
  let x : K := ⟨H0 0, hc 0, hU 0⟩
  let y : K := ⟨H0 1, hc 1, hU 1⟩
  let p : Path x y := {
    toFun := fun a => ⟨H0 a, hc a, hU a⟩
    continuous_toFun := H0.continuous.subtype_mk _
    source' := rfl
    target' := rfl }
  let H : C(unitInterval, C(unitInterval, ℂ)) :=
    ⟨fun a => (p.symm a).val, continuous_subtype_val.comp p.symm.continuous⟩
  refine ⟨H, ?_, ?_, fun a => (p.symm a).property.1, fun a => (p.symm a).property.2⟩
  · exact congrArg Subtype.val p.symm.source
  · exact congrArg Subtype.val p.symm.target

end
end TightVer401
