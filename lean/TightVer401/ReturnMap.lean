import OAI.Geometry.IsometricImmersion.Calculus.CoordinateDerivatives
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Algebra and actual first derivative of the return formula in eq:return.
Derivation of this map from the asymptotic differential equation is a separate target.
-/
namespace TightVer401
noncomputable section

def projectiveReturn (c u : ℝ) : ℝ := u / (1 + c * u)

theorem projectiveReturn_zero (u : ℝ) : projectiveReturn 0 u = u := by
  simp [projectiveReturn]

theorem projectiveReturn_fixed_iff (c u : ℝ) (hu : u ≠ 0) (hd : 1 + c * u ≠ 0) :
    projectiveReturn c u = u ↔ c = 0 := by
  unfold projectiveReturn
  rw [div_eq_iff hd]
  constructor
  · intro h
    have hz : c * u * u = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hu)).resolve_right hu
  · intro hc
    simp [hc]

theorem projectiveReturn_multiplier_one (c : ℝ) :
    HasDerivAt (projectiveReturn c) 1 0 := by
  have hd : HasDerivAt (fun u : ℝ => 1 + c * u) c 0 := by
    exact (hasDerivAt_const_mul c).const_add 1
  convert! (hasDerivAt_id' (0 : ℝ)).fun_div hd (by simp) using 1
  simp

theorem projectiveReturn_deriv_zero (c : ℝ) : deriv (projectiveReturn c) 0 = 1 :=
  (projectiveReturn_multiplier_one c).deriv

theorem projectiveReturn_comp (c d u : ℝ)
    (hd : 1 + d * u ≠ 0) (_hcd : 1 + (c + d) * u ≠ 0) :
    projectiveReturn c (projectiveReturn d u) = projectiveReturn (c + d) u := by
  unfold projectiveReturn
  have heq : 1 + c * (u / (1 + d * u)) = (1 + (c + d) * u) / (1 + d * u) := by
    apply (eq_div_iff hd).mpr
    rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hd]
    ring
  rw [heq]
  exact div_div_div_cancel_right₀ hd _ _

end
end TightVer401
