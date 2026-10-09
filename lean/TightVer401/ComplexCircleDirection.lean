import TightVer401.CircleDiskWinding

namespace TightVer401
noncomputable section
open Set
open scoped Topology

def complexCircleDirection (z : ℂ) : Circle :=
  AddCircle.toCircle (T := 2 * Real.pi) (Complex.arg z : Real.Angle)

theorem complexCircleDirection_continuousOn :
    ContinuousOn complexCircleDirection {z : ℂ | z ≠ 0} := by
  intro z hz
  exact ((AddCircle.continuous_toCircle (T := 2 * Real.pi)).continuousAt.comp
    (Complex.continuousAt_arg_coe_angle hz)).continuousWithinAt

theorem complexCircleDirection_coe (z : ℂ) :
    (complexCircleDirection z : ℂ) = Complex.exp ((z.arg : ℂ) * Complex.I) := by
  change (AddCircle.toCircle (T := 2 * Real.pi) (z.arg : AddCircle (2 * Real.pi)) : ℂ) = _
  rw [AddCircle.toCircle_apply_mk]
  simp only [div_self (ne_of_gt Real.two_pi_pos), one_mul, Circle.coe_exp]

theorem complexCircleDirection_normalized {z : ℂ} (hz : z ≠ 0) :
    (complexCircleDirection z : ℂ) = ‖z‖⁻¹ • z := by
  rw [complexCircleDirection_coe, Complex.real_smul]
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  apply (mul_left_cancel₀ hn)
  rw [Complex.norm_mul_exp_arg_mul_I]
  push_cast
  field_simp

theorem complexCircleDirection_eq_of_exp {z : ℂ} {φ : ℝ} (hz : z ≠ 0)
    (hφ : Complex.exp ((φ : ℂ) * Complex.I) = ‖z‖⁻¹ • z) :
    complexCircleDirection z = Circle.exp φ := by
  apply Subtype.ext
  exact (complexCircleDirection_normalized hz).trans hφ.symm
end
end TightVer401
