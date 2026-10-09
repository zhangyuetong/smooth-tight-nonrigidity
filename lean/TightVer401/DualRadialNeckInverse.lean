import TightVer401.DualRadialNeckConstants

namespace TightVer401
noncomputable section
open Set

def dualRadialNeckInverseRadius (a B p : ℝ) : ℝ := a + B / p ^ 2

theorem dualRadialNeck_inverse_radius_gt {a B p : ℝ} (hB : 0 < B) (hp : 0 < p) :
    a < dualRadialNeckInverseRadius a B p := by
  dsimp [dualRadialNeckInverseRadius]
  exact lt_add_of_pos_right _ (div_pos hB (sq_pos_of_pos hp))

theorem dualRadialNeck_inverse_sqrt {a B p : ℝ} (hB : 0 < B) (hp : 0 < p) :
    Real.sqrt (B * (dualRadialNeckInverseRadius a B p - a)) = B / p := by
  have heq : B * (dualRadialNeckInverseRadius a B p - a) = (B / p) ^ 2 := by
    dsimp [dualRadialNeckInverseRadius]
    field_simp [hB.ne', hp.ne']
    <;> ring
  rw [heq, Real.sqrt_sq (div_pos hB hp).le]

theorem dualRadialNeck_inverse_deriv (C a : ℝ) {B p : ℝ}
    (hB : 0 < B) (hp : 0 < p) :
    deriv (dualRadialNeck C B a) (dualRadialNeckInverseRadius a B p) = p := by
  rw [dualRadialNeck_deriv C a hB (dualRadialNeck_inverse_radius_gt hB hp),
    dualRadialNeck_inverse_sqrt hB hp]
  field_simp [hB.ne', hp.ne']

theorem dualRadialNeck_inverse_legendre (C a : ℝ) {B p : ℝ}
    (hB : 0 < B) (hp : 0 < p) :
    p * dualRadialNeckInverseRadius a B p -
        dualRadialNeck C B a (dualRadialNeckInverseRadius a B p) =
      a * p - B / p - C := by
  rw [dualRadialNeck, dualRadialNeck_inverse_sqrt hB hp]
  dsimp [dualRadialNeckInverseRadius]
  field_simp [hB.ne', hp.ne']
  <;> ring

theorem dualRadialNeck_radius_of_derivative (C a : ℝ) {B r p : ℝ}
    (hB : 0 < B) (hr : a < r) (hp : 0 < p)
    (hd : deriv (dualRadialNeck C B a) r = p) :
    r = dualRadialNeckInverseRadius a B p := by
  have hdisc : 0 < B * (r - a) := mul_pos hB (sub_pos.mpr hr)
  have hs : Real.sqrt (B * (r - a)) ≠ 0 := (Real.sqrt_pos.mpr hdisc).ne'
  rw [dualRadialNeck_deriv C a hB hr] at hd
  have hm : B = p * Real.sqrt (B * (r - a)) := (div_eq_iff hs).mp hd
  have hsq := congrArg (fun x : ℝ => x ^ 2) hm
  rw [mul_pow, Real.sq_sqrt hdisc.le] at hsq
  have hz : B * (p ^ 2 * (r - a) - B) = 0 := by nlinarith [hsq]
  have heq := (mul_eq_zero.mp hz).resolve_left hB.ne'
  dsimp [dualRadialNeckInverseRadius]
  have hp2 : p ^ 2 ≠ 0 := (sq_pos_of_pos hp).ne'
  have h : r - a = B / p ^ 2 := by
    apply (eq_div_iff hp2).mpr
    nlinarith [heq]
  linarith [h]

end
end TightVer401
