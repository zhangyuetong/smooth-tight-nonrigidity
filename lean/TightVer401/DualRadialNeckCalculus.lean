import TightVer401.RadialCapCalculus

namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology

/-- The actual square-root profile of ver500, before relative radial smoothing. -/
def dualRadialNeck (C B a r : ℝ) : ℝ := C + 2 * Real.sqrt (B * (r - a))

theorem dualRadialNeck_contDiffOn (C a : ℝ) {B : ℝ} (hB : 0 < B) :
    ContDiffOn ℝ ∞ (dualRadialNeck C B a) (Ioi a) := by
  apply contDiffOn_const.add
  apply contDiffOn_const.mul
  apply (contDiff_const.mul (contDiff_id.sub contDiff_const)).contDiffOn.sqrt
  intro r hr
  exact ne_of_gt (mul_pos hB (sub_pos.mpr hr))

theorem dualRadialNeck_hasDerivAt (C a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : a < r) :
    HasDerivAt (dualRadialNeck C B a)
      (B / Real.sqrt (B * (r - a))) r := by
  have hdisc : 0 < B * (r - a) := mul_pos hB (sub_pos.mpr hr)
  have hs : Real.sqrt (B * (r - a)) ≠ 0 := (Real.sqrt_pos.mpr hdisc).ne'
  have hd := ((hasDerivAt_id r).sub_const a).const_mul B
  have hd' := (hd.sqrt (ne_of_gt hdisc)).const_mul 2
  simp only [id_eq, mul_one] at hd'
  convert hd'.const_add C using 1 <;> try rfl
  field_simp [hs]
  <;> ring

theorem dualRadialNeck_deriv (C a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : a < r) :
    deriv (dualRadialNeck C B a) r = B / Real.sqrt (B * (r - a)) :=
  (dualRadialNeck_hasDerivAt C a hB hr).deriv

theorem dualRadialNeck_deriv_hasDerivAt (C a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : a < r) :
    HasDerivAt (deriv (dualRadialNeck C B a))
      (-(B ^ 2) / (2 * Real.sqrt (B * (r - a)) ^ 3)) r := by
  have hdisc : 0 < B * (r - a) := mul_pos hB (sub_pos.mpr hr)
  have hs : Real.sqrt (B * (r - a)) ≠ 0 := (Real.sqrt_pos.mpr hdisc).ne'
  have hd := ((hasDerivAt_id r).sub_const a).const_mul B
  have hd' := hd.sqrt (ne_of_gt hdisc)
  have hquot := (hasDerivAt_const r B).div hd' hs
  have heq : deriv (dualRadialNeck C B a) =ᶠ[𝓝 r]
      (fun t => B / Real.sqrt (B * (t - a))) := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    exact dualRadialNeck_deriv C a hB ht
  simp only [id_eq, mul_one] at hquot
  convert hquot.congr_of_eventuallyEq heq using 1 <;> try rfl
  field_simp [hs]
  <;> ring

theorem dualRadialNeck_second_deriv (C a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : a < r) :
    deriv (deriv (dualRadialNeck C B a)) r =
      -(B ^ 2) / (2 * Real.sqrt (B * (r - a)) ^ 3) :=
  (dualRadialNeck_deriv_hasDerivAt C a hB hr).deriv

theorem dualRadialNeck_strict_derivative_signs (C a : ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : a < r) :
    0 < deriv (dualRadialNeck C B a) r ∧
      deriv (deriv (dualRadialNeck C B a)) r < 0 := by
  have hs := Real.sqrt_pos.mpr (mul_pos hB (sub_pos.mpr hr))
  constructor
  · rw [dualRadialNeck_deriv C a hB hr]
    exact div_pos hB hs
  · rw [dualRadialNeck_second_deriv C a hB hr]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hB)) (by positivity)

end
end TightVer401
