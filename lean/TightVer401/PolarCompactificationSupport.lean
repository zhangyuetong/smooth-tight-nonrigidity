import TightVer401.PolarCompactificationCalculus
import TightVer401.PolarSupportGerm

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def polarGaussSource (θ t : ℝ) : Coord :=
  ![(Real.sin t / Real.cos t) * Real.cos θ, (Real.sin t / Real.cos t) * Real.sin θ]

theorem polarGaussSource_sq (θ t : ℝ) :
    (polarGaussSource θ t) 0 ^ 2 + (polarGaussSource θ t) 1 ^ 2 =
      (Real.sin t / Real.cos t)^2 := by
  dsimp [polarGaussSource]
  have hh := congrArg (fun x : ℝ => (Real.sin t / Real.cos t)^2 * x)
    (Real.sin_sq_add_cos_sq θ)
  nlinarith [hh]

theorem polarGaussSource_radius {θ t : ℝ} (hs : 0 < Real.sin t) (hc : 0 < Real.cos t) :
    planarRadius (polarGaussSource θ t) = Real.sin t / Real.cos t := by
  rw [planarRadius, polarGaussSource_sq, Real.sqrt_sq (div_pos hs hc).le]

theorem polarGaussSource_weight {θ t : ℝ} (hc : 0 < Real.cos t) :
    planarWeight (polarGaussSource θ t) = 1 / Real.cos t := by
  have hsq : planarWeight (polarGaussSource θ t)^2 = (1 / Real.cos t)^2 := by
    rw [planarWeight_sq]
    have hp := polarGaussSource_sq θ t
    rw [show 1 + (polarGaussSource θ t) 0 ^ 2 + (polarGaussSource θ t) 1 ^ 2 =
      1 + ((polarGaussSource θ t) 0 ^ 2 + (polarGaussSource θ t) 1 ^ 2) by ring, hp]
    field_simp [hc.ne']
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hw := planarWeight_pos (polarGaussSource θ t)
  have hi : 0 < 1 / Real.cos t := div_pos zero_lt_one hc
  nlinarith [hsq]

theorem planarSupportMap_neg (G : Coord → ℝ) (p : Coord) :
    planarSupportMap (fun q => -G q) p = -planarSupportMap G p := by
  have hpartial (i : Fin 2) : coordPartial i (fun q => -G q) p = -coordPartial i G p := by
    simp [coordPartial, fderiv_fun_neg]
  ext i
  fin_cases i <;> simp [planarSupportMap, hpartial] <;> ring

theorem polarCompactification_eq_support {θ t : ℝ}
    (hs : 0 < Real.sin t) (hc : 0 < Real.cos t) (R a C : ℝ) :
    polarCompactification R a C ![θ, t] =
      planarSupportMap (fun p => -polarSupportPotential R a C p) (polarGaussSource θ t) := by
  have hp : 0 < (polarGaussSource θ t) 0 ^ 2 + (polarGaussSource θ t) 1 ^ 2 := by
    rw [polarGaussSource_sq]
    exact sq_pos_of_pos (div_pos hs hc)
  rw [planarSupportMap_neg, polarSupportPotential_supportMap R a C hp,
    polarGaussSource_radius hs hc, polarGaussSource_weight hc]
  ext i
  fin_cases i <;> simp [polarCompactification, revolutionRadial, revolutionAxis, polarGaussSource]
  all_goals field_simp [hs.ne', hc.ne'] <;> ring

end
end TightVer401
