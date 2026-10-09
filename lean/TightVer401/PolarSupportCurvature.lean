import TightVer401.PolarSupportHessian

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem planarRadius_sq (p : Coord) :
    planarRadius p ^ 2 = p 0 ^ 2 + p 1 ^ 2 := Real.sq_sqrt (by positivity)

theorem planarRadius_lt_weight (p : Coord) : planarRadius p < planarWeight p := by
  have hr : 0 ≤ planarRadius p := Real.sqrt_nonneg _
  have hw := planarWeight_pos p
  nlinarith [planarRadius_sq p, planarWeight_sq p]

theorem polarSupportPotential_hessian_factored (R a C : ℝ) {p : Coord}
    (hp : 0 < p 0 ^ 2 + p 1 ^ 2) (i j : Fin 2) :
    planarHessian (polarSupportPotential R a C) p i j =
      (R / planarRadius p - a / planarWeight p) * (if i = j then 1 else 0) +
      (-R / planarRadius p ^ 3 + a / planarWeight p ^ 3) * p i * p j := by
  rw [polarSupportPotential_hessian R a C hp i j]
  ring

theorem polarSupportPotential_hessian_det (R a C : ℝ) {p : Coord}
    (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    (planarHessian (polarSupportPotential R a C) p).det =
      -a * (R * planarWeight p - a * planarRadius p) /
        (planarRadius p * planarWeight p ^ 4) := by
  let A := R / planarRadius p - a / planarWeight p
  let B := -R / planarRadius p ^ 3 + a / planarWeight p ^ 3
  have hdet : (planarHessian (polarSupportPotential R a C) p).det =
      A * (A + B * (p 0 ^ 2 + p 1 ^ 2)) := by
    rw [Matrix.det_fin_two]
    simp only [polarSupportPotential_hessian_factored R a C hp]
    norm_num
    dsimp [A, B]
    ring
  have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hw : planarWeight p ≠ 0 := (planarWeight_pos p).ne'
  have hradial : A + B * (p 0 ^ 2 + p 1 ^ 2) = -a / planarWeight p ^ 3 := by
    rw [← planarRadius_sq p]
    dsimp [A, B]
    field_simp
    have hs : planarWeight p ^ 2 = planarRadius p ^ 2 + 1 := by
      nlinarith [planarWeight_sq p, planarRadius_sq p]
    have heq := congrArg (fun x : ℝ => a * planarRadius p * x) hs
    nlinarith [heq]
  rw [hdet, hradial]
  dsimp [A]
  field_simp <;> ring

theorem polarSupportPotential_hessian_det_neg {R a C : ℝ}
    (ha : 0 < a) (hR : a < R) {p : Coord} (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    (planarHessian (polarSupportPotential R a C) p).det < 0 := by
  rw [polarSupportPotential_hessian_det R a C hp]
  have hr : 0 < planarRadius p := Real.sqrt_pos.mpr hp
  have hw := planarWeight_pos p
  have hwr := planarRadius_lt_weight p
  have hnum : 0 < R * planarWeight p - a * planarRadius p := by
    have h₁ := mul_lt_mul_of_pos_right hR hw
    have h₂ := mul_lt_mul_of_pos_left hwr ha
    linarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hnum)
    (mul_pos hr (pow_pos hw 4))

theorem polarSupportPotential_gaussianCurvature {R a C : ℝ}
    (ha : 0 < a) (hR : a < R) {p : Coord} (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    gaussianCurvature (inducedMetric (planarSupportMap (polarSupportPotential R a C))) p =
      -planarRadius p / (a * (R * planarWeight p - a * planarRadius p)) := by
  have hU : IsOpen {p : Coord | 0 < p 0 ^ 2 + p 1 ^ 2} :=
    isOpen_lt continuous_const (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
  have hdet := polarSupportPotential_hessian_det_neg (C := C) ha hR hp
  rw [planarSupportMap_gaussianCurvature_at (polarSupportPotential_contDiffOn R a C)
    hU hp (ne_of_lt hdet), polarSupportPotential_hessian_det R a C hp]
  have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hw : planarWeight p ≠ 0 := (planarWeight_pos p).ne'
  have hnum : 0 < R * planarWeight p - a * planarRadius p := by
    have h₁ := mul_lt_mul_of_pos_right hR (planarWeight_pos p)
    have h₂ := mul_lt_mul_of_pos_left (planarRadius_lt_weight p) ha
    linarith
  field_simp [hr, hw, ha.ne', hnum.ne'] <;> ring

theorem polarSupportPotential_gaussianCurvature_neg {R a C : ℝ}
    (ha : 0 < a) (hR : a < R) {p : Coord} (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    gaussianCurvature (inducedMetric (planarSupportMap (polarSupportPotential R a C))) p < 0 := by
  have hU : IsOpen {p : Coord | 0 < p 0 ^ 2 + p 1 ^ 2} :=
    isOpen_lt continuous_const (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
  have hdet := polarSupportPotential_hessian_det_neg (C := C) ha hR hp
  exact (planarSupportMap_negative_curvature_iff (polarSupportPotential_contDiffOn R a C)
    hU hp (ne_of_lt hdet)).mpr hdet

end
end TightVer401
