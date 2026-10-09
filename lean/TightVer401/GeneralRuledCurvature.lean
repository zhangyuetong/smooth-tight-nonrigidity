import TightVer401.GeneralRuledGeometry

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem ambientCross_zero_left (e : Ambient) : ambientCross 0 e = 0 := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply]

theorem ambientCross_self (e : Ambient) : ambientCross e e = 0 := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply, mul_comm]

theorem ambientCross_zero_right (e : Ambient) : ambientCross e 0 = 0 := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply]

theorem ambientCross_norm_sq (a e : Ambient) :
    ‖ambientCross a e‖^2 = inner ℝ a a * inner ℝ e e - (inner ℝ a e)^2 := by
  rw [← real_inner_self_eq_norm_sq, ambient_inner_dot, ambient_inner_dot,
    ambient_inner_dot, ambient_inner_dot]
  have h := cross_dot_cross (fun i => a i) (fun i => e i) (fun i => a i) (fun i => e i)
  simpa only [ambientCross, pow_two, dotProduct_comm (fun i => e i) (fun i => a i)] using h

theorem general_ruled_differential_injective {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : HasDerivAt c (c₁ (p 0)) (p 0)) (he : HasDerivAt e (e₁ (p 0)) (p 0))
    (hδ : generalRuledDelta c₁ e e₁ (p 0) ≠ 0) :
    Function.Injective (fderiv ℝ (ruledMap c e) p) := by
  intro v w hvw
  have hz : fderiv ℝ (ruledMap c e) p (v - w) = 0 := by simp [map_sub, hvw]
  rw [fderiv_two_coordinates, general_ruled_partial_t hc he, general_ruled_partial_u hc he] at hz
  have hC : generalRuledCross c₁ e e₁ p ≠ 0 := general_ruled_cross_ne_zero hδ
  have hzC := congrArg (fun a => ambientCross a (e (p 0))) hz
  rw [ambientCross_add_left, ambientCross_smul_left, ambientCross_smul_left,
    ambientCross_self, smul_zero, add_zero, ambientCross_zero_left] at hzC
  have h0 : (v - w) 0 = 0 := (smul_eq_zero.mp hzC).resolve_right hC
  rw [h0, zero_smul, zero_add] at hz
  have he0 : e (p 0) ≠ 0 := by
    intro hez
    have hD : generalRuledDelta c₁ e e₁ (p 0) = 0 := by
      rw [generalRuledDelta, hez, ambientCross_zero_right, inner_zero_right]
    exact hδ hD
  have h1 : (v - w) 1 = 0 := (smul_eq_zero.mp hz).resolve_right he0
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

theorem general_ruled_metric_det {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : HasDerivAt c (c₁ (p 0)) (p 0)) (he : HasDerivAt e (e₁ (p 0)) (p 0)) :
    (inducedMetric (ruledMap c e) p).det = ‖generalRuledCross c₁ e e₁ p‖^2 := by
  rw [Matrix.det_fin_two]
  simp only [inducedMetric, general_ruled_partial_t hc he, general_ruled_partial_u hc he]
  rw [generalRuledCross, ambientCross_norm_sq,
    real_inner_comm (e (p 0)) (c₁ (p 0) + p 1 • e₁ (p 0))]
  ring

theorem general_ruled_gaussianCurvature {c e : ℝ → Ambient}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e)
    (hδ : ∀ s, generalRuledDelta (deriv c) e (deriv e) s ≠ 0) (p : Coord) :
    gaussianCurvature (inducedMetric (ruledMap c e)) p =
      -(generalRuledDelta (deriv c) e (deriv e) (p 0))^2 /
        ‖generalRuledCross (deriv c) e (deriv e) p‖^4 := by
  have hcd := fun s => (hc.differentiable (by simp) s).hasDerivAt
  have hed := fun s => (he.differentiable (by simp) s).hasDerivAt
  have hX := general_ruled_contDiff hc he
  have hg := inducedMetric_smoothPositiveOn hX.contDiffOn isOpen_univ
    (fun q _ => general_ruled_differential_injective (hcd (q 0)) (hed (q 0)) (hδ (q 0)))
  rw [curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hX.contDiffOn)
    isOpen_univ (Set.mem_univ p) (general_ruled_isUnitNormal (hcd (p 0)) (hed (p 0)) (hδ (p 0)))]
  have hc₁ := (contDiff_infty_iff_deriv.mp hc).2
  have he₁ := (contDiff_infty_iff_deriv.mp he).2
  obtain ⟨_, h01, h11⟩ := general_ruled_second_forms hcd hed
    (hc₁.differentiable (by simp) (p 0)).hasDerivAt (he₁.differentiable (by simp) (p 0)).hasDerivAt
  have h10 : secondFundamental (ruledMap c e) (generalRuledNormal (deriv c) e (deriv e) p) p 1 0 =
      generalRuledDelta (deriv c) e (deriv e) (p 0) / ‖generalRuledCross (deriv c) e (deriv e) p‖ := by
    rw [secondFundamental, coordPartial_comm hX.contDiffOn isOpen_univ (Set.mem_univ p) 1 0]
    exact h01
  rw [Matrix.det_fin_two, h01, h10, h11, mul_zero, zero_sub,
    general_ruled_metric_det (hcd (p 0)) (hed (p 0))]
  ring

end
end TightVer401
