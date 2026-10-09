import TightVer401.SurfaceMetric

/-! Strict negativity of the actual intrinsic curvature of the ruled band.
Smooth positivity and isometry for its induced metric are proved here, then
OpenAI's Gauss equation is applied to the actual unit normal and second form. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix

theorem ruled_differential_injective
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : τ (p 0) ≠ 0) : Function.Injective (fderiv ℝ (ruledMap γ E) p) := by
  intro v w hvw
  have hz : fderiv ℝ (ruledMap γ E) p (v - w) = 0 := by simp [map_sub, hvw]
  obtain ⟨h00, h01, h10, h11⟩ := ruled_metric_entries hγ hE hf
  have he := inducedMetric_bilinear (ruledMap γ E) p (v - w) (v - w)
  rw [hz, inner_zero_left] at he
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, h00, h01, h10, h11,
    zero_mul, one_mul, add_zero, zero_add] at he
  have hp := ruledEnergy_pos (k := k (p 0)) (u := p 1) hτ
  have h0 : (v - w) 0 = 0 := by
    by_contra hn
    have hs := mul_pos hp (sq_pos_of_ne_zero hn)
    nlinarith [sq_nonneg ((v - w) 1)]
  have h1 : (v - w) 1 = 0 := by
    rw [h0] at he
    nlinarith [sq_nonneg ((v - w) 1)]
  have hsub : v - w = 0 := by
    ext i
    fin_cases i <;> assumption
  exact sub_eq_zero.mp hsub

theorem ruled_second_form_det
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {U : Set Coord} {p : Coord}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hF : ContDiffOn ℝ ∞ (ruledMap γ E) U) (hU : IsOpen U) (hp : p ∈ U)
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : τ (p 0) ≠ 0) :
    (secondFundamental (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p).det =
      -(τ (p 0))^2 / ruledEnergy (k (p 0)) (τ (p 0)) (p 1) := by
  obtain ⟨h01, h11⟩ := ruled_mixed_and_ruling_second_form hγ hE hf
  have h10 : secondFundamental (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p 1 0 =
      τ (p 0) / Real.sqrt (ruledEnergy (k (p 0)) (τ (p 0)) (p 1)) := by
    rw [secondFundamental, coordPartial_comm hF hU hp 1 0]
    exact h01
  rw [Matrix.det_fin_two, h01, h10, h11, mul_zero, zero_sub]
  have hpos := ruledEnergy_pos (k := k (p 0)) (u := p 1) hτ
  have hsq := Real.sq_sqrt hpos.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp
  nlinarith [hsq]

theorem ruled_gaussianCurvature
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {U : Set Coord}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hF : ContDiffOn ℝ ∞ (ruledMap γ E) U) (hU : IsOpen U)
    (hf : ∀ p ∈ U, IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : ∀ p ∈ U, τ (p 0) ≠ 0)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (inducedMetric (ruledMap γ E)) p =
      -(τ (p 0))^2 / (ruledEnergy (k (p 0)) (τ (p 0)) (p 1))^2 := by
  have hg := inducedMetric_smoothPositiveOn hF hU
    (fun q hq => ruled_differential_injective (hγ (q 0)) (hE (q 0)) (hf q hq) (hτ q hq))
  rw [curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hF) hU hp
    (ruled_isUnitNormal (hγ (p 0)) (hE (p 0)) (hf p hp) (hτ p hp)),
    ruled_second_form_det hγ hE hF hU hp (hf p hp) (hτ p hp),
    ruled_metric_det (hγ (p 0)) (hE (p 0)) (hf p hp), div_div]
  simp only [pow_two]

theorem ruled_gaussianCurvature_neg
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {U : Set Coord}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hF : ContDiffOn ℝ ∞ (ruledMap γ E) U) (hU : IsOpen U)
    (hf : ∀ p ∈ U, IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : ∀ p ∈ U, τ (p 0) ≠ 0)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (inducedMetric (ruledMap γ E)) p < 0 := by
  rw [ruled_gaussianCurvature hγ hE hF hU hf hτ hp]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (hτ p hp)))
    (sq_pos_of_pos (ruledEnergy_pos (hτ p hp)))

end
end TightVer401
