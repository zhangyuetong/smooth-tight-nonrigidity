import TightVer401.RevolutionEndCurvature
import TightVer401.RevolutionEndNormalHeight
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

 def revolutionEndAbsoluteCurvatureDensity (q : ℝ → ℝ) (p : Coord) : ℝ :=
  |gaussianCurvature (inducedMetric (revolutionEnd q)) p| *
    Real.sqrt (inducedMetric (revolutionEnd q) p).det

 def revolutionEndHeightDensity (q : ℝ → ℝ) (z : ℝ) : ℝ :=
  deriv (deriv q) z / revolutionWeight (deriv q z)^3

 theorem revolutionEnd_metric_areaDensity {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {p : Coord} (hqp : 0 < q (p 1)) :
    Real.sqrt (inducedMetric (revolutionEnd q) p).det =
      q (p 1) * revolutionWeight (deriv q (p 1)) := by
  rw [revolutionEnd_metric_det hq p]
  have hs : q (p 1)^2 * (1 + deriv q (p 1)^2) =
      (q (p 1) * revolutionWeight (deriv q (p 1)))^2 := by
    rw [mul_pow, revolutionWeight_sq]
  rw [hs, Real.sqrt_sq (mul_nonneg hqp.le (revolutionWeight_pos _).le)]

 theorem revolutionEnd_absoluteCurvatureDensity_eq {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {p : Coord} (hqp : 0 < q (p 1)) (hc : 0 < deriv (deriv q) (p 1)) :
    revolutionEndAbsoluteCurvatureDensity q p = revolutionEndHeightDensity q (p 1) := by
  unfold revolutionEndAbsoluteCurvatureDensity revolutionEndHeightDensity
  rw [abs_of_neg (revolutionEnd_gaussianCurvature_neg hq hqp hc),
    revolutionEnd_gaussianCurvature hq hqp, revolutionEnd_metric_areaDensity hq hqp,
    ← revolutionWeight_sq]
  have hw := ne_of_gt (revolutionWeight_pos (deriv q (p 1)))
  field_simp [ne_of_gt hqp, hw]
  <;> ring

 theorem revolutionEndHeightDensity_continuous {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    Continuous (revolutionEndHeightDensity q) := by
  have hqd := (contDiff_infty_iff_deriv.mp hq).2
  have hqdd := (contDiff_infty_iff_deriv.mp hqd).2
  exact hqdd.continuous.div
    ((Real.continuous_sqrt.comp (continuous_const.add (hqd.continuous.pow 2))).pow 3)
    (fun z => pow_ne_zero 3 (ne_of_gt (revolutionWeight_pos (deriv q z))))

 theorem revolutionEndHeightDensity_integral {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (H R : ℝ) :
    (∫ z in H..R, revolutionEndHeightDensity q z) =
      revolutionNormalHeight q R - revolutionNormalHeight q H := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => revolutionNormalHeight_hasDerivAt hq z)
    ((revolutionEndHeightDensity_continuous hq).intervalIntegrable H R)

 theorem revolutionEndHeightDensity_integrableOn {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    IntegrableOn (revolutionEndHeightDensity q) (Ici H) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun z _ => revolutionNormalHeight_hasDerivAt hq z)
    (fun z hz => div_nonneg (hc z hz.out.le).le (pow_pos (revolutionWeight_pos _) 3).le)
    (revolutionNormalHeight_tendsto hslope)

 theorem revolutionEndHeightDensity_integral_Ici {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    (∫ z in Ici H, revolutionEndHeightDensity q z) = 1 - revolutionNormalHeight q H := by
  rw [integral_Ici_eq_integral_Ioi]
  exact integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun z _ => revolutionNormalHeight_hasDerivAt hq z)
    (fun z hz => div_nonneg (hc z hz.out.le).le (pow_pos (revolutionWeight_pos _) 3).le)
    (revolutionNormalHeight_tendsto hslope)

 theorem revolutionEnd_absoluteCurvature_integral_Ici {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z)
    (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) (θ : ℝ) :
    (∫ z in Ici H, revolutionEndAbsoluteCurvatureDensity q (![θ, z] : Coord)) =
      1 - revolutionNormalHeight q H := by
  rw [← revolutionEndHeightDensity_integral_Ici hq hc hslope]
  apply setIntegral_congr_fun measurableSet_Ici
  intro z hz
  exact revolutionEnd_absoluteCurvatureDensity_eq hq (hpos z hz) (hc z hz)

 theorem revolutionEnd_absoluteCurvature_iterated_integral {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z)
    (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      ∫ z in Ici H, revolutionEndAbsoluteCurvatureDensity q (![θ, z] : Coord)) =
      2 * Real.pi * (1 - revolutionNormalHeight q H) := by
  simp_rw [revolutionEnd_absoluteCurvature_integral_Ici hq hpos hc hslope]
  simp [intervalIntegral.integral_const]
  ring

end
end TightVer401

