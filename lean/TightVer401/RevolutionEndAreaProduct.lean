import TightVer401.RevolutionEndArea
import Mathlib.MeasureTheory.Integral.Prod

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped Topology ContDiff

 theorem revolutionEnd_absoluteCurvature_product_integrable {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z)
    (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    IntegrableOn (fun p : ℝ × ℝ => revolutionEndAbsoluteCurvatureDensity q (![p.1, p.2] : Coord))
      (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Ici H) (volume.prod volume) := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => revolutionEndHeightDensity q p.2)
      (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Ici H) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact (revolutionEndHeightDensity_integrableOn hq hc hslope).comp_snd _
  apply hi.congr_fun _ (measurableSet_Icc.prod measurableSet_Ici)
  intro p hp
  exact (revolutionEnd_absoluteCurvatureDensity_eq hq (p := ![p.1, p.2]) (hpos p.2 hp.2) (hc p.2 hp.2)).symm

 theorem revolutionEnd_absoluteCurvature_product_integral {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z)
    (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    (∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Ici H,
      revolutionEndAbsoluteCurvatureDensity q (![p.1, p.2] : Coord) ∂volume.prod volume) =
      2 * Real.pi * (1 - revolutionNormalHeight q H) := by
  rw [setIntegral_prod _ (revolutionEnd_absoluteCurvature_product_integrable hq hpos hc hslope)]
  simp_rw [revolutionEnd_absoluteCurvature_integral_Ici hq hpos hc hslope]
  simp [setIntegral_const, Real.volume_Icc, Real.pi_pos.le]

 theorem revolutionEnd_absoluteCurvature_product_integral_lt {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z)
    (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) (hstart : 0 < deriv q H) :
    (∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Ici H,
      revolutionEndAbsoluteCurvatureDensity q (![p.1, p.2] : Coord) ∂volume.prod volume) < 2 * Real.pi := by
  rw [revolutionEnd_absoluteCurvature_product_integral hq hpos hc hslope]
  have hheight : 0 < revolutionNormalHeight q H := (revolutionNormalHeight_mem_Ioo hstart).1
  nlinarith [Real.pi_pos]

end
end TightVer401

