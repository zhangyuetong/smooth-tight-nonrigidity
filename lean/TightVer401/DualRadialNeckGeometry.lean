import TightVer401.DualRadialNeckLimits
import TightVer401.RadialPlanarCurvature

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The literal inverse Legendre profile in ver500. -/
def dualRadialNeckLegendreGerm (a B C p : ℝ) : ℝ := a * p - B / p - C

theorem dualRadialNeckLegendreGerm_contDiffOn (a B C : ℝ) :
    ContDiffOn ℝ ∞ (dualRadialNeckLegendreGerm a B C) (Ioi 0) := by
  apply (contDiff_const.mul contDiff_id).contDiffOn.sub _ |>.sub contDiffOn_const
  apply contDiffOn_const.div contDiffOn_id
  intro p hp
  exact ne_of_gt hp

theorem dualRadialNeckLegendreGerm_hasDerivAt (a B C : ℝ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (dualRadialNeckLegendreGerm a B C) (a + B / p ^ 2) p := by
  have hd := (((hasDerivAt_id p).const_mul a).sub
    ((hasDerivAt_const p B).div (hasDerivAt_id p) hp.ne')).sub_const C
  simp only [id_eq, mul_one] at hd
  convert hd using 1 <;> try rfl
  field_simp [hp.ne']
  <;> ring

theorem dualRadialNeckLegendreGerm_deriv (a B C : ℝ) {p : ℝ} (hp : 0 < p) :
    deriv (dualRadialNeckLegendreGerm a B C) p = a + B / p ^ 2 :=
  (dualRadialNeckLegendreGerm_hasDerivAt a B C hp).deriv

theorem dualRadialNeckLegendreGerm_deriv_hasDerivAt (a B C : ℝ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (deriv (dualRadialNeckLegendreGerm a B C)) (-2 * B / p ^ 3) p := by
  have hd := ((hasDerivAt_const p B).div ((hasDerivAt_id p).pow 2) (pow_ne_zero 2 hp.ne')).const_add a
  simp only [Pi.pow_apply, id_eq] at hd
  have heq : deriv (dualRadialNeckLegendreGerm a B C) =ᶠ[𝓝 p]
      (fun q => a + B / q ^ 2) := by
    filter_upwards [eventually_gt_nhds hp] with q hq
    exact dualRadialNeckLegendreGerm_deriv a B C hq
  convert hd.congr_of_eventuallyEq heq using 1 <;> try rfl
  field_simp [hp.ne']
  <;> ring

theorem dualRadialNeckLegendreGerm_second_deriv (a B C : ℝ) {p : ℝ} (hp : 0 < p) :
    deriv (deriv (dualRadialNeckLegendreGerm a B C)) p = -2 * B / p ^ 3 :=
  (dualRadialNeckLegendreGerm_deriv_hasDerivAt a B C hp).deriv

theorem dualRadialNeckLegendreGerm_strict_derivative_signs (C : ℝ) {a B p : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hp : 0 < p) :
    0 < deriv (dualRadialNeckLegendreGerm a B C) p ∧
      deriv (deriv (dualRadialNeckLegendreGerm a B C)) p < 0 := by
  constructor
  · rw [dualRadialNeckLegendreGerm_deriv _ _ _ hp]
    exact add_pos ha (div_pos hB (sq_pos_of_pos hp))
  · rw [dualRadialNeckLegendreGerm_second_deriv _ _ _ hp]
    exact div_neg_of_neg_of_pos (by nlinarith) (pow_pos hp 3)

/-- The square-root radial support has an actual nonsingular differential
and strictly negative intrinsic Gaussian curvature. -/
theorem dualRadialNeck_radial_support_geometry (C a : ℝ) {B : ℝ} (hB : 0 < B)
    {p : Coord} (hp : p ∈ radialPlanarDomain (Ioi a)) :
    Function.Injective (fderiv ℝ
      (planarSupportMap (radialPlanarPotential (dualRadialNeck C B a))) p) ∧
    gaussianCurvature (inducedMetric
      (planarSupportMap (radialPlanarPotential (dualRadialNeck C B a)))) p < 0 := by
  have hs := dualRadialNeck_strict_derivative_signs C a hB hp.2
  have hprod := mul_neg_of_pos_of_neg hs.1 hs.2
  have hf := dualRadialNeck_contDiffOn C a hB
  have hdet := radialPlanarPotential_hessian_det_neg hf isOpen_Ioi hp hprod
  exact ⟨planarSupportMap_differential_injective
    (radialPlanarPotential_contDiffOn hf) (radialPlanarDomain_isOpen isOpen_Ioi) hp hdet.ne,
    radialPlanarPotential_gaussianCurvature_neg hf isOpen_Ioi hp hprod⟩

/-- The inverse Legendre germ is also realized with the actual induced
metric, differential, and Gaussian curvature used throughout the checked engine. -/
theorem dualRadialNeckLegendreGerm_radial_support_geometry (C : ℝ) {a B : ℝ}
    (ha : 0 < a) (hB : 0 < B) {p : Coord}
    (hp : p ∈ radialPlanarDomain (Ioi 0)) :
    Function.Injective (fderiv ℝ
      (planarSupportMap (radialPlanarPotential (dualRadialNeckLegendreGerm a B C))) p) ∧
    gaussianCurvature (inducedMetric
      (planarSupportMap (radialPlanarPotential (dualRadialNeckLegendreGerm a B C)))) p < 0 := by
  have hs := dualRadialNeckLegendreGerm_strict_derivative_signs C ha hB hp.2
  have hprod := mul_neg_of_pos_of_neg hs.1 hs.2
  have hf := dualRadialNeckLegendreGerm_contDiffOn a B C
  have hdet := radialPlanarPotential_hessian_det_neg hf isOpen_Ioi hp hprod
  exact ⟨planarSupportMap_differential_injective
    (radialPlanarPotential_contDiffOn hf) (radialPlanarDomain_isOpen isOpen_Ioi) hp hdet.ne,
    radialPlanarPotential_gaussianCurvature_neg hf isOpen_Ioi hp hprod⟩

end
end TightVer401
