import TightVer401.FermiSupportPositiveGraph
import TightVer401.SphereSupportOpenGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiMetric_smoothPositiveOn {h : Coord → ℝ} {U : Set Coord}
    (hh : ContDiff ℝ ∞ h) (hn : ∀ p ∈ U, h p ≠ 0) :
    SmoothPositiveOn (fermiMetric h) U := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · exact (hh.pow 2).contDiffOn
    all_goals exact contDiffOn_const
  · intro p hp
    have he : fermiMetric h p = Matrix.diagonal (![h p^2,1] : Fin 2 → ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fermiMetric,Matrix.diagonal]
    rw [he,Matrix.posDef_diagonal_iff]
    intro i
    fin_cases i
    · exact sq_pos_of_ne_zero (hn p hp)
    · exact zero_lt_one

theorem fermiSupport_actual_spatial_saddle {ζ : ℝ → Ambient}
    {H : Coord → ℝ} {U : Set Coord}
    (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    {p : Coord} (hp : p ∈ U)
    (hB : (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) H p).det < 0) :
    let Q := fermiNormalMap ζ
    let g := inducedMetric Q
    let X := sphereSupportMap g Q H
    ContDiffOn ℝ ∞ X U ∧ Function.Injective (fderiv ℝ X p) ∧
      IsUnitNormalAt X (Q p) p ∧ secondFundamental X (Q p) p = -sphereSupportTensor g H p ∧
      gaussianCurvature (inducedMetric X) p < 0 := by
  let Q := fermiNormalMap ζ
  let g := inducedMetric Q
  have hQ : ContDiff ℝ ∞ Q := fermiNormalMap_contDiff hζ
  have hemetric : g = fermiMetric (fermiNormalScale (normalLoopCurvature ζ)) :=
    fermiNormalMap_inducedMetric hζ hunit hspeed
  have hg : SmoothPositiveOn g U := by
    rw [hemetric]
    exact fermiMetric_smoothPositiveOn (fermiNormalScale_contDiff (normalLoop_actual_smooth hζ).2) hscale
  have hi : IsometricOn g Q U := inducedMetric_isometricOn hQ.contDiffOn
  have hQu : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1 :=
    fun q _ => fermiNormalMap_unit hζ hunit hspeed q
  refine ⟨sphereSupportMap_contDiffOn hg hi.1 hH hU,
    sphereSupportMap_differential_injective hg hi hH hU hp hQu hB.ne,
    sphereSupportMap_isUnitNormal hg hi hH hU hp hQu,
    sphereSupportMap_secondFundamental hg hi hH hU hp hQu,?_⟩
  rw [sphereSupportMap_curvature_at hg hi hH hU hQu hp hB.ne]
  have hd : 0 < (g p).det := by
    rw [hemetric]
    simpa [fermiMetric,Matrix.det_fin_two] using sq_pos_of_ne_zero (hscale p hp)
  have hn : (sphereSupportEndomorphism g H p).det < 0 := by
    rw [sphereSupportEndomorphism,Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hd) hB
  exact div_neg_of_pos_of_neg zero_lt_one hn

end
end TightVer401
