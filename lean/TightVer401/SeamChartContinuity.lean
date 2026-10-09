import TightVer401.SeamChartHessian

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

theorem seamCoordinateJacobian_continuous {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (seamCoordinateJacobian Φ) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro i
  exact (smoothing_partial_contDiff ((contDiff_apply ℝ ℝ a).comp hΦ) i).continuous

theorem seamChartConnection_continuousAt {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ)
    {p : Coord} (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) (k i j : Fin 2) :
    ContinuousAt (seamChartConnection Φ k i j) p := by
  have hInv : ContinuousAt (fun q => (seamCoordinateJacobian Φ q)⁻¹) p := by
    apply (continuousAt_matrix_inv (seamCoordinateJacobian Φ p) ?_).comp
      (seamCoordinateJacobian_continuous hΦ).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hJ
  have hentry (a : Fin 2) : ContinuousAt (fun q => (seamCoordinateJacobian Φ q)⁻¹ k a) p :=
    (continuous_apply a).continuousAt.comp ((continuous_apply k).continuousAt.comp hInv)
  have hH (a : Fin 2) : ContinuousAt (fun q => planarHessian (fun x => Φ x a) q i j) p :=
    (smoothing_partial_contDiff (smoothing_partial_contDiff ((contDiff_apply ℝ ℝ a).comp hΦ) j) i).continuous.continuousAt
  change ContinuousAt (fun q => ∑ a : Fin 2,
    (seamCoordinateJacobian Φ q)⁻¹ k a*planarHessian (fun x => Φ x a) q i j) p
  simp only [Fin.sum_univ_two]
  exact (hentry 0 |>.mul (hH 0)).add (hentry 1 |>.mul (hH 1))

theorem seamCorrectedHessian_continuousAt {Φ : Coord → Coord} {F : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F) {p : Coord}
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    ContinuousAt (seamCorrectedHessian Φ F) p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hH := (smoothing_partial_contDiff (smoothing_partial_contDiff hF j) i).continuous.continuousAt (x := p)
  have hgrad (k : Fin 2) := (smoothing_partial_contDiff hF k).continuous.continuousAt (x := p)
  have hΓ (k : Fin 2) := seamChartConnection_continuousAt hΦ hJ k i j
  change ContinuousAt (fun q => planarHessian F q i j-
    ∑ k : Fin 2, seamChartConnection Φ k i j q*coordPartial k F q) p
  simp only [Fin.sum_univ_two]
  exact hH.sub (((hΓ 0).mul (hgrad 0)).add ((hΓ 1).mul (hgrad 1)))

end
end TightVer401
