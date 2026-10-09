import TightVer401.SmoothingTubeTransfer
import TightVer401.SmoothingChartC1

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem seamNormalTubePotential_raw_germ {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} (H : Coord → ℝ)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    {p : Coord} (hp : |p 1| < r) :
    (fun q => seamNormalTubePotential γ hL r H hPeriod (seamNormalCoordinates γ q)) =ᶠ[𝓝 p] H := by
  have hU : IsOpen {q : Coord | |q 1| < r} := isOpen_lt (continuous_apply 1 |>.abs) continuous_const
  filter_upwards [hU.mem_nhds hp] with q hq
  have he := seamNormalTubePotential_coe hL H hPeriod hi (q 0) (q 1) hq.le
  have hqv : (![q 0,q 1] : Coord)=q := by ext i; fin_cases i <;> rfl
  simpa only [hqv] using he

theorem seam_planarGradient_comp_at {F : Coord → ℝ} {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {p : Coord} (hF : DifferentiableAt ℝ F (Φ p)) :
    planarGradient (fun q => F (Φ q)) p=(seamCoordinateJacobian Φ p).transpose *ᵥ planarGradient F (Φ p) := by
  ext i
  change coordPartial i (fun q => F (Φ q)) p=_
  rw [seam_coordPartial_comp_at hF (hΦ.differentiable (by simp) p)]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.transpose_apply,
    seamCoordinateJacobian,planarGradient,seam_coordPartial_component hΦ]
  ring

/-- The actual ambient gradient is obtained by the inverse of the actual
transpose Jacobian, with no derivative identity assumed. -/
theorem seamNormalTubePotential_gradient {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ} (H : Coord → ℝ)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    {p : Coord} (hp : |p 1| < r)
    (hJ : (seamCoordinateJacobian (seamNormalCoordinates γ) p).det ≠ 0)
    (hDiff : DifferentiableAt ℝ (seamNormalTubePotential γ hL r H hPeriod) (seamNormalCoordinates γ p)) :
    planarGradient (seamNormalTubePotential γ hL r H hPeriod) (seamNormalCoordinates γ p)=
      ((seamCoordinateJacobian (seamNormalCoordinates γ) p).transpose)⁻¹ *ᵥ planarGradient H p := by
  have hg := smoothing_planarGradient_germ (seamNormalTubePotential_raw_germ hL H hPeriod hi hp)
  rw [seam_planarGradient_comp_at (seamNormalCoordinates_contDiff hγ) hDiff] at hg
  have ht : (seamCoordinateJacobian (seamNormalCoordinates γ) p).transpose.det ≠ 0 := by
    simpa only [Matrix.det_transpose] using hJ
  have he := congrArg (fun v : Coord =>
    ((seamCoordinateJacobian (seamNormalCoordinates γ) p).transpose)⁻¹ *ᵥ v) hg
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht),Matrix.one_mulVec] at he
  exact he

end
end TightVer401
