import TightVer401.AnnularDegreeLocalInverse
import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth

/-! Reuse of the actual smooth-image inverse after compact annular exhaustion. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- The basis-free actual Jacobian of the gradient is the actual Hessian determinant. -/
theorem dualRadialCompletion_gradient_jacobian {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    annularJacobian (planarGradient G) p = (planarHessian G p).det := by
  have he : (fderiv ℝ (planarGradient G) p).toLinearMap = (planarHessian G p).toLin' := by
    apply LinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.coe_coe, Matrix.toLin'_apply] using
      planarGradient_fderiv_apply hG hU hp v
  unfold annularJacobian
  rw [he, LinearMap.det_toLin']

/-- Global injection/image is supplied by the proved compact-band exhaustion;
the smooth inverse is assembled by the existing actual inverse helper. -/
theorem exists_dualRadialCompletion_gradient_inverse {G : Coord → ℝ} {A RN : ℝ}
    (hG : ContDiffOn ℝ ∞ G {p | 0 < planarRadius p})
    (hneg : ∀ p, 0 < planarRadius p → (planarHessian G p).det < 0)
    (hBij : BijOn (planarGradient G) {p | 0 < planarRadius p}
      {y | A < planarRadius y ∧ planarRadius y < RN}) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      e.source = {p | 0 < planarRadius p} ∧
      e.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (e : Coord → Coord) = planarGradient G ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hU : IsOpen {p : Coord | 0 < planarRadius p} :=
    isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
  have hJ : ∀ p ∈ {p : Coord | 0 < planarRadius p},
      annularJacobian (planarGradient G) p ≠ 0 := by
    intro p hp
    rw [dualRadialCompletion_gradient_jacobian hG hU hp]
    exact (hneg p hp).ne
  have hUnique : ∀ y ∈ planarGradient G '' {p | 0 < planarRadius p},
      ∃! x, x ∈ {p | 0 < planarRadius p} ∧ planarGradient G x = y := by
    rintro y ⟨x, hx, hxy⟩
    refine ⟨x, ⟨hx, hxy⟩, ?_⟩
    intro z hz
    exact hBij.injOn hz.1 hx (hz.2.trans hxy.symm)
  obtain ⟨e, hs, ht, hf, hi⟩ := annular_exists_smooth_image_inverse hU
    (planarGradient_contDiffOn hG hU) hJ hUnique
  exact ⟨e, hs, ht.trans hBij.image_eq, hf, hi⟩

end
end TightVer401
