import TightVer401.SeamChartContinuity
import TightVer401.RegularLocalInverse

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix

theorem seamCoordinateJacobian_fderiv_apply {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) (p v : Coord) :
    fderiv ℝ Φ p v=seamCoordinateJacobian Φ p *ᵥ v := by
  have he (a : Fin 2) : fderiv ℝ (fun q => Φ q a) p v=(fderiv ℝ Φ p v) a := by
    have hd := (hasFDerivAt_apply (𝕜 := ℝ) a (Φ p)).comp p
      (hΦ.differentiable (by simp) p).hasFDerivAt
    have hd' := hd.congr_of_eventuallyEq (f₁ := fun q => Φ q a)
      (Filter.Eventually.of_forall (fun _ => rfl))
    rw [hd'.fderiv]
    rfl
  ext a
  rw [← he,seam_fderiv_coordinate_apply]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,seamCoordinateJacobian]

theorem seamCoordinateJacobian_differential_injective {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {p : Coord} (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    Function.Injective (fderiv ℝ Φ p) := by
  intro v w hvw
  have hz : fderiv ℝ Φ p (v-w)=0 := by simp [map_sub,hvw]
  rw [seamCoordinateJacobian_fderiv_apply hΦ] at hz
  have he : (seamCoordinateJacobian Φ p)⁻¹ *ᵥ (seamCoordinateJacobian Φ p *ᵥ (v-w))=v-w := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJ),Matrix.one_mulVec]
  rw [hz,Matrix.mulVec_zero] at he
  exact sub_eq_zero.mp he.symm

/-- Every actual regular point admits an actual smooth inverse chart whose
inverse is smooth on its entire target. -/
theorem seamCoordinateJacobian_exists_smooth_chart {Φ : Coord → Coord}
    (hΦ : ContDiff ℝ ∞ Φ) {U : Set Coord} (hU : IsOpen U)
    (hJ : ∀ q ∈ U, (seamCoordinateJacobian Φ q).det ≠ 0) {p : Coord} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ U ∧ (e : Coord → Coord)=Φ ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  exact exists_smooth_local_inverse hU hΦ.contDiffOn
    (fun q hq => seamCoordinateJacobian_differential_injective hΦ (hJ q hq)) hp

end
end TightVer401
