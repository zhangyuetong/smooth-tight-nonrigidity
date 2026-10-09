import TightVer401.PlanarSupportCurvature
import TightVer401.RegularLocalInverse

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def planarGradient (G : Coord → ℝ) (p : Coord) : Coord := fun j => coordPartial j G p

theorem planarGradient_contDiffOn {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (planarGradient G) U :=
  contDiffOn_pi.mpr (fun j => partial_contDiffOn hG hU j)

theorem planarGradient_fderiv_apply {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (v : Coord) :
    fderiv ℝ (planarGradient G) p v = planarHessian G p *ᵥ v := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  have hpartial (j : Fin 2) : fderiv ℝ (coordPartial j G) p v =
      v 0 * coordPartial 0 (coordPartial j G) p +
        v 1 * coordPartial 1 (coordPartial j G) p := by
    conv_lhs => rw [hv]
    simp [coordPartial]
  unfold planarGradient
  rw [fderiv_pi (fun j => ((partial_contDiffOn hG hU j) p hp).contDiffAt
    (hU.mem_nhds hp) |>.differentiableAt (by simp))]
  ext j
  change fderiv ℝ (coordPartial j G) p v = _
  rw [hpartial]
  change v 0 * planarHessian G p 0 j + v 1 * planarHessian G p 1 j = _
  rw [planarHessian_symm hG hU hp 0 j, planarHessian_symm hG hU hp 1 j]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem planarGradient_differential_injective {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hdet : (planarHessian G p).det ≠ 0) :
    Function.Injective (fderiv ℝ (planarGradient G) p) := by
  intro v w hvw
  have hz : fderiv ℝ (planarGradient G) p (v - w) = 0 := by simp [map_sub, hvw]
  rw [planarGradient_fderiv_apply hG hU hp] at hz
  have heq : (planarHessian G p)⁻¹ *ᵥ (planarHessian G p *ᵥ (v - w)) = v - w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  rw [hz, Matrix.mulVec_zero] at heq
  exact sub_eq_zero.mp heq.symm

theorem planarGradient_exists_smooth_local_inverse {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (hdet : ∀ q ∈ U, (planarHessian G q).det ≠ 0) {p : Coord} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ U ∧ (e : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ e.symm e.target :=
  exists_smooth_local_inverse hU (planarGradient_contDiffOn hG hU)
    (fun q hq => planarGradient_differential_injective hG hU hq (hdet q hq)) hp

theorem planarGradient_exists_smooth_local_inverse_at {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hdet : (planarHessian G p).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ U ∧ (e : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  let V := U ∩ (fun q => (planarHessian G q).det) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV : IsOpen V :=
    (planarHessian_det_contDiffOn hG hU).continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton.isOpen_compl)
  have hpV : p ∈ V := ⟨hp, hdet⟩
  obtain ⟨e, he, heV, hef, hei⟩ := planarGradient_exists_smooth_local_inverse
    (hG.mono inter_subset_left) hV (fun q hq => hq.2) hpV
  exact ⟨e, he, heV.trans inter_subset_left, hef, hei⟩

end
end TightVer401
