import TightVer401.SeamCoordinateChain
import TightVer401.SeamFrameJet
import Mathlib.Topology.Instances.Matrix

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix Matrix.Norms.Elementwise

/-- The chart correction is constructed from its actual first and second derivatives. -/
def seamChartConnection (Φ : Coord → Coord) (k i j : Fin 2) (p : Coord) : ℝ :=
  ((seamCoordinateJacobian Φ p)⁻¹ *ᵥ fun a => planarHessian (fun q => Φ q a) p i j) k

def seamCorrectedHessian (Φ : Coord → Coord) (F : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => planarHessian F p i j-
    ∑ k : Fin 2, seamChartConnection Φ k i j p*coordPartial k F p

theorem seamChartConnection_cancel {Φ : Coord → Coord} {p : Coord}
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) (i j : Fin 2) :
    seamCoordinateJacobian Φ p *ᵥ (fun k => seamChartConnection Φ k i j p) =
      fun a => planarHessian (fun q => Φ q a) p i j := by
  change seamCoordinateJacobian Φ p *ᵥ
    ((seamCoordinateJacobian Φ p)⁻¹ *ᵥ (fun a => planarHessian (fun q => Φ q a) p i j)) = _
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ),Matrix.one_mulVec]

theorem seamChartConnection_gradient_comp {F : Coord → ℝ} {Φ : Coord → Coord}
    (hF : ContDiff ℝ ∞ F) (hΦ : ContDiff ℝ ∞ Φ) {p : Coord}
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) (i j : Fin 2) :
    (∑ k : Fin 2, seamChartConnection Φ k i j p*coordPartial k (fun q => F (Φ q)) p) =
      ∑ a : Fin 2, coordPartial a F (Φ p)*planarHessian (fun q => Φ q a) p i j := by
  have hc := seamChartConnection_cancel hJ i j
  have h₀ := congrFun hc 0
  have h₁ := congrFun hc 1
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,seamCoordinateJacobian] at h₀ h₁
  simp only [Fin.sum_univ_two,seam_coordPartial_comp hF hΦ]
  linear_combination coordPartial 0 F (Φ p)*h₀+coordPartial 1 F (Φ p)*h₁

/-- The constructed correction removes precisely the non-Euclidean chart terms. -/
theorem seamCorrectedHessian_comp {F : Coord → ℝ} {Φ : Coord → Coord}
    (hF : ContDiff ℝ ∞ F) (hΦ : ContDiff ℝ ∞ Φ) {p : Coord}
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    seamCorrectedHessian Φ (fun q => F (Φ q)) p =
      (seamCoordinateJacobian Φ p).transpose * planarHessian F (Φ p) * seamCoordinateJacobian Φ p := by
  ext i j
  unfold seamCorrectedHessian
  rw [seam_planarHessian_comp hF hΦ,seamChartConnection_gradient_comp hF hΦ hJ]
  ring

theorem seamCorrectedHessian_comp_det {F : Coord → ℝ} {Φ : Coord → Coord}
    (hF : ContDiff ℝ ∞ F) (hΦ : ContDiff ℝ ∞ Φ) {p : Coord}
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    (seamCorrectedHessian Φ (fun q => F (Φ q)) p).det =
      (seamCoordinateJacobian Φ p).det^2*(planarHessian F (Φ p)).det := by
  rw [seamCorrectedHessian_comp hF hΦ hJ]
  simp only [Matrix.det_mul,Matrix.det_transpose]
  ring

theorem seamCorrectedHessian_comp_saddle_iff {F : Coord → ℝ} {Φ : Coord → Coord}
    (hF : ContDiff ℝ ∞ F) (hΦ : ContDiff ℝ ∞ Φ) {p : Coord}
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    (seamCorrectedHessian Φ (fun q => F (Φ q)) p).det < 0 ↔
      (planarHessian F (Φ p)).det < 0 := by
  rw [seamCorrectedHessian_comp_det hF hΦ hJ]
  have hpos := sq_pos_of_ne_zero hJ
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_,hneg⟩ | ⟨hneg,_⟩
    · exact hneg
    · linarith
  · exact fun h => mul_neg_of_pos_of_neg hpos h

end
end TightVer401
