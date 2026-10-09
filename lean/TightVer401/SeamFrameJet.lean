import TightVer401.SeamHessian

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix

def seamFrame (u v : Coord) : Matrix (Fin 2) (Fin 2) ℝ := !![u 0, v 0; u 1, v 1]

def seamFramedHessian (G : Coord → ℝ) (p u v : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  (seamFrame u v).transpose * planarHessian G p * seamFrame u v

theorem seamFramedHessian_det (G : Coord → ℝ) (p u v : Coord) :
    (seamFramedHessian G p u v).det = (seamFrame u v).det^2 * (planarHessian G p).det := by
  simp only [seamFramedHessian, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem seamFramedHessian_saddle {G : Coord → ℝ} {p u v : Coord}
    (hframe : (seamFrame u v).det ≠ 0) (hG : (planarHessian G p).det < 0) :
    (seamFramedHessian G p u v).det < 0 := by
  rw [seamFramedHessian_det]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hframe) hG

theorem seamFramedHessian_first_column {G H : Coord → ℝ} {p u v : Coord}
    (haction : planarHessian G p *ᵥ u = planarHessian H p *ᵥ u) (i : Fin 2) :
    seamFramedHessian G p u v i 0 = seamFramedHessian H p u v i 0 := by
  have h0 := congrFun haction 0
  have h1 := congrFun haction 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  fin_cases i <;>
    simp [seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  · linear_combination u 0 * h0 + u 1 * h1
  · linear_combination v 0 * h0 + v 1 * h1

theorem seamFramedHessian_symm {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (u v : Coord)
    (i j : Fin 2) : seamFramedHessian G p u v i j = seamFramedHessian G p u v j i := by
  have h01 := planarHessian_symm hG hU hp 0 1
  fin_cases i <;> fin_cases j <;>
    simp [seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, h01] <;>
    ring

theorem seamFramedHessian_eq_secondJet {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (u v : Coord) :
    seamFramedHessian G p u v = seamSecondJet (seamFramedHessian G p u v 0 0)
      (seamFramedHessian G p u v 1 0) (seamFramedHessian G p u v 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change seamFramedHessian G p u v 0 1 = seamFramedHessian G p u v 1 0
    exact seamFramedHessian_symm hG hU hp u v 0 1
  · rfl
  · rfl

theorem seamFramedHessian_common_secondJet {G H : Coord → ℝ} {U : Set Coord}
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U)
    {p u v : Coord} (hp : p ∈ U)
    (haction : planarHessian G p *ᵥ u = planarHessian H p *ᵥ u) :
    seamFramedHessian H p u v = seamSecondJet (seamFramedHessian G p u v 0 0)
      (seamFramedHessian G p u v 1 0) (seamFramedHessian H p u v 1 1) := by
  have he := seamFramedHessian_eq_secondJet hH hU hp u v
  rw [← seamFramedHessian_first_column haction 0, ← seamFramedHessian_first_column haction 1] at he
  exact he

end
end TightVer401
