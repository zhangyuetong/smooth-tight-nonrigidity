import TightVer401.PlanarSupportNormal

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix RealInnerProductSpace

def planarHessian (G : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordPartial i (coordPartial j G) p

theorem planarSupportMap_inducedMetric {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    inducedMetric (planarSupportMap G) p = planarHessian G p *
      (1 + Matrix.of (fun i j => p i * p j)) * (planarHessian G p).transpose := by
  ext i j
  change inner ℝ (coordPartial i (planarSupportMap G) p)
    (coordPartial j (planarSupportMap G) p) = _
  rw [planarSupportMap_coordPartial hG hU hp i, planarSupportMap_coordPartial hG hU hp j]
  simp only [EuclideanSpace.inner_toLp_toLp]
  fin_cases i <;> fin_cases j <;>
    simp [planarHessian, dotProduct, Fin.sum_univ_succ, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply] <;> ring

end
end TightVer401
