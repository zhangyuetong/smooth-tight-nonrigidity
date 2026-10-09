import TightVer401.PlanarSupport

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace

def planarWeight (p : Coord) : ℝ := Real.sqrt (1 + p 0 ^ 2 + p 1 ^ 2)

def planarUnitNormal (p : Coord) : Ambient :=
  WithLp.toLp 2 ![p 0 / planarWeight p, p 1 / planarWeight p, 1 / planarWeight p]

theorem planarWeight_pos (p : Coord) : 0 < planarWeight p := by
  unfold planarWeight
  apply Real.sqrt_pos.mpr
  positivity

theorem planarWeight_sq (p : Coord) : planarWeight p ^ 2 = 1 + p 0 ^ 2 + p 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem planarUnitNormal_unit (p : Coord) : inner ℝ (planarUnitNormal p) (planarUnitNormal p) = 1 := by
  have hw : planarWeight p ≠ 0 := ne_of_gt (planarWeight_pos p)
  simp only [planarUnitNormal, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_succ]
  field_simp [hw]
  nlinarith [planarWeight_sq p]

theorem planarSupportMap_isUnitNormal {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    IsUnitNormalAt (planarSupportMap G) (planarUnitNormal p) p := by
  refine ⟨planarUnitNormal_unit p, ?_⟩
  have hpartial (i : Fin 2) :
      inner ℝ (coordPartial i (planarSupportMap G) p) (planarUnitNormal p) = 0 := by
    rw [planarSupportMap_coordPartial hG hU hp i]
    simp only [planarUnitNormal, EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, Fin.sum_univ_succ]
    ring
  intro v
  rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    hpartial 0, hpartial 1]
  simp

end
end TightVer401
