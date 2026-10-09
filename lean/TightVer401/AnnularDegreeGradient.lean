import TightVer401.AnnularDegree
import TightVer401.PlanarGradientInverse

/-! The actual engine gradient specializes the annular inverse theorem.
Its Jacobian is the determinant of the actual Hessian, derived from the
actual Frechet derivative. Only the interior Hessian sign is required;
boundary differential rank may degenerate. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- The actual planar gradient derivative has the actual Hessian determinant. -/
theorem annularGradientJacobian_eq_hessian_det
    {G : Coord → ℝ} {O : Set Coord}
    (hG : ContDiffOn ℝ ∞ G O) (hO : IsOpen O)
    {p : Coord} (hp : p ∈ O) :
    annularJacobian (planarGradient G) p = (planarHessian G p).det := by
  have hD : (fderiv ℝ (planarGradient G) p).toLinearMap =
      Matrix.toLin' (planarHessian G p) := by
    apply LinearMap.ext
    intro v
    change fderiv ℝ (planarGradient G) p v = Matrix.toLin' (planarHessian G p) v
    rw [Matrix.toLin'_apply]
    exact planarGradient_fderiv_apply hG hO hp v
  unfold annularJacobian
  rw [hD, LinearMap.det_toLin']

/-- The ordinary annular inverse for the actual gradient of an actual
smooth potential, using only its interior Hessian determinant sign. -/
theorem annular_degree_planarGradient_global_diffeomorphism : AnnularDegreeGradientClaim := by
  intro Ho Hi To Ti γo γi hγo hγi hnS hnT G O hO hG hKO s hs hH
    swap Bo Bi hBo hBi w hw hWo hWi
  refine annular_degree_global_diffeomorphism Ho Hi To Ti γo γi hγo hγi
    hnS hnT (planarGradient G) O hO (planarGradient_contDiffOn hG hO)
    hKO s hs ?_ swap Bo Bi hBo hBi w hw hWo hWi
  intro x hx
  have hxK : x ∈ annularCoordJordanClosure Ho Hi := by
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, annularJordanInterior_subset_closure Ho Hi hz, rfl⟩
  rw [annularGradientJacobian_eq_hessian_det hG hO (hKO hxK)]
  exact hH x hx

end
end TightVer401
