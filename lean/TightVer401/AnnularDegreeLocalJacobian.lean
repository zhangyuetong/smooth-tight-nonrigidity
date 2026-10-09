import TightVer401.AnnularDegreeLocal
import TightVer401.SeamNormalCoordinates

/-!
The actual Jacobian is unchanged under the existing real-linear identification
of the complex plane with Coord. This is determinant conjugation and asserts
no metric compatibility. The pinned product-to-complex planarMapJacobian has
a different domain and is not redefined here.
-/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

/-- Chain rule for the actual complex-coordinate conjugate of a planar map. -/
theorem annular_complex_conjugate_hasFDerivAt {F : Coord → Coord} {z : ℂ}
    (hF : DifferentiableAt ℝ F (seamComplexCoord z)) :
    HasFDerivAt (seamComplexCoord.symm ∘ F ∘ seamComplexCoord)
      ((seamComplexCoord.symm : Coord →L[ℝ] ℂ).comp
        ((fderiv ℝ F (seamComplexCoord z)).comp
          (seamComplexCoord : ℂ →L[ℝ] Coord))) z :=
  seamComplexCoord.symm.hasFDerivAt.comp z
    (hF.hasFDerivAt.comp z seamComplexCoord.hasFDerivAt)

/-- Conjugation preserves the signed determinant of the actual derivative. -/
theorem annular_complex_conjugate_jacobian {F : Coord → Coord} {z : ℂ}
    (hF : DifferentiableAt ℝ F (seamComplexCoord z)) :
    annularJacobian F (seamComplexCoord z) =
      (fderiv ℝ (seamComplexCoord.symm ∘ F ∘ seamComplexCoord) z).toLinearMap.det := by
  rw [(annular_complex_conjugate_hasFDerivAt hF).fderiv]
  exact (LinearMap.det_conj (fderiv ℝ F (seamComplexCoord z)).toLinearMap
    seamComplexCoord.symm.toLinearEquiv).symm

end
end TightVer401
