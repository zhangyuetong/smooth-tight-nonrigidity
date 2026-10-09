import TightVer401.AffineMarkedTorusLinearSphere
import TightVer401.AffineMarkedTorusLinearApplications
import TightVer401.ProtectedTorusPositiveGaussNormalCore

/-! The literal affine marker transports the actual native global cross
normal, with the retained height-first frame orientation unchanged.

The actual native manifold differential chain proves cross(B X) =
2 C(cross X). Since two and the reciprocal cross norm are positive,
normalization yields the actual normalized inverse-transpose sphere
diffeomorphism applied to the original actual native normal. The marked
immersion is derived from the original differential injection. No metric
compatibility, normal orientation, curvature, or support conclusion is a
premise.
-/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Actual native height-first cross covariance for the literal marker. -/
theorem affineMarkedTorusLinear_nativeCross {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X) (p : NonrigidTorusSource) :
    nativeTorusImmersionCross (affineMarkedTorusLinearBase X) p =
      (2 : ℝ) • torusAffineMarkerContra (nativeTorusImmersionCross X p) := by
  have hd := affineMarkedTorusLinearBase_mfderiv_apply ((hX p).mdifferentiableAt (by simp))
  exact (congrArg₂ ambientCross (hd (0, 1)) (hd (1, 0))).trans
    (affineMarkedTorusLinear_cross _ _)

/-- Actual equality of sphere-valued native normals, using the derived
marked immersion and the actual inverse-transpose sphere diffeomorphism. -/
theorem affineMarkedTorusLinear_nativeNormal {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p))
    (p : NonrigidTorusSource) :
    nativeTorusImmersionNormal (affineMarkedTorusLinearBase X)
        (affineMarkedTorusLinearBase_immersion hX himm) p =
      torusAffineMarkerContraSphereDiffeomorph (nativeTorusImmersionNormal X himm p) := by
  apply Subtype.ext
  change NormedSpace.normalize (nativeTorusImmersionCross (affineMarkedTorusLinearBase X) p) =
    NormedSpace.normalize (torusAffineMarkerContraLinearEquiv
      (NormedSpace.normalize (nativeTorusImmersionCross X p)))
  rw [affineMarkedTorusLinear_nativeCross hX p,
    NormedSpace.normalize_smul_of_pos (by norm_num : 0 < (2 : ℝ))]
  change NormedSpace.normalize (torusAffineMarkerContraLinearEquiv (nativeTorusImmersionCross X p)) =
    NormedSpace.normalize (torusAffineMarkerContraLinearEquiv
      (‖nativeTorusImmersionCross X p‖⁻¹ • nativeTorusImmersionCross X p))
  rw [map_smul, NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr (nativeTorusImmersionCross_ne_zero himm p)))]

end
end TightVer401
