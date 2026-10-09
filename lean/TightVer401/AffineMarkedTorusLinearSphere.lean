import TightVer401.AffineMarkedTorusLinearNormals
import TightVer401.SphereCharts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Actual smooth sphere transport by a normalized invertible linear map.
The forward map is normalize(A n), and its actual inverse is
normalize(A inverse n). Positivity of the scalar normalization factor and
the linear inverse laws prove both inverse identities. Norm/inverse/smul
calculus proves both directions infinity smooth in the actual sphere model.
The marker specialization is its actual inverse transpose; the inverse
operator is identified with the actual adjoint of B.
-/
open scoped Manifold ContDiff Topology Matrix RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance affineMarkedTorusLinearSphereDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem affineMarkedTorusLinearSphere_linear_ne_zero (A : Ambient ≃L[ℝ] Ambient)
    (n : RoundSphere) : A (n : Ambient) ≠ 0 := by
  intro hn
  exact roundSphere_ne_zero n (A.injective (hn.trans A.map_zero.symm))

/-- Actual normalization of an invertible linear map on the round sphere. -/
def affineMarkedTorusLinearSphereMap (A : Ambient ≃L[ℝ] Ambient) (n : RoundSphere) : RoundSphere :=
  ⟨NormedSpace.normalize (A (n : Ambient)), by
    simpa using NormedSpace.norm_normalize (affineMarkedTorusLinearSphere_linear_ne_zero A n)⟩

@[simp] theorem affineMarkedTorusLinearSphereMap_coe (A : Ambient ≃L[ℝ] Ambient)
    (n : RoundSphere) : (affineMarkedTorusLinearSphereMap A n : Ambient) =
      NormedSpace.normalize (A (n : Ambient)) := rfl

/-- Both normalization inverse laws follow from positive scaling and the
actual continuous linear inverse, without an inverse-map hypothesis. -/
theorem affineMarkedTorusLinearSphereMap_left_inverse (A : Ambient ≃L[ℝ] Ambient)
    (n : RoundSphere) :
    affineMarkedTorusLinearSphereMap A.symm (affineMarkedTorusLinearSphereMap A n) = n := by
  apply Subtype.ext
  change NormedSpace.normalize
    (A.symm (‖A (n : Ambient)‖⁻¹ • A (n : Ambient))) = (n : Ambient)
  rw [map_smul, A.symm_apply_apply,
    NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (affineMarkedTorusLinearSphere_linear_ne_zero A n))),
    NormedSpace.normalize_eq_self_of_norm_eq_one (roundSphere_norm n)]

theorem affineMarkedTorusLinearSphereMap_right_inverse (A : Ambient ≃L[ℝ] Ambient)
    (n : RoundSphere) :
    affineMarkedTorusLinearSphereMap A (affineMarkedTorusLinearSphereMap A.symm n) = n := by
  simpa only [ContinuousLinearEquiv.symm_symm] using
    affineMarkedTorusLinearSphereMap_left_inverse A.symm n

theorem affineMarkedTorusLinearSphereMap_contMDiff (A : Ambient ≃L[ℝ] Ambient) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (affineMarkedTorusLinearSphereMap A) := by
  have hx : ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞ (fun n : RoundSphere => A (n : Ambient)) :=
    A.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere
  have hn : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun n : RoundSphere => ‖A (n : Ambient)‖) := by
    intro n
    have hnorm : ContDiffAt ℝ ∞ (fun v : Ambient => ‖v‖) (A (n : Ambient)) :=
      contDiffAt_norm ℝ (affineMarkedTorusLinearSphere_linear_ne_zero A n)
    exact hnorm.contMDiffAt.comp n (hx n)
  have hs : ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞
      (fun n : RoundSphere => NormedSpace.normalize (A (n : Ambient))) :=
    (hn.inv₀ (fun n => norm_ne_zero_iff.mpr (affineMarkedTorusLinearSphere_linear_ne_zero A n))).smul hx
  exact hs.codRestrict_sphere (fun n => by
    simpa using NormedSpace.norm_normalize (affineMarkedTorusLinearSphere_linear_ne_zero A n))

/-- Actual global infinity diffeomorphism of the sphere. -/
def affineMarkedTorusLinearSphereDiffeomorph (A : Ambient ≃L[ℝ] Ambient) :
    Diffeomorph (𝓡 2) (𝓡 2) RoundSphere RoundSphere ∞ where
  toFun := affineMarkedTorusLinearSphereMap A
  invFun := affineMarkedTorusLinearSphereMap A.symm
  left_inv := affineMarkedTorusLinearSphereMap_left_inverse A
  right_inv := affineMarkedTorusLinearSphereMap_right_inverse A
  contMDiff_toFun := affineMarkedTorusLinearSphereMap_contMDiff A
  contMDiff_invFun := affineMarkedTorusLinearSphereMap_contMDiff A.symm

@[simp] theorem affineMarkedTorusLinearSphereDiffeomorph_coe (A : Ambient ≃L[ℝ] Ambient)
    (n : RoundSphere) :
    (affineMarkedTorusLinearSphereDiffeomorph A n : Ambient) =
      NormedSpace.normalize (A (n : Ambient)) := rfl

@[simp] theorem affineMarkedTorusLinearSphereDiffeomorph_symm_coe (A : Ambient ≃L[ℝ] Ambient)
    (n : RoundSphere) :
    ((affineMarkedTorusLinearSphereDiffeomorph A).symm n : Ambient) =
      NormedSpace.normalize (A.symm (n : Ambient)) := rfl

theorem affineMarkedTorusLinearSphere_finite_image (A : Ambient ≃L[ℝ] Ambient)
    {E : Set RoundSphere} (hE : E.Finite) :
    ((affineMarkedTorusLinearSphereDiffeomorph A) '' E).Finite := hE.image _

/-- The inverse contragredient operator is the actual marker adjoint. -/
theorem torusAffineMarkerContra_inverse_eq_adjoint :
    torusAffineMarkerContraLinearEquiv.symm.toContinuousLinearMap =
      torusAffineMarkerLinearEquiv.toContinuousLinearMap.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℝ (torusAffineMarkerContraInverse x) y = inner ℝ x (torusAffineMarker y)
  simp [torusAffineMarkerContraInverse, torusAffineMarker, torusAffineMarkerVec,
    PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Actual normalized inverse-transpose diffeomorphism used to transport
the Gauss partial homeomorphism and its exceptional set. -/
def torusAffineMarkerContraSphereDiffeomorph :
    Diffeomorph (𝓡 2) (𝓡 2) RoundSphere RoundSphere ∞ :=
  affineMarkedTorusLinearSphereDiffeomorph torusAffineMarkerContraLinearEquiv

@[simp] theorem torusAffineMarkerContraSphereDiffeomorph_normal (n : RoundSphere) :
    (torusAffineMarkerContraSphereDiffeomorph n : Ambient) =
      affineMarkedTorusLinearNormal (n : Ambient) := rfl

@[simp] theorem torusAffineMarkerContraSphereDiffeomorph_inverse (n : RoundSphere) :
    (torusAffineMarkerContraSphereDiffeomorph.symm n : Ambient) =
      NormedSpace.normalize (torusAffineMarkerLinearEquiv.toContinuousLinearMap.adjoint (n : Ambient)) := by
  change NormedSpace.normalize (torusAffineMarkerContraLinearEquiv.symm.toContinuousLinearMap (n : Ambient)) = _
  rw [torusAffineMarkerContra_inverse_eq_adjoint]

end
end TightVer401
