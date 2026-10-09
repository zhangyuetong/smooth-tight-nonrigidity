import TightVer401.ClassicalEmbeddedReparamProof
import TightVer401.NativeProductPlaneIntrinsicDistanceCurves

/-! Actual reparameterization differential preserves the common induced metric.
All tangent norms are those of the induced Riemannian bundles. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4

/-- Smoothness of a native self map in the transported Plane atlas. -/
theorem classicalCoincident_plane_contMDiff
    {e : NonrigidTorusSource → NonrigidTorusSource}
    (he : ContMDiff nativeProductModel nativeProductModel ∞ e) :
    letI := nativeProductPlaneChartedSpace NonrigidTorusSource
    ContMDiff planeModel planeModel ∞ e := by
  letI := nativeProductPlaneChartedSpace NonrigidTorusSource
  exact (nativeProductPlane_identity_contMDiff NonrigidTorusSource).comp
    (he.comp (nativeProductPlane_inverse_contMDiff NonrigidTorusSource))

/-- The actual native differential chain rule for Y ∘ e = X. -/
theorem classicalCoincident_native_mfderiv
    {X Y : NonrigidTorusSource → Ambient}
    {e : NonrigidTorusSource → NonrigidTorusSource}
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y)
    (he : ContMDiff nativeProductModel nativeProductModel ∞ e)
    (heq : ∀ p, Y (e p) = X p) (p : NonrigidTorusSource) :
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) Y (e p)).comp
      (mfderiv nativeProductModel nativeProductModel e p) =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p := by
  have hcomp : Y ∘ e = X := funext heq
  have h := mfderiv_comp p ((hY (e p)).mdifferentiableAt (by simp))
    ((he p).mdifferentiableAt (by simp))
  rw [hcomp] at h
  exact h.symm

/-- The common actual induced metric is preserved by the native differential. -/
theorem classicalCoincident_native_inducedForm
    {X Y : NonrigidTorusSource → Ambient}
    {e : NonrigidTorusSource → NonrigidTorusSource}
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y)
    (he : ContMDiff nativeProductModel nativeProductModel ∞ e)
    (heq : ∀ p, Y (e p) = X p)
    (hmetric : ∀ p (v w : ℝ × ℝ),
      nativeProductInducedForm X p v w = nativeProductInducedForm Y p v w)
    (p : NonrigidTorusSource) (v w : ℝ × ℝ) :
    nativeProductInducedForm Y (e p)
      (mfderiv nativeProductModel nativeProductModel e p v)
      (mfderiv nativeProductModel nativeProductModel e p w) =
      nativeProductInducedForm Y p v w := by
  have hv := congrArg (fun L => L v) (classicalCoincident_native_mfderiv hY he heq p)
  have hw := congrArg (fun L => L w) (classicalCoincident_native_mfderiv hY he heq p)
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  exact (congrArg₂ (fun a b : Ambient => @inner ℝ Ambient _ a b) hv hw).trans
    (hmetric p v w)

/-- Genuine induced Riemannian tangent ENorm is preserved, not the product norm. -/
theorem classicalCoincident_native_enorm
    {X Y : NonrigidTorusSource → Ambient}
    {e : NonrigidTorusSource → NonrigidTorusSource}
    (hY : NativeTorusSmoothEmbedding Y)
    (he : ContMDiff nativeProductModel nativeProductModel ∞ e)
    (heq : ∀ p, Y (e p) = X p)
    (hmetric : ∀ p (v w : ℝ × ℝ),
      nativeProductInducedForm X p v w = nativeProductInducedForm Y p v w)
    (p : NonrigidTorusSource) (v : TangentSpace nativeProductModel p) :
    @enorm (TangentSpace nativeProductModel (e p))
      (nativeProductImmersionENorm Y hY.1 hY.2.1 (e p))
      (mfderiv nativeProductModel nativeProductModel e p v) =
    @enorm (TangentSpace nativeProductModel p)
      (nativeProductImmersionENorm Y hY.1 hY.2.1 p) v := by
  letI := nativeProductImmersionRiemannianBundle Y hY.1 hY.2.1
  change ‖mfderiv nativeProductModel nativeProductModel e p v‖ₑ = ‖v‖ₑ
  apply enorm_eq_iff_norm_eq.mpr
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  congr 1
  exact classicalCoincident_native_inducedForm hY.1 he heq hmetric p v v

/-- Injectivity of the SAME Y turns open map agreement into fixed points of e. -/
theorem classicalCoincident_reparam_fixedOn
    {X Y : NonrigidTorusSource → Ambient}
    {e : NonrigidTorusSource → NonrigidTorusSource}
    (hY : NativeTorusSmoothEmbedding Y)
    (heq : ∀ p, Y (e p) = X p)
    {U : Set NonrigidTorusSource} (hagree : EqOn X Y U) : EqOn e id U := by
  intro p hp
  apply hY.2.2.injective
  exact (heq p).trans (hagree hp)

end
end TightVer401

