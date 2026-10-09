import TightVer401.ClassicalExternal

/-! Same-object application data for the external Gauss criterion.
Every field is ordinary actual geometry to be constructed by the torus producer.
No inhabitant, tightness premise, or construction existence is assumed. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

structure NativeTorusPositiveGaussData (X : NonrigidTorusSource → Ambient) where
  embedding : NativeTorusSmoothEmbedding X
  normal : NonrigidTorusSource → RoundSphere
  normal_smooth : ContMDiff nativeProductModel (𝓡 2) ∞ normal
  normal_orthogonal : ∀ p (v : ℝ × ℝ), @inner ℝ Ambient _ (normal p : Ambient)
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) = 0
  exceptional : Set RoundSphere
  exceptional_finite : exceptional.Finite
  gauss : OpenPartialHomeomorph NonrigidTorusSource RoundSphere
  gauss_source : gauss.source = nativeTorusPositiveRegion X
  gauss_target : gauss.target = univ \ exceptional
  gauss_eq : EqOn gauss normal gauss.source
  gauss_smooth : ContMDiffOn nativeProductModel (𝓡 2) ∞ gauss gauss.source
  gauss_inverse_smooth : ContMDiffOn (𝓡 2) nativeProductModel ∞ gauss.symm gauss.target

/-- The external parameter is visible in this checked application type. -/
theorem nativeTorusPositiveGaussData_tight_of_classical
    (background : ClassicalExternalResults) {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) : IsTightImage X :=
  classicalPositiveGauss_tightness background X data.embedding data.normal
    data.normal_smooth data.normal_orthogonal data.exceptional data.exceptional_finite
    data.gauss data.gauss_source data.gauss_target data.gauss_eq
    data.gauss_smooth data.gauss_inverse_smooth

end
end TightVer401
