import TightVer401.AffineMarkedTorusGaussCurvature
import TightVer401.AffineMarkedTorusLinearSphere

/-! Actual positive Gauss data for the literal affine marker.

Input is actual native embedding, sphere normal, and smooth Gauss partial
homeomorphism data for X. The output uses B X, the normalized inverse
transpose normal H N, the actual partial homeomorphism followed by H, and
the image under H of the actual finite exceptional set. The source equality
uses the proved positive curvature factor, rather than an isometry or a
curvature equality. Native differential orthogonality uses the actual B
chain rule and inverse-transpose pairing. The tightness application exposes
its classical mathematical background parameter explicitly.
-/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- The actual invertible marker preserves native smooth embedding. -/
theorem affineMarkedTorus_nativeSmoothEmbedding {X : NonrigidTorusSource → Ambient}
    (hX : NativeTorusSmoothEmbedding X) :
    NativeTorusSmoothEmbedding (affineMarkedTorusLinearBase X) := by
  refine ⟨affineMarkedTorusLinearBase_contMDiff hX.1,
    affineMarkedTorusLinearBase_immersion hX.1 hX.2.1, ?_⟩
  exact torusAffineMarkerHomeomorph.isEmbedding.comp hX.2.2

/-- Orthogonality of the actual normalized inverse-transpose sphere normal
to the marked native manifold differential. -/
theorem affineMarkedTorusGauss_normal_orthogonal {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) (p : NonrigidTorusSource) (v : ℝ × ℝ) :
    @inner ℝ Ambient _ (torusAffineMarkerContraSphereDiffeomorph (data.normal p) : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (affineMarkedTorusLinearBase X) p v) = 0 := by
  have hd := affineMarkedTorusLinearBase_mfderiv_apply
    ((data.embedding.1 p).mdifferentiableAt (by simp)) v
  apply (congrArg (fun z : Ambient =>
    inner ℝ (torusAffineMarkerContraSphereDiffeomorph (data.normal p) : Ambient) z) hd).trans
  change inner ℝ (‖torusAffineMarkerContra (data.normal p : Ambient)‖⁻¹ •
    torusAffineMarkerContra (data.normal p : Ambient))
    (torusAffineMarker (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v)) = 0
  rw [real_inner_smul_left]
  have hz : inner ℝ (torusAffineMarkerContra (data.normal p : Ambient))
      (torusAffineMarker (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v)) = 0 := by
    calc
      _ = inner ℝ (torusAffineMarker (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v))
          (torusAffineMarkerContra (data.normal p : Ambient)) := real_inner_comm _ _
      _ = @inner ℝ Ambient _ (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v : Ambient)
          (data.normal p : Ambient) := torusAffineMarker_dual_pairing _ _
      _ = @inner ℝ Ambient _ (data.normal p : Ambient)
          (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) := real_inner_comm _ _
      _ = 0 := data.normal_orthogonal p v
  rw [hz, mul_zero]

/-- The target of the actual postcomposed partial homeomorphism is precisely
the complement of the transported exceptional set. -/
theorem affineMarkedTorusGauss_target {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) :
    (data.gauss.transHomeomorph torusAffineMarkerContraSphereDiffeomorph.toHomeomorph).target =
      univ \ (torusAffineMarkerContraSphereDiffeomorph '' data.exceptional) := by
  ext n
  change torusAffineMarkerContraSphereDiffeomorph.symm n ∈ data.gauss.target ↔ _
  rw [data.gauss_target]
  simp only [mem_diff, mem_univ, true_and]
  constructor
  · intro hn he
    rcases he with ⟨m, hm, he⟩
    apply hn
    have hi : torusAffineMarkerContraSphereDiffeomorph.symm n = m := by
      rw [← he, Diffeomorph.symm_apply_apply]
    simpa only [hi] using hm
  · intro hn hm
    apply hn
    exact ⟨torusAffineMarkerContraSphereDiffeomorph.symm n, hm,
      torusAffineMarkerContraSphereDiffeomorph.apply_symm_apply n⟩

/-- Construct the actual marked native Gauss data from the actual unmarked
data, with no curvature, normal, inverse or tightness conclusion as input. -/
def affineMarkedTorusPositiveGaussData {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) :
    NativeTorusPositiveGaussData (affineMarkedTorusLinearBase X) where
  embedding := affineMarkedTorus_nativeSmoothEmbedding data.embedding
  normal := torusAffineMarkerContraSphereDiffeomorph ∘ data.normal
  normal_smooth := torusAffineMarkerContraSphereDiffeomorph.contMDiff_toFun.comp data.normal_smooth
  normal_orthogonal := affineMarkedTorusGauss_normal_orthogonal data
  exceptional := torusAffineMarkerContraSphereDiffeomorph '' data.exceptional
  exceptional_finite := data.exceptional_finite.image _
  gauss := data.gauss.transHomeomorph torusAffineMarkerContraSphereDiffeomorph.toHomeomorph
  gauss_source := by
    change data.gauss.source = nativeTorusPositiveRegion (affineMarkedTorusLinearBase X)
    rw [affineMarkedTorusGauss_positive_region data, data.gauss_source]
  gauss_target := affineMarkedTorusGauss_target data
  gauss_eq := by
    intro p hp
    change torusAffineMarkerContraSphereDiffeomorph (data.gauss p) =
      torusAffineMarkerContraSphereDiffeomorph (data.normal p)
    exact congrArg torusAffineMarkerContraSphereDiffeomorph (data.gauss_eq hp)
  gauss_smooth :=
    torusAffineMarkerContraSphereDiffeomorph.contMDiff_toFun.comp_contMDiffOn data.gauss_smooth
  gauss_inverse_smooth := by
    change ContMDiffOn (𝓡 2) nativeProductModel ∞
      (data.gauss.symm ∘ torusAffineMarkerContraSphereDiffeomorph.symm)
      (torusAffineMarkerContraSphereDiffeomorph.symm ⁻¹' data.gauss.target)
    exact data.gauss_inverse_smooth.comp
      torusAffineMarkerContraSphereDiffeomorph.contMDiff_invFun.contMDiffOn (fun _ hp => hp)

@[simp] theorem affineMarkedTorusPositiveGaussData_normal
    {X : NonrigidTorusSource → Ambient} (data : NativeTorusPositiveGaussData X)
    (p : NonrigidTorusSource) :
    (affineMarkedTorusPositiveGaussData data).normal p =
      torusAffineMarkerContraSphereDiffeomorph (data.normal p) := rfl

@[simp] theorem affineMarkedTorusPositiveGaussData_exceptional
    {X : NonrigidTorusSource → Ambient} (data : NativeTorusPositiveGaussData X) :
    (affineMarkedTorusPositiveGaussData data).exceptional =
      torusAffineMarkerContraSphereDiffeomorph '' data.exceptional := rfl

@[simp] theorem affineMarkedTorusPositiveGaussData_gauss
    {X : NonrigidTorusSource → Ambient} (data : NativeTorusPositiveGaussData X) :
    (affineMarkedTorusPositiveGaussData data).gauss =
      data.gauss.transHomeomorph torusAffineMarkerContraSphereDiffeomorph.toHomeomorph := rfl

/-- Explicit classical Gauss-criterion application for the actual marked
native embedding. The classical background remains a visible parameter. -/
theorem affineMarkedTorus_tight_of_classical (background : ClassicalExternalResults)
    {X : NonrigidTorusSource → Ambient} (data : NativeTorusPositiveGaussData X) :
    IsTightImage (affineMarkedTorusLinearBase X) :=
  nativeTorusPositiveGaussData_tight_of_classical background
    (affineMarkedTorusPositiveGaussData data)

end
end TightVer401
