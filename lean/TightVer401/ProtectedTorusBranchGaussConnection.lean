import TightVer401.ProtectedTorusPositiveGaussData
import TightVer401.TorusMetricBranchingPositive

/-! Actual Gauss data for a branch of the SAME constructed saddle/meridian map.
The global branch normal is the existing actual normalized native derivative
cross. Its agreement on the unchanged positive phase follows from map germs,
while the actual baseline producer supplies the same Gauss map and inverse. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- The canonical actual native unit normal depends only on the actual map germ.
The immersion proofs certify sphere membership and do not affect its value. -/
theorem nativeTorusImmersionNormal_eq_of_eventuallyEq
    {F G : NonrigidTorusSource → Ambient}
    (hF : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q))
    (hG : ∀ q, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) G q))
    {p : NonrigidTorusSource} (h : F =ᶠ[𝓝 p] G) :
    nativeTorusImmersionNormal F hF p = nativeTorusImmersionNormal G hG p := by
  have hd : mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient) G p := h.mfderiv_eq
  apply Subtype.ext
  change NormedSpace.normalize (nativeTorusImmersionCross F p) =
    NormedSpace.normalize (nativeTorusImmersionCross G p)
  unfold nativeTorusImmersionCross
  rw [hd]
  rfl

/-- Construct actual branch Gauss data from the actual completed-cylinder
baseline producer; no baseline Gauss-data package or unit normal is assumed.
The whole positive source and baseline germs are actual branch-stability outputs. -/
def protectedTorusActualCylinderBranchPositiveGaussData {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S) (G : NonrigidTorusSource → Ambient)
    (hG : NativeTorusSmoothEmbedding G)
    (hregion : nativeTorusPositiveRegion G =
      nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h))
    (hgerm : ∀ p ∈ nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h),
      G =ᶠ[𝓝 p] protectedTorusMap S.saddle D.meridian h) :
    NativeTorusPositiveGaussData G := by
  let base := protectedTorusActualCylinderPositiveGaussData S D C
  refine {
    embedding := hG
    normal := nativeTorusImmersionNormal G hG.2.1
    normal_smooth := nativeTorusImmersionNormal_contMDiff hG.1 hG.2.1
    normal_orthogonal := nativeTorusImmersionNormal_orthogonal hG.2.1
    exceptional := base.exceptional
    exceptional_finite := base.exceptional_finite
    gauss := base.gauss
    gauss_source := base.gauss_source.trans hregion.symm
    gauss_target := base.gauss_target
    gauss_eq := ?_
    gauss_smooth := base.gauss_smooth
    gauss_inverse_smooth := base.gauss_inverse_smooth }
  intro p hp
  have hpF : p ∈ nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h) := by
    rwa [base.gauss_source] at hp
  calc
    base.gauss p = base.normal p := base.gauss_eq hp
    _ = nativeTorusImmersionNormal G hG.2.1 p := by
      change nativeTorusImmersionNormal (protectedTorusMap S.saddle D.meridian h)
        base.embedding.2.1 p = nativeTorusImmersionNormal G hG.2.1 p
      exact (nativeTorusImmersionNormal_eq_of_eventuallyEq hG.2.1 base.embedding.2.1
        (hgerm p hpF)).symm

/-- The external classical criterion is kept explicit for this SAME actual branch. -/
theorem protectedTorusActualCylinderBranch_tight_of_classical
    (background : ClassicalExternalResults) {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S) (G : NonrigidTorusSource → Ambient)
    (hG : NativeTorusSmoothEmbedding G)
    (hregion : nativeTorusPositiveRegion G =
      nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h))
    (hgerm : ∀ p ∈ nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h),
      G =ᶠ[𝓝 p] protectedTorusMap S.saddle D.meridian h) : IsTightImage G :=
  nativeTorusPositiveGaussData_tight_of_classical background
    (protectedTorusActualCylinderBranchPositiveGaussData S D C G hG hregion hgerm)

/-- Actual negative support excludes the whole baseline positive phase from
that support, so both literal supported branches have the baseline map germ there. -/
theorem protectedTorus_bending_positive_phase_germs {T w : ℝ} [Fact (0 < T)]
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (a : ℝ)
    (hFneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature F p < 0) :
    (∀ p ∈ nativeTorusPositiveRegion F,
      F + a • protectedTorusBendingField e A Y =ᶠ[𝓝 p] F) ∧
    (∀ p ∈ nativeTorusPositiveRegion F,
      F - a • protectedTorusBendingField e A Y =ᶠ[𝓝 p] F) := by
  have hout : ∀ p ∈ nativeTorusPositiveRegion F, p ∉ e '' tsupport Y := by
    intro p hp hsupport
    exact lt_asymm hp (hFneg p hsupport)
  exact ⟨fun p hp => (protectedTorus_bending_branch_germs_off_support e A hcompact hsupport
      F a (hout p hp)).1,
    fun p hp => (protectedTorus_bending_branch_germs_off_support e A hcompact hsupport
      F a (hout p hp)).2⟩

/-- Fixed-D branch stability now supplies TWO actual tight branches, with the
same full meridian and ordinary completed-cylinder data. No branch Gauss datum
or tightness conclusion is supplied as a premise. -/
theorem protectedTorusActualCylinder_supported_branches_tight
    (background : ClassicalExternalResults) {RN μ h T w : ℝ} [Fact (0 < T)]
    (S : ProtectedSaddleCylinderInput RN μ h) (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source) (a : ℝ)
    (hFneg : ∀ p ∈ e '' tsupport Y,
      nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p < 0)
    (hplus : NativeTorusSmoothEmbedding
      (protectedTorusMap S.saddle D.meridian h + a • protectedTorusBendingField e A Y))
    (hminus : NativeTorusSmoothEmbedding
      (protectedTorusMap S.saddle D.meridian h - a • protectedTorusBendingField e A Y))
    (hplusRegion : nativeTorusPositiveRegion
      (protectedTorusMap S.saddle D.meridian h + a • protectedTorusBendingField e A Y) =
        nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h))
    (hminusRegion : nativeTorusPositiveRegion
      (protectedTorusMap S.saddle D.meridian h - a • protectedTorusBendingField e A Y) =
        nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h)) :
    IsTightImage (protectedTorusMap S.saddle D.meridian h + a • protectedTorusBendingField e A Y) ∧
      IsTightImage (protectedTorusMap S.saddle D.meridian h - a • protectedTorusBendingField e A Y) := by
  obtain ⟨hp, hm⟩ := protectedTorus_bending_positive_phase_germs e A hcompact hsupport
    (protectedTorusMap S.saddle D.meridian h) a hFneg
  exact ⟨protectedTorusActualCylinderBranch_tight_of_classical background S D C _ hplus
      hplusRegion hp,
    protectedTorusActualCylinderBranch_tight_of_classical background S D C _ hminus
      hminusRegion hm⟩

end
end TightVer401
