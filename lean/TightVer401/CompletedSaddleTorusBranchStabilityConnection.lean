import TightVer401.CompletedSaddleTorusBendingConnection
import TightVer401.TorusBandCurvatureConnection
import TightVer401.NativeCompactEmbeddingStability

/-! One selected actual completed saddle torus and one literal protected
bending field admit small opposite smooth embedded branches. Both entire
positive-curvature source regions and their actual images are unchanged.
The convex meridian is selected once; no tightness or marking is assumed. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold

variable {T w RN μ h : ℝ} [Fact (0 < T)]
variable {d : PeriodicRuledFrame T} {K : Set (AddCircle T × Ioo (0 : ℝ) w)}
variable (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)

/-- A single fixed actual assembly retains the same protected chart and field
through embedding and curvature stability. The radius is the minimum of the
two derived thresholds, and both amplitude signs are included. -/
theorem completedSaddleTorusBending_branch_stability
    (hw : 0 < w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hsK : tsupport Y ⊆ K)
    (D : ProtectedTorusAssemblyInput RN μ h)
    (hD : D.toProtectedSaddleCylinderInput = Q.cylinder)
    (hF : NativeTorusSmoothEmbedding (protectedTorusMap D.saddle D.meridian h)) :
    let F := protectedTorusMap D.saddle D.meridian h
    let e := completedSaddleTorusBandChart Q
    let Z := protectedTorusBendingField e (completedSaddleTorusBandAffine Q) Y
    ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      NativeTorusSmoothEmbedding (F + a • Z) ∧
      NativeTorusSmoothEmbedding (F - a • Z) ∧
      nativeTorusPositiveRegion (F + a • Z) = nativeTorusPositiveRegion F ∧
      nativeTorusPositiveRegion (F - a • Z) = nativeTorusPositiveRegion F ∧
      EqOn (F + a • Z) F (nativeTorusPositiveRegion F) ∧
      EqOn (F - a • Z) F (nativeTorusPositiveRegion F) ∧
      (F + a • Z) '' nativeTorusPositiveRegion (F + a • Z) =
        F '' nativeTorusPositiveRegion F ∧
      (F - a • Z) '' nativeTorusPositiveRegion (F - a • Z) =
        F '' nativeTorusPositiveRegion F ∧
      (F + a • Z) '' nativeTorusPositiveRegion (F + a • Z) =
        (F - a • Z) '' nativeTorusPositiveRegion (F - a • Z) := by
  letI : CompactSpace NonrigidTorusSource := nonrigidTorusSource_compact
  let F := protectedTorusMap D.saddle D.meridian h
  let e := completedSaddleTorusBandChart Q
  let A := completedSaddleTorusBandAffine Q
  let Z := protectedTorusBendingField e A Y
  have hsupport : tsupport Y ⊆ e.source :=
    hsK.trans (completedSaddleTorusBandChart_protected_source Q)
  have hplace := completedSaddleTorusBending_placement Q D hD
  have hi := completedSaddleTorusBandChart_inverse_smooth Q
  have he := completedSaddleTorusBandChart_forward_smooth Q
  have hZ : nativeProductIsBending F Z :=
    protectedTorus_isNativeBending d.bandMap_contMDiff hY hcompact hnonzero
      e hsupport hi A F hplace
  obtain ⟨δe, hδe, hembed⟩ := nativeCompactEmbedding_exists_amplitude_threshold
    hF.1 hZ.1 hF.2.2 hF.2.1
  obtain ⟨δk, hδk, hcurv⟩ := protectedTorus_ruled_bending_curvature_threshold
    d hw hY hcompact hnonzero F hF.1 hF.2.1 e hsupport he hi A hplace
  refine ⟨min δe δk, lt_min hδe hδk, ?_⟩
  intro a ha
  have hae : |a| < δe := lt_of_lt_of_le ha (min_le_left _ _)
  have hak : |a| < δk := lt_of_lt_of_le ha (min_le_right _ _)
  have hscaled := nativeProduct_bending_const_smul hF.1 hZ a
  have hplus : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (F + a • Z) :=
    hF.1.add hscaled.1
  have hminus : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (F - a • Z) :=
    hF.1.sub hscaled.1
  have hip := nativeProduct_bending_branch_immersion hF.1 hZ a hF.2.1
  have him := nativeProduct_opposite_branch_immersion hF.1 hscaled hip
  have hemp : Topology.IsEmbedding (F + a • Z) := hembed a hae
  have hemm : Topology.IsEmbedding (F - a • Z) := by
    have ht : Topology.IsEmbedding (F + (-a) • Z) :=
      hembed (-a) (by simpa only [abs_neg] using hae)
    have heq : F + (-a) • Z = F - a • Z := by
      simp only [neg_smul, sub_eq_add_neg]
    rw [heq] at ht
    exact ht
  have hregions := protectedTorus_bending_positive_regions e A hcompact hsupport F a
    (fun q hq => (hcurv a hak q hq).1)
    (fun q hq => (hcurv a hak q hq).2.1)
    (fun q hq => (hcurv a hak q hq).2.2)
  exact ⟨⟨hplus, hip, hemp⟩, ⟨hminus, him, hemm⟩, hregions⟩

/-- Select the completed saddle torus once and retain that same assembly,
chart, field, support and positive stability radius for every small amplitude.
No existence of the incoming completed saddle, tightness, marking, or image
noncongruence is claimed by this application. -/
theorem exists_completedSaddleTorus_embedded_stable_branches
    (hw : 0 < w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hsK : tsupport Y ⊆ K) :
    ∃ D : ProtectedTorusAssemblyInput RN μ h,
      D.toProtectedSaddleCylinderInput = Q.cylinder ∧
      NativeTorusSmoothEmbedding (protectedTorusMap D.saddle D.meridian h) ∧
      let F := protectedTorusMap D.saddle D.meridian h
      let e := completedSaddleTorusBandChart Q
      let Z := protectedTorusBendingField e (completedSaddleTorusBandAffine Q) Y
      (ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Z ∧
        (∀ p (v z : ℝ × ℝ), nativeProductLinearMetricForm F Z p v z = 0) ∧
        HasCompactSupport Z ∧ (∃ p, Z p ≠ 0) ∧ tsupport Z ⊆ e '' tsupport Y) ∧
      ∃ δ > 0, ∀ a : ℝ, |a| < δ →
        NativeTorusSmoothEmbedding (F + a • Z) ∧
        NativeTorusSmoothEmbedding (F - a • Z) ∧
        nativeTorusPositiveRegion (F + a • Z) = nativeTorusPositiveRegion F ∧
        nativeTorusPositiveRegion (F - a • Z) = nativeTorusPositiveRegion F ∧
        EqOn (F + a • Z) F (nativeTorusPositiveRegion F) ∧
        EqOn (F - a • Z) F (nativeTorusPositiveRegion F) ∧
        (F + a • Z) '' nativeTorusPositiveRegion (F + a • Z) =
          F '' nativeTorusPositiveRegion F ∧
        (F - a • Z) '' nativeTorusPositiveRegion (F - a • Z) =
          F '' nativeTorusPositiveRegion F ∧
        (F + a • Z) '' nativeTorusPositiveRegion (F + a • Z) =
          (F - a • Z) '' nativeTorusPositiveRegion (F - a • Z) := by
  obtain ⟨D, hD, hF, hplace, hZ⟩ :=
    exists_completedSaddleTorus_compact_nonzero_bending Q d.bandMap_contMDiff
      hY hcompact hnonzero hsK
  exact ⟨D, hD, hF, hZ,
    completedSaddleTorusBending_branch_stability Q hw hY hcompact hnonzero hsK D hD hF⟩

end
end TightVer401