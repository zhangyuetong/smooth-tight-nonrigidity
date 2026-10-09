import TightVer401.CompletedSaddleTorusBendingConnection
import TightVer401.TorusMarkedBandCurvatureConnection
import TightVer401.TorusMarkedBranchGermConnection
import TightVer401.NativeCompactEmbeddingStability
import TightVer401.NativeTorusGaussBranchConnection
import TightVer401.AffineMarkedTorusGaussApplications

/-! Conditional geometric stability of the literal marked pair B(F) ± a C(Z).
One completed cylinder, its actual G/e/beta data, and one FULL convex closure
are retained throughout. Native bending, branch embeddings, whole positive
regions/images and actual branch Gauss data are derived from existing producers.
The classical tightness parameter and physical-coordinate threshold hypotheses
remain explicit. No completion, markedness or final pair existence is granted. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold

variable {T w RN μ h : ℝ} [Fact (0 < T)]
variable {d : PeriodicRuledFrame T} {K : Set (AddCircle T × Ioo (0 : ℝ) w)}

/-- Fixed SAME-cylinder/full-meridian consumer. The physical-coordinate
hypotheses are precisely those of the existing fresh marked K threshold;
all native bending and both actual branch Gauss/tightness outputs are derived. -/
theorem completedSaddleTorus_marked_branch_stability
    (background : ClassicalExternalResults)
    (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)
    (Cdata : ProtectedTorusActualGraphCylinderData Q.cylinder)
    (D : ParabolicConvexClosureData RN μ h)
    (hw : 0 < w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hsK : tsupport Y ⊆ K)
    (hXcoord : ContDiff ℝ ∞ (markedRuledBandCoordinateBase d
      (completedSaddleTorusBandAffine Q) torusAffineMarkerLinearEquiv.toContinuousLinearMap))
    (hYcoord : IsInfinitesimalBendingOn (markedRuledBandCoordinateBase d
      (completedSaddleTorusBandAffine Q) torusAffineMarkerLinearEquiv.toContinuousLinearMap)
      (markedRuledBandCoordinateField Y (completedSaddleTorusBandAffine Q)
        torusAffineMarkerContraLinearEquiv.toContinuousLinearMap)
      (markedRuledBandCoordinateDomain w))
    (hicoord : ∀ q ∈ markedRuledBandCoordinateDomain w, Function.Injective
      (fderiv ℝ (markedRuledBandCoordinateBase d (completedSaddleTorusBandAffine Q)
        torusAffineMarkerLinearEquiv.toContinuousLinearMap) q))
    (hnegcoord : ∀ q ∈ markedRuledBandCoordinateDomain w, gaussianCurvature
      (inducedMetric (markedRuledBandCoordinateBase d (completedSaddleTorusBandAffine Q)
        torusAffineMarkerLinearEquiv.toContinuousLinearMap)) q < 0) :
    let F := protectedTorusMap Q.cylinder.saddle D.meridian h
    let Z := protectedTorusBendingField (completedSaddleTorusBandChart Q)
      (completedSaddleTorusBandAffine Q) Y
    let G := affineMarkedTorusLinearBase F
    let W := affineMarkedTorusLinearBending Z
    nativeProductIsBending F Z ∧
    ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      NativeTorusSmoothEmbedding (G + a • W) ∧
      NativeTorusSmoothEmbedding (G - a • W) ∧
      (∀ p ∈ (completedSaddleTorusBandChart Q) '' tsupport Y,
        nativeTorusChartCurvature G p < 0 ∧
        nativeTorusChartCurvature (G + a • W) p < 0 ∧
        nativeTorusChartCurvature (G - a • W) p < 0) ∧
      nativeTorusPositiveRegion (G + a • W) = nativeTorusPositiveRegion G ∧
      nativeTorusPositiveRegion (G - a • W) = nativeTorusPositiveRegion G ∧
      EqOn (G + a • W) G (nativeTorusPositiveRegion G) ∧
      EqOn (G - a • W) G (nativeTorusPositiveRegion G) ∧
      (G + a • W) '' nativeTorusPositiveRegion (G + a • W) =
        G '' nativeTorusPositiveRegion G ∧
      (G - a • W) '' nativeTorusPositiveRegion (G - a • W) =
        G '' nativeTorusPositiveRegion G ∧
      (G + a • W) '' nativeTorusPositiveRegion (G + a • W) =
        (G - a • W) '' nativeTorusPositiveRegion (G - a • W) ∧
      (∀ p ∈ nativeTorusPositiveRegion G, (G + a • W) =ᶠ[𝓝 p] G) ∧
      (∀ p ∈ nativeTorusPositiveRegion G, (G - a • W) =ᶠ[𝓝 p] G) ∧
      Nonempty (NativeTorusPositiveGaussData (G + a • W)) ∧
      Nonempty (NativeTorusPositiveGaussData (G - a • W)) ∧
      IsTightImage (G + a • W) ∧ IsTightImage (G - a • W) := by
  letI : CompactSpace NonrigidTorusSource := nonrigidTorusSource_compact
  let F := protectedTorusMap Q.cylinder.saddle D.meridian h
  let e := completedSaddleTorusBandChart Q
  let A := completedSaddleTorusBandAffine Q
  let Z := protectedTorusBendingField e A Y
  let G := affineMarkedTorusLinearBase F
  let W := affineMarkedTorusLinearBending Z
  let data := protectedTorusActualCylinderPositiveGaussData Q.cylinder D Cdata
  let base := affineMarkedTorusPositiveGaussData data
  have hF : NativeTorusSmoothEmbedding F := data.embedding
  have hG : NativeTorusSmoothEmbedding G := base.embedding
  have hsupport : tsupport Y ⊆ e.source :=
    hsK.trans (completedSaddleTorusBandChart_protected_source Q)
  have hplace : ∀ p ∈ e.source, F (e p) = A ((d.bandMap (b := w)) p) := by
    intro p hp
    rw [completedSaddleTorusBandAffine_apply]
    exact completedSaddleTorusBandChart_placement Q D.meridian h hp
  have hZ : nativeProductIsBending F Z := protectedTorus_isNativeBending
    d.bandMap_contMDiff hY hcompact hnonzero e hsupport
    (completedSaddleTorusBandChart_inverse_smooth Q) A F hplace
  have hW : nativeProductIsBending G W := affineMarkedTorusLinear_isBending hF.1 hZ
  have hcanonical : base.normal = nativeTorusImmersionNormal G base.embedding.2.1 := by
    funext p
    exact affineMarkedTorusGauss_actualCylinder_normal_eq_native Q.cylinder D Cdata p
  obtain ⟨δe, hδe, hembed⟩ := nativeCompactEmbedding_exists_amplitude_threshold
    hG.1 hW.1 hG.2.2 hG.2.1
  obtain ⟨δk, hδk, hcurv⟩ := protectedTorus_marked_bending_curvature_threshold
    d hw Y hcompact F e hsupport (completedSaddleTorusBandChart_forward_smooth Q)
    (completedSaddleTorusBandChart_inverse_smooth Q) A
    torusAffineMarkerLinearEquiv.toContinuousLinearMap
    torusAffineMarkerContraLinearEquiv.toContinuousLinearMap
    hplace hXcoord hYcoord hicoord hnegcoord hG.1 hG.2.1 hW
  refine ⟨hZ, min δe δk, lt_min hδe hδk, ?_⟩
  intro a ha
  have hae : |a| < δe := lt_of_lt_of_le ha (min_le_left _ _)
  have hak : |a| < δk := lt_of_lt_of_le ha (min_le_right _ _)
  have hscaled := nativeProduct_bending_const_smul hG.1 hW a
  have hip := nativeProduct_bending_branch_immersion hG.1 hW a hG.2.1
  have him := nativeProduct_opposite_branch_immersion hG.1 hscaled hip
  have hemp : Topology.IsEmbedding (G + a • W) := hembed a hae
  have hemm : Topology.IsEmbedding (G - a • W) := by
    have heq : (fun p => G p + (-a) • W p) = G - a • W := by
      funext p
      change G p + (-a) • W p = G p - a • W p
      rw [neg_smul, sub_eq_add_neg]
    rw [← heq]
    exact hembed (-a) (by simpa only [abs_neg] using hae)
  have hplus : NativeTorusSmoothEmbedding (G + a • W) :=
    ⟨hG.1.add hscaled.1, hip, hemp⟩
  have hminus : NativeTorusSmoothEmbedding (G - a • W) :=
    ⟨hG.1.sub hscaled.1, him, hemm⟩
  have hnegative : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature G p < 0 :=
    fun p hp => (hcurv a hak p hp).1
  obtain ⟨hrplus, hrminus, heqplus, heqminus, himgplus, himgminus, himgpair⟩ :=
    protectedTorus_marked_positive_regions e A hcompact hsupport F
      torusAffineMarkerLinearEquiv.toContinuousLinearMap
      torusAffineMarkerContraLinearEquiv.toContinuousLinearMap a hnegative
      (fun p hp => (hcurv a hak p hp).2.1)
      (fun p hp => (hcurv a hak p hp).2.2)
  have hgerms : ∀ p ∈ nativeTorusPositiveRegion G,
      (G + a • W) =ᶠ[𝓝 p] G ∧ (G - a • W) =ᶠ[𝓝 p] G := by
    intro p hp
    have hout : p ∉ e '' tsupport Y := fun hK => lt_asymm hp (hnegative p hK)
    exact protectedTorus_marked_branch_germs_off_support e A hcompact hsupport F
      torusAffineMarkerLinearEquiv.toContinuousLinearMap
      torusAffineMarkerContraLinearEquiv.toContinuousLinearMap a hout
  let plusData := nativeTorusPositiveGaussData_of_branch_germs base hcanonical
    (G + a • W) hplus hrplus (fun p hp => (hgerms p hp).1)
  let minusData := nativeTorusPositiveGaussData_of_branch_germs base hcanonical
    (G - a • W) hminus hrminus (fun p hp => (hgerms p hp).2)
  exact ⟨hplus, hminus, (fun p hp => hcurv a hak p hp),
    hrplus, hrminus, heqplus, heqminus,
    himgplus, himgminus, himgpair, (fun p hp => (hgerms p hp).1),
    (fun p hp => (hgerms p hp).2), ⟨plusData⟩, ⟨minusData⟩,
    nativeTorusPositiveGaussData_tight_of_classical background plusData,
    nativeTorusPositiveGaussData_tight_of_classical background minusData⟩

end
end TightVer401
