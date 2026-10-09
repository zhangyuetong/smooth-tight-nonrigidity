import TightVer401.TorusMarkedPairStabilityConnection
import TightVer401.TorusMarkedPairImageConnection
import TightVer401.TorusMarkedNoPlanarConnection
import TightVer401.TorusMarkedBandInputConnection

/-! Produce the actual marked pair FROM one completed protected saddle,
its actual graph data and one full convex closure. The amplitude, metric,
open agreement and all geometric conclusions refer to the same literal pair.
The original completion and the classical background remain explicit inputs. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold
local instance : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource
local instance : IsManifold planeModel ∞ NonrigidTorusSource :=
  nativeProductPlane_isManifold NonrigidTorusSource

variable {T w RN μ h : ℝ} [Fact (0 < T)]
variable {d : PeriodicRuledFrame T} {K : Set (AddCircle T × Ioo (0 : ℝ) w)}

/-- Conditional pair existence from SAME completed Q/Cdata/full D. All
conclusions use B(F) ± a C(Z), with one positive nonzero a chosen below the
single derived geometric stability bound. No original completion is granted. -/
theorem exists_completedSaddleTorus_marked_pair
    (background : ClassicalExternalResults)
    (reparam : ClassicalEmbeddedImageReparametrizationClaim)
    (axes : MarkerEllipseAxesRecognition)
    (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)
    (Cdata : ProtectedTorusActualGraphCylinderData Q.cylinder)
    (D : ParabolicConvexClosureData RN μ h)
    (hw : 0 < w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (_hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)))
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hsK : tsupport Y ⊆ K) :
    let F := protectedTorusMap Q.cylinder.saddle D.meridian h
    let e := completedSaddleTorusBandChart Q
    let Z := protectedTorusBendingField e (completedSaddleTorusBandAffine Q) Y
    let G := affineMarkedTorusLinearBase F
    let W := affineMarkedTorusLinearBending Z
    let U := (e '' tsupport Y)ᶜ
    ∃ a : ℝ, 0 < a ∧ ∃ g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : NonrigidTorusSource => TangentSpace planeModel p),
      NativeTorusSmoothEmbedding (G + a • W) ∧
      NativeTorusSmoothEmbedding (G - a • W) ∧
      IsTightImage (G + a • W) ∧ IsTightImage (G - a • W) ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (G + a • W) ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (G - a • W) ∧
      (∀ (p : NonrigidTorusSource) (v z : TangentSpace planeModel p),
        g.inner p v z = inducedForm (G + a • W) p v z ∧
        g.inner p v z = inducedForm (G - a • W) p v z) ∧
      (∀ p (v z : ℝ × ℝ),
        nativeProductInducedForm (G + a • W) p v z =
          nativeProductInducedForm (G - a • W) p v z) ∧
      ImageNoncongruent (G + a • W) (G - a • W) ∧
      IsOpen U ∧ U.Nonempty ∧ EqOn (G + a • W) (G - a • W) U ∧
      HasNoOpenPlanarPatch (G + a • W) ∧ HasNoOpenPlanarPatch (G - a • W) := by
  let F := protectedTorusMap Q.cylinder.saddle D.meridian h
  let e := completedSaddleTorusBandChart Q
  let A := completedSaddleTorusBandAffine Q
  let Z := protectedTorusBendingField e A Y
  let G := affineMarkedTorusLinearBase F
  let W := affineMarkedTorusLinearBending Z
  let U := (e '' tsupport Y)ᶜ
  obtain ⟨hXcoord, hYcoord, hicoord, hnegcoord⟩ :=
    periodicRuledFrame_marked_coordinate_inputs d (completedSaddleTorusBandAffine Q) hY
  obtain ⟨hZ, δ, hδ, hstable⟩ := completedSaddleTorus_marked_branch_stability
    background Q Cdata D hw hY hcompact hnonzero hsK
    hXcoord hYcoord hicoord hnegcoord
  let a := δ / 2
  have hapos : 0 < a := div_pos hδ (by norm_num)
  have ha : |a| < δ := by
    rw [abs_of_pos hapos]
    dsimp only [a]
    linarith
  obtain ⟨hplus, hminus, hnegative, _hrplus, _hrminus, _heqplus, _heqminus,
      _himgplus, _himgminus, _himgpair, _hgermplus, _hgermminus,
      _hgaussplus, _hgaussminus, htightplus, htightminus⟩ := hstable a ha
  have hsupport : tsupport Y ⊆ e.source :=
    hsK.trans (completedSaddleTorusBandChart_protected_source Q)
  have hout : ∃ q, q ∉ e '' tsupport Y :=
    completedSaddleTorusBending_exists_outside Q hsK
  have hF := (protectedTorusActualCylinderPositiveGaussData Q.cylinder D Cdata).embedding
  obtain ⟨g, hplusPlane, hminusPlane, hmetric, _hrank, _hquadratic⟩ :=
    affineMarkedTorusLinear_common_smooth_metric hF.1 hZ a hF.2.1
  have hnoPlanar := affineMarkedTorus_actualCylinder_bending_hasNoOpenPlanarPatch
    Q.cylinder D Cdata e A hcompact hsupport a hplus hminus
    (fun p hp => (hnegative p hp).2.1)
    (fun p hp => (hnegative p hp).2.2)
  have hnoncongruent := affineMarkedTorus_actualCylinder_bending_imageNoncongruent
    background reparam axes Q.cylinder D Cdata e A hcompact hsupport hnonzero
    hZ hout hapos.ne' hplus hminus
    (fun p hp => (hnegative p hp).1)
    (fun p hp => (hnegative p hp).2.1)
    (fun p hp => (hnegative p hp).2.2)
  have hopen : IsOpen U :=
    (protectedTorusBendingField_support_image_isCompact e hcompact hsupport).isClosed.isOpen_compl
  have hagree : EqOn (G + a • W) (G - a • W) U := by
    intro p hp
    have hgerm := protectedTorus_marked_branch_germs_off_support e A hcompact hsupport F
      torusAffineMarkerLinearEquiv.toContinuousLinearMap
      torusAffineMarkerContraLinearEquiv.toContinuousLinearMap a hp
    exact hgerm.1.self_of_nhds.trans hgerm.2.self_of_nhds.symm
  exact ⟨a, hapos, g, hplus, hminus, htightplus, htightminus,
    hplusPlane, hminusPlane, hmetric,
    affineMarkedTorusLinear_opposite_native_forms hF.1 hZ a,
    hnoncongruent, hopen, hout, hagree, hnoPlanar.1, hnoPlanar.2⟩

end
end TightVer401
