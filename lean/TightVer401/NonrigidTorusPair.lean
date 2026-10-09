import TightVer401.PositiveExitConstructionActualPair
import TightVer401.VisibleConnectorOrdinaryFamilyFromIncomingAssembly
import TightVer401.MarkerEllipseAxesRecognitionProof
import TightVer401.ClassicalEmbeddedReparamProof
import TightVer401.ClassicalExternalProof

/-! The concrete seed and universal original-data connector construction
discharge all original first-pair premises. All four background claims have closed proofs. The canonical existence
theorem has no background or construction premises.
Completion choices, the full meridian and marked pair are those returned by the
existing caller, selected once with the SAME native band and protected field. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
open OAI.CircleDomainRigidity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

local instance nonrigidPairPeriodOne : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
local instance nonrigidPairNativeManifold :
    IsManifold nativeProductModel ∞ NonrigidTorusSource := nonrigidTorusSource_isManifold
local instance nonrigidPairPlaneChart : ChartedSpace Plane NonrigidTorusSource :=
    nativeProductPlaneChartedSpace NonrigidTorusSource
local instance nonrigidPairPlaneManifold : IsManifold planeModel ∞ NonrigidTorusSource :=
    nativeProductPlane_isManifold NonrigidTorusSource

/-- The actual global pair, retaining the completed tuple and SAME full meridian. -/
theorem exists_noncongruent_isometric_tight_tori_pair_of_classical
    (positiveGaussTightness : ClassicalPositiveGaussTightnessClaim)
 :
    ∃ T : ℝ, ∃ hT : 0 < T,
      letI : Fact (0 < T) := ⟨hT⟩
      ∃ d : PeriodicRuledFrame T, ∃ w : ℝ,
      ∃ c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
      ∃ G0 : Coord → ℝ, ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
      ∃ (Ge : Coord → ℝ) (e0 : OpenPartialHomeomorph Coord Coord) (O : Set Coord),
    ∃ (Xplus Xminus : NonrigidTorusSource → Ambient)
      (g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : NonrigidTorusSource => TangentSpace planeModel p))
      (V : Set NonrigidTorusSource),
      NativeTorusSmoothEmbedding Xplus ∧ NativeTorusSmoothEmbedding Xminus ∧
      IsTightImage Xplus ∧ IsTightImage Xminus ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ Xplus ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ Xminus ∧
      (∀ (p : NonrigidTorusSource) (v z : TangentSpace planeModel p),
        g.inner p v z = inducedForm Xplus p v z ∧
        g.inner p v z = inducedForm Xminus p v z) ∧
      (∀ p (v z : ℝ × ℝ),
        nativeProductInducedForm Xplus p v z = nativeProductInducedForm Xminus p v z) ∧
      ImageNoncongruent Xplus Xminus ∧ IsOpen V ∧ V.Nonempty ∧
      EqOn Xplus Xminus V ∧ HasNoOpenPlanarPatch Xplus ∧ HasNoOpenPlanarPatch Xminus ∧
      ∃ (A RN mu B d0 dInfinity epsilon L : ℝ)
        (Gtilde : Coord → ℝ) (W : Set Coord) (E : OpenPartialHomeomorph Coord Coord)
        (β : ℝ → ℝ)
        (Q : CompletedSaddleAnnulusGeometryOutput d (tsupport Y) RN mu (dInfinity - d0))
        (Cdata : ProtectedTorusActualGraphCylinderData Q.cylinder)
        (D : ParabolicConvexClosureData RN mu (dInfinity - d0)) (a : ℝ),
        0 < A ∧ A < RN ∧ 0 < mu ∧ 0 < B ∧ 0 < epsilon ∧ epsilon < L ∧
        d0 < dInfinity ∧ 0 < a ∧ IsOpen W ∧ c0 '' tsupport Y ⊆ W ∧
        W ⊆ c0.target ∧ W ⊆ E.source ∧ W ⊆ e0.source ∧ W ⊆ O ∧
        EqOn Gtilde Ge W ∧ EqOn Gtilde G0 W ∧
        (∀ p ∈ W, Gtilde =ᶠ[𝓝 p] G0) ∧
        E.source = {p : Coord | 0 < planarRadius p} ∧
        E.target = quadraticRadialFillingOpenAnnulus A RN ∧
        Q.cylinder.saddle = completedSaddleAnnulusCylinderMap Gtilde E A RN d0 dInfinity β ∧
        Q.verticalOffset = dInfinity ∧
        Cdata.G = Gtilde ∧ Cdata.e = E ∧ Cdata.beta = β ∧
        Cdata.A = A ∧ Cdata.B = B ∧ Cdata.L = L ∧
        Cdata.d0 = d0 ∧ Cdata.dInfinity = dInfinity ∧
        let F := protectedTorusMap Q.cylinder.saddle D.meridian (dInfinity - d0)
        let Z := protectedTorusBendingField (completedSaddleTorusBandChart Q)
          (completedSaddleTorusBandAffine Q) Y
        Xplus = affineMarkedTorusLinearBase F + a • affineMarkedTorusLinearBending Z ∧
        Xminus = affineMarkedTorusLinearBase F - a • affineMarkedTorusLinearBending Z ∧
        V = ((completedSaddleTorusBandChart Q) '' tsupport Y)ᶜ
    := by
  have hOrdinary : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R),
      ∀ etaMax : ℝ, 0 < etaMax →
        Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax) := by
    intro Gin Uin R D etaMax hetaMax
    exact visibleConnectorOrdinaryFamily_nonempty_from_incoming D hetaMax
  exact actualSeed_exists_markedTorus_pair_of_ordinary_connector_family
    ⟨positiveGaussTightness, classicalCoincidentEmbeddingFixedOpen_proved⟩
    classicalEmbeddedImageReparametrization_proved
    markerEllipseAxesRecognition_proved hOrdinary

/-- The unconditional actual pair with its common smooth positive induced metric,
noncongruent images, open agreement and no open planar patches. All completed
objects and the once-chosen full meridian are retained literally. -/
theorem exists_noncongruent_isometric_tight_tori_pair
 :
    ∃ T : ℝ, ∃ hT : 0 < T,
      letI : Fact (0 < T) := ⟨hT⟩
      ∃ d : PeriodicRuledFrame T, ∃ w : ℝ,
      ∃ c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord,
      ∃ G0 : Coord → ℝ, ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
      ∃ (Ge : Coord → ℝ) (e0 : OpenPartialHomeomorph Coord Coord) (O : Set Coord),
    ∃ (Xplus Xminus : NonrigidTorusSource → Ambient)
      (g : Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
        (fun p : NonrigidTorusSource => TangentSpace planeModel p))
      (V : Set NonrigidTorusSource),
      NativeTorusSmoothEmbedding Xplus ∧ NativeTorusSmoothEmbedding Xminus ∧
      IsTightImage Xplus ∧ IsTightImage Xminus ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ Xplus ∧
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ Xminus ∧
      (∀ (p : NonrigidTorusSource) (v z : TangentSpace planeModel p),
        g.inner p v z = inducedForm Xplus p v z ∧
        g.inner p v z = inducedForm Xminus p v z) ∧
      (∀ p (v z : ℝ × ℝ),
        nativeProductInducedForm Xplus p v z = nativeProductInducedForm Xminus p v z) ∧
      ImageNoncongruent Xplus Xminus ∧ IsOpen V ∧ V.Nonempty ∧
      EqOn Xplus Xminus V ∧ HasNoOpenPlanarPatch Xplus ∧ HasNoOpenPlanarPatch Xminus ∧
      ∃ (A RN mu B d0 dInfinity epsilon L : ℝ)
        (Gtilde : Coord → ℝ) (W : Set Coord) (E : OpenPartialHomeomorph Coord Coord)
        (β : ℝ → ℝ)
        (Q : CompletedSaddleAnnulusGeometryOutput d (tsupport Y) RN mu (dInfinity - d0))
        (Cdata : ProtectedTorusActualGraphCylinderData Q.cylinder)
        (D : ParabolicConvexClosureData RN mu (dInfinity - d0)) (a : ℝ),
        0 < A ∧ A < RN ∧ 0 < mu ∧ 0 < B ∧ 0 < epsilon ∧ epsilon < L ∧
        d0 < dInfinity ∧ 0 < a ∧ IsOpen W ∧ c0 '' tsupport Y ⊆ W ∧
        W ⊆ c0.target ∧ W ⊆ E.source ∧ W ⊆ e0.source ∧ W ⊆ O ∧
        EqOn Gtilde Ge W ∧ EqOn Gtilde G0 W ∧
        (∀ p ∈ W, Gtilde =ᶠ[𝓝 p] G0) ∧
        E.source = {p : Coord | 0 < planarRadius p} ∧
        E.target = quadraticRadialFillingOpenAnnulus A RN ∧
        Q.cylinder.saddle = completedSaddleAnnulusCylinderMap Gtilde E A RN d0 dInfinity β ∧
        Q.verticalOffset = dInfinity ∧
        Cdata.G = Gtilde ∧ Cdata.e = E ∧ Cdata.beta = β ∧
        Cdata.A = A ∧ Cdata.B = B ∧ Cdata.L = L ∧
        Cdata.d0 = d0 ∧ Cdata.dInfinity = dInfinity ∧
        let F := protectedTorusMap Q.cylinder.saddle D.meridian (dInfinity - d0)
        let Z := protectedTorusBendingField (completedSaddleTorusBandChart Q)
          (completedSaddleTorusBandAffine Q) Y
        Xplus = affineMarkedTorusLinearBase F + a • affineMarkedTorusLinearBending Z ∧
        Xminus = affineMarkedTorusLinearBase F - a • affineMarkedTorusLinearBending Z ∧
        V = ((completedSaddleTorusBandChart Q) '' tsupport Y)ᶜ
    := by
  exact exists_noncongruent_isometric_tight_tori_pair_of_classical
    classicalPositiveGaussTightness_proved

end
end TightVer401
