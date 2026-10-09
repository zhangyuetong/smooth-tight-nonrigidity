import TightVer401.TorusMarkedHomotopyExitTraceConnection
import TightVer401.VisibleConnectorWitnessAssembly

/-! The same ordinary homotopy/trace first-pair application using canonical
connector assembly. The ordinary final Cartesian scalar/germ/boundary/source
family is still an explicit original producer obligation, not asserted here. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

local instance ordinaryConnectorDataPeriodOne : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
local instance ordinaryConnectorDataNativeManifold :
    IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold
local instance ordinaryConnectorDataPlaneChart : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource
local instance ordinaryConnectorDataPlaneManifold :
    IsManifold planeModel ∞ NonrigidTorusSource :=
  nativeProductPlane_isManifold NonrigidTorusSource

variable {T w : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G0 Gexit : Coord → ℝ}
    {c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord}
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {HpPlus HpMinus HgPlus HgMinus : ℂ ≃ₜ ℂ}
    {pPlus pMinus gammaPlus gammaMinus : ℝ → ℂ}
    {RPlus RMinus : ℝ} {O : Set Coord}

/-- Derive the connector statement from the existing ordinary data family,
then apply the SAME homotopy/trace pair caller once. No ordinary data family,
selected geometry, completed scalar or pair is constructed by this adapter. -/
theorem exists_markedTorus_pair_of_ordinary_connector_data
    (background : ClassicalExternalResults)
    (reparam : ClassicalEmbeddedImageReparametrizationClaim)
    (axes : MarkerEllipseAxesRecognition)
    (hOrdinary : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R),
      ∀ etaMax : ℝ, 0 < etaMax →
        Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax))
    (e0 : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ Gexit e0.source)
    (hNegative : ∀ p ∈ e0.source, (planarHessian Gexit p).det < 0)
    (heG : ∀ p ∈ e0.source, e0 p = planarGradient Gexit p)
    (hInverse : ContDiffOn ℝ ∞ e0.symm e0.target)
    (hpPlus : DualRadialCompletionPositiveTrace HpPlus pPlus)
    (hpMinus : DualRadialCompletionPositiveTrace HpMinus pMinus)
    (hgPlus : DualRadialCompletionPositiveTrace HgPlus gammaPlus)
    (hgMinus : DualRadialCompletionPositiveTrace HgMinus gammaMinus)
    (hSourceNested : closure (HpMinus '' ball (0 : ℂ) 1) ⊆ HpPlus '' ball (0 : ℂ) 1)
    (hGradientNested : closure (HgPlus '' ball (0 : ℂ) 1) ⊆ HgMinus '' ball (0 : ℂ) 1)
    (hpMinus0 : (0 : ℂ) ∈ HpMinus '' ball (0 : ℂ) 1)
    (hgPlus0 : (0 : ℂ) ∈ HgPlus '' ball (0 : ℂ) 1)
    (H : C(unitInterval, C(unitInterval, ℂ)))
    (hH0 : ∀ t, H 0 t = pMinus (t : ℝ))
    (hH1 : ∀ t, H 1 t = pPlus (t : ℝ))
    (hclosed : ∀ a, H a 1 = H a 0)
    (hHU : ∀ a t, H a t ∈ angularDescentComplex '' e0.source)
    (hActualPlus : ∀ t, e0 (seamComplexCoord (pPlus t)) = seamComplexCoord (gammaPlus t))
    (hActualMinus : ∀ t, e0 (seamComplexCoord (pMinus t)) = seamComplexCoord (gammaMinus t))
    (hPairPlus : ∀ t, 0 < inner ℝ (deriv pPlus t) (deriv gammaPlus t))
    (hPairMinus : ∀ t, 0 < inner ℝ (deriv pMinus t) (deriv gammaMinus t))
    (hRPlus : 0 < RPlus) (hRMinus : 0 < RMinus)
    (hVisPlus : ComplexVisiblePair RPlus pPlus (fun t => Complex.I * gammaPlus t))
    (hVisMinus : ComplexVisiblePair RMinus (corrugatedReverseReflect gammaMinus)
      (fun t => Complex.I * corrugatedReverseReflect pMinus t))
    (hCore : c0 '' tsupport Y ⊆ seamComplexCoord ''
      ((HpPlus '' ball (0 : ℂ) 1) \ closure (HpMinus '' ball (0 : ℂ) 1)))
    (hw : 0 < w)
    (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
    (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
    (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
    (hY : IsBandBending (d.bandMap (b := w)) Y)
    (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    (hKsource : tsupport Y ⊆ c0.source)
    (hO : IsOpen O) (hKO : c0 '' tsupport Y ⊆ O)
    (hOldEq : EqOn Gexit G0 O) :
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
        EqOn Gtilde Gexit W ∧ EqOn Gtilde G0 W ∧
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
        V = ((completedSaddleTorusBandChart Q) '' tsupport Y)ᶜ := by
  have hConnector : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R),
      VisibleConnectorConstructionStatement D :=
    fun Gin Uin R D =>
      visibleConnectorWitnessAssembly_statement D (hOrdinary Gin Uin R D)
  exact exists_markedTorus_pair_of_homotopy_exit_traces
    (d := d) (G0 := G0) (Gexit := Gexit) (c0 := c0) (Y := Y)
    background reparam axes hConnector e0 hG hNegative heG hInverse
    hpPlus hpMinus hgPlus hgMinus hSourceNested hGradientNested hpMinus0 hgPlus0
    H hH0 hH1 hclosed hHU hActualPlus hActualMinus hPairPlus hPairMinus
    hRPlus hRMinus hVisPlus hVisMinus hCore hw hc0 hci0 hBand hY hcompact hnonzero
    hKsource hO hKO hOldEq

end
end TightVer401
