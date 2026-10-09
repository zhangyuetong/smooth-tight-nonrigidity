import TightVer401.DualRadialCompletion
import TightVer401.TorusMarkedOrdinaryCompletionConnection

/-! The first marked pair from ordinary actual positive traces and the
original protected scalar germ. This caller does not need the full native
positive-exit annulus charts or Fermi-return package. Source/gradient nesting,
closed source-domain containment and protected core placement remain genuine
ordinary input obligations. The actual completion and one full convex witness
are constructed by the existing producers. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

local instance ordinaryExitTracePeriodOne : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

local instance ordinaryExitTraceNativeManifold : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold
local instance ordinaryExitTracePlaneChart : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource
local instance ordinaryExitTracePlaneManifold : IsManifold planeModel ∞ NonrigidTorusSource :=
  nativeProductPlane_isManifold NonrigidTorusSource

variable {T w : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G0 Gexit : Coord → ℝ}
    {c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord}
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {HpPlus HpMinus HgPlus HgMinus : ℂ ≃ₜ ℂ}
    {pPlus pMinus gammaPlus gammaMinus : ℝ → ℂ}
    {RPlus RMinus : ℝ} {O : Set Coord}

/-- Ordinary actual exits complete ONE scalar and its actual gradient inverse,
then construct ONE protected cylinder, its actual graph and ONE full meridian.
No positive-exit native chart, return package, completion or pair is assumed. -/
theorem exists_markedTorus_pair_of_ordinary_exit_traces
    (background : ClassicalExternalResults)
    (reparam : ClassicalEmbeddedImageReparametrizationClaim)
    (axes : MarkerEllipseAxesRecognition)
    (hConnector : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R), VisibleConnectorConstructionStatement D)
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
    (hClosedBand : seamComplexCoord '' (closure (HpPlus '' ball (0 : ℂ) 1) \
      (HpMinus '' ball (0 : ℂ) 1)) ⊆ e0.source)
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
  have hKcompact : IsCompact (c0 '' tsupport Y) :=
    hcompact.image_of_continuousOn (hc0.continuousOn.mono hKsource)
  obtain ⟨A, RN, mu, B, d0, dInfinity, epsilon, L, Gtilde, W0, E,
      hA, hARN, hmu, hB, hepsilon, heL, hSmooth, hSaddle, hW0, hKW0,
      hWSource, hWPositive, hExitEq, hInner, hOuter,
      hESource, hETarget, hEActual, hEInverse⟩ :=
    (exists_dual_radial_support_completion_of_visible_connector hConnector)
      Gexit e0 HpPlus HpMinus HgPlus HgMinus pPlus pMinus gammaPlus gammaMinus
      RPlus RMinus (c0 '' tsupport Y)
      hG hNegative heG hInverse hpPlus hpMinus hgPlus hgMinus
      hSourceNested hGradientNested hpMinus0 hgPlus0 hClosedBand
      hActualPlus hActualMinus hPairPlus hPairMinus hRPlus hRMinus hVisPlus hVisMinus
      hKcompact hCore
  have hKTarget : c0 '' tsupport Y ⊆ c0.target := by
    rintro p ⟨q, hq, rfl⟩
    exact c0.map_source (hKsource hq)
  let W : Set Coord := (W0 ∩ O) ∩ c0.target
  have hW : IsOpen W := (hW0.inter hO).inter c0.open_target
  have hKW : c0 '' tsupport Y ⊆ W := fun p hp =>
    ⟨⟨hKW0 hp, hKO hp⟩, hKTarget hp⟩
  have hWChart : W ⊆ c0.target := inter_subset_right
  have hWPositive' : W ⊆ {p : Coord | 0 < planarRadius p} :=
    fun p hp => hWPositive hp.1.1
  have hWE : W ⊆ E.source := by
    rw [hESource]
    exact hWPositive'
  have hWSource' : W ⊆ e0.source := fun p hp => hWSource hp.1.1
  have hWO : W ⊆ O := fun p hp => hp.1.2
  have hRetainedExit : EqOn Gtilde Gexit W := fun p hp => hExitEq hp.1.1
  have hRetainedOld : EqOn Gtilde G0 W := fun p hp =>
    (hExitEq hp.1.1).trans (hOldEq hp.1.2)
  have hOldGerm : ∀ p ∈ W, Gtilde =ᶠ[𝓝 p] G0 :=
    fun p hp => hRetainedOld.eventuallyEq_of_mem (hW.mem_nhds hp)
  have hL : 0 < L := lt_trans hepsilon heL
  have hSmoothSource : ContDiffOn ℝ ∞ Gtilde E.source := by
    rw [hESource]
    exact hSmooth
  have hSaddleSource : ∀ p ∈ E.source, (planarHessian Gtilde p).det < 0 := by
    intro p hp
    exact hSaddle p (by simpa only [hESource, Set.mem_setOf_eq] using hp)
  have hTarget : E.target = quadraticRadialFillingOpenAnnulus A RN := hETarget
  obtain ⟨hHeight, Xplus, Xminus, g, V, hplus, hminus, htightplus, htightminus,
      hplusPlane, hminusPlane, hmetric, hnativeForms, hnoncongruent,
      hopen, hnonempty, hagree, hnoPlus, hnoMinus,
      β, Q, Cdata, D, a, ha, hLiteral, hOffset, hCG, hCe, hCβ,
      hCA, hCB, hCL, hCd0, hCdInfinity, hPlusLiteral, hMinusLiteral, hVLiteral⟩ :=
    exists_markedTorus_pair_of_ordinary_completed_support background reparam axes
      d (tsupport Y) E hA hARN hmu hB hepsilon hL hESource hTarget
      hSmoothSource hEInverse hEActual hSaddleSource hInner hOuter
      c0 hc0 hci0 hBand hKsource hW hWE hKW hRetainedOld hw hY
      hcompact hnonzero (Subset.refl _)
  exact ⟨Xplus, Xminus, g, V, hplus, hminus, htightplus, htightminus,
    hplusPlane, hminusPlane, hmetric, hnativeForms, hnoncongruent,
    hopen, hnonempty, hagree, hnoPlus, hnoMinus,
    A, RN, mu, B, d0, dInfinity, epsilon, L, Gtilde, W, E, β, Q, Cdata, D, a,
    hA, hARN, hmu, hB, hepsilon, heL, hHeight, ha, hW, hKW, hWChart, hWE,
    hWSource', hWO, hRetainedExit, hRetainedOld, hOldGerm, hESource, hTarget,
    hLiteral, hOffset, hCG, hCe, hCβ, hCA, hCB, hCL, hCd0, hCdInfinity,
    hPlusLiteral, hMinusLiteral, hVLiteral⟩

end
end TightVer401