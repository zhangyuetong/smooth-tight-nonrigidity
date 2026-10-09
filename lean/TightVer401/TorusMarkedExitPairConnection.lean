import TightVer401.DualRadialCompletionExitApplication
import TightVer401.TorusMarkedOrdinaryCompletionConnection

/-! Connect actual positive-exit output and the explicit original visible
connector producer to the actual marked torus pair. The completed scalar,
retained open germ, graph cylinder and full convex closure are all produced;
none is a premise. Actual exit/connector construction remains explicit. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4
set_option backward.isDefEq.respectTransparency false

local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

local instance : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
  nonrigidTorusSource_isManifold
local instance : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource
local instance : IsManifold planeModel ∞ NonrigidTorusSource :=
  nativeProductPlane_isManifold NonrigidTorusSource

variable {T w delta : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G0 : Coord → ℝ} {U0 : Set Coord}
    {c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord}
    {he : c0.source = univ} {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0}
    {hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w}
    {O : Set Coord} {xi : ℝ}

/-- From actual exits, produce the completed tuple and use it ONCE to
construct the literal marked pair. The universal visible-connector producer
and the named classical backgrounds remain explicit, original obligations. -/
theorem exists_markedTorus_pair_of_actual_positive_exits
    (background : ClassicalExternalResults)
    (reparam : ClassicalEmbeddedImageReparametrizationClaim)
    (axes : MarkerEllipseAxesRecognition)
    (hConnector : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R), VisibleConnectorConstructionStatement D)
    (X : PositiveExitConstructionData d G0 U0 c0 he Y hbalance hinside O xi)
    (hw : 0 < w)
    (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
    (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
    (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
    (hY : IsBandBending (d.bandMap (b := w)) Y) :
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
        W ⊆ c0.target ∧ W ⊆ E.source ∧ EqOn Gtilde G0 W ∧
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
  obtain ⟨A, RN, mu, B, d0, dInfinity, epsilon, L, Gtilde, W, E,
      hA, hARN, hmu, hB, hepsilon, heL, hSmooth, hSaddle, hW, hCore, hWChart,
      _hWAnnulus, _hWExit, hWPositive, _hExitEq, hOldEq, hOldGerm,
      hInner, hOuter, hESource, hETarget, hEActual, hEInverse⟩ :=
    exists_dualRadialCompletionExitApplication_of_visible_connector hConnector X
  have hL : 0 < L := lt_trans hepsilon heL
  have hSmoothSource : ContDiffOn ℝ ∞ Gtilde E.source := by
    rw [hESource]
    exact hSmooth
  have hSaddleSource : ∀ p ∈ E.source, (planarHessian Gtilde p).det < 0 := by
    intro p hp
    exact hSaddle p (by simpa only [hESource, Set.mem_setOf_eq] using hp)
  have hTarget : E.target = quadraticRadialFillingOpenAnnulus A RN := hETarget
  have hK : tsupport Y ⊆ c0.source := by
    rw [he]
    exact subset_univ _
  have hWE : W ⊆ E.source := by simpa only [hESource] using hWPositive
  obtain ⟨hHeight, Xplus, Xminus, g, V, hplus, hminus, htightplus, htightminus,
      hplusPlane, hminusPlane, hmetric, hnativeForms, hnoncongruent,
      hopen, hnonempty, hagree, hnoPlus, hnoMinus,
      β, Q, Cdata, D, a, ha, hLiteral, hOffset, hCG, hCe, hCβ,
      hCA, hCB, hCL, hCd0, hCdInfinity, hPlusLiteral, hMinusLiteral, hVLiteral⟩ :=
    exists_markedTorus_pair_of_ordinary_completed_support background reparam axes
      d (tsupport Y) E hA hARN hmu hB hepsilon hL hESource hTarget
      hSmoothSource hEInverse hEActual hSaddleSource hInner hOuter
      c0 hc0 hci0 hBand hK hW hWE hCore hOldEq hw hY
      X.same_native_compact_support X.same_native_nonzero (Subset.refl _)
  exact ⟨Xplus, Xminus, g, V, hplus, hminus, htightplus, htightminus,
    hplusPlane, hminusPlane, hmetric, hnativeForms, hnoncongruent,
    hopen, hnonempty, hagree, hnoPlus, hnoMinus,
    A, RN, mu, B, d0, dInfinity, epsilon, L, Gtilde, W, E, β, Q, Cdata, D, a,
    hA, hARN, hmu, hB, hepsilon, heL, hHeight, ha, hW, hCore, hWChart, hWE,
    hOldEq, hOldGerm, hESource, hTarget, hLiteral, hOffset,
    hCG, hCe, hCβ, hCA, hCB, hCL, hCd0, hCdInfinity,
    hPlusLiteral, hMinusLiteral, hVLiteral⟩

end
end TightVer401
