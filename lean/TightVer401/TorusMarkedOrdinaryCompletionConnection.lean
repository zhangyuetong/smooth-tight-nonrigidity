import TightVer401.CompletedSaddleTorusActualGraphConnection
import TightVer401.TorusMarkedCompletedPairConnection

/-! Actual marked pair from ordinary completed scalar/inverse/end data and
an original protected open scalar germ. The actual graph-cylinder producer
constructs Q/Cdata and chooses the full convex closure D exactly once.
This does not construct the incoming exits, connector or completed potential. -/
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

section OrdinaryData
variable {T w : ℝ} [Fact (0 < T)]
variable (background : ClassicalExternalResults)
variable (reparam : ClassicalEmbeddedImageReparametrizationClaim)
variable (axes : MarkerEllipseAxesRecognition)
variable (d : PeriodicRuledFrame T) (K : Set (AddCircle T × Ioo (0 : ℝ) w))
variable {G G0 : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
variable {A RN μ B ε L d0 dInfinity : ℝ}
variable (hA : 0 < A) (hARN : A < RN) (hμ : 0 < μ) (hB : 0 < B)
variable (hε : 0 < ε) (hL : 0 < L)
variable (hSource : e.source = {p : Coord | 0 < planarRadius p})
variable (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
variable (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
variable (heG : ∀ p ∈ e.source, e p = planarGradient G p)
variable (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
variable (hQuadratic : ∀ p : Coord, 0 < planarRadius p → planarRadius p < ε →
  G p = RN * planarRadius p - μ * planarRadius p ^ 2 / 2 + d0)
variable (hInfinity : ∀ p : Coord, L < planarRadius p →
  G p = A * planarRadius p - B / planarRadius p + dInfinity)
variable (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
variable (hc0 : ContMDiffOn nativeProductModel 𝓘(ℝ, Coord) ∞ c0 c0.source)
variable (hci0 : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ c0.symm c0.target)
variable (hBand : ∀ p ∈ c0.source, planarSupportMap G0 (c0 p) = d.bandMap p)
variable (hK : K ⊆ c0.source) {W : Set Coord} (hW : IsOpen W)
variable (hWe : W ⊆ e.source) (hKW : c0 '' K ⊆ W) (hEq : EqOn G G0 W)
variable (hw : 0 < w) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
variable (hY : IsBandBending (d.bandMap (b := w)) Y)
variable (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
variable (hsK : tsupport Y ⊆ K)

include background reparam axes e hA hARN hμ hB hε hL hSource hTarget hG hi heG
  hNeg hQuadratic hInfinity c0 hc0 hci0 hBand hK hW hWe hKW hEq hw hY hcompact
  hnonzero hsK in
/-- Construct Q/Cdata and one FULL D from the ordinary completed tuple, then
produce the actual literal marked pair. All classical inputs remain explicit;
no original completion, torus or pair witness is an assumption. -/
theorem exists_markedTorus_pair_of_ordinary_completed_support :
    d0 < dInfinity ∧
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
      ImageNoncongruent Xplus Xminus ∧
      IsOpen V ∧ V.Nonempty ∧ EqOn Xplus Xminus V ∧
      HasNoOpenPlanarPatch Xplus ∧ HasNoOpenPlanarPatch Xminus ∧
      ∃ (β : ℝ → ℝ)
        (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ (dInfinity - d0))
        (Cdata : ProtectedTorusActualGraphCylinderData Q.cylinder)
        (D : ParabolicConvexClosureData RN μ (dInfinity - d0)) (a : ℝ),
        0 < a ∧
        Q.cylinder.saddle = completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β ∧
        Q.verticalOffset = dInfinity ∧
        Cdata.G = G ∧ Cdata.e = e ∧ Cdata.beta = β ∧
        Cdata.A = A ∧ Cdata.B = B ∧ Cdata.L = L ∧
        Cdata.d0 = d0 ∧ Cdata.dInfinity = dInfinity ∧
        let F := protectedTorusMap Q.cylinder.saddle D.meridian (dInfinity - d0)
        let Z := protectedTorusBendingField (completedSaddleTorusBandChart Q)
          (completedSaddleTorusBandAffine Q) Y
        Xplus = affineMarkedTorusLinearBase F + a • affineMarkedTorusLinearBending Z ∧
        Xminus = affineMarkedTorusLinearBase F - a • affineMarkedTorusLinearBending Z ∧
        V = ((completedSaddleTorusBandChart Q) '' tsupport Y)ᶜ := by
  obtain ⟨hHeight, β, _hβ, _hMono, _hβA, _hβRN, _hβDerivative, _hβNeck, _hβNorth,
      Q, hLiteral, hOffset, Cdata, hCG, hCe, hCβ, hCA, hCB, hCL, hCd0, hCdInfinity,
      D, _Assembly, _hAssembly, _hAssemblyS, _hAssemblyM, _hAssemblyMeridian, _hEmbedding⟩ :=
    exists_completedSaddleTorusActualGraph_with_full_meridian d K e
      hA hARN hμ hB hε hL hSource hTarget hG hi heG hNeg hQuadratic hInfinity
      c0 hc0 hci0 hBand hK hW hWe hKW hEq
  obtain ⟨a, ha, g, hplus, hminus, htightplus, htightminus,
      hplusPlane, hminusPlane, hmetric, hnativeForms, hnoncongruent,
      hopen, hnonempty, hagree, hnoPlus, hnoMinus⟩ :=
    exists_completedSaddleTorus_marked_pair background reparam axes Q Cdata D hw
      d.bandMap_contMDiff hY hcompact hnonzero hsK
  let F := protectedTorusMap Q.cylinder.saddle D.meridian (dInfinity - d0)
  let Z := protectedTorusBendingField (completedSaddleTorusBandChart Q)
    (completedSaddleTorusBandAffine Q) Y
  let Xplus := affineMarkedTorusLinearBase F + a • affineMarkedTorusLinearBending Z
  let Xminus := affineMarkedTorusLinearBase F - a • affineMarkedTorusLinearBending Z
  let V := ((completedSaddleTorusBandChart Q) '' tsupport Y)ᶜ
  exact ⟨hHeight, Xplus, Xminus, g, V, hplus, hminus, htightplus, htightminus,
    hplusPlane, hminusPlane, hmetric, hnativeForms, hnoncongruent,
    hopen, hnonempty, hagree, hnoPlus, hnoMinus,
    β, Q, Cdata, D, a, ha, hLiteral, hOffset, hCG, hCe, hCβ, hCA, hCB, hCL,
    hCd0, hCdInfinity, rfl, rfl, rfl⟩

end OrdinaryData
end
end TightVer401
