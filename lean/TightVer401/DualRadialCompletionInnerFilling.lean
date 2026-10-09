import TightVer401.DualRadialCompletionInnerFillingPatch
import TightVer401.DualRadialCompletionInnerBranch

/-! The concrete reflected inner application constructs its scalar paste
from ordinary returned filling data, then retains the original potential. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Construct the SAME physical inner branch from the actual inner filling
packet. Neither a patched scalar nor a local completion is an input. -/
theorem exists_dualRadialCompletion_inner_filling
    {G : Coord → ℝ} (e0 : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e0.source)
    (hNegative : ∀ p ∈ e0.source, (planarHessian G p).det < 0)
    (heG : ∀ p ∈ e0.source, e0 p = planarGradient G p)
    (hInverse : ContDiffOn ℝ ∞ e0.symm e0.target)
    {L R etaMax : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0).source L R}
    (C : VisibleConnectorConstructionData D etaMax)
    (E : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ E.source)
    (hActual : (E : Coord → Coord) = planarGradient C.G)
    (hC : ContDiffOn ℝ ∞ C.G E.source)
    (hNegC : ∀ p ∈ E.source, (planarHessian C.G p).det < 0)
    (hi : ContDiffOn ℝ ∞ E.symm E.target)
    {HMinus : ℂ ≃ₜ ℂ} {pMinus : ℝ → ℂ}
    (hpMinus : DualRadialCompletionPositiveTrace HMinus pMinus)
    (hDgamma : D.incoming.gamma = seamComplexCoord ∘ corrugatedReverseReflect pMinus)
    {H : Coord → ℝ} {U : Set Coord} {S M S0 : ℝ}
    (hU : IsOpen U) (hUUfill : U ⊆ dualRadialCompletionFillingDomain C E)
    (hH : ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U))
    (hnH : ∀ p ∈ quadraticRadialFillingDomain R U, (planarHessian H p).det < 0)
    (hDisk : {p : Coord | 0 < planarRadius p ∧ planarRadius p < S} ⊆
      quadraticRadialFillingDomain R U)
    (hM : 0 < M) (hRS0 : R < S0) (hS0S : S0 < S)
    (hInnerH : ∀ p : Coord, 0 < planarRadius p → planarRadius p < R/2 →
      H =ᶠ[𝓝 p] dualRadialQuadraticPotential R M (-M*R^2/2))
    {Uc : Set Coord} (hUc : IsOpen Uc) (hUcU : Uc ⊆ U)
    (hCircle : quadraticRadialFillingRadiusLevel S0 ⊆ Uc)
    (hRetained : ∀ p ∈ Uc, H =ᶠ[𝓝 p] planarLegendre C.G E) :
    ∃ (RN mu : ℝ) (Fi : Coord → ℝ) (Ui Nin : Set Coord),
      RN = M*R ∧ mu = M ∧ 0 < RN ∧ 0 < mu ∧
      IsOpen Ui ∧ Ui ⊆ {p | 0 < planarRadius p} ∧ IsOpen Nin ∧
      frontier (seamComplexCoord '' (HMinus '' Metric.ball (0 : ℂ) 1)) ⊆ Nin ∧
      Nin ⊆ e0.source ∧
      ((seamComplexCoord '' (HMinus '' Metric.ball (0 : ℂ) 1)) ∩
        {p : Coord | 0 < planarRadius p}) ∪ Nin ⊆ Ui ∧
      ContDiffOn ℝ ∞ Fi Ui ∧
      (∀ p ∈ Ui, (planarHessian Fi p).det < 0) ∧
      EqOn Fi G Nin ∧ (∀ p ∈ Nin, Fi =ᶠ[𝓝 p] G) ∧
      EqOn Fi (fun p => RN*planarRadius p-mu*planarRadius p^2/2-M*R^2/2)
        {p | 0 < planarRadius p ∧ planarRadius p < R/2} ∧
      (∀ p, 0 < planarRadius p → planarRadius p < R/2 →
        Fi =ᶠ[𝓝 p] (fun q => RN*planarRadius q-mu*planarRadius q^2/2-M*R^2/2)) := by
  let F := planarLegendre C.G E
  have hR : 0 < R := D.radius_pos
  have hS0 : 0 < S0 := hR.trans hRS0
  have heC : ∀ p ∈ E.source, E p = planarGradient C.G p :=
    fun p _ => congrFun hActual p
  have hF : ContDiffOn ℝ ∞ F E.target := planarLegendre_contDiffOn E hC hi
  have hnF : ∀ p ∈ E.target, (planarHessian F p).det < 0 := by
    intro p hp
    exact planarLegendre_saddle E hC hi heC hp (hNegC _ (E.map_target hp))
  have hUTarget : U ⊆ E.target := fun p hp => (hUUfill hp).1
  have hDisk0 : {p : Coord | 0 < planarRadius p ∧ planarRadius p < S0} ⊆
      quadraticRadialFillingDomain R U := by
    intro p hp
    exact hDisk ⟨hp.1, hp.2.trans hS0S⟩
  have hCircleU (theta : ℝ) : saddlePolarChart ![S0,theta] ∈ U :=
    hUcU (hCircle (angularDescent_radius_polar (q := ![S0,theta]) hS0))
  have hCircleGerm (theta : ℝ) : H =ᶠ[𝓝 (saddlePolarChart ![S0,theta])] F :=
    hRetained _ (hCircle (angularDescent_radius_polar (q := ![S0,theta]) hS0))
  obtain ⟨delta,P,hDelta,hDeltaR,hP,hnP,hPH,hPF⟩ :=
    exists_dualRadialCompletion_inner_filling_patch hR hRS0 hU E.open_target hUTarget
      hF hnF hH hnH hDisk0 hCircleU hCircleGerm
  obtain ⟨W,hW,hSeamW,hWSource,hWTarget,hRecover,_hRecoverGerm⟩ :=
    exists_dualRadialCompletionInnerRetain e0 hG hNegative heG hInverse C E hClosed hActual hDgamma
  have hDomain : quadraticRadialFillingDomain R U ⊆
      quadraticRadialFillingDomain R (dualRadialCompletionFillingDomain C E) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    rcases hp.2 with hpR | hpU
    · exact Or.inl hpR
    · exact Or.inr (hUUfill hpU)
  have hDiskFill : {p : Coord | 0 < planarRadius p ∧ planarRadius p < S0} ⊆
      quadraticRadialFillingDomain R (dualRadialCompletionFillingDomain C E) :=
    fun p hp => hDomain (hDisk0 hp)
  have hCircleFill (theta : ℝ) :
      saddlePolarChart ![S0,theta] ∈ dualRadialCompletionFillingDomain C E :=
    hUUfill (hCircleU theta)
  obtain ⟨Fi,Ui,Nin,_hFi,hUi,hUiOpen,hNinOpen,hFront,hNinSource,hCover,
    hFiSmooth,hFiNeg,hEq,hGerm,hInner,hInnerGerm⟩ :=
    exists_dualRadialCompletion_inner_branch e0 C E hClosed hActual hpMinus hDgamma
      hW hSeamW hWSource hWTarget hRecover hRS0 hDelta hDeltaR hDiskFill hCircleFill
      hP hnP hPH hPF hInnerH
  refine ⟨M*R,M,Fi,Ui,Nin,rfl,rfl,mul_pos hM hR,hM,hUiOpen,?_,hNinOpen,
    hFront,hNinSource,hCover,hFiSmooth,hFiNeg,hEq,hGerm,hInner,hInnerGerm⟩
  intro p hp
  rw [hUi] at hp
  change dualRadialCompletionReflection p ∈ quadraticRadialFillingDomain S0 E.target at hp
  have hPositive : 0 < planarRadius (dualRadialCompletionReflection p) := hp.1
  change 0 < planarRadius p
  simpa only [dualRadialCompletionReflection_radius] using hPositive

end
end TightVer401
