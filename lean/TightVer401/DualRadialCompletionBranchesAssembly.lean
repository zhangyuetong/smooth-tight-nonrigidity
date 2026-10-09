import TightVer401.DualRadialCompletionInnerFilling
import TightVer401.DualRadialCompletionOuterFilling
import TightVer401.DualRadialCompletionPairAssembly

/-! One actual completed potential from the two concrete filling applications.
The original Jordan fills determine the source topology. Connector and filling
producer witnesses remain ordinary incoming data; no branch or completion
conclusion is assumed. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
set_option backward.isDefEq.respectTransparency false

/-- Invoke both actual filling applications, derive the original nested source
regions and protected core, and construct ONE scalar with its actual global
annular gradient inverse. The final caller supplies the proved circular degree
argument and the genuine connector/filling producer witnesses. -/
theorem exists_dualRadialCompletion_branches_assembly
    (hDegree : DualRadialCompletionCircularDegreeClaim)
    {G : Coord → ℝ} (e0 : OpenPartialHomeomorph Coord Coord)
    (HpMinus HpPlus : ℂ ≃ₜ ℂ) (pMinus pPlus : ℝ → ℂ) (K : Set Coord)
    (hG : ContDiffOn ℝ ∞ G e0.source)
    (hnG : ∀ p ∈ e0.source, (planarHessian G p).det < 0)
    (heG : ∀ p ∈ e0.source, e0 p = planarGradient G p)
    (hi0 : ContDiffOn ℝ ∞ e0.symm e0.target)
    (hpMinus : DualRadialCompletionPositiveTrace HpMinus pMinus)
    (hpPlus : DualRadialCompletionPositiveTrace HpPlus pPlus)
    (hNested : closure (HpMinus '' ball (0 : ℂ) 1) ⊆ HpPlus '' ball (0 : ℂ) 1)
    (hOrigin : (0 : ℂ) ∈ HpMinus '' ball (0 : ℂ) 1)
    (hBand : seamComplexCoord '' (closure (HpPlus '' ball (0 : ℂ) 1) \
      (HpMinus '' ball (0 : ℂ) 1)) ⊆ e0.source)
    (hKCompact : IsCompact K)
    (hK : K ⊆ seamComplexCoord '' ((HpPlus '' ball (0 : ℂ) 1) \
      closure (HpMinus '' ball (0 : ℂ) 1)))
    {RMinus etaMinus : ℝ}
    {DMinus : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0).source 1 RMinus}
    (CMinus : VisibleConnectorConstructionData DMinus etaMinus)
    (EMinus : OpenPartialHomeomorph Coord Coord)
    (hClosedMinus : closure CMinus.source_annulus ⊆ EMinus.source)
    (hActualMinus : (EMinus : Coord → Coord) = planarGradient CMinus.G)
    (hCMinus : ContDiffOn ℝ ∞ CMinus.G EMinus.source)
    (hnCMinus : ∀ p ∈ EMinus.source, (planarHessian CMinus.G p).det < 0)
    (hiMinus : ContDiffOn ℝ ∞ EMinus.symm EMinus.target)
    (hDMinusGamma : DMinus.incoming.gamma = seamComplexCoord ∘ corrugatedReverseReflect pMinus)
    (HMinus : Coord → ℝ) (UMinus : Set Coord) (SMinus MMinus S0Minus : ℝ)
    (hUMinus : IsOpen UMinus)
    (hUMinusFill : UMinus ⊆ dualRadialCompletionFillingDomain CMinus EMinus)
    (hHMinus : ContDiffOn ℝ ∞ HMinus (quadraticRadialFillingDomain RMinus UMinus))
    (hnHMinus : ∀ p ∈ quadraticRadialFillingDomain RMinus UMinus, (planarHessian HMinus p).det < 0)
    (hDiskMinus : {p : Coord | 0 < planarRadius p ∧ planarRadius p < SMinus} ⊆
      quadraticRadialFillingDomain RMinus UMinus)
    (hMMinus : 0 < MMinus) (hRS0Minus : RMinus < S0Minus) (hS0SMinus : S0Minus < SMinus)
    (hInnerMinus : ∀ p : Coord, 0 < planarRadius p → planarRadius p < RMinus/2 →
      HMinus =ᶠ[𝓝 p] dualRadialQuadraticPotential RMinus MMinus (-MMinus*RMinus^2/2))
    (UcMinus : Set Coord) (hUcMinus : IsOpen UcMinus) (hUcMinusU : UcMinus ⊆ UMinus)
    (hCircleMinus : quadraticRadialFillingRadiusLevel S0Minus ⊆ UcMinus)
    (hRetainedMinus : ∀ p ∈ UcMinus, HMinus =ᶠ[𝓝 p] planarLegendre CMinus.G EMinus)
    {RPlus etaPlus : ℝ} {DPlus : VisibleConnectorIncomingData G e0.source 1 RPlus}
    (CPlus : VisibleConnectorConstructionData DPlus etaPlus)
    (EPlus : OpenPartialHomeomorph Coord Coord)
    (hClosedPlus : closure CPlus.source_annulus ⊆ EPlus.source)
    (hDomainPlus : EPlus.source ⊆ CPlus.U)
    (hCPlus : ContDiffOn ℝ ∞ CPlus.G EPlus.source)
    (hnCPlus : ∀ p ∈ EPlus.source, (planarHessian CPlus.G p).det < 0)
    (hActualPlus : (EPlus : Coord → Coord) = planarGradient CPlus.G)
    (hiPlus : ContDiffOn ℝ ∞ EPlus.symm EPlus.target)
    (hAgreementPlus : EqOn EPlus.symm CPlus.gradient_chart.symm CPlus.gradient_annulus)
    (hDPlusP : DPlus.incoming.p = seamComplexCoord ∘ pPlus)
    (SPlus MPlus S0Plus : ℝ) (hRSPlus : RPlus < SPlus) (hMPlus : 0 < MPlus)
    (HPlus : Coord → ℝ) (eFPlus : OpenPartialHomeomorph Coord Coord)
    (GammaSPlus Gamma0Plus : ℂ ≃ₜ ℂ)
    (hHPlus : ContDiffOn ℝ ∞ HPlus {p | 0 < planarRadius p ∧ planarRadius p < SPlus})
    (hnHPlus : ∀ p, 0 < planarRadius p → planarRadius p < SPlus → (planarHessian HPlus p).det < 0)
    (hInnerPlus : ∀ p : Coord, 0 < planarRadius p → planarRadius p < RPlus/2 →
      HPlus =ᶠ[𝓝 p] dualRadialQuadraticPotential RPlus MPlus (-MPlus*RPlus^2/2))
    (heFPlusSource : eFPlus.source = {p | 0 < planarRadius p ∧ planarRadius p < SPlus})
    (heFPlusTarget : eFPlus.target = seamComplexCoord ''
      (ball (0 : ℂ) (MPlus*RPlus) \ GammaSPlus '' closedBall (0 : ℂ) 1))
    (hActualFPlus : (eFPlus : Coord → Coord) = planarGradient HPlus)
    (hGammaSPlus0 : (0 : ℂ) ∈ jordanInterior GammaSPlus)
    (hGammaSPlusDisk : GammaSPlus '' closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) (MPlus*RPlus))
    (hRS0Plus : RPlus < S0Plus) (hS0SPlus : S0Plus < SPlus)
    (UcPlus : Set Coord) (hUcPlus : IsOpen UcPlus)
    (hUcPlusRetained : UcPlus ⊆ dualRadialCompletionFillingDomain CPlus EPlus ∩ eFPlus.source)
    (hCirclePlus : quadraticRadialFillingRadiusLevel S0Plus ⊆ UcPlus)
    (hRetainedPlus : ∀ p ∈ UcPlus, HPlus =ᶠ[𝓝 p] planarLegendre CPlus.G EPlus)
    (hPositivePlus : ∀ p ∈ UcPlus, 0 < planarGradient (planarLegendre CPlus.G EPlus) p ⬝ᵥ p)
    (hRangePlus : range (quadraticRadialFillingGradientComplexTrace HPlus S0Plus) =
      Gamma0Plus '' sphere (0 : ℂ) 1) :
    ∃ (A RN mu B d0 dInfinity epsilon Lout : ℝ) (F : Coord → ℝ) (W : Set Coord)
      (e : OpenPartialHomeomorph Coord Coord),
      RN = MMinus*RMinus ∧ mu = MMinus ∧ d0 = -MMinus*RMinus^2/2 ∧
      0 < A ∧ A < RN ∧ 0 < mu ∧ 0 < B ∧ 0 < epsilon ∧ epsilon < Lout ∧
      ContDiffOn ℝ ∞ F {p | 0 < planarRadius p} ∧
      (∀ p, 0 < planarRadius p → (planarHessian F p).det < 0) ∧
      IsOpen W ∧ K ⊆ W ∧ W ⊆ e0.source ∧ W ⊆ {p | 0 < planarRadius p} ∧
      EqOn F G W ∧ (∀ p ∈ W, F =ᶠ[𝓝 p] G) ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        F p = RN*planarRadius p-mu*planarRadius p^2/2+d0) ∧
      (∀ p, Lout < planarRadius p → F p = A*planarRadius p-B/planarRadius p+dInfinity) ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        F =ᶠ[𝓝 p] (fun q => RN*planarRadius q-mu*planarRadius q^2/2+d0)) ∧
      (∀ p, Lout < planarRadius p →
        F =ᶠ[𝓝 p] (fun q => A*planarRadius q-B/planarRadius q+dInfinity)) ∧
      e.source = {p | 0 < planarRadius p} ∧
      e.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (∀ p ∈ e.source, e p = planarGradient F p) ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨RN,mu,Fi,Ui,Nin,hRN,hmu,hRNPos,hmuPos,hUi,_hUiPositive,hNin,hFrontIn,
      hNinSource,hCoverIn,hFi,hnFi,hEqIn,_hGermIn,hInner,_hInnerGerm⟩ :=
    exists_dualRadialCompletion_inner_filling e0 hG hnG heG hi0 CMinus EMinus
      hClosedMinus hActualMinus hCMinus hnCMinus hiMinus hpMinus hDMinusGamma
      hUMinus hUMinusFill hHMinus hnHMinus hDiskMinus hMMinus hRS0Minus hS0SMinus
      hInnerMinus hUcMinus hUcMinusU hCircleMinus hRetainedMinus
  have hOldPlusRange : range (positiveExitComplexTrace DPlus.incoming.p) = HpPlus '' sphere (0 : ℂ) 1 := by
    have he : positiveExitComplexTrace DPlus.incoming.p = pPlus := by
      rw [hDPlusP]
      funext s
      apply Complex.ext <;> rfl
    rw [he]
    exact dualRadialCompletion_positiveTrace_range hpPlus
  obtain ⟨a,B,Cneck,Fo,Uo,Nout,L0,ha,haRN,hB,hUo,hNout,hNoutSource,hFrontOut,
      hCoverOut,hFo,hnFo,hEqOut,_hGermOut,_hL0,hOuter,_hOuterGerm⟩ :=
    exists_dualRadialCompletion_outer_filling CPlus EPlus hClosedPlus hDomainPlus
      hCPlus hnCPlus hActualPlus hiPlus hAgreementPlus hRNPos hRSPlus hMPlus
      HPlus eFPlus GammaSPlus Gamma0Plus HpPlus hHPlus hnHPlus hInnerPlus
      heFPlusSource heFPlusTarget hActualFPlus hGammaSPlus0 hGammaSPlusDisk
      hRS0Plus hS0SPlus hUcPlus hUcPlusRetained hCirclePlus hRetainedPlus hPositivePlus
      hRangePlus hOldPlusRange
  let I := seamComplexCoord '' (HpMinus '' ball (0 : ℂ) 1)
  let O := seamComplexCoord '' (HpPlus '' ball (0 : ℂ) 1)
  have hI : IsOpen I := seamComplexCoord.isOpenMap _ (HpMinus.isOpenMap _ isOpen_ball)
  have hO : IsOpen O := seamComplexCoord.isOpenMap _ (HpPlus.isOpenMap _ isOpen_ball)
  have hClI : closure I = seamComplexCoord '' closure (HpMinus '' ball (0 : ℂ) 1) :=
    (seamComplexCoord.image_closure _).symm
  have hClO : closure O = seamComplexCoord '' closure (HpPlus '' ball (0 : ℂ) 1) :=
    (seamComplexCoord.image_closure _).symm
  have hIO : closure I ⊆ O := by rw [hClI]; exact image_mono hNested
  have h0I : (0 : Coord) ∈ I := by
    simpa only [map_zero] using mem_image_of_mem seamComplexCoord hOrigin
  have hCompactO : IsCompact (closure O) := by
    rw [hClO]
    exact (isCompact_closure_jordanInterior HpPlus).image seamComplexCoord.continuous
  have hBandCoord : closure O \ I ⊆ e0.source := by
    intro p hp
    rw [hClO] at hp
    obtain ⟨z,hz,rfl⟩ := hp.1
    apply hBand
    exact ⟨z,⟨hz,fun hzI => hp.2 ⟨z,hzI,rfl⟩⟩,rfl⟩
  have hKCoord : K ⊆ O \ closure I := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := hK hp
    refine ⟨⟨z,hz.1,rfl⟩,?_⟩
    rw [hClI]
    rintro ⟨w,hw,he⟩
    have hwz : w = z := seamComplexCoord.injective he
    exact hz.2 (hwz ▸ hw)
  have hRMinus : 0 < RMinus := DMinus.radius_pos
  have hInner' : EqOn Fi (fun p => RN*planarRadius p-mu*planarRadius p^2/2+(-MMinus*RMinus^2/2))
      {p | 0 < planarRadius p ∧ planarRadius p < RMinus/2} := by
    simpa only [sub_eq_add_neg, neg_mul, neg_div] using hInner
  have hOuter' : EqOn Fo (fun p => a*planarRadius p-B/planarRadius p+(-Cneck))
      {p | L0 < planarRadius p} := by
    simpa only [sub_eq_add_neg] using hOuter
  obtain ⟨epsilon,Lout,F,W,e,hEpsilon,hEL,hF,hnF,hW,hKW,hWSource,hWPos,hEq,hGerm,
      hIn,hOut,hInGerm,hOutGerm,heSource,heTarget,heGradient,hi⟩ :=
    exists_dualRadialCompletion_pair_assembly hDegree e0 hI hO hIO h0I hCompactO
      hBandCoord hG hnG hUi hUo hNin hNout hNinSource hNoutSource hFrontIn hFrontOut
      hCoverIn hCoverOut hFi hFo hnFi hnFo hEqIn hEqOut hKCompact hKCoord
      ha haRN hmuPos hB (half_pos hRMinus) hInner' hOuter'
  exact ⟨a,RN,mu,B,-MMinus*RMinus^2/2,-Cneck,epsilon,Lout,F,W,e,
    hRN,hmu,rfl,ha,haRN,hmuPos,hB,hEpsilon,hEL,hF,hnF,hW,hKW,hWSource,hWPos,
    hEq,hGerm,hIn,hOut,hInGerm,hOutGerm,heSource,heTarget,
    fun p _ => congrFun heGradient p,hi⟩

end
end TightVer401
