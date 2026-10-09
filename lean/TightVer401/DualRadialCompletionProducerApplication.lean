import TightVer401.DualRadialCompletionContract
import TightVer401.DualRadialCompletionConnectorInputs
import TightVer401.DualRadialCompletionConnectorCollar
import TightVer401.DualRadialCompletionFillingInputs
import TightVer401.DualRadialCompletionBranchesAssembly
import TightVer401.QuadraticRadialFillingGlobalTrimmed

/-! Pending caller connection. This file stays outside the audited root until
its genuine producer dependencies are frozen and checked locally. The visible
connector obligation remains explicit; no full completion credit is claimed. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix RealInnerProductSpace
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- Ordinary original data construct the two SAME connector inputs, their
actual collars, and both SAME retained fillings before the final scalar
assembly. The three original producer obligations remain explicit. -/
theorem dualRadialCompletionClaim_of_producers
    (hConnector : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R), VisibleConnectorConstructionStatement D)
    (hFilling : QuadraticRadialFillingGlobalGradientTrimmedClaim)
    (hDegree : DualRadialCompletionCircularDegreeClaim) : DualRadialCompletionClaim := by
  intro G e0 HpPlus HpMinus HgPlus HgMinus pPlus pMinus gammaPlus gammaMinus RPlus RMinus K
    hG hnG heG hi0 hpPlus hpMinus hgPlus hgMinus hSourceNested hGradientNested
    hpMinus0 hgPlus0 hBand hActualPlus hActualMinus hPairPlus hPairMinus
    hRPlus hRMinus hVisPlus hVisMinus hKCompact hK
  obtain ⟨DPlus,DMinus,hDPlusP,_hDPlusGamma,_hDMinusP,hDMinusGamma⟩ :=
    exists_dualRadialCompletionConnectorInputs e0 hG hnG heG hi0 hpPlus hpMinus hgPlus hgMinus
      hSourceNested hGradientNested hpMinus0 hgPlus0 hBand hActualPlus hActualMinus
      hPairPlus hPairMinus hRPlus hRMinus hVisPlus hVisMinus
  obtain ⟨CMinus⟩ := (hConnector _ _ _ DMinus) 1 (by norm_num)
  obtain ⟨CPlus⟩ := (hConnector _ _ _ DPlus) 1 (by norm_num)
  obtain ⟨EMinus,hClosedMinus,_hDomainMinus,hCMinus,hnCMinus,hActualMinusC,hiMinus,
    _hAnnulusMinus,_hAgreementMinus⟩ := exists_dualRadialCompletion_connector_collar CMinus
  obtain ⟨EPlus,hClosedPlus,hDomainPlus,hCPlus,hnCPlus,hActualPlusC,hiPlus,
    _hAnnulusPlus,hAgreementPlus⟩ := exists_dualRadialCompletion_connector_collar CPlus
  obtain ⟨UMinus,hUMinus,hUMinusFill,hCircleUMinus,hFMinus,hnFMinus,
    _hPositiveMinus,hRadialMinus,hTangentialMinus,hJordanMinus⟩ :=
    exists_dualRadialCompletion_filling_inputs CMinus EMinus hClosedMinus
      hCMinus hnCMinus hActualMinusC hiMinus
  obtain ⟨UPlus,hUPlus,hUPlusFill,hCircleUPlus,hFPlus,hnFPlus,
    hPositivePlus,hRadialPlus,hTangentialPlus,hJordanPlus⟩ :=
    exists_dualRadialCompletion_filling_inputs CPlus EPlus hClosedPlus
      hCPlus hnCPlus hActualPlusC hiPlus
  obtain ⟨SMinus,MMinus,HMinus,GammaSMinus,eFMinus,_hRSMinus,_hM0Minus,hMMinus,
    hHMinus,hnHMinus,hDiskMinus,_hExteriorMinus,hInnerMinus,_hOuterMinus,
    _hTraceMinus,_hOriginMinus,_hNestedMinus,_hSourceMinus,_hTargetMinus,
    _hActualFMinus,_hiFMinus,hRetainedMinusPacket⟩ :=
    hFilling RMinus hRMinus (planarLegendre CMinus.G EMinus) UMinus UMinus
      hUMinus hUMinus hCircleUMinus hCircleUMinus hFMinus hnFMinus
      hRadialMinus hTangentialMinus hJordanMinus 0 1 (by norm_num)
  obtain ⟨SPlus,MPlus,HPlus,GammaSPlus,eFPlus,hRSPlus,_hM0Plus,hMPlus,
    hHPlus,hnHPlus,hDiskPlus,_hExteriorPlus,hInnerPlus,_hOuterPlus,
    _hTracePlus,hOriginPlus,hNestedPlus,hSourcePlus,hTargetPlus,
    hActualFPlus,_hiFPlus,hRetainedPlusPacket⟩ :=
    hFilling RPlus hRPlus (planarLegendre CPlus.G EPlus) UPlus UPlus
      hUPlus hUPlus hCircleUPlus hCircleUPlus hFPlus hnFPlus
      hRadialPlus hTangentialPlus hJordanPlus 0 1 (by norm_num)
  obtain ⟨S0Minus,deltaMinus,Gamma0Minus,hRS0Minus,hS0SMinus,hDeltaMinus,hUcMinus,
    hUcMinusSub,_hScalarMinus,hRetainedMinus,_hGradientMinus,_hRangeMinus,
    _hOriginalNestedMinus,_hRetainedBoundMinus,_hRetainedOriginMinus⟩ := hRetainedMinusPacket
  obtain ⟨S0Plus,deltaPlus,Gamma0Plus,hRS0Plus,hS0SPlus,hDeltaPlus,hUcPlus,
    hUcPlusSub,_hScalarPlus,hRetainedPlus,_hGradientPlus,hRangePlus,
    _hOriginalNestedPlus,_hRetainedBoundPlus,_hRetainedOriginPlus⟩ := hRetainedPlusPacket
  let UcMinus := quadraticRadialFillingRetainedCollar S0Minus deltaMinus
  let UcPlus := quadraticRadialFillingRetainedCollar S0Plus deltaPlus
  have hUcMinusU : UcMinus ⊆ UMinus := fun p hp => (hUcMinusSub hp).1.1
  have hCircleMinus : quadraticRadialFillingRadiusLevel S0Minus ⊆ UcMinus := by
    intro p hp
    change |planarRadius p-S0Minus| < deltaMinus
    rw [show planarRadius p = S0Minus from hp,sub_self,abs_zero]
    exact hDeltaMinus
  have hUcPlusRetained : UcPlus ⊆ dualRadialCompletionFillingDomain CPlus EPlus ∩ eFPlus.source := by
    intro p hp
    exact ⟨hUPlusFill (hUcPlusSub hp).1.1,(hUcPlusSub hp).2⟩
  have hCirclePlus : quadraticRadialFillingRadiusLevel S0Plus ⊆ UcPlus := by
    intro p hp
    change |planarRadius p-S0Plus| < deltaPlus
    rw [show planarRadius p = S0Plus from hp,sub_self,abs_zero]
    exact hDeltaPlus
  have hUcPositivePlus : ∀ p ∈ UcPlus,
      0 < planarGradient (planarLegendre CPlus.G EPlus) p ⬝ᵥ p :=
    fun p hp => hPositivePlus p (hUcPlusSub hp).1.1
  have hHPlusDisk : ContDiffOn ℝ ∞ HPlus {p | 0 < planarRadius p ∧ planarRadius p < SPlus} :=
    hHPlus.mono hDiskPlus
  have hnHPlusDisk : ∀ p, 0 < planarRadius p → planarRadius p < SPlus →
      (planarHessian HPlus p).det < 0 := fun p hp hr => hnHPlus p (hDiskPlus ⟨hp,hr⟩)
  have hSourcePlusExact : eFPlus.source = {p | 0 < planarRadius p ∧ planarRadius p < SPlus} := by
    simpa only [quadraticRadialFillingPuncturedDisk] using hSourcePlus
  have hTargetPlusExact : eFPlus.target = seamComplexCoord ''
      (ball (0 : ℂ) (MPlus*RPlus) \ GammaSPlus '' closedBall (0 : ℂ) 1) := by
    simpa only [quadraticRadialFillingGlobalGradientTarget] using hTargetPlus
  obtain ⟨A,RN,mu,B,d0,dInfinity,epsilon,Lout,F,W,e,_hRN,_hmu,_hd0,
    hA,hARN,hmu,hB,hEpsilon,hEL,hF,hnF,hW,hKW,hWSource,hWPositive,hEq,_hGerm,
    hInner,hOuter,_hInnerGerm,_hOuterGerm,heSource,heTarget,heActual,hi⟩ :=
    exists_dualRadialCompletion_branches_assembly hDegree e0 HpMinus HpPlus pMinus pPlus K
      hG hnG heG hi0 hpMinus hpPlus hSourceNested hpMinus0 hBand hKCompact hK
      CMinus EMinus hClosedMinus hActualMinusC hCMinus hnCMinus hiMinus hDMinusGamma
      HMinus UMinus SMinus MMinus S0Minus hUMinus hUMinusFill hHMinus hnHMinus hDiskMinus
      hMMinus hRS0Minus hS0SMinus hInnerMinus UcMinus hUcMinus hUcMinusU hCircleMinus hRetainedMinus
      CPlus EPlus hClosedPlus hDomainPlus hCPlus hnCPlus hActualPlusC hiPlus hAgreementPlus hDPlusP
      SPlus MPlus S0Plus hRSPlus hMPlus HPlus eFPlus GammaSPlus Gamma0Plus
      hHPlusDisk hnHPlusDisk hInnerPlus hSourcePlusExact hTargetPlusExact hActualFPlus
      hOriginPlus hNestedPlus hRS0Plus hS0SPlus UcPlus hUcPlus hUcPlusRetained
      hCirclePlus hRetainedPlus hUcPositivePlus hRangePlus
  exact ⟨A,RN,mu,B,d0,dInfinity,epsilon,Lout,F,W,e,hA,hARN,hmu,hB,hEpsilon,hEL,
    hF,hnF,hW,hKW,hWSource,hWPositive,hEq,hInner,hOuter,heSource,heTarget,heActual,hi⟩

end
end TightVer401
