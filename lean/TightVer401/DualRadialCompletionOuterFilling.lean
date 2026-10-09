import TightVer401.DualRadialCompletionOuterBranch
import TightVer401.DualRadialCompletionFillingSeparation
import TightVer401.DualRadialCompletionNeckFilling
import TightVer401.DualRadialCompletionNeckTail

/-! Actual outer application of the same connector and filling witnesses.
The scalar neck, actual global neck inverse, retained contour recovery and
outgoing branch are constructed here from ordinary producer fields. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Complete the outgoing branch from the actual filling producer's SAME
potential, inverse and retained contour. No local-branch conclusion is an input. -/
theorem exists_dualRadialCompletion_outer_filling
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax RN S M S0 : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData Gin Uin L R}
    (C : VisibleConnectorConstructionData D etaMax)
    (eC : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (_hDomainC : eC.source ⊆ C.U)
    (hG : ContDiffOn ℝ ∞ C.G eC.source)
    (hnG : ∀ p ∈ eC.source, (planarHessian C.G p).det < 0)
    (hActualC : (eC : Coord → Coord) = planarGradient C.G)
    (hiC : ContDiffOn ℝ ∞ eC.symm eC.target)
    (hAgreement : EqOn eC.symm C.gradient_chart.symm C.gradient_annulus)
    (hRN : 0 < RN) (hRS : R < S) (hM : 0 < M)
    (H : Coord → ℝ) (eF : OpenPartialHomeomorph Coord Coord)
    (GammaS Gamma0 HOld : ℂ ≃ₜ ℂ)
    (hH : ContDiffOn ℝ ∞ H {p | 0 < planarRadius p ∧ planarRadius p < S})
    (hnH : ∀ p, 0 < planarRadius p → planarRadius p < S → (planarHessian H p).det < 0)
    (hHQuad : ∀ p : Coord, 0 < planarRadius p → planarRadius p < R/2 →
      H =ᶠ[𝓝 p] dualRadialQuadraticPotential R M (-M*R^2/2))
    (heFSource : eF.source = {p | 0 < planarRadius p ∧ planarRadius p < S})
    (heFTarget : eF.target = seamComplexCoord ''
      (ball (0 : ℂ) (M*R) \ GammaS '' closedBall (0 : ℂ) 1))
    (hActualF : (eF : Coord → Coord) = planarGradient H)
    (hGammaS0 : (0 : ℂ) ∈ jordanInterior GammaS)
    (hGammaDisk : GammaS '' closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) (M*R))
    (hS0 : R < S0) (_hS0S : S0 < S)
    {Uc : Set Coord} (hUc : IsOpen Uc)
    (hRetained : Uc ⊆ dualRadialCompletionFillingDomain C eC ∩ eF.source)
    (hCircle : quadraticRadialFillingRadiusLevel S0 ⊆ Uc)
    (hGerms : ∀ y ∈ Uc, H =ᶠ[𝓝 y] planarLegendre C.G eC)
    (hPositive : ∀ y ∈ Uc, 0 < planarGradient (planarLegendre C.G eC) y ⬝ᵥ y)
    (hRange : range (quadraticRadialFillingGradientComplexTrace H S0) = Gamma0 '' sphere (0 : ℂ) 1)
    (hOldRange : range (positiveExitComplexTrace D.incoming.p) = HOld '' sphere (0 : ℂ) 1) :
    ∃ (a B Cneck : ℝ) (Fo : Coord → ℝ) (Uo Nout : Set Coord) (Lout : ℝ),
      0 < a ∧ a < RN ∧ 0 < B ∧
      IsOpen Uo ∧ IsOpen Nout ∧ Nout ⊆ Uin ∧
      frontier (seamComplexCoord '' (HOld '' ball (0 : ℂ) 1)) ⊆ Nout ∧
      (((closure (seamComplexCoord '' (HOld '' ball (0 : ℂ) 1)))ᶜ ∩
        {p : Coord | 0 < planarRadius p}) ∪ Nout) ⊆ Uo ∧
      ContDiffOn ℝ ∞ Fo Uo ∧ (∀ p ∈ Uo, (planarHessian Fo p).det < 0) ∧
      EqOn Fo Gin Nout ∧ (∀ p ∈ Nout, Fo =ᶠ[𝓝 p] Gin) ∧
      0 < Lout ∧
      EqOn Fo (fun p => a*planarRadius p-B/planarRadius p-Cneck)
        {p | Lout < planarRadius p} ∧
      (∀ p, Lout < planarRadius p →
        Fo =ᶠ[𝓝 p] (fun q => a*planarRadius q-B/planarRadius q-Cneck)) := by
  have hR : 0 < R := D.radius_pos
  have hRS' : R/2 < S := by linarith
  have hQuad : EqOn H (dualRadialQuadraticPotential R M (-M*R^2/2))
      {p | 0 < planarRadius p ∧ planarRadius p < R/2} :=
    fun p hp => (hHQuad p hp.1 hp.2).eq_of_nhds
  obtain ⟨rho,hrho,hrhoR,hGap⟩ := exists_dualRadialCompletion_filling_separation hR hM GammaS hGammaDisk
  obtain ⟨a,B,Cneck,b,c,d,g,Fneck,ha,haRN,hac,hcd,hdb,hbrho,hB,
      hg,hSigns,hEscape,hgQuad,hFg,hFneck,hnFneck,hLiteralNeck,hFH⟩ :=
    exists_dualRadialCompletion_neck_filling_data hR hM hrho hrhoR
      (hrhoR.trans_lt hRS') hRN hH hnH hQuad
  have had : a < d := hac.trans hcd
  have hcb : c < b := hcd.trans hdb
  have hbR : b < R/2 := hbrho.trans_le hrhoR
  have hdR : d < R := (hdb.trans hbR).trans (by linarith)
  have hBoundB : ∀ z ∈ GammaS '' closedBall (0 : ℂ) 1, ‖z‖ < M*(R-b) := by
    intro z hz
    exact (hGap z hz).trans (mul_lt_mul_of_pos_left (sub_lt_sub_left hbrho R) hM)
  have hGammaClosed0 : (0 : ℂ) ∈ GammaS '' closedBall (0 : ℂ) 1 :=
    image_mono ball_subset_closedBall hGammaS0
  have heF : ∀ p ∈ eF.source, eF p = planarGradient H p := fun p _ => congrFun hActualF p
  have hFOld : EqOn Fneck H {p | d < planarRadius p ∧ planarRadius p < S} := fun _ hp => hFH hp.1
  obtain ⟨eN,heNSource,heNTarget,hActualN,hiN⟩ :=
    exists_dualRadialCompletionNeck_gradient_inverse hR hM ha had hdb hbR hRS'
      hg (fun r hr => (hSigns r hr).1) (fun r hr => (hSigns r hr).2) hEscape hgQuad
      hFg hFOld hQuad hFneck hnFneck GammaS hGammaClosed0 hBoundB
      eF heFSource heFTarget heF
  have hBoundMR : ∀ z ∈ GammaS '' closedBall (0 : ℂ) 1, ‖z‖ < M*R := by
    intro z hz
    simpa only [mem_ball,dist_zero_right] using hGammaDisk hz
  obtain ⟨T0,_hT0,_hHigh,hTailLiteral,_hTailGerm⟩ :=
    exists_dualRadialCompletionNeck_legendre_tail hR hM ha hac hcb hdb hB hg
      (fun r hr => (hSigns r hr).1) (fun r hr => (hSigns r hr).2)
      hFg hFOld hLiteralNeck GammaS hBoundMR eF heFSource heFTarget heF
      eN heNSource heNTarget hActualN
  have hFN : ContDiffOn ℝ ∞ Fneck eN.source := by rw [heNSource]; exact hFneck
  have heN : ∀ p ∈ eN.source, eN p = planarGradient Fneck p := fun p _ => congrFun hActualN p
  have hTail : ContDiffOn ℝ ∞ (planarLegendre Fneck eN) eN.target :=
    planarLegendre_contDiffOn eN hFN hiN
  have hnTail : ∀ p ∈ eN.target, (planarHessian (planarLegendre Fneck eN) p).det < 0 := by
    intro p hp
    have hq := eN.map_target hp
    rw [heNSource] at hq
    exact planarLegendre_saddle eN hFN hiN heN hp (hnFneck _ hq.1 hq.2)
  have hPunct : IsOpen {p : Coord | 0 < planarRadius p ∧ planarRadius p < S} :=
    isOpen_Ioo.preimage quadraticFillerCartesianGradient_radius_continuous
  have hRetainedFull : Uc ⊆ (dualRadialCompletionFillingDomain C eC ∩ eF.source) ∩
      {p : Coord | 0 < planarRadius p ∧ planarRadius p < S} := by
    intro p hp
    refine ⟨hRetained hp,?_⟩
    have hs := (hRetained hp).2
    rwa [heFSource] at hs
  have hTargetOutside : eF.target ⊆ (seamComplexCoord '' closure (jordanInterior GammaS))ᶜ := by
    intro p hp
    rw [heFTarget] at hp
    obtain ⟨z,hz,rfl⟩ := hp
    rintro ⟨w,hw,he⟩
    have hwz : w = z := seamComplexCoord.injective he
    apply hz.2
    rwa [closure_jordanInterior,hwz] at hw
  obtain ⟨_hGamma00,_hContourAnnulus,hOldNested,hGammaNested,hTerminalNested⟩ :=
    dualRadialCompletionRetainedContour_geometry C eC eF hClosed hActualC hG hiC hAgreement
      hPunct hH hActualF hUc hRetainedFull hS0 hCircle hGerms hPositive
      hOldRange hGammaS0 hTargetOutside hRange
  let Uc' := Uc ∩ {y : Coord | R < planarRadius y}
  have hUc' : IsOpen Uc' := hUc.inter
    (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous)
  have hCircle' : quadraticRadialFillingRadiusLevel S0 ⊆ Uc' := by
    intro y hy
    exact ⟨hCircle hy,by change R < planarRadius y; rw [show planarRadius y = S0 from hy]; exact hS0⟩
  have hUc'C : Uc' ⊆ eC.target := fun y hy => (hRetained hy.1).1.1
  have hUc'F : Uc' ⊆ eF.source := fun y hy => (hRetained hy.1).2
  have hUc'N : Uc' ⊆ eN.source := by
    intro y hy
    have hs := hUc'F hy
    rw [heFSource] at hs
    rw [heNSource]
    exact ⟨had.trans (hdR.trans hy.2),hs.2⟩
  have hEqNeckDual : EqOn Fneck (planarLegendre C.G eC) Uc' := by
    intro y hy
    exact (hFH (hdR.trans hy.2)).trans (hGerms y hy.1).eq_of_nhds
  have heC : ∀ p ∈ eC.source, eC p = planarGradient C.G p := fun p _ => congrFun hActualC p
  let V := eC.source ∩ (eC : Coord → Coord) ⁻¹' Uc'
  obtain ⟨hV,hVT,hRecovery,_hRecoveryGerm⟩ :=
    dualRadialCompletionNeck_legendre_recovery eC eN hG hiC heC hActualN
      hUc' hUc'C hUc'N hEqNeckDual
  have hRetainedInverse : EqOn (eF : Coord → Coord) eC.symm Uc' := by
    intro y hy
    calc
      eF y = planarGradient H y := congrFun hActualF y
      _ = planarGradient (planarLegendre C.G eC) y :=
        quadraticRadialFilling_gradient_eq_of_germ (hGerms y hy.1)
      _ = eC.symm y := planarLegendre_gradient eC hG hiC heC (hUc'C hy)
  obtain ⟨W,hW,hContourW,hWDomain,hWInverse⟩ :=
    dualRadialCompletionRetainedContour_inverse_neighborhood eC eF hUc'
      (fun y hy => ⟨hUc'C hy,hUc'F hy⟩) hCircle' (hR.trans hS0)
      hActualF hRetainedInverse hRange
  have hContourV : seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) ⊆ V := by
    intro p hp
    have hpW := hContourW hp
    exact ⟨(hWDomain hpW).2,by
      change eC p ∈ Uc'
      rw [← (hWInverse p hpW).2]
      exact (hWInverse p hpW).1⟩
  have hVC : V ⊆ eC.source := inter_subset_left
  obtain ⟨Fo,Uo,Nout,Lout,hUo,hNout,hNsource,hFront,hCover,hFo,hnFo,hEq,hEqGerm,hL,hEnd,hEndGerm⟩ :=
    exists_dualRadialCompletion_outer_branch C eC eN hClosed hG hnG hOldRange
      hOldNested hGammaNested hTerminalNested heNTarget hTail hnTail
      hV hContourV hVC hVT hRecovery (fun p hp => hTailLiteral p hp)
  exact ⟨a,B,Cneck,Fo,Uo,Nout,Lout,ha,haRN,hB,hUo,hNout,hNsource,hFront,hCover,
    hFo,hnFo,hEq,hEqGerm,hL,hEnd,hEndGerm⟩

end
end TightVer401
