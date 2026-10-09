import TightVer401.VisibleConnectorIncomingParametersFromData
import TightVer401.VisibleConnectorIncomingTerminalGinStability
import TightVer401.VisibleConnectorIncomingParametersGinChoice
import TightVer401.VisibleConnectorIncomingRebaseOriginalTrace

/-! Concrete retained incoming choices built only from original incoming D.
The angle is selected first, its literal Gin family and ONE native inverse are
fixed next, and ONE displacement follows all constructed thresholds. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Retained actual choices, not a premise granting a connector or smoothing. -/
structure VisibleConnectorIncomingParametersChoice {Gin : Coord → ℝ} {Uin : Set Coord}
    {L R : ℝ} [Fact (0 < L)] (D : VisibleConnectorIncomingData Gin Uin L R)
    (etaMax : ℝ) where
  theta : ℝ → ℝ
  theta_smooth : ContDiff ℝ ∞ theta
  theta_shift : ∀ s, theta (s + L) = theta s + 2 * Real.pi
  theta_positive : ∀ s, 0 < deriv theta s
  theta_actual : ∀ s, visibleConnectorTangentDirection R D.incoming.gamma s =
    visibleConnectorUnitDirection (theta s)
  etaAngle : ℝ
  eta_pos : 0 < etaAngle
  eta_small : etaAngle < etaMax
  w0 : ℝ → Coord
  w0_actual : w0 = visibleConnectorGinRotatedRuling R etaAngle D.incoming.gamma
  w0_smooth : ContDiff ℝ ∞ w0
  w0_periodic : Periodic w0 L
  w_periodic : ∀ rho, Periodic
    (fun s => visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0 (rho, s)) L
  e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord)
  e_actual : (e : (ℝ × (AddCircle L × ℝ)) → ℝ × Coord) =
    visibleConnectorDisplacedNativePsi D.incoming.p_periodic w0_periodic w_periodic
  e_inverse_local : ∀ y ∈ e.target, ∃ s : ℝ,
    ∃ chart : OpenPartialHomeomorph (ℝ × Coord) (ℝ × Coord),
    ContDiffOn ℝ ∞ chart.symm chart.target ∧
    ∃ B : Set (ℝ × Coord), IsOpen B ∧ y ∈ B ∧ B ⊆ e.target ∧ B ⊆ chart.target ∧
      (∀ v ∈ B, e.symm v = visibleConnectorDisplacedNativeChart L s (chart.symm v))
  e_central : ∀ s, (0, D.incoming.p s) ∈ e.target ∧
    visibleConnectorDisplacedNativeSolution e D.incoming.p (0, s) = (periodProjection L s, 0)
  e_zero_source : ∀ q : AddCircle L, (0, (q, 0)) ∈ e.source
  phase_domain_open : IsOpen (visibleConnectorDisplacedRealPhaseDomain e D.incoming.p)
  phase_smooth : ContDiffOn ℝ ∞ (visibleConnectorDisplacedRealPhase e D.incoming.p)
    (visibleConnectorDisplacedRealPhaseDomain e D.incoming.p)
  height_smooth : ContDiffOn ℝ ∞
    (fun z => (visibleConnectorDisplacedNativeSolution e D.incoming.p z).2)
    (visibleConnectorDisplacedRealPhaseDomain e D.incoming.p)
  phase_shift : ∀ rho s, visibleConnectorDisplacedRealPhase e D.incoming.p (rho, s + L) =
    visibleConnectorDisplacedRealPhase e D.incoming.p (rho, s) + L
  height_periodic : ∀ rho, Periodic
    (fun s => (visibleConnectorDisplacedNativeSolution e D.incoming.p (rho, s)).2) L
  phase_zero : ∀ s, visibleConnectorDisplacedRealPhase e D.incoming.p (0, s) = s
  height_zero : ∀ s, (visibleConnectorDisplacedNativeSolution e D.incoming.p (0, s)).2 = 0
  rhoDomain : ℝ
  rhoDomain_pos : 0 < rhoDomain
  native_strip : Icc (-rhoDomain) rhoDomain ×ˢ (univ : Set ℝ) ⊆
    visibleConnectorDisplacedRealPhaseDomain e D.incoming.p
  rho : ℝ
  rho_pos : 0 < rho
  rho_small : rho < rhoDomain
  chosen_domain : ∀ s, (rho, s) ∈ visibleConnectorDisplacedRealPhaseDomain e D.incoming.p
  phase_positive : ∀ s, 0 < deriv
    (fun t => visibleConnectorDisplacedRealPhase e D.incoming.p (rho, t)) s
  height_negative : ∀ s, (visibleConnectorDisplacedNativeSolution e D.incoming.p (rho, s)).2 < 0
  height_small : ∀ s, |(visibleConnectorDisplacedNativeSolution e D.incoming.p (rho, s)).2| < 1
  phase_homeomorph : ℝ ≃ₜ ℝ
  phase_actual : (phase_homeomorph : ℝ → ℝ) =
    (fun s => visibleConnectorDisplacedRealPhase e D.incoming.p (rho, s))
  phase_inverse_smooth : ContDiff ℝ ∞ phase_homeomorph.symm
  phase_inverse_shift : ∀ s, phase_homeomorph.symm (s + L) = phase_homeomorph.symm s + L
  coefficients_positive : let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p w0 (rho, s)
    let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p w0 (rho, s)
    let wc := fun s => visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0 (rho, s)
    ∀ s, 0 < visibleConnectorA pc wc s ∧ 0 < visibleConnectorB gc wc s ∧
      0 < visibleConnectorC gc wc s
  lower_delta_positive : let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p w0 (rho, s)
    let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p w0 (rho, s)
    let wc := fun s => visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0 (rho, s)
    ∀ s, 0 < visibleConnectorDelta pc gc wc
      (![visibleConnectorDisplacedRealPhase e D.incoming.p (rho, s),
        (visibleConnectorDisplacedNativeSolution e D.incoming.p (rho, s)).2] : Coord)
  lower_strip_in_GinU : ∀ s u,
    (visibleConnectorDisplacedNativeSolution e D.incoming.p (rho, s)).2 ≤ u → u ≤ 0 →
    visibleConnectorGinDisplacedPosition D.incoming.p w0
      (rho, visibleConnectorDisplacedRealPhase e D.incoming.p (rho, s)) +
    u • visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0
      (rho, visibleConnectorDisplacedRealPhase e D.incoming.p (rho, s)) ∈ Uin
  original_trace : ∀ s, visibleConnectorRebasedSource
    (fun t => visibleConnectorGinDisplacedPosition D.incoming.p w0 (rho, t))
    (fun t => visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0 (rho, t))
    (fun t => visibleConnectorDisplacedRealPhase e D.incoming.p (rho, t))
    (fun t => (visibleConnectorDisplacedNativeSolution e D.incoming.p (rho, t)).2) s = D.incoming.p s
  family_domain : ∀ s, (rho, s) ∈
    visibleConnectorGinDisplacedVisibilityDomain Gin Uin R D.incoming.p w0
  normBudget : ℝ
  original_norm_bounded : ∀ s, ‖positiveExitComplexTrace D.incoming.p s‖ < normBudget
  terminal_geometry :
    let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p w0 (rho, s)
    let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p w0 (rho, s)
    let wc := fun s => visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0 (rho, s)
    let T := visibleConnectorActualTerminalSource pc gc wc
    ContDiff ℝ ∞ T ∧ Periodic T L ∧
    (∀ s, normBudget < ‖positiveExitComplexTrace T s‖) ∧
    (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
    InjOn T (Ico (0 : ℝ) L) ∧ ∃ H : ℂ ≃ₜ ℂ,
      DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
      (0 : ℂ) ∈ jordanInterior H ∧
      range (positiveExitComplexTrace T) = frontier (jordanInterior H)


/-- The original incoming trace constructs a full-period escape budget. -/
private theorem incomingParametersChoice_norm_budget
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) :
    ∃ M : ℝ, ∀ s, ‖positiveExitComplexTrace D.incoming.p s‖ < M := by
  have heq : positiveExitComplexPoint = angularDescentComplex := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have htrace : Continuous (positiveExitComplexTrace D.incoming.p) := by
    change Continuous (positiveExitComplexPoint ∘ D.incoming.p)
    rw [heq]
    exact angularDescentComplex_contDiff.continuous.comp D.incoming.p_smooth.continuous
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.out.le⟩) htrace.norm.continuousOn
  refine ⟨‖positiveExitComplexTrace D.incoming.p s0‖ + 1, ?_⟩
  intro s
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL.out s 0
  simp only [mem_Ico, zero_add] at hn
  have hh := hmax (show s - n • L ∈ Icc (0 : ℝ) L from ⟨hn.1, hn.2.le⟩)
  have hp : Periodic (positiveExitComplexTrace D.incoming.p) L := by
    intro t
    exact congrArg positiveExitComplexPoint (D.incoming.p_periodic t)
  change ‖positiveExitComplexTrace D.incoming.p (s - n • L)‖ ≤
    ‖positiveExitComplexTrace D.incoming.p s0‖ at hh
  rw [hp.sub_zsmul_eq n] at hh
  linarith

/-- Construct every retained choice from original incoming D alone. -/
theorem visibleConnectorIncomingParametersChoice_nonempty
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (hetaMax : 0 < etaMax) :
    Nonempty (VisibleConnectorIncomingParametersChoice D etaMax) := by
  obtain ⟨M, hM⟩ := incomingParametersChoice_norm_budget D
  obtain ⟨theta, ht, hshift, htpos, hdir, etaAngle, heta, hetamax,
      hwactual, hw, hw0L, hcoeff, hgamma, hmargin, hTs, hTp, hTne, hTdet,
      hTturn, hTi, hTj, hnorm, hTr, H0, hH0, hHorigin, hHfront⟩ :=
    visibleConnectorIncomingParameters_exists_original_choice_from_data (M := M) D hetaMax
  let w0 := visibleConnectorShiftedRuling R D.incoming.gamma theta etaAngle
  let w := visibleConnectorGinDisplacedRuling Gin R etaAngle D.incoming.p w0
  have hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R etaAngle D.incoming.gamma s :=
    fun s => congrFun hwactual s
  obtain ⟨hpc, hDU, hgc, hV, hVsub, hVaxis, hW, hpcL, hgcL, hWL, hVperiod, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties D.radius_pos D.domain_open D.potential_smooth
      D.incoming.p_smooth hw D.incoming.p_periodic hw0L
      (fun s => D.incoming.p_in_domain (mem_univ s)) hgamma hmargin hw0same
  have hdet : ∀ s, visibleConnectorDet (deriv D.incoming.p s) (w0 s) ≠ 0 := by
    intro s
    have h := (hcoeff s).1.ne'
    change -visibleConnectorDet (deriv D.incoming.p s) (w0 s) ≠ 0 at h
    exact neg_ne_zero.mp h
  obtain ⟨e, hef, hLocal, hCentral, hSource, hD, ha, hb, hashift, hbL, ha0, hb0,
      rhoDomain, hrhoDomain, phase, hphase, hphaseLe, hstrip,
      hphaseSigns, hbNeg, hphaseHomeo, hsourceEq⟩ :=
    visibleConnectorDisplaced_exists_uniform_phase_signs D.incoming.p_smooth hw
      D.incoming.p_periodic hw0L hWL D.incoming.source_injective hV hW hVaxis hW0 hdet
  have haxis (s : ℝ) : (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e D.incoming.p :=
    hstrip ⟨⟨by linarith, by linarith⟩, mem_univ s⟩
  obtain ⟨terminalBound, hterminalBound, hterminal⟩ :=
    visibleConnectorIncomingTerminal_Gin_exists_positive_filling (M := M)
      D hw hw0L hw0same (fun s => (hcoeff s).2.2)
      (fun s _ => hnorm s) (fun s _ => hTdet s) hTne hTturn
  obtain ⟨rho, hrho, hrhoPhase, hrhoTerminal, hcurrent, hlowerDelta, hlowerStrip, hheight⟩ :=
    visibleConnectorIncomingParameters_exists_Gin_compatible_rho
      D.radius_pos D.domain_open D.potential_smooth D.incoming.p_smooth hw
      D.incoming.p_periodic hw0L (fun s => D.incoming.p_in_domain (mem_univ s))
      hgamma hmargin hw0same hcoeff e hD ha hb haxis ha0 hb0 hashift hbL
      hphase hterminalBound (show (0 : ℝ) < 1 by norm_num)
  have habsPhase : |rho| < phase := by simpa only [abs_of_pos hrho] using hrhoPhase
  have habsTerminal : |rho| < terminalBound := by
    simpa only [abs_of_pos hrho] using hrhoTerminal
  have hrhoDomainLt : rho < rhoDomain := hrhoPhase.trans_le hphaseLe
  have hchosen (s : ℝ) : (rho, s) ∈ visibleConnectorDisplacedRealPhaseDomain e D.incoming.p :=
    hstrip ⟨⟨by linarith, hrhoDomainLt.le⟩, mem_univ s⟩
  obtain ⟨A, hA, hAs, hAsh⟩ := hphaseHomeo rho habsPhase
  obtain ⟨hfamilyDomain, hchosenC, hterminalSmooth, hterminalPeriod,
    hterminalNorm, hterminalDet, hterminalInj, H, hpositive, h0, hfront⟩ :=
    hterminal rho habsTerminal
  refine ⟨{
    theta := theta
    theta_smooth := ht
    theta_shift := hshift
    theta_positive := htpos
    theta_actual := hdir
    etaAngle := etaAngle
    eta_pos := heta
    eta_small := hetamax
    w0 := w0
    w0_actual := hwactual
    w0_smooth := hw
    w0_periodic := hw0L
    w_periodic := hWL
    e := e
    e_actual := hef
    e_inverse_local := hLocal
    e_central := hCentral
    e_zero_source := hSource
    phase_domain_open := hD
    phase_smooth := ha
    height_smooth := hb
    phase_shift := hashift
    height_periodic := hbL
    phase_zero := ha0
    height_zero := hb0
    rhoDomain := rhoDomain
    rhoDomain_pos := hrhoDomain
    native_strip := hstrip
    rho := rho
    rho_pos := hrho
    rho_small := hrhoDomainLt
    chosen_domain := hchosen
    phase_positive := fun s => (hphaseSigns rho s habsPhase).1
    height_negative := fun s => hbNeg rho s hrho hrhoPhase
    height_small := hheight
    phase_homeomorph := A
    phase_actual := hA
    phase_inverse_smooth := hAs
    phase_inverse_shift := hAsh
    coefficients_positive := hcurrent
    lower_delta_positive := hlowerDelta
    lower_strip_in_GinU := hlowerStrip
    original_trace := ?_
    family_domain := hfamilyDomain
    normBudget := M
    original_norm_bounded := hM
    terminal_geometry := ?_ }⟩
  · intro s
    exact visibleConnectorIncomingRebase_original_trace D.incoming.p_periodic hw0L hWL
      e hef rho s (hchosen s)
  · exact ⟨hterminalSmooth, hterminalPeriod, hterminalNorm, hterminalDet,
      hterminalInj, H, hpositive, h0, hfront⟩

end
end TightVer401
