import TightVer401.VisibleConnectorOrdinaryFamilyFromIncomingScalar
import TightVer401.VisibleConnectorOrdinaryFamilyActualChoiceTurn
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedGradientCircle
import TightVer401.VisibleConnectorOrdinaryFamilyTerminalJets
import TightVer401.VisibleConnectorOrdinaryFamilySourceClosure
import TightVer401.VisibleConnectorOrdinaryFamilyGradientEnclosure

/-! Packing the actual D-only scalar and SAME selected terminal into ordinary
data. Native choice C, Cartesian E and final H are each selected once. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem incomingAssembly_regular_of_det {f : ℝ → Coord}
    (hdet : ∀ s, 0 < visibleConnectorDet (f s) (deriv f s)) :
    ∀ s, deriv f s ≠ 0 := by
  intro s hz
  have h := hdet s
  rw [hz] at h
  simpa [visibleConnectorDet] using h

private theorem incomingAssembly_nonzero_of_complex {f : ℝ → Coord}
    (hne : ∀ s, positiveExitComplexTrace f s ≠ 0) : ∀ s, f s ≠ 0 := by
  intro s hs
  apply hne s
  simp [positiveExitComplexTrace, hs, positiveExitComplexPoint]
  apply Complex.ext <;> rfl

/-- Original incoming D alone populates actual universal ordinary data. -/
theorem visibleConnectorOrdinaryFamily_nonempty_from_incoming
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (hetaMax : 0 < etaMax) :
    Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax) := by
  obtain ⟨C, Ho, Hi, hInner, hPositive, hOrigin, hInnerOrigin, hFrontier,
    e0, E, Hband, raw, Uraw, hRaw, hOriginal, hBandEq, hScalar⟩ :=
    visibleConnectorOrdinaryFamily_exists_scalar_from_incoming D hetaMax
  let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
  let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
  let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
  let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
  let b := fun s => (visibleConnectorDisplacedNativeSolution C.e D.incoming.p (C.rho, s)).2
  let tc := visibleConnectorActualTerminalHeight pc gc wc
  let d := fun s => tc (a s) - b s
  let P := visibleConnectorRebasedSource pc wc a b
  let W := visibleConnectorRebasedRuling wc a d
  let Gamma := visibleConnectorRebasedGradient pc gc wc a b
  let T := visibleConnectorActualTerminalSource pc gc wc
  let Ta := fun s => T (a s)
  let Y := fun s => visibleConnectorGradient pc gc wc ![s, tc s]
  let Ya := fun s => Y (a s)
  let F := visibleConnectorCartesianSource L P W (fun _ => 1)
  let V := visibleConnectorFinalSmoothingCarrier Uraw Uin (visibleConnectorFinalSmoothingHeight L b d E)
  obtain ⟨H, Oin, Ot, hV, hVE, hAnnV, hBandV, hH, hNeg, hClosedNeg,
    hHeight, hIn, hOt, hClose⟩ := hScalar 1 zero_lt_one
  change VisibleConnectorOrdinaryFamilyIncomingRawFields L pc gc wc (Gin ∘ pc) a b
    Ho Hi e0 E Hband raw Uraw at hRaw
  rcases hRaw with ⟨h0s, h0t, h0actual, h0inv, hHband, hImage, hclosed, hEs,
    hF, hJac, hE, hi, hAnnE, hInvEq, hrawDef, hUraw, hAnnU, hUE,
    hrawSmooth, hrawNeg, hMap, hVal, hGrad, hAction, hDet, hJets⟩
  have hgamma0 (s : ℝ) : D.incoming.gamma s = planarGradient Gin (D.incoming.p s) :=
    congrFun D.incoming.actual_gradient s
  have hcomplex : positiveExitComplexPoint = angularDescentComplex := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have hvis := D.visibility
  rw [D.actual_delta] at hvis
  have hmargin (s : ℝ) : R < ‖Complex.I * angularDescentComplex (D.incoming.gamma s)‖ := by
    simpa only [hcomplex] using (hvis s).1
  obtain ⟨hpcJoint, hDU, hgcJoint, hVF, hVsub, _haxis, hwJoint,
      hpcL, hgcL, hwL, _hPeriod, _hgc0, _hw0⟩ :=
    visibleConnectorGinDisplacedFamily_properties D.radius_pos D.domain_open D.potential_smooth
      D.incoming.p_smooth C.w0_smooth D.incoming.p_periodic C.w0_periodic
      (fun s => D.incoming.p_in_domain (mem_univ s)) hgamma0 hmargin
      (fun s => congrFun C.w0_actual s)
  have hslice : ContDiff ℝ ∞ (fun s : ℝ => (C.rho, s)) := contDiff_const.prodMk contDiff_id
  have hpc : ContDiff ℝ ∞ pc := hpcJoint.comp hslice
  have hgc : ContDiff ℝ ∞ gc := contDiffOn_univ.mp
    (hgcJoint.comp hslice.contDiffOn (fun s _ => hVsub (C.family_domain s)))
  have hwc : ContDiff ℝ ∞ wc := contDiffOn_univ.mp
    (hwJoint.comp hslice.contDiffOn (fun s _ => C.family_domain s))
  have hpcU : ∀ s, pc s ∈ Uin := fun s => (C.family_domain s).1
  have hg : ContDiff ℝ ∞ (Gin ∘ pc) := contDiffOn_univ.mp
    (D.potential_smooth.comp hpc.contDiffOn (fun s _ => hpcU s))
  have ha : ContDiff ℝ ∞ a := contDiffOn_univ.mp
    (C.phase_smooth.comp hslice.contDiffOn (fun s _ => C.chosen_domain s))
  have hb : ContDiff ℝ ∞ b := contDiffOn_univ.mp
    (C.height_smooth.comp hslice.contDiffOn (fun s _ => C.chosen_domain s))
  have hvalue (s : ℝ) : deriv (Gin ∘ pc) s = gc s ⬝ᵥ deriv pc s :=
    visibleConnectorIncomingSeam_trace_deriv D.domain_open D.potential_smooth hpc hpcU s
  obtain ⟨htc, htcL, htcpos, hd, hdL, hdpos, hUpper,
      hP, hf, hW, hGamma, hPL, hfL, hWL, hGammaL, hval, hANew, hBNew, hDelta, hOut⟩ :=
    visibleConnectorOrdinaryFamilyRebasedCoefficients_actual hpc hgc hwc hg ha hb
      (hpcL C.rho) (hgcL C.rho) (hwL C.rho) ((hpcL C.rho).comp Gin)
      (C.phase_shift C.rho) (C.height_periodic C.rho) C.phase_positive C.height_negative
      (fun s => (C.coefficients_positive s).1)
      (fun s => (C.coefficients_positive s).2.1)
      (fun s => (C.coefficients_positive s).2.2) C.lower_delta_positive hvalue
  have hEndpoint (s : ℝ) : P s + W s = Ta s := hOut s
  have hclock (s : ℝ) : visibleConnectorPhysicalParameter L (2 * Real.pi * s / L) = s := by
    unfold visibleConnectorPhysicalParameter
    field_simp [hL.out.ne', Real.two_pi_pos.ne']
  have hIncoming (s : ℝ) : F (saddlePolarChart ![1, 2 * Real.pi * s / L]) = D.incoming.p s := by
    dsimp only [F]
    rw [visibleConnectorCartesianSource_polar hPL hWL (fun _ => rfl) (by norm_num)]
    simpa [visibleConnectorPolarSource, hclock] using hOriginal s
  have hTerminal (s : ℝ) : F (saddlePolarChart ![2, 2 * Real.pi * s / L]) = Ta s := by
    dsimp only [F]
    rw [visibleConnectorCartesianSource_polar hPL hWL (fun _ => rfl) (by norm_num)]
    simp only [visibleConnectorPolarSource, Matrix.cons_val_zero, Matrix.cons_val_one,
      hclock, mul_one]
    change P s + ((2 : ℝ) - 1) • W s = Ta s
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, one_smul] using hEndpoint s
  obtain ⟨hT, hTL, hTnorm, hTdet, hTi, _HT, _hHT, _hHT0, _hHTFront⟩ := C.terminal_geometry
  have hBudget : 0 < C.normBudget := lt_of_le_of_lt (norm_nonneg _) (C.original_norm_bounded 0)
  have hTne (s : ℝ) : positiveExitComplexTrace T s ≠ 0 := by
    intro hz
    have hn := hTnorm s
    rw [hz, norm_zero] at hn
    exact (not_lt_of_ge hBudget.le) hn
  have hTurnNormalized := dualRadialCompletion_positiveTrace_turn hPositive hOrigin
  have hTturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L := by
    obtain ⟨phi, hphi, hproj, hinc⟩ := hTurnNormalized
    refine ⟨fun s => phi (s / L), hphi.comp (continuous_id.div_const L), ?_, ?_⟩
    · intro s
      have he : L * (s / L) = s := by field_simp [hL.out.ne']
      simpa only [visibleConnectorTerminalNormalizedTrace, he] using hproj (s / L)
    · simpa only [div_self hL.out.ne', zero_div] using hinc
  obtain ⟨hTa, hTaL, hTai, hTane, hTadet, hTaturn, hTarange⟩ :=
    visibleConnectorOrdinaryFamily_rebased_terminal_fields hL.out hT ha hTL hTi
      hTne hTdet hTturn C.phase_positive (C.phase_shift C.rho)
  obtain ⟨hOuterNormalized, _, _⟩ := visibleConnectorOrdinaryFamily_rebased_same_positive_jordan
    hL.out Ho hT ha hTL hTi hTne hTdet hTturn C.phase_positive
      (C.phase_shift C.rho) hFrontier hOrigin
  have hOuter : PositiveJordanParametrization Ho (fun t => seamComplexCoord.symm (Ta (L*t))) := by
    have he : visibleConnectorTerminalNormalizedTrace L Ta =
        (fun t => seamComplexCoord.symm (Ta (L*t))) := by
      funext t
      exact visibleConnectorWitnessAssemblyTopology_complex_point (Ta (L*t))
    rw [he] at hOuterNormalized
    exact hOuterNormalized
  obtain ⟨hTaJordan, hSeparate, hInsideInner, hInsideOuter, hNested, hClosure, _⟩ :=
    visibleConnectorOrdinaryFamilySourceClosure_actual hL.out E hE hF hclosed hJac
      hIncoming hTerminal hInner hOuter D.incoming.source_jordan
      hTa hTaL hTane hTaturn hTadet hInnerOrigin hOrigin hAnnV
  have hRawEndpoint (s : ℝ) : planarGradient raw (P s + W s) =
      visibleConnectorGradient P Gamma W ![s, 1] := by
    simpa only [one_smul] using (hJets s).2.2.2.2.2
  have hDt (s : ℝ) : visibleConnectorDelta pc gc wc ![a s, tc (a s)] ≠ 0 := by
    rw [visibleConnectorOrdinaryFamilyRebasedCoefficients_terminal_delta pc gc wc (a s)
      (C.coefficients_positive (a s)).2.2.ne']
    exact (div_pos (mul_pos (C.coefficients_positive (a s)).1
      (C.coefficients_positive (a s)).2.1) (C.coefficients_positive (a s)).2.2).ne'
  obtain ⟨_, hRawTerminal⟩ := visibleConnectorOrdinaryFamilyTerminalJets_rebased_endpoint
    hpc hgc hwc ha hb hd (fun s => (C.lower_delta_positive s).ne')
    (fun s => (C.phase_positive s).ne') (fun s => (hdpos s).ne')
    (fun _ => rfl) hDt hRawEndpoint
  obtain ⟨_hdir, _hY, hYJet, _hNormY, _hSignsY⟩ :=
    visibleConnectorOrdinaryFamilyActualChoiceTerminal_of_choice D C
  obtain ⟨hGradGerm, _⟩ := visibleConnectorFinalSmoothing_open_equality_derivatives hOt.1 hOt.2.2.2
  have hTaOt (s : ℝ) : Ta s ∈ Ot := by
    rw [← hEndpoint s]
    exact hOt.2.1 (mem_range_self s)
  have hTaV (s : ℝ) : Ta s ∈ V := (hOt.2.2.1 (hTaOt s)).1
  have hGradient : Ya = planarGradient H ∘ Ta := by
    funext s
    exact ((hGradGerm (hTaOt s)).trans (hRawTerminal s)).symm

  obtain ⟨hYsmooth, hYL, hYa, hYaL, hYaReg, hYai, hYaLift, hYaJordan, hYaNe,
    hYaTurn, hYaRange, hYaInside, hYaClosure, hYaOrigin,
    theta, hTheta, hThetaPos, hThetaShift, hCircle⟩ :=
    visibleConnectorOrdinaryFamilyRebasedGradientCircle_of_choice D C
  let Y0 := fun s => -R • visibleConnectorJ (visibleConnectorGinRotatedDirection R C.etaAngle gc s)
  have hYRep : Y = Y0 := funext hYJet
  have hRadialY (s : ℝ) : 0 < T s ⬝ᵥ Y s := by
    rw [hYRep]
    exact (_hSignsY s).1
  have hPairY (s : ℝ) : 0 < deriv T s ⬝ᵥ deriv Y s := by
    rw [hYRep]
    exact (_hSignsY s).2.1
  have hTaDeriv (s : ℝ) : deriv Ta s = deriv a s • deriv T (a s) :=
    (((hT.differentiable (by simp) (a s)).hasDerivAt).scomp s
      ((ha.differentiable (by simp) s).hasDerivAt)).deriv
  have hYaDeriv (s : ℝ) : deriv Ya s = deriv a s • deriv Y (a s) :=
    (((hYsmooth.differentiable (by simp) (a s)).hasDerivAt).scomp s
      ((ha.differentiable (by simp) s).hasDerivAt)).deriv
  have hPair (s : ℝ) : 0 < deriv Ta s ⬝ᵥ deriv Ya s := by
    rw [hTaDeriv, hYaDeriv, smul_dotProduct, dotProduct_smul]
    exact mul_pos (C.phase_positive s) (mul_pos (C.phase_positive s) (hPairY (a s)))
  have hRadial (s : ℝ) : 0 < Ta s ⬝ᵥ visibleConnectorUnitDirection (theta s) := by
    have hh := hRadialY (a s)
    change 0 < Ta s ⬝ᵥ Ya s at hh
    have hCircle' : Ya s = R • visibleConnectorUnitDirection (theta s) := hCircle s
    rw [hCircle', dotProduct_smul] at hh
    exact pos_of_mul_pos_right hh D.radius_pos.le
  have hTaOrigin : (0 : Coord) ∈ positiveExitInside Ta := by
    rw [hInsideOuter]
    exact ⟨0, hOrigin, by simp⟩
  obtain ⟨_, Hgin, _, hGinPositive, _, _, _, _⟩ :=
    visibleConnectorWitnessAssemblyTopology_positive_traces D.incoming
  have hGradientNested : closure (positiveExitInside Ya) ⊆ positiveExitInside D.incoming.gamma := by
    rw [hYaClosure]
    exact visibleConnectorOrdinaryFamily_closed_terminal_disk_in_incoming D hGinPositive
  let terminal : VisibleConnectorWitnessAssemblyTerminalFacts H V L := {
    p := Ta
    gamma := Ya
    p_smooth := hTa
    gamma_smooth := hYa
    p_periodic := hTaL
    gamma_periodic := hYaL
    p_in_domain := fun s _ => hTaV s
    actual_gradient := hGradient
    source_regular := incomingAssembly_regular_of_det hTadet
    gradient_regular := hYaReg
    source_injective := periodicComplexCurve_lift_injective hTaL hTai
    gradient_injective := hYaLift hYaL
    source_jordan := hTaJordan
    gradient_jordan := hYaJordan
    source_nonzero := incomingAssembly_nonzero_of_complex hTane
    gradient_nonzero := hYaNe
    source_turn := hTaturn
    gradient_turn := hYaTurn
    source_enclosure := hTaOrigin
    gradient_enclosure := hYaOrigin
    tangent_pairing := hPair }
  refine ⟨{
    eta := C.etaAngle
    eta_pos := C.eta_pos
    eta_small := C.eta_small
    G := H
    U := V
    U_open := hV
    G_smooth := hH
    terminal := terminal
    theta := theta
    theta_smooth := hTheta
    theta_increasing := hThetaPos
    theta_turn := hThetaShift
    terminal_circle := hCircle
    terminal_radial_positive := hRadial
    source_nesting := hNested
    gradient_nesting := hGradientNested
    source_closure_in_domain := by rw [hClosure]; exact hAnnV
    actual_saddle_closed := by
      intro q hq
      apply hNeg q
      apply hAnnV
      rwa [← hClosure]
    incoming_neighborhood := Oin
    incoming_neighborhood_open := hIn.1
    incoming_curve_in_neighborhood := hIn.2.1
    incoming_neighborhood_in_domains := hIn.2.2.1
    incoming_germ_retained := hIn.2.2.2
    F := F
    O := E.source
    O_open := E.open_source
    F_smooth := hF
    closed_round_in_domain := hclosed
    F_jacobian_positive := fun q hq1 hq2 => hJac q (hclosed ⟨hq1, hq2⟩)
    source_incoming := hIncoming
    source_terminal := hTerminal }⟩
end
end TightVer401




