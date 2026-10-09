import TightVer401.VisibleConnectorIncomingParametersChoice
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedRawPotential
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedTopology
import TightVer401.VisibleConnectorWitnessAssemblyTopology
import TightVer401.VisibleConnectorIncomingSeamJets
import TightVer401.DualRadialCompletionExitTrace

/-! D-only raw assembly retaining ONE proved incoming choice, its native e,
actual Gin slices, phase and height, and the terminal filling selected with
that choice. The original and terminal norm margins use the SAME budget. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The complete raw output, including closed-band inverse coverage and
literal value, gradient and Hessian identities. B is the raw support scalar. -/
def VisibleConnectorOrdinaryFamilyIncomingRawResult (L : ℝ)
    (p gamma w : ℝ → Coord) (g a b : ℝ → ℝ) (Ho Hi : ℂ ≃ₜ ℂ) : Prop :=
    let tc := visibleConnectorActualTerminalHeight p gamma w
    let d := fun s => tc (a s) - b s
    let P := visibleConnectorRebasedSource p w a b
    let f := visibleConnectorRebasedHeight g gamma w a b
    let W := visibleConnectorRebasedRuling w a d
    let Gamma := visibleConnectorRebasedGradient p gamma w a b
    let h := fun _ : ℝ => (1 : ℝ)
    ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
      (H : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
        annularCoordJordanClosure Ho Hi) (B : Coord → ℝ) (U : Set Coord),
      e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧
      (e0 : Coord → Coord) = visibleConnectorCartesianSource L P W h ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ z, (H z : Coord) = visibleConnectorCartesianSource L P W h z) ∧
      visibleConnectorCartesianSource L P W h ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} = annularCoordJordanClosure Ho Hi ∧
      {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source ∧
      E.source ⊆ {z : Coord | 0 < planarRadius z} ∧
      ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L P W h) E.source ∧
      (∀ z ∈ E.source, 0 < annularJacobian (visibleConnectorCartesianSource L P W h) z) ∧
      (E : Coord → Coord) = visibleConnectorCartesianSource L P W h ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      annularCoordJordanClosure Ho Hi ⊆ E.target ∧
      EqOn E.symm e0.symm (annularCoordJordanInterior Ho Hi) ∧
      B = visibleConnectorCartesianPotential L f Gamma W h E ∧
      IsOpen U ∧ annularCoordJordanClosure Ho Hi ⊆ U ∧ U ⊆ E.target ∧
      ContDiffOn ℝ ∞ B U ∧ (∀ y ∈ U, (planarHessian B y).det < 0) ∧
      MapsTo (visibleConnectorSource P W) (visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E) U ∧
      EqOn (B ∘ visibleConnectorSource P W) (visibleConnectorHeight f Gamma W)
        (visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E) ∧
      EqOn (planarGradient B ∘ visibleConnectorSource P W) (visibleConnectorGradient P Gamma W)
        (visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E,
        planarHessian B (visibleConnectorSource P W q) *ᵥ W (q 0) =
          (visibleConnectorA P W (q 0)*visibleConnectorB Gamma W (q 0) /
            (visibleConnectorDelta P Gamma W q)^2) • visibleConnectorJ (W (q 0))) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E,
        (planarHessian B (visibleConnectorSource P W q)).det =
          -(visibleConnectorA P W (q 0))^2*(visibleConnectorB Gamma W (q 0))^2 /
            (visibleConnectorDelta P Gamma W q)^4) ∧
      (∀ s : ℝ, P s ∈ U ∧ B (P s) = f s ∧ planarGradient B (P s) = Gamma s ∧
        P s + h s • W s ∈ U ∧
        B (P s + h s • W s) = f s + h s*(Gamma s ⬝ᵥ W s) ∧
        planarGradient B (P s + h s • W s) = visibleConnectorGradient P Gamma W ![s,h s])

/-- Original incoming data alone construct the SAME raw annular potential.
The choice is retained explicitly for subsequent seam matching and smoothing.
No extra source geometry, coefficient, inverse or nesting grant is required. -/
theorem visibleConnectorOrdinaryFamily_exists_raw_from_incoming
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (hetaMax : 0 < etaMax) :
    ∃ C : VisibleConnectorIncomingParametersChoice D etaMax,
    ∃ Ho Hi : ℂ ≃ₜ ℂ,
      let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
      let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
      let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
      let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
      let b := fun s => (visibleConnectorDisplacedNativeSolution C.e D.incoming.p (C.rho, s)).2
      PositiveJordanParametrization Hi
        (fun t => seamComplexCoord.symm (D.incoming.p (L * t))) ∧
      DualRadialCompletionPositiveTrace Ho (visibleConnectorTerminalNormalizedTrace L
        (visibleConnectorActualTerminalSource pc gc wc)) ∧
      (0 : ℂ) ∈ jordanInterior Ho ∧ (0 : ℂ) ∈ jordanInterior Hi ∧
      range (positiveExitComplexTrace (visibleConnectorActualTerminalSource pc gc wc)) =
        frontier (jordanInterior Ho) ∧
      VisibleConnectorOrdinaryFamilyIncomingRawResult L pc gc wc (Gin ∘ pc) a b Ho Hi := by
  obtain ⟨C⟩ := visibleConnectorIncomingParametersChoice_nonempty D hetaMax
  let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
  let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
  let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
  let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
  let b := fun s => (visibleConnectorDisplacedNativeSolution C.e D.incoming.p (C.rho, s)).2
  have hgamma0 (s : ℝ) : D.incoming.gamma s = planarGradient Gin (D.incoming.p s) :=
    congrFun D.incoming.actual_gradient s
  have hcomplex : positiveExitComplexPoint = angularDescentComplex := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have hvis := D.visibility
  rw [D.actual_delta] at hvis
  have hmargin (s : ℝ) : R < ‖Complex.I * angularDescentComplex (D.incoming.gamma s)‖ := by
    simpa only [hcomplex] using (hvis s).1
  obtain ⟨hpcJoint, hDU, hgcJoint, hV, hVsub, _haxis, hwJoint,
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
  let T := visibleConnectorActualTerminalSource pc gc wc
  obtain ⟨hT, hTL, hTnorm, hTdet, hTi, Ho, hPositive, hOrigin, hFrontier⟩ := C.terminal_geometry
  change ContDiff ℝ ∞ T at hT
  change Periodic T L at hTL
  have hNormBudget : 0 < C.normBudget :=
    lt_of_le_of_lt (norm_nonneg _) (C.original_norm_bounded 0)
  have hTne : ∀ s, positiveExitComplexTrace T s ≠ 0 := by
    intro s he
    have hn := hTnorm s
    change C.normBudget < ‖positiveExitComplexTrace T s‖ at hn
    rw [he, norm_zero] at hn
    exact (not_lt_of_ge hNormBudget.le) hn
  have hTurnNormalized := dualRadialCompletion_positiveTrace_turn hPositive hOrigin
  have hTturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L := by
    obtain ⟨phi, hphi, hproj, hinc⟩ := hTurnNormalized
    refine ⟨fun s => phi (s / L), hphi.comp (continuous_id.div_const L), ?_, ?_⟩
    · intro s
      have he : L * (s / L) = s := by field_simp [hL.out.ne']
      simpa only [visibleConnectorTerminalNormalizedTrace, he] using hproj (s / L)
    · simpa only [div_self hL.out.ne', zero_div] using hinc
  obtain ⟨hRebased, _hRange, _hFront⟩ :=
    visibleConnectorOrdinaryFamily_rebased_same_positive_jordan hL.out Ho hT ha hTL
      hTi hTne hTdet hTturn C.phase_positive (C.phase_shift C.rho) hFrontier hOrigin
  have hOuter : PositiveJordanParametrization Ho (fun t => seamComplexCoord.symm
      (pc (a (L * t)) + visibleConnectorActualTerminalHeight pc gc wc (a (L * t)) •
        wc (a (L * t)))) := by
    have he : visibleConnectorTerminalNormalizedTrace L (fun s => T (a s)) =
        (fun t => seamComplexCoord.symm
          (pc (a (L * t)) + visibleConnectorActualTerminalHeight pc gc wc (a (L * t)) •
            wc (a (L * t)))) := by
      funext t
      exact visibleConnectorWitnessAssemblyTopology_complex_point (T (a (L * t)))
    rw [he] at hRebased
    exact hRebased
  obtain ⟨Hi, _Hg, hInner, _hgInner, hInnerOrigin, _hgOrigin, _hpInside, _hgInside⟩ :=
    visibleConnectorWitnessAssemblyTopology_positive_traces D.incoming
  have hDisjoint : Disjoint (range D.incoming.p)
      (range (fun s => pc (a s) + visibleConnectorActualTerminalHeight pc gc wc (a s) • wc (a s))) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    change T (a t) = D.incoming.p s at ht
    have hn := hTnorm (a t)
    change C.normBudget < ‖positiveExitComplexTrace T (a t)‖ at hn
    change C.normBudget < ‖positiveExitComplexPoint (T (a t))‖ at hn
    rw [ht] at hn
    exact (not_lt_of_ge (C.original_norm_bounded s).le) hn
  refine ⟨C, Ho, Hi, hInner, hPositive, hOrigin, hInnerOrigin, hFrontier, ?_⟩
  exact visibleConnectorOrdinaryFamilyRebasedRawPotential_actual hL.out
    hpc hgc hwc hg ha hb (hpcL C.rho) (hgcL C.rho) (hwL C.rho)
    ((hpcL C.rho).comp Gin) (C.phase_shift C.rho) (C.height_periodic C.rho)
    C.phase_positive C.height_negative
    (fun s => (C.coefficients_positive s).1)
    (fun s => (C.coefficients_positive s).2.1)
    (fun s => (C.coefficients_positive s).2.2)
    C.lower_delta_positive hvalue C.original_trace hOuter hInner hDisjoint hOrigin hInnerOrigin

end
end TightVer401

