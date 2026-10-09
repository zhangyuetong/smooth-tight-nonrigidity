import TightVer401.VisibleConnectorOrdinaryFamilyFromIncomingRaw
import TightVer401.VisibleConnectorOrdinaryFamilySeamMatching
import TightVer401.VisibleConnectorFinalSmoothingActual

/-! Final scalar from original incoming D. ONE selected native choice, raw
Cartesian E, raw support and raw domain are retained. The height classifier
uses that E; the final carrier contains the complete physical closed band.
This is a scalar producer, not the remaining terminal OrdinaryData producer. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- All raw fields retained for the SAME witnesses subsequently smoothed. -/
def VisibleConnectorOrdinaryFamilyIncomingRawFields (L : ℝ)
    (p gamma w : ℝ → Coord) (g a b : ℝ → ℝ) (Ho Hi : ℂ ≃ₜ ℂ)
    (e0 E : OpenPartialHomeomorph Coord Coord)
    (Hband : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
      annularCoordJordanClosure Ho Hi) (B : Coord → ℝ) (U : Set Coord) : Prop :=
    let tc := visibleConnectorActualTerminalHeight p gamma w
    let d := fun s => tc (a s) - b s
    let P := visibleConnectorRebasedSource p w a b
    let f := visibleConnectorRebasedHeight g gamma w a b
    let W := visibleConnectorRebasedRuling w a d
    let Gamma := visibleConnectorRebasedGradient p gamma w a b
    let h := fun _ : ℝ => (1 : ℝ)
    e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧
      (e0 : Coord → Coord) = visibleConnectorCartesianSource L P W h ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ z, (Hband z : Coord) = visibleConnectorCartesianSource L P W h z) ∧
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

/-- D alone selects the raw objects once; every positive tolerance then
produces a final scalar with an actual original incoming open germ. -/
theorem visibleConnectorOrdinaryFamily_exists_scalar_from_incoming
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (hetaMax : 0 < etaMax) :
    ∃ C : VisibleConnectorIncomingParametersChoice D etaMax,
    ∃ Ho Hi : ℂ ≃ₜ ℂ,
      let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
      let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
      let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
      let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
      let b := fun s => (visibleConnectorDisplacedNativeSolution C.e D.incoming.p (C.rho, s)).2
      let tc := visibleConnectorActualTerminalHeight pc gc wc
      let d := fun s => tc (a s) - b s
      let P := visibleConnectorRebasedSource pc wc a b
      let W := visibleConnectorRebasedRuling wc a d
      PositiveJordanParametrization Hi
        (fun t => seamComplexCoord.symm (D.incoming.p (L * t))) ∧
      DualRadialCompletionPositiveTrace Ho (visibleConnectorTerminalNormalizedTrace L
        (visibleConnectorActualTerminalSource pc gc wc)) ∧
      (0 : ℂ) ∈ jordanInterior Ho ∧ (0 : ℂ) ∈ jordanInterior Hi ∧
      range (positiveExitComplexTrace (visibleConnectorActualTerminalSource pc gc wc)) =
        frontier (jordanInterior Ho) ∧
      ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
        (Hband : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
          annularCoordJordanClosure Ho Hi) (raw : Coord → ℝ) (Uraw : Set Coord),
        VisibleConnectorOrdinaryFamilyIncomingRawFields L pc gc wc (Gin ∘ pc) a b
          Ho Hi e0 E Hband raw Uraw ∧
        (∀ s, P s = D.incoming.p s) ∧
        annularCoordJordanClosure Ho Hi =
          visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d ∧
        ∀ epsilon : ℝ, 0 < epsilon →
          let Bheight := visibleConnectorFinalSmoothingHeight L b d E
          let V := visibleConnectorFinalSmoothingCarrier Uraw Uin Bheight
          ∃ H : Coord → ℝ, ∃ Oin Ot : Set Coord,
            IsOpen V ∧ V ⊆ E.target ∧
            annularCoordJordanClosure Ho Hi ⊆ V ∧
            visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d ⊆ V ∧
            ContDiffOn ℝ ∞ H V ∧ (∀ x ∈ V, (planarHessian H x).det < 0) ∧
            (∀ x ∈ visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d,
              (planarHessian H x).det < 0) ∧
            (∀ s u, u ∈ Icc (0 : ℝ) 1 →
              Bheight (visibleConnectorSource P W (![s,u] : Coord)) = b s + u * d s) ∧
            (IsOpen Oin ∧ range D.incoming.p ⊆ Oin ∧ Oin ⊆ V ∩ Uin ∧ EqOn H Gin Oin) ∧
            (IsOpen Ot ∧ range (fun s => P s + W s) ⊆ Ot ∧
              Ot ⊆ V ∩ Uraw ∧ EqOn H raw Ot) ∧
            ∀ x ∈ V,
              |H x - relativeSaddlePiecewise {y | Bheight y < 0} Gin raw x| < epsilon ∧
              ‖planarGradient H x -
                planarGradient (relativeSaddlePiecewise {y | Bheight y < 0} Gin raw) x‖ < epsilon := by
  obtain ⟨C, Ho, Hi, hInner, hPositive, hOrigin, hInnerOrigin, hFrontier, hRawExists⟩ :=
    visibleConnectorOrdinaryFamily_exists_raw_from_incoming D hetaMax
  let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
  let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
  let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
  let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
  let b := fun s => (visibleConnectorDisplacedNativeSolution C.e D.incoming.p (C.rho, s)).2
  let tc := visibleConnectorActualTerminalHeight pc gc wc
  let d := fun s => tc (a s) - b s
  let P := visibleConnectorRebasedSource pc wc a b
  let f := visibleConnectorRebasedHeight (Gin ∘ pc) gc wc a b
  let W := visibleConnectorRebasedRuling wc a d
  let Gamma := visibleConnectorRebasedGradient pc gc wc a b
  change VisibleConnectorOrdinaryFamilyIncomingRawResult L pc gc wc (Gin ∘ pc) a b Ho Hi at hRawExists
  obtain ⟨e0, E, Hband, raw, Uraw, hRaw⟩ := hRawExists
  have hRawCopy := hRaw
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
  obtain ⟨htc, htcL, htcpos, hd, hdL, hdpos, hUpper,
      hP, hf, hW, hGamma, hPL, hfL, hWL, hGammaL, hval, hANew, hBNew, hDelta, hOut⟩ :=
    visibleConnectorOrdinaryFamilyRebasedCoefficients_actual hpc hgc hwc hg ha hb
      (hpcL C.rho) (hgcL C.rho) (hwL C.rho) ((hpcL C.rho).comp Gin)
      (C.phase_shift C.rho) (C.height_periodic C.rho) C.phase_positive C.height_negative
      (fun s => (C.coefficients_positive s).1)
      (fun s => (C.coefficients_positive s).2.1)
      (fun s => (C.coefficients_positive s).2.2) C.lower_delta_positive hvalue
  have htop (s : ℝ) : 0 < b s + d s := by
    change 0 < b s + (tc (a s) - b s)
    linarith [htcpos (a s)]
  have haShift : ∀ s, a (s + L) = a s + L := C.phase_shift C.rho
  have hcL : Periodic (pc ∘ a) L := by
    intro s
    change pc (a (s + L)) = pc (a s)
    rw [haShift s]
    exact hpcL C.rho (a s)
  have hBandEq : annularCoordJordanClosure Ho Hi =
      visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d :=
    visibleConnectorOrdinaryFamily_source_closure_eq_closed_rebased_band hL.out hPL hWL hImage
  have hRawBand (s u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      visibleConnectorSource P W (![s,u] : Coord) ∈ Uraw := by
    apply hAnnU
    rw [hBandEq]
    exact ⟨s, u, hu, rfl⟩
  have hGinStrip (s t : ℝ) (hlo : b s ≤ t) (hhi : t ≤ 0) :
      visibleConnectorSource pc wc (![a s,t] : Coord) ∈ Uin :=
    C.lower_strip_in_GinU s t hlo hhi
  have hgcActual : gc = planarGradient Gin ∘ pc := rfl
  obtain ⟨hVphys, hStrip, hCartesianSmooth, hSeam⟩ :=
    visibleConnectorOrdinaryFamilySeamMatching_actual hL.out D.domain_open D.potential_smooth
      hpc hwc hpcU ha hb (hpcL C.rho) (hwL C.rho)
      (C.phase_shift C.rho) (C.height_periodic C.rho) C.phase_positive C.height_negative
      (fun s => (C.coefficients_positive s).1)
      (fun s => (C.coefficients_positive s).2.1)
      (fun s => (C.coefficients_positive s).2.2) C.lower_delta_positive
      E hE hEs hi hclosed hImage hAnnU
  have hMatchValue (s : ℝ) : Gin (pc (a s)) = raw (pc (a s)) := by
    rw [hrawDef]
    exact (hSeam s).2.2.2.1.symm
  have hMatchGradient (s : ℝ) : planarGradient Gin (pc (a s)) =
      planarGradient raw (pc (a s)) := by
    rw [hrawDef]
    exact (hSeam s).2.2.2.2.symm
  have hPactual : P = D.incoming.p := funext C.original_trace
  refine ⟨C, Ho, Hi, hInner, hPositive, hOrigin, hInnerOrigin, hFrontier,
    e0, E, Hband, raw, Uraw, hRawCopy, C.original_trace, hBandEq, ?_⟩
  intro epsilon hepsilon
  obtain ⟨H, Oin, Ot, hV, hVE, hH, hNeg, hClosedNeg, hIn, hOt, hClose⟩ :=
    visibleConnectorFinalSmoothing_exists_scalar_from_cartesian
      hpc hwc ha hb hd hPL hWL (C.height_periodic C.rho) hdL hcL
      C.height_negative hdpos htop C.phase_positive Gamma hDelta E hE hEs hi hclosed
      D.domain_open hUraw hUE D.potential_smooth hrawSmooth D.potential_saddle hrawNeg
      hMatchValue hMatchGradient hRawBand hGinStrip hepsilon
  have hBandV := visibleConnectorFinalSmoothingHeightCarrier_closed_band hL.out
    hPL hWL (C.height_periodic C.rho) hdL hdpos E hE hclosed hRawBand hGinStrip
  have hAnnV : annularCoordJordanClosure Ho Hi ⊆
      visibleConnectorFinalSmoothingCarrier Uraw Uin (visibleConnectorFinalSmoothingHeight L b d E) := by
    rw [hBandEq]
    exact hBandV
  have hHeight (s u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      visibleConnectorFinalSmoothingHeight L b d E (visibleConnectorSource P W (![s,u] : Coord)) =
        b s + u * d s :=
    (visibleConnectorFinalSmoothingHeight_closed_band hL.out hPL hWL
      (C.height_periodic C.rho) hdL E hE hclosed s u hu.1 hu.2).2
  have hInOriginal : IsOpen Oin ∧ range D.incoming.p ⊆ Oin ∧
      Oin ⊆ visibleConnectorFinalSmoothingCarrier Uraw Uin
        (visibleConnectorFinalSmoothingHeight L b d E) ∩ Uin ∧ EqOn H Gin Oin := by
    rw [← hPactual]
    exact hIn
  exact ⟨H, Oin, Ot, hV, hVE, hAnnV, hBandV, hH, hNeg, hClosedNeg,
    hHeight, hInOriginal, hOt, hClose⟩

end
end TightVer401




