import TightVer401.PositiveExitConstructionSelectedPatches
import TightVer401.PositiveExitConstructionSelectedAssembly
import TightVer401.PositiveExitConstructionSelectedSourceGeometryCore
import TightVer401.PositiveExitConstructionSelectedHomotopyPair
import TightVer401.PositiveExitConstructionFinalGradientConnection
import TightVer401.CorrugatedSeedFrameVisibility

/-! Actual single-prefix selected geometry assembly.
One selected prefix, one common geometric budget, one final paired trace call.
This constructs actual selected data; it does not assume source nesting/core.
The final ordinary connector family remains a separate original obligation. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function Filter MeasureTheory OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

private def draftNormalizedSource {G : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (t : PositiveExitTrace G U P) : ℝ → ℂ :=
  fun s => positiveExitComplexTrace t.p (P*s)
private def draftNormalizedGradient {G : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (t : PositiveExitTrace G U P) : ℝ → ℂ :=
  fun s => positiveExitComplexTrace t.gamma (P*s)

private theorem draftPointInverse (q : Coord) :
    seamComplexCoord (positiveExitComplexPoint q) = q := by
  ext i
  fin_cases i <;> simp [positiveExitComplexPoint, seamComplexCoord_apply]

private theorem draftTraceSmooth {p : ℝ → Coord} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (positiveExitComplexTrace p) := by
  have he : positiveExitComplexPoint = (seamComplexCoord.symm : Coord → ℂ) := by
    funext q
    apply seamComplexCoord.injective
    rw [seamComplexCoord.apply_symm_apply]
    exact draftPointInverse q
  rw [positiveExitComplexTrace, he]
  exact seamComplexCoord.symm.contDiff.comp hp

private theorem draftClockDeriv (P s : ℝ) : deriv (fun r : ℝ => P*r) s = P := by
  have h : HasDerivAt (fun r : ℝ => P*r) P s := by
    simpa using (hasDerivAt_id s).const_mul P
  exact h.deriv

private theorem draftOuterVisibility {G : Coord → ℝ} {U : Set Coord} {P R : ℝ}
    (t : PositiveExitTrace G U P)
    (hv : ComplexVisiblePair R (positiveExitComplexTrace t.p)
      (fun s => Complex.I * positiveExitComplexTrace t.gamma s)) :
    ComplexVisiblePair R (draftNormalizedSource t)
      (fun s => Complex.I * draftNormalizedGradient t s) := by
  have hp := (draftTraceSmooth t.p_smooth).differentiable (by simp)
  have hg : Differentiable ℝ (fun s => Complex.I * positiveExitComplexTrace t.gamma s) :=
    (contDiff_const.mul (draftTraceSmooth t.gamma_smooth)).differentiable (by simp)
  have hclock : Differentiable ℝ (fun s : ℝ => P*s) := by
    intro s
    exact ((hasDerivAt_id s).const_mul P).differentiableAt
  have hc := hv.comp (ψ := fun s : ℝ => P*s) hp hg hclock
    (fun s => by rw [draftClockDeriv]; exact t.period_pos)
  have hpEq : (positiveExitComplexTrace t.p ∘ fun s : ℝ => P*s) =
      draftNormalizedSource t := by
    funext s
    rfl
  have hgEq : ((fun s => Complex.I * positiveExitComplexTrace t.gamma s) ∘
      fun s : ℝ => P*s) = (fun s => Complex.I * draftNormalizedGradient t s) := by
    funext s
    rfl
  rw [hpEq, hgEq] at hc
  exact hc

private theorem draftInnerVisibility {G : Coord → ℝ} {U : Set Coord} {P R : ℝ}
    (t : PositiveExitTrace G U P)
    (hv : ComplexVisiblePair R (corrugatedReverseReflect (positiveExitComplexTrace t.gamma))
      (fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace t.p) s)) :
    ComplexVisiblePair R (corrugatedReverseReflect (draftNormalizedGradient t))
      (fun s => Complex.I * corrugatedReverseReflect (draftNormalizedSource t) s) := by
  have hp := (corrugatedReverseReflect_contDiff (draftTraceSmooth t.gamma_smooth)).differentiable (by simp)
  have hg : Differentiable ℝ (fun s => Complex.I *
      corrugatedReverseReflect (positiveExitComplexTrace t.p) s) :=
    (contDiff_const.mul
      (corrugatedReverseReflect_contDiff (draftTraceSmooth t.p_smooth))).differentiable (by simp)
  have hclock : Differentiable ℝ (fun s : ℝ => P*s) := by
    intro s
    exact ((hasDerivAt_id s).const_mul P).differentiableAt
  have hc := hv.comp (ψ := fun s : ℝ => P*s) hp hg hclock
    (fun s => by rw [draftClockDeriv]; exact t.period_pos)
  have hpEq : (corrugatedReverseReflect (positiveExitComplexTrace t.gamma) ∘
      fun s : ℝ => P*s) = corrugatedReverseReflect (draftNormalizedGradient t) := by
    funext s
    simp only [Function.comp_def, draftNormalizedGradient, corrugatedReverseReflect, mul_neg]
  have hgEq : ((fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace t.p) s) ∘
      fun s : ℝ => P*s) =
      (fun s => Complex.I * corrugatedReverseReflect (draftNormalizedSource t) s) := by
    funext s
    simp only [Function.comp_def, draftNormalizedSource, corrugatedReverseReflect, mul_neg]
  rw [hpEq, hgEq] at hc
  exact hc

/-- Output only: final scalar, actual final inverse, one selected trace pair,
positive fills and the exact source/gradient/protected data for the pair caller.
Native chart e and protected Y are retained as parameters, not reselected. -/
structure PositiveExitSinglePrefixGeometry {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (G : Coord → ℝ) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient) where
  Ge : Coord → ℝ
  J : Coord → ℝ
  scalar_eq : Ge = fun q => G q + J q
  change_smooth : ContDiff ℝ ∞ J
  change_compact : HasCompactSupport J
  smooth : ContDiffOn ℝ ∞ Ge e.target
  negative : ∀ q ∈ e.target, (planarHessian Ge q).det < 0
  bending : IsInfinitesimalBendingOn (planarSupportMap Ge) (Y ∘ e.symm) e.target
  e0 : OpenPartialHomeomorph Coord Coord
  e0_source : e0.source = e.target
  e0_actual : ∀ q ∈ e0.source, e0 q = planarGradient Ge q
  e0_inverse_smooth : ContDiffOn ℝ ∞ e0.symm e0.target
  P1 : ℝ
  P2 : ℝ
  t1 : PositiveExitTrace Ge e.target P1
  t2 : PositiveExitTrace Ge e.target P2
  HpPlus : ℂ ≃ₜ ℂ
  HpMinus : ℂ ≃ₜ ℂ
  HgPlus : ℂ ≃ₜ ℂ
  HgMinus : ℂ ≃ₜ ℂ
  sourcePlus : DualRadialCompletionPositiveTrace HpPlus (draftNormalizedSource t2)
  sourceMinus : DualRadialCompletionPositiveTrace HpMinus (draftNormalizedSource t1)
  gradientPlus : DualRadialCompletionPositiveTrace HgPlus (draftNormalizedGradient t2)
  gradientMinus : DualRadialCompletionPositiveTrace HgMinus (draftNormalizedGradient t1)
  sourcePlus_origin : (0 : ℂ) ∈ jordanInterior HpPlus
  sourceMinus_origin : (0 : ℂ) ∈ jordanInterior HpMinus
  gradientPlus_origin : (0 : ℂ) ∈ jordanInterior HgPlus
  gradientMinus_origin : (0 : ℂ) ∈ jordanInterior HgMinus
  source_nested : closure (jordanInterior HpMinus) ⊆ jordanInterior HpPlus
  protected_core : e '' tsupport Y ⊆ annularCoordJordanInterior HpPlus HpMinus
  actualPlus : ∀ s, e0 (seamComplexCoord (draftNormalizedSource t2 s)) =
    seamComplexCoord (draftNormalizedGradient t2 s)
  actualMinus : ∀ s, e0 (seamComplexCoord (draftNormalizedSource t1 s)) =
    seamComplexCoord (draftNormalizedGradient t1 s)
  pairPlus : ∀ s, 0 < inner ℝ (deriv (draftNormalizedSource t2) s)
    (deriv (draftNormalizedGradient t2) s)
  pairMinus : ∀ s, 0 < inner ℝ (deriv (draftNormalizedSource t1) s)
    (deriv (draftNormalizedGradient t1) s)
  visiblePlus : ComplexVisiblePair (1/4) (draftNormalizedSource t2)
    (fun s => Complex.I * draftNormalizedGradient t2 s)
  visibleMinus : ComplexVisiblePair (4/5)
    (corrugatedReverseReflect (draftNormalizedGradient t1))
    (fun s => Complex.I * corrugatedReverseReflect (draftNormalizedSource t1) s)
  H : C(unitInterval, C(unitInterval, ℂ))
  H0 : ∀ s, H 0 s = draftNormalizedSource t1 (s : ℝ)
  H1 : ∀ s, H 1 s = draftNormalizedSource t2 (s : ℝ)
  Hclosed : ∀ a, H a 1 = H a 0
  Hdomain : ∀ a s, H a s ∈ angularDescentComplex '' e0.source
  O : Set Coord
  Oopen : IsOpen O
  protected_O : e '' tsupport Y ⊆ O
  old_eq : EqOn Ge G O

theorem positiveExit_exists_single_prefix_source_geometry {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hδ : 0 < δ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hNi : Function.Injective (d.bandGaussMap (b := w)))
    (hbandNorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ t, ambientCross (d.T t) (d.E t) = d.n t)
    (hτ : ∀ t, d.τ t < 0)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (heD : ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ e)
    (heI : ContMDiffOn 𝓘(ℝ, Coord) nativeProductModel ∞ e.symm e.target)
    (G : Coord → ℝ) (hG : ContDiffOn ℝ ∞ G e.target)
    (hrec : ∀ p, planarSupportMap G (e p) = d.bandMap p)
    (hdet : ∀ y ∈ e.target, (planarHessian G y).det < 0)
    (hemb : Topology.IsEmbedding (fun y : e.target => planarGradient G y.val))
    (C : Set Coord) (hC : IsCompact C) (hne : C.Nonempty)
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbend : IsInfinitesimalBendingOn (planarSupportMap G) (Y ∘ e.symm) e.target)
    (hsupport : e '' tsupport Y ⊆ C)
    {η ξ σin σout : ℝ} (hηBudget : 0 < η) (hξ : 0 < ξ)
    (hσin : σin ≠ 0) (hσout : σout ≠ 0)
    (hmargin : ∀ v : Ioo (0 : ℝ) δ,
      (∀ s, angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0) ∧
      (∀ s, angularDescentComplex (planarGradient G
        (gnomonicInverse (positiveExitRawLeaf d hb hinside v s))) ≠ 0) ∧
      HasPositiveArgumentTurn
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T ∧
      HasPositiveArgumentTurn (angularDescentComplex ∘ planarGradient G ∘
        gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T ∧
      ComplexVisiblePair (1/4) (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v)
        (fun s => Complex.I * angularDescentComplex (planarGradient G
          (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)))) ∧
      ComplexVisiblePair (4/5)
        (corrugatedReverseReflect (angularDescentComplex ∘ planarGradient G ∘
          gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v))
        (fun s => Complex.I * corrugatedReverseReflect
          (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) s)) :

    Nonempty (PositiveExitSinglePrefixGeometry d e G Y) := by
  -- Retain one prefix. No final graph/trace pair is chosen at this step.
  obtain ⟨etaChosen, hetaChosen, hetaBudget, vin, vout, horder,
      S1, P1, hP1, rhoMax1, hp1, D1, B1,
      S2, P2, hP2, rhoMax2, hp2, D2, B2,
      hdis, hGe, hJs, hJc, hC2, hOpen, hProtected, hOld,
      hGerm, hBend, hNegative, hPres1, hPres2, hEmbedding,
      h, hhS, hhT, hhActual, hhInverse,
      hS1, hLength1, hS2, hLength2, hlabels, hselect⟩ :=
    positiveExit_exists_two_selected_visible_cartesian_patches
      d hb hδ hinside hNi hbandNorth horient hτ e heS heF heD heI
      G hG hrec hdet hemb C hC hne hprotect Y hbend hsupport
      hηBudget hξ hσin hσout hmargin
  letI : Fact (0 < P1) := ⟨hP1⟩
  letI : Fact (0 < P2) := ⟨hP2⟩
  let A1 := positiveExitFermiPatchStrip D1.fermi_chart D1.rho_lt_tube
  let A2 := positiveExitFermiPatchStrip D2.fermi_chart D2.rho_lt_tube
  let Ge : Coord → ℝ := fun q => G q + B1.change q + B2.change q
  let J : Coord → ℝ := fun q => B1.change q + B2.change q
  let zeta1 := positiveExitRawLeaf d hb hinside vin ∘ S1.symm
  let zeta2 := positiveExitRawLeaf d hb hinside vout ∘ S2.symm
  let v1 := exitPositiveGraphProfile P1 (fermiSupportSeamSlope (normalLoopCurvature zeta1)
    (fermiPerturbedSupport B1.epsilon (normalLoopCurvature zeta1) (positiveExitFermiHeight G zeta1)
      (fermiExitCutoff D1.rho D1.rho_pos)))
  let v2 := exitPositiveGraphProfile P2 (fermiSupportSeamSlope (normalLoopCurvature zeta2)
    (fermiPerturbedSupport B2.epsilon (normalLoopCurvature zeta2) (positiveExitFermiHeight G zeta2)
      (fermiExitCutoff D2.rho D2.rho_pos)))
  have hCT : C ⊆ e.target := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := hprotect hq
    exact e.map_source (by rw [heS]; exact mem_univ _)
  obtain ⟨eps, heps, W, hW, hCW, hWT, hlabelsW⟩ :=
    positiveExit_selectedSourceGeometry_core_uniform_gap
      d hb e heI hC hne hCT hlabels
  -- Tubes belong to the SAME fixed seams/clocks; no new leaves are chosen.
  obtain ⟨r1, hr1, htube1⟩ :=
    positiveExitFermiLabel_selected_exists_uniform_tube
      d hb e heS heF heI hinside vin S1.symm
      D1.zeta_smooth hp1 hP1 (fun _ => rfl) hbandNorth heps
  obtain ⟨r2, hr2, htube2⟩ :=
    positiveExitFermiLabel_selected_exists_uniform_tube
      d hb e heS heF heI hinside vout S2.symm
      D2.zeta_smooth hp2 hP2 (fun _ => rfl) hbandNorth heps
  obtain ⟨hv1, hv1P⟩ := positiveExit_actual_fermi_profile_smooth_periodic D1 B1.epsilon
  obtain ⟨hv2, hv2P⟩ := positiveExit_actual_fermi_profile_smooth_periodic D2 B2.epsilon
  obtain ⟨nu, hnu, hbudget⟩ := positiveExitSelected_exists_common_graph_budget
    hP1 hP2 hr1 hr2 hv1.continuous hv2.continuous hv1P hv2P
  -- The ONLY final paired trace selection. All later producers use these t1/t2.
  obtain ⟨a1, a2, t1, t2, ha1, ha1nu, ha1side,
      ha2, ha2nu, ha2side, hgraph1, hgraph2, hstrip1, hstrip2,
      hjets1, hjets2, hvisibleOuter1, hvisibleInner1,
      hvisibleOuter2, hvisibleInner2, _hS1again, _hP1again,
      _hS2again, _hP2again, _hlabelsAgain⟩ := hselect nu hnu
  obtain ⟨hbudget1, hbudget2⟩ := hbudget a1 a2 ha1nu ha2nu
  obtain ⟨HpPlus, HpMinus, HgPlus, HgMinus,
      hpPlus, hpMinus, hgPlus, hgMinus, hpPlus0, hpMinus0, hgPlus0, hgMinus0,
      hNested, hCore⟩ := positiveExitSelected_actual_traces_source_geometry
    d hb hinside vin vout horder hNi hbandNorth horient
    (fun v => ⟨(hmargin v).1, (hmargin v).2.2.1⟩)
    e heS heF S1 S2 hS1 hLength1 hS2 hLength2 D1 D2
    hv1 hv2 hv1P hv2P a1 a2 t1 t2 hgraph1 hgraph2 hstrip1 hstrip2
    (C := C) (K := e '' tsupport Y) hne hsupport hprotect heps
    (fun q hq => hlabelsW q (hCW hq)) htube1 htube2
    (fun s => (hbudget1 s).le) (fun s => (hbudget2 s).le)
  obtain ⟨H, hH0, hH1, hHclosed, hHdomain⟩ :=
    positiveExit_actual_selected_pair_source_homotopy
      d hb hinside e heS heF hbandNorth vin vout horder
      S1 S2 hS1 hLength1 hS2 hLength2 D1 D2
      B1.epsilon B2.epsilon a1 a2 t1.p t2.p
      hgraph1 hgraph2 hstrip1 hstrip2
  -- Flatten the ALREADY constructed final gradient inverse; do not re-invert G.
  let e0 := positiveExitFinalGradientChart e.open_target h
  obtain ⟨he0S, he0T, he0Actual, he0InverseEq, he0Smooth, he0Inverse⟩ :=
    positiveExit_final_gradient_cartesian_connection e.open_target hGe h hhS hhActual hhInverse
  have hActual1 (s : ℝ) :
      e0 (seamComplexCoord (draftNormalizedSource t1 s)) =
        seamComplexCoord (draftNormalizedGradient t1 s) := by
    change e0 (seamComplexCoord (positiveExitComplexPoint (t1.p (P1*s)))) =
      seamComplexCoord (positiveExitComplexPoint (t1.gamma (P1*s)))
    rw [draftPointInverse, draftPointInverse]
    have hp : t1.p (P1*s) ∈ e0.source := by
      rw [he0S]
      exact t1.p_in_domain (mem_univ (P1*s))
    rw [he0Actual _ hp]
    exact (congrFun t1.actual_gradient (P1*s)).symm
  have hActual2 (s : ℝ) :
      e0 (seamComplexCoord (draftNormalizedSource t2 s)) =
        seamComplexCoord (draftNormalizedGradient t2 s) := by
    change e0 (seamComplexCoord (positiveExitComplexPoint (t2.p (P2*s)))) =
      seamComplexCoord (positiveExitComplexPoint (t2.gamma (P2*s)))
    rw [draftPointInverse, draftPointInverse]
    have hp : t2.p (P2*s) ∈ e0.source := by
      rw [he0S]
      exact t2.p_in_domain (mem_univ (P2*s))
    rw [he0Actual _ hp]
    exact (congrFun t2.actual_gradient (P2*s)).symm
  refine ⟨{
    Ge := Ge
    J := J
    scalar_eq := ?_
    change_smooth := hJs
    change_compact := hJc
    smooth := hGe
    negative := hNegative
    bending := hBend
    e0 := e0
    e0_source := he0S
    e0_actual := he0Actual
    e0_inverse_smooth := he0Inverse
    P1 := P1
    P2 := P2
    t1 := t1
    t2 := t2
    HpPlus := HpPlus
    HpMinus := HpMinus
    HgPlus := HgPlus
    HgMinus := HgMinus
    sourcePlus := hpPlus
    sourceMinus := hpMinus
    gradientPlus := hgPlus
    gradientMinus := hgMinus
    sourcePlus_origin := hpPlus0
    sourceMinus_origin := hpMinus0
    gradientPlus_origin := hgPlus0
    gradientMinus_origin := hgMinus0
    source_nested := hNested
    protected_core := hCore
    actualPlus := hActual2
    actualMinus := hActual1
    pairPlus := dualRadialCompletionExitApplicationPeriod_pairing t2
    pairMinus := dualRadialCompletionExitApplicationPeriod_pairing t1
    visiblePlus := draftOuterVisibility t2 hvisibleOuter2
    visibleMinus := draftInnerVisibility t1 hvisibleInner1
    H := H
    H0 := hH0
    H1 := hH1
    Hclosed := hHclosed
    Hdomain := ?_
    O := (A1 ∪ A2)ᶜ
    Oopen := hOpen
    protected_O := hsupport.trans hProtected
    old_eq := hOld
  }⟩
  · funext q
    dsimp [Ge, J]
    ring
  · intro a s
    rw [he0S]
    exact hHdomain a s

end
end TightVer401
