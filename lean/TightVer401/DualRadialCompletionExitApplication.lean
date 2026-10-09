import TightVer401.DualRadialCompletionExitApplicationInputs
import TightVer401.DualRadialCompletion

/-! Consume the ordinary SAME positive-exit output in the actual completion
caller. Only the original visible-connector construction remains explicit. -/
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

variable {T w delta : ℝ} [Fact (0 < T)]
    {d : PeriodicRuledFrame T} {G : Coord → ℝ} {U : Set Coord}
    {e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord}
    {he : e.source = univ} {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0}
    {hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w}
    {O : Set Coord} {xi : ℝ}

/-- Construct the full support from the actual exit output, preserving a
full open scalar germ of the SAME original potential at its protected field.
This theorem does not produce exits or the still-pending visible connector. -/
theorem exists_dualRadialCompletionExitApplication_of_visible_connector
    (hConnector : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R), VisibleConnectorConstructionStatement D)
    (X : PositiveExitConstructionData d G U e he Y hbalance hinside O xi) :
    ∃ (A RN mu B d0 dInfinity epsilon L : ℝ) (Gtilde : Coord → ℝ)
      (W : Set Coord) (E : OpenPartialHomeomorph Coord Coord),
      0 < A ∧ A < RN ∧ 0 < mu ∧ 0 < B ∧ 0 < epsilon ∧ epsilon < L ∧
      ContDiffOn ℝ ∞ Gtilde {p | 0 < planarRadius p} ∧
      (∀ p, 0 < planarRadius p → (planarHessian Gtilde p).det < 0) ∧
      IsOpen W ∧ e '' tsupport Y ⊆ W ∧ W ⊆ e.target ∧ W ⊆ X.source_annulus ∧
      W ⊆ X.Uexit ∧ W ⊆ {p | 0 < planarRadius p} ∧
      EqOn Gtilde X.Gexit W ∧ EqOn Gtilde G W ∧
      (∀ p ∈ W, Gtilde =ᶠ[𝓝 p] G) ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        Gtilde p = RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0) ∧
      (∀ p, L < planarRadius p →
        Gtilde p = A * planarRadius p - B / planarRadius p + dInfinity) ∧
      E.source = {p | 0 < planarRadius p} ∧
      E.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (∀ p ∈ E.source, E p = planarGradient Gtilde p) ∧
      ContDiffOn ℝ ∞ E.symm E.target := by
  obtain ⟨P⟩ := exists_dualRadialCompletionExitApplication_inputs X
  have hBand : annularCoordJordanClosure P.HpPlus P.HpMinus ⊆ P.E.source := by
    rw [← P.closed_annulus_eq]
    exact P.closed_in_source
  have hActualPlus (t : ℝ) :
      P.E (seamComplexCoord (positiveExitComplexTrace X.outer.p (X.outer_return.period*t))) =
        seamComplexCoord (positiveExitComplexTrace X.outer.gamma (X.outer_return.period*t)) := by
    simp only [positiveExitComplexTrace, Function.comp_def,
      dualRadialCompletionExitApplication_coord_complex, P.actual_gradient]
    rw [X.outer.actual_gradient]
    rfl
  have hActualMinus (t : ℝ) :
      P.E (seamComplexCoord (positiveExitComplexTrace X.inner.p (X.inner_return.period*t))) =
        seamComplexCoord (positiveExitComplexTrace X.inner.gamma (X.inner_return.period*t)) := by
    simp only [positiveExitComplexTrace, Function.comp_def,
      dualRadialCompletionExitApplication_coord_complex, P.actual_gradient]
    rw [X.inner.actual_gradient]
    rfl
  obtain ⟨A,RN,mu,B,d0,dInfinity,epsilon,L,Gtilde,W0,E,hA,hARN,hmu,hB,hepsilon,heL,
    hSmooth,hSaddle,hW0,hCore,hWSource,hWPositive,hExitEq,hInner,hOuter,
    hESource,hETarget,hEActual,hEInverse⟩ :=
    (exists_dual_radial_support_completion_of_visible_connector hConnector)
      X.Gexit P.E P.HpPlus P.HpMinus P.HgPlus P.HgMinus
      (fun t => positiveExitComplexTrace X.outer.p (X.outer_return.period*t))
      (fun t => positiveExitComplexTrace X.inner.p (X.inner_return.period*t))
      (fun t => positiveExitComplexTrace X.outer.gamma (X.outer_return.period*t))
      (fun t => positiveExitComplexTrace X.inner.gamma (X.inner_return.period*t))
      (1/4) (4/5) (e '' tsupport Y) P.smooth P.saddle
      (fun p _ => congrFun P.actual_gradient p) P.inverse_smooth
      P.p_plus P.p_minus P.g_plus P.g_minus P.source_nested P.gradient_nested
      P.source_origin P.gradient_origin hBand hActualPlus hActualMinus
      (dualRadialCompletionExitApplicationPeriod_pairing X.outer)
      (dualRadialCompletionExitApplicationPeriod_pairing X.inner)
      (by norm_num) (by norm_num)
      (dualRadialCompletionExitApplication_outer_visibility X.outer X.outer_visibility)
      (dualRadialCompletionExitApplication_inner_visibility X.inner X.inner_visibility)
      P.core_compact P.core_in_annulus
  let W := W0 ∩ O
  have hW : IsOpen W := hW0.inter X.protected_open
  have hRetained : e '' tsupport Y ⊆ W := fun p hp => ⟨hCore hp, X.protected_support hp⟩
  have hInAnnulus : W ⊆ X.source_annulus := fun _ hp => X.protected_in_annulus hp.2
  have hOldEq : EqOn Gtilde G W :=
    fun p hp => (hExitEq hp.1).trans (X.protected_equality hp.2)
  refine ⟨A,RN,mu,B,d0,dInfinity,epsilon,L,Gtilde,W,E,hA,hARN,hmu,hB,hepsilon,heL,
    hSmooth,hSaddle,hW,hRetained,hInAnnulus.trans X.source_annulus_in_chart,hInAnnulus,
    hInAnnulus.trans X.source_annulus_in_domain,(fun _ hp => hWPositive hp.1),
    (fun _ hp => hExitEq hp.1),hOldEq,?_,hInner,hOuter,hESource,hETarget,hEActual,hEInverse⟩
  intro p hp
  filter_upwards [hW.mem_nhds hp] with q hq
  exact hOldEq hq

end
end TightVer401
