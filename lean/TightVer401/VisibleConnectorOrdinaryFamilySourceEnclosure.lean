import TightVer401.VisibleConnectorOrdinaryFamilyTerminalEscape
import TightVer401.VisibleConnectorTerminalPositiveTrace

/-! Genuine source enclosure for any fixed incoming Jordan filling, including
an incoming filling different from the displaced source underlying the ruling.
The bound is constructed from compactness; the terminal is the SAME formula. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual closure of a fixed incoming Jordan filling has a norm bound;
no bound on the supplied filling is assumed. -/
theorem visibleConnectorOrdinaryFamily_jordan_closure_norm_bound (Hin : ℂ ≃ₜ ℂ) :
    ∃ M ≥ 0, ∀ z ∈ closure (jordanInterior Hin), ‖z‖ ≤ M := by
  have hne : (closure (jordanInterior Hin)).Nonempty :=
    (isConnected_jordanInterior Hin).nonempty.mono subset_closure
  obtain ⟨z0, hz0, hmax⟩ := (isCompact_closure_jordanInterior Hin).exists_isMaxOn
    hne continuous_norm.continuousOn
  exact ⟨‖z0‖, norm_nonneg _, fun z hz => hmax hz⟩

/-- Choose ONE threshold before choosing a terminal filling. EVERY actual
origin-containing filling of the SAME terminal range strictly encloses Hin. -/
theorem visibleConnectorOrdinaryFamily_actual_terminal_encloses_fixed_jordan
    (Hin : ℂ ≃ₜ ℂ) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    (hpperiod : Periodic p L) (hgperiod : Periodic gamma L)
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hkpos : ∀ s, 0 < kappa s)
    (hpv : ∀ s, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ Hout : ℂ ≃ₜ ℂ,
      range (positiveExitComplexTrace (visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta))) = frontier (jordanInterior Hout) →
      (0 : ℂ) ∈ jordanInterior Hout →
      closure (jordanInterior Hin) ⊆ jordanInterior Hout := by
  obtain ⟨M, hM, hin⟩ := visibleConnectorOrdinaryFamily_jordan_closure_norm_bound Hin
  obtain ⟨eps, heps, hout⟩ := visibleConnectorOrdinaryFamily_uniform_actual_terminal_norm_gt
    (M := M) hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv htpos
  refine ⟨eps, heps, ?_⟩
  intro eta heta he Hout hfront h0
  apply visibleConnector_jordan_enclosure_of_frontier_norm_bounds Hin Hout hM
  · intro z hz
    exact hin z (frontier_subset_closure hz)
  · intro z hz
    rw [← hfront] at hz
    obtain ⟨s, rfl⟩ := hz
    exact hout eta heta he s
  · exact h0

/-- The actual positive-terminal producer supplies Hout as well. Its chosen
positive trace, origin, frontier and strict enclosure are retained together. -/
theorem visibleConnectorOrdinaryFamily_actual_terminal_positive_trace_encloses
    (Hin : ℂ ≃ₜ ℂ) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    (hpperiod : Periodic p L) (hgperiod : Periodic gamma L)
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hkpos : ∀ s, 0 < kappa s)
    (hpv : ∀ s, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (hgv : ∀ s, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps →
      let T := visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta)
      ∃ Hout : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace Hout (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ jordanInterior Hout ∧
        range (positiveExitComplexTrace T) = frontier (jordanInterior Hout) ∧
        HasPositiveArgumentTurn (visibleConnectorTerminalNormalizedTrace L T) 1 ∧
        (∀ t, visibleConnectorTerminalNormalizedTrace L T t ≠ 0) ∧
        closure (jordanInterior Hin) ⊆ jordanInterior Hout := by
  obtain ⟨ee, hee, henclose⟩ := visibleConnectorOrdinaryFamily_actual_terminal_encloses_fixed_jordan
    Hin hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv htpos
  obtain ⟨et, het, htrace⟩ := visibleConnector_periodic_actual_terminal_positive_trace
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  refine ⟨min ee et, lt_min hee het, ?_⟩
  intro eta heta he
  have hee' := he.trans_le (min_le_left ee et)
  have het' := he.trans_le (min_le_right ee et)
  obtain ⟨Hout, hpositive, h0, hfront, hturn, hne⟩ := htrace eta heta het'
  refine ⟨Hout, hpositive, h0, hfront, hturn, hne, ?_⟩
  exact henclose eta heta hee' Hout hfront h0

end
end TightVer401
