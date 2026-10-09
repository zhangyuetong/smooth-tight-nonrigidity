import TightVer401.VisibleConnectorTerminalPositiveTrace
import TightVer401.VisibleConnectorTerminalEnclosure
import TightVer401.VisibleConnectorRadialTerminal

/-! Choose eta BEFORE constructing its displaced family. The coefficient,
radial, Jordan, filling and enclosure margins refer to one literal ruling.
No Gin match, displaced inverse, or completed connector is assumed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- One original eta satisfies all retained terminal margins at once. The
returned actual ruling is the only ruling to use in subsequent rho selection. -/
theorem visibleConnectorIncomingParameters_exists_eta_original_margins
    {R L etaMax M : ℝ} (hR : 0 < R) (hL : 0 < L) (hetaMax : 0 < etaMax)
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
    (hgv : ∀ s, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ
      visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eta > 0, eta < etaMax ∧
      let w0 := visibleConnectorShiftedRuling R gamma theta eta
      let T := visibleConnectorActualTerminalSource p gamma w0
      (∀ s, 0 < visibleConnectorA p w0 s ∧
        0 < visibleConnectorB gamma w0 s ∧ 0 < visibleConnectorC gamma w0 s ∧
        0 < T s ⬝ᵥ (-visibleConnectorJ (visibleConnectorShiftedDirection theta eta s))) ∧
      ContDiff ℝ ∞ T ∧ Periodic T L ∧
      (∀ s, positiveExitComplexTrace T s ≠ 0) ∧
      (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
      HasPositiveArgumentTurn (positiveExitComplexTrace T) L ∧ InjOn T (Ico 0 L) ∧
      Schoenflies.IsJordanCurve
        (range (jordanComplexCoordinates.symm ∘ positiveExitComplexTrace T)) ∧
      (∀ s, M < ‖positiveExitComplexPoint (T s)‖) ∧
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ H '' Metric.ball (0 : ℂ) 1 ∧
        range (positiveExitComplexTrace T) = frontier (H '' Metric.ball (0 : ℂ) 1) := by
  obtain ⟨ec, hec, hcoeff⟩ := visibleConnector_periodic_actual_coefficients_and_terminal_radial
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  obtain ⟨et, het, hterminal⟩ := visibleConnector_periodic_actual_terminal_jordan
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  obtain ⟨en, hen, hnorm⟩ := visibleConnector_uniform_actual_terminal_norm_gt
    (M := M) hR hp hg ht hk (K := Icc (0 : ℝ) L) isCompact_Icc hdecomp
    (fun s _ => hkpos s) (fun s _ => hpv s) (fun s _ => htpos s)
  let eps := min etaMax (min ec (min et en))
  have heps : 0 < eps := lt_min hetaMax (lt_min hec (lt_min het hen))
  let eta := eps / 2
  have heta : 0 < eta := half_pos heps
  have hsmall : eta < eps := half_lt_self heps
  have hmax : eta < etaMax := hsmall.trans_le (min_le_left _ _)
  have hrest : eta < min ec (min et en) := hsmall.trans_le (min_le_right _ _)
  have hetaC : eta < ec := hrest.trans_le (min_le_left _ _)
  have hetaTN : eta < min et en := hrest.trans_le (min_le_right _ _)
  have hetaT : eta < et := hetaTN.trans_le (min_le_left _ _)
  have hetaN : eta < en := hetaTN.trans_le (min_le_right _ _)
  let w0 := visibleConnectorShiftedRuling R gamma theta eta
  let T := visibleConnectorActualTerminalSource p gamma w0
  obtain ⟨hT, hperiod, hne, hdet, hturn, hi, hjordan, _⟩ := hterminal eta heta hetaT
  have hperiodT : Periodic T L := hperiod
  have hnormAll (s : ℝ) : M < ‖positiveExitComplexPoint (T s)‖ := by
    obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico, zero_add] at hn
    have hh := hnorm eta heta hetaN (s - n • L) ⟨hn.1, hn.2.le⟩
    change M < ‖positiveExitComplexPoint (T (s - n • L))‖ at hh
    rw [hperiodT.sub_zsmul_eq n] at hh
    exact hh
  obtain ⟨H, hpositive, h0, hboundary, _, _⟩ :=
    visibleConnectorTerminal_exists_positive_completion_trace hL hT hperiod hne hdet hturn hi
  refine ⟨eta, heta, hmax, ?_, hT, hperiod, hne, hdet, hturn, hi, hjordan,
    hnormAll, H, hpositive, h0, hboundary⟩
  intro s
  exact hcoeff eta heta hetaC s

end
end TightVer401

