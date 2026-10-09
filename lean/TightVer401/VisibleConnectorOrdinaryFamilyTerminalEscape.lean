import TightVer401.VisibleConnectorTerminalEnclosure

/-! Periodic, all-real escape of the SAME actual terminal source. The compact
incoming bound and source separation are constructed, rather than assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem ordinaryEscape_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have h := ((hf.differentiable (by simp) (s + L)).hasDerivAt).scomp s
    ((hasDerivAt_id s).add_const L)
  have h' : HasDerivAt (fun r => f (r + L)) (deriv f (s + L)) s := by
    simpa only [Function.comp_def, id_eq, one_smul] using h
  exact (h'.congr_of_eventuallyEq
    (Eventually.of_forall (fun r => (hp r).symm))).deriv.symm

/-- Periodicity holds for the literal terminal formula, at every angle,
including angles where its quotient denominator vanishes. -/
theorem visibleConnectorOrdinaryFamily_actual_terminal_periodic
    {R L : ℝ} {p gamma : ℝ → Coord} {theta : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta)
    (hpperiod : Periodic p L) (hgperiod : Periodic gamma L)
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi) (eta : ℝ) :
    Periodic (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorShiftedRuling R gamma theta eta)) L := by
  let w := visibleConnectorShiftedRuling R gamma theta eta
  have he : ContDiff ℝ ∞ (visibleConnectorShiftedDirection theta eta) :=
    visibleConnectorUnitDirection_contDiff.comp (ht.sub contDiff_const)
  have hw : ContDiff ℝ ∞ w := visibleConnectorActualRuling_contDiff hg he
  have hwper : Periodic w L := by
    intro s
    dsimp [w, visibleConnectorShiftedRuling, visibleConnectorActualRuling]
    rw [hgperiod s, visibleConnector_shifted_direction_periodic hshift eta s]
  have hdpper := ordinaryEscape_deriv_periodic hp hpperiod
  have hdgper := ordinaryEscape_deriv_periodic hg hgperiod
  have hdwper := ordinaryEscape_deriv_periodic hw hwper
  have hAper : Periodic (visibleConnectorA p w) L := by
    intro s
    unfold visibleConnectorA
    rw [hdpper s, hwper s]
  have hBper : Periodic (visibleConnectorB gamma w) L := by
    intro s
    unfold visibleConnectorB
    rw [hdgper s, hwper s]
  have hCper : Periodic (visibleConnectorC gamma w) L := by
    intro s
    unfold visibleConnectorC
    rw [hBper s, hdwper s, hwper s]
  have hhper : Periodic (visibleConnectorActualTerminalHeight p gamma w) L := by
    intro s
    unfold visibleConnectorActualTerminalHeight
    rw [hAper s, hCper s]
  intro s
  change p (s + L) + visibleConnectorActualTerminalHeight p gamma w (s + L) • w (s + L) =
    p s + visibleConnectorActualTerminalHeight p gamma w s • w s
  rw [hpperiod s, hhper s, hwper s]

/-- ONE threshold makes the terminal escape an arbitrary complex norm bound
on ALL real parameters, without an assumed terminal embedding or separation. -/
theorem visibleConnectorOrdinaryFamily_uniform_actual_terminal_norm_gt
    {R L M : ℝ} (hR : 0 < R) (hL : 0 < L)
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
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s,
      M < ‖positiveExitComplexPoint (visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta) s)‖ := by
  obtain ⟨eps, heps, hbound⟩ := visibleConnector_uniform_actual_terminal_norm_gt
    (M := M) hR hp hg ht hk (isCompact_Icc : IsCompact (Icc (0 : ℝ) L))
    hdecomp (fun s _ => hkpos s) (fun s _ => hpv s) (fun s _ => htpos s)
  refine ⟨eps, heps, ?_⟩
  intro eta heta he s
  have hperiod := visibleConnectorOrdinaryFamily_actual_terminal_periodic (R := R)
    hp hg ht hpperiod hgperiod hshift eta
  have heq : visibleConnectorActualTerminalSource p gamma
      (visibleConnectorShiftedRuling R gamma theta eta) s =
      visibleConnectorActualTerminalSource p gamma
      (visibleConnectorShiftedRuling R gamma theta eta) (toIcoMod hL 0 s) := by
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL 0 s]
    exact hperiod.zsmul (toIcoDiv hL 0 s) _
  have hs : toIcoMod hL 0 s ∈ Icc (0 : ℝ) L :=
    Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have hb := hbound eta heta he (toIcoMod hL 0 s) hs
  rwa [← heq] at hb

/-- A periodic continuous incoming source has an actual global norm bound. -/
theorem visibleConnectorOrdinaryFamily_incoming_source_norm_bound
    {L : ℝ} (hL : 0 < L) {p : ℝ → Coord}
    (hp : Continuous p) (hpperiod : Periodic p L) :
    ∃ M ≥ 0, ∀ s, ‖positiveExitComplexPoint (p s)‖ ≤ M := by
  have hcomplex : positiveExitComplexPoint = seamComplexCoord.symm := by
    funext q
    apply seamComplexCoord.injective
    rw [ContinuousLinearEquiv.apply_symm_apply, seamComplexCoord_apply]
    ext i
    fin_cases i <;> rfl
  have hc : Continuous (fun s => ‖positiveExitComplexPoint (p s)‖) := by
    rw [hcomplex]
    exact (seamComplexCoord.symm.continuous.comp hp).norm
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hL.le) hc.continuousOn
  refine ⟨‖positiveExitComplexPoint (p s0)‖, norm_nonneg _, ?_⟩
  intro s
  have heq : p s = p (toIcoMod hL 0 s) := by
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL 0 s]
    exact hpperiod.zsmul (toIcoDiv hL 0 s) _
  rw [heq]
  exact hmax (Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s))

/-- The actual terminal and original incoming source ranges are disjoint
for all sufficiently small positive angles, from their constructed norm gap. -/
theorem visibleConnectorOrdinaryFamily_actual_ruling_source_boundaries_disjoint
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
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
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps →
      Disjoint (range p) (range (visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta))) := by
  obtain ⟨M, hM, hin⟩ := visibleConnectorOrdinaryFamily_incoming_source_norm_bound
    hL hp.continuous hpperiod
  obtain ⟨eps, heps, hout⟩ := visibleConnectorOrdinaryFamily_uniform_actual_terminal_norm_gt
    (M := M) hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv htpos
  refine ⟨eps, heps, ?_⟩
  intro eta heta he
  apply disjoint_left.mpr
  rintro q ⟨s, rfl⟩ ⟨t, ht⟩
  have hb := hout eta heta he t
  rw [ht] at hb
  exact (not_lt_of_ge (hin s)) hb

/-- The SAME construction forces an arbitrary actual coordinate norm bound. -/
theorem visibleConnectorOrdinaryFamily_uniform_actual_terminal_coord_norm_gt
    {R L M : ℝ} (hR : 0 < R) (hL : 0 < L)
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
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s,
      M < ‖visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta) s‖ := by
  obtain ⟨eps, heps, hbound⟩ := visibleConnectorOrdinaryFamily_uniform_actual_terminal_norm_gt
    (M := 2 * M) hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv htpos
  refine ⟨eps, heps, ?_⟩
  intro eta heta he s
  have hb := hbound eta heta he s
  have hle := visibleConnector_complex_norm_le_twice_coord_norm
    (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorShiftedRuling R gamma theta eta) s)
  linarith

end
end TightVer401




