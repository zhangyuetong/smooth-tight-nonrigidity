import TightVer401.VisibleConnectorTerminalEnclosure
import TightVer401.VisibleConnectorTerminalPositiveTrace

/-! SAME-terminal escape margins and actual filling enclosure.  The rotation
threshold is chosen from original smooth periodic ruling data, before any
eta-dependent displaced inverse is selected.  Compact strict norm separation
also produces a numerical C0 perturbation budget for the later rho choice. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Strict separation on a compact terminal produces a positive numerical
budget. Every C0 perturbation within that budget retains the requested norm
bound; neither the budget nor the perturbed bound is an assumption. -/
theorem visibleConnectorIncomingTerminal_compact_norm_margin
    {A E : Type*} [TopologicalSpace A] [NormedAddCommGroup E]
    {K : Set A} (hK : IsCompact K) {T : A → E}
    (hT : ContinuousOn T K) {M : ℝ}
    (hsep : ∀ s ∈ K, M < ‖T s‖) :
    ∃ delta > 0, (∀ s ∈ K, M + 2 * delta ≤ ‖T s‖) ∧
      ∀ U : A → E, (∀ s ∈ K, ‖U s - T s‖ < delta) →
        ∀ s ∈ K, M + delta < ‖U s‖ := by
  by_cases hne : K.Nonempty
  · obtain ⟨s0, hs0, hmin⟩ := hK.exists_isMinOn hne hT.norm
    let delta := (‖T s0‖ - M) / 2
    have hd : 0 < delta := by dsimp [delta]; linarith [hsep s0 hs0]
    refine ⟨delta, hd, ?_, ?_⟩
    · intro s hs
      have hm : ‖T s0‖ ≤ ‖T s‖ := hmin hs
      dsimp [delta]
      linarith
    · intro U hclose s hs
      have hm : ‖T s0‖ ≤ ‖T s‖ := hmin hs
      have hc := hclose s hs
      have ht : ‖T s‖ - ‖U s‖ ≤ ‖U s - T s‖ := by
        simpa only [norm_sub_rev] using norm_sub_norm_le (T s) (U s)
      dsimp [delta] at hc ⊢
      linarith
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · intro s hs
      exact False.elim (hne ⟨s, hs⟩)
    · intro U hclose s hs
      exact False.elim (hne ⟨s, hs⟩)

/-- ONE eta threshold yields the SAME actual terminal, its positive filling,
and escape beyond M at EVERY physical phase, rather than only representatives.
This is an original-data producer: terminal geometry is constructed internally. -/
theorem visibleConnectorIncomingTerminal_exists_escape_and_filling
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
    (hgv : ∀ s, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ
      visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps →
      let T := visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta)
      ContDiff ℝ ∞ T ∧ Periodic T L ∧
      (∀ s, M < ‖positiveExitComplexTrace T s‖) ∧
      (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ jordanInterior H ∧
        range (positiveExitComplexTrace T) = frontier (jordanInterior H) := by
  obtain ⟨ej, hej, hj⟩ := visibleConnector_periodic_actual_terminal_jordan
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  obtain ⟨en, hen, hn⟩ := visibleConnector_uniform_actual_terminal_norm_gt
    (M := M) hR hp hg ht hk (K := Icc (0 : ℝ) L) isCompact_Icc
    hdecomp (fun s _ => hkpos s) (fun s _ => hpv s) (fun s _ => htpos s)
  refine ⟨min ej en, lt_min hej hen, ?_⟩
  intro eta heta heps
  dsimp only
  let T := visibleConnectorActualTerminalSource p gamma
    (visibleConnectorShiftedRuling R gamma theta eta)
  obtain ⟨hT, hperiod, hne, hdet, hturn, hi, _⟩ :=
    hj eta heta (heps.trans_le (min_le_left _ _))
  have hnorm (s : ℝ) : M < ‖positiveExitComplexTrace T s‖ := by
    obtain ⟨n, hnrep, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico, zero_add] at hnrep
    have he := hn eta heta (heps.trans_le (min_le_right _ _))
      (s - n • L) ⟨hnrep.1, hnrep.2.le⟩
    change M < ‖positiveExitComplexPoint (T (s - n • L))‖ at he
    have hperiodT : Periodic T L := hperiod
    rw [hperiodT.sub_zsmul_eq n] at he
    exact he
  obtain ⟨H, hpositive, h0, hfront, _⟩ :=
    visibleConnectorTerminal_exists_positive_completion_trace hL hT hperiod hne hdet hturn hi
  exact ⟨hT, hperiod, hnorm, hdet, H, hpositive, h0, hfront⟩

/-- Actual strict filled-disk nesting is produced from the original ruling
and a radius containing the incoming frontier. No outer filling or desired
nesting is granted, and one terminal/filling is retained throughout. -/
theorem visibleConnectorIncomingTerminal_exists_enclosing_filling
    {R L M : ℝ} (hR : 0 < R) (hL : 0 < L) (hM : 0 ≤ M)
    (Hin : ℂ ≃ₜ ℂ)
    (hin : ∀ z ∈ frontier (jordanInterior Hin), ‖z‖ ≤ M)
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
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps →
      let T := visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta)
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        range (positiveExitComplexTrace T) = frontier (jordanInterior H) ∧
        closure (jordanInterior Hin) ⊆ jordanInterior H ∧
        closedBall (0 : ℂ) M ⊆ jordanInterior H := by
  obtain ⟨eps, heps, hterminal⟩ :=
    visibleConnectorIncomingTerminal_exists_escape_and_filling (M := M)
      hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  refine ⟨eps, heps, ?_⟩
  intro eta heta hetaeps
  dsimp only
  obtain ⟨hT, hperiod, hnorm, hdet, H, hpositive, h0, hfront⟩ :=
    hterminal eta heta hetaeps
  have hout : ∀ z ∈ frontier (jordanInterior H), M < ‖z‖ := by
    intro z hz
    rw [← hfront] at hz
    obtain ⟨s, rfl⟩ := hz
    exact hnorm s
  exact ⟨H, hpositive, hfront,
    visibleConnector_jordan_enclosure_of_frontier_norm_bounds Hin H hM hin hout h0,
    visibleConnector_closedBall_subset_jordanInterior H hM h0 hout⟩

end
end TightVer401

/-! A fixed-eta displaced family uses this threshold only after eta has been
selected. Both continuity inputs concern actual values and actual derivatives;
no rho-smallness, nonzero, norm or determinant conclusion is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- From pointwise joint C1 continuity at rho=0 on the compact period,
produce ONE rho threshold preserving terminal norm and positive polar
Jacobian. The derivative in the conclusion is the actual phase derivative. -/
theorem visibleConnectorIncomingTerminal_exists_displacement_threshold
    {F : ℝ × ℝ → Coord} {K : Set ℝ} (hK : IsCompact K) {M : ℝ}
    (hF : ∀ s ∈ K, ContinuousAt F (0, s))
    (hFd : ∀ s ∈ K, ContinuousAt
      (fun q : ℝ × ℝ => deriv (fun t => F (q.1, t)) q.2) (0, s))
    (hnorm : ∀ s ∈ K, M < ‖positiveExitComplexPoint (F (0, s))‖)
    (hdet : ∀ s ∈ K, 0 < visibleConnectorDet (F (0, s))
      (deriv (fun t => F (0, t)) s)) :
    ∃ rhoMax > 0, ∀ rho, |rho| < rhoMax → ∀ s ∈ K,
      M < ‖positiveExitComplexPoint (F (rho, s))‖ ∧
      0 < visibleConnectorDet (F (rho, s))
        (deriv (fun t => F (rho, t)) s) := by
  have hevent : ∀ᶠ rho in 𝓝 (0 : ℝ), ∀ s ∈ K,
      M < ‖positiveExitComplexPoint (F (rho, s))‖ ∧
      0 < visibleConnectorDet (F (rho, s))
        (deriv (fun t => F (rho, t)) s) := by
    apply hK.eventually_forall_of_forall_eventually
    intro s hs
    have hc : ContinuousAt (fun q : ℝ × ℝ =>
        positiveExitComplexPoint (F q)) (0, s) := by
      have he : positiveExitComplexPoint = seamComplexCoord.symm := by
        funext q
        apply seamComplexCoord.injective
        rw [ContinuousLinearEquiv.apply_symm_apply, seamComplexCoord_apply]
        ext i
        fin_cases i <;> rfl
      rw [he]
      exact seamComplexCoord.symm.continuous.continuousAt.comp (hF s hs)
    have hd : ContinuousAt (fun q : ℝ × ℝ => visibleConnectorDet (F q)
        (deriv (fun t => F (q.1, t)) q.2)) (0, s) := by
      unfold visibleConnectorDet
      exact (((continuous_apply 0).continuousAt.comp (hF s hs)).mul
        ((continuous_apply 1).continuousAt.comp (hFd s hs))).sub
          (((continuous_apply 1).continuousAt.comp (hF s hs)).mul
            ((continuous_apply 0).continuousAt.comp (hFd s hs)))
    exact (hc.norm.eventually (lt_mem_nhds (hnorm s hs))).and
      (hd.eventually (lt_mem_nhds (hdet s hs)))
  obtain ⟨rhoMax, hrhoMax, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨rhoMax, hrhoMax, ?_⟩
  intro rho hrho s hs
  apply hball _ s hs
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hrho

end
end TightVer401



