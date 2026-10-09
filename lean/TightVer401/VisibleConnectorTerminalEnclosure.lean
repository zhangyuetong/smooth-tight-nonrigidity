import TightVer401.VisibleConnectorTerminalJordan
import TightVer401.PositiveExitConstructionWindingBridge
import TightVer401.SeamNormalCoordinates

/-! Actual terminal escape and Jordan enclosure. Continuity of the rescaled
terminal is used only near its nonzero denominator at eta=0. No global
denominator sign, target nesting, or terminal construction package is granted. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem terminalEnclosure_complex_eq : positiveExitComplexPoint = seamComplexCoord.symm := by
  funext q
  apply seamComplexCoord.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, seamComplexCoord_apply]
  ext i
  fin_cases i <;> rfl

private theorem terminalEnclosure_complex_smul (a : ℝ) (q : Coord) :
    positiveExitComplexPoint (a • q) = a • positiveExitComplexPoint q := by
  rw [terminalEnclosure_complex_eq]
  exact seamComplexCoord.symm.map_smul a q

theorem visibleConnector_complex_norm_le_twice_coord_norm (q : Coord) :
    ‖positiveExitComplexPoint q‖ ≤ 2 * ‖q‖ := by
  have he : positiveExitComplexPoint q = (q 0 : ℂ) + (q 1 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [positiveExitComplexPoint, Complex.mul_re, Complex.mul_im]
  rw [he]
  calc
    ‖(q 0 : ℂ) + (q 1 : ℂ) * Complex.I‖ ≤ ‖(q 0 : ℂ)‖ + ‖(q 1 : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖q 0‖ + ‖q 1‖ := by simp [norm_mul]
    _ ≤ ‖q‖ + ‖q‖ := add_le_add (norm_le_pi_norm q 0) (norm_le_pi_norm q 1)
    _ = 2 * ‖q‖ := by ring

/-- ONE local compact threshold makes the actual terminal arbitrarily far
from the origin, uniformly along the chosen compact period representatives. -/
theorem visibleConnector_uniform_actual_terminal_norm_gt
    {R M : ℝ} (hR : 0 < R) {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    {K : Set ℝ} (hK : IsCompact K)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hkpos : ∀ s ∈ K, 0 < kappa s)
    (hpv : ∀ s ∈ K, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s ∈ K, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s ∈ K,
      M < ‖positiveExitComplexPoint (visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta) s)‖ := by
  let W : ℝ × ℝ → Coord := fun q => visibleConnectorShiftedRuling R gamma theta q.1 q.2
  let D : ℝ × ℝ → ℝ := fun q => R * deriv theta q.2 *
    visibleConnectorActualExcessRatio R kappa q.1 q.2
  let Q : ℝ × ℝ → Coord := fun q => visibleConnectorRescaledTerminalSource
    R p gamma theta kappa q.1 q.2
  have hpc := hp.continuous
  have hgc := hg.continuous
  have htc := ht.continuous
  have hkc := hk.continuous
  have hdpc := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hdtc := (contDiff_infty_iff_deriv.mp ht).2.continuous
  have hW : Continuous W := by
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp only [W, visibleConnectorShiftedRuling, visibleConnectorActualRuling,
        visibleConnectorShiftedDirection, visibleConnectorUnitDirection, visibleConnectorJ,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    <;> fun_prop
  have hA : Continuous (fun q : ℝ × ℝ =>
      visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2) := by
    change Continuous (fun q : ℝ × ℝ => -(deriv p q.2 0 * W q 1 - deriv p q.2 1 * W q 0))
    fun_prop
  have hEx : Continuous (fun q : ℝ × ℝ => visibleConnectorActualExcessRatio R kappa q.1 q.2) := by
    unfold visibleConnectorActualExcessRatio
    fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hlarge : ∀ᶠ eta in 𝓝 (0 : ℝ), ∀ s ∈ K,
      M * |eta| < ‖positiveExitComplexPoint (Q (eta, s))‖ := by
    apply hK.eventually_forall_of_forall_eventually
    intro s hs
    have hD0 : D (0, s) ≠ 0 := by
      have hd : 0 < D (0, s) := by
        simpa [D, visibleConnectorActualExcessRatio] using
          mul_pos (mul_pos hR (htpos s hs)) (hkpos s hs)
      exact hd.ne'
    have hQ : ContinuousAt Q (0, s) := by
      change ContinuousAt (fun q : ℝ × ℝ => q.1 • p q.2 +
        (visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2 / D q) • W q)
        (0, s)
      exact (continuous_fst.continuousAt.smul (hpc.comp continuous_snd).continuousAt).add
        ((hA.continuousAt.div hD.continuousAt hD0).smul hW.continuousAt)
    have hcQ : ContinuousAt (fun q => positiveExitComplexPoint (Q q)) (0, s) := by
      rw [terminalEnclosure_complex_eq]
      exact seamComplexCoord.symm.continuous.continuousAt.comp hQ
    have hQne : positiveExitComplexPoint (Q (0, s)) ≠ 0 := by
      have hscale : 0 < kappa s * (deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s)) /
          (R * deriv theta s) := div_pos (mul_pos (hkpos s hs) (hpv s hs))
            (mul_pos hR (htpos s hs))
      have hunit : visibleConnectorJ (visibleConnectorUnitDirection (theta s)) ⬝ᵥ
          visibleConnectorJ (visibleConnectorUnitDirection (theta s)) = 1 := by
        simpa [visibleConnectorUnitDirection, visibleConnectorJ, dotProduct,
          Fin.sum_univ_two, pow_two, add_comm] using Real.cos_sq_add_sin_sq (theta s)
      intro hz
      have hzero : Q (0, s) = 0 := by
        apply seamComplexCoord.symm.injective
        rw [← terminalEnclosure_complex_eq, hz]
        simp [positiveExitComplexPoint] <;> rfl
      have hdot : Q (0, s) ⬝ᵥ (-visibleConnectorJ (visibleConnectorUnitDirection (theta s))) =
          kappa s * (deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s)) /
            (R * deriv theta s) := by
        dsimp only [Q]
        rw [visibleConnector_rescaled_terminal_zero hdecomp (hkpos s hs).ne']
        simp only [smul_dotProduct, smul_eq_mul, dotProduct_neg, hunit]
        ring
      rw [hzero, zero_dotProduct] at hdot
      linarith
    have hz : M * |(0 : ℝ)| < ‖positiveExitComplexPoint (Q (0, s))‖ := by
      simpa only [abs_zero, mul_zero] using norm_pos_iff.mpr hQne
    have hc : ContinuousAt (fun q : ℝ × ℝ =>
        ‖positiveExitComplexPoint (Q q)‖ - M * |q.1|) (0, s) :=
      hcQ.norm.sub (continuous_const.continuousAt.mul continuous_fst.continuousAt.abs)
    have hp0 : 0 < ‖positiveExitComplexPoint (Q (0, s))‖ - M * |(0 : ℝ)| := sub_pos.mpr hz
    filter_upwards [hc.eventually (lt_mem_nhds hp0)] with q hq
    exact sub_pos.mp hq
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hlarge
  refine ⟨eps, heps, ?_⟩
  intro eta heta hepsEta s hs
  have hetaBall : eta ∈ Metric.ball (0 : ℝ) eps := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos heta] using hepsEta
  have hm := hball hetaBall s hs
  dsimp only [Q] at hm
  rw [visibleConnector_rescaled_terminal_eq hg ht hdecomp heta.ne',
    terminalEnclosure_complex_smul, norm_smul, Real.norm_eq_abs, abs_of_pos heta] at hm
  change M * eta < eta * ‖positiveExitComplexPoint
    (visibleConnectorActualTerminalSource p gamma (visibleConnectorShiftedRuling R gamma theta eta) s)‖ at hm
  rw [mul_comm M eta] at hm
  nlinarith [hm]

/-- The Euclidean norm maximum of a bounded filled Jordan disk is attained
on its actual frontier. This proves the closed-interior bound from the curve. -/
theorem visibleConnector_jordan_closure_norm_le (H : ℂ ≃ₜ ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hfront : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ M) :
    ∀ z ∈ closure (jordanInterior H), ‖z‖ ≤ M := by
  have hne : (closure (jordanInterior H)).Nonempty :=
    (isConnected_jordanInterior H).nonempty.mono subset_closure
  obtain ⟨x, hx, hmax⟩ := (isCompact_closure_jordanInterior H).exists_isMaxOn hne
    continuous_norm.continuousOn
  have hxM : ‖x‖ ≤ M := by
    by_contra hm
    have hpos : 0 < ‖x‖ := lt_of_le_of_lt hM (lt_of_not_ge hm)
    have hxD : x ∈ jordanInterior H := by
      by_contra hn
      have hf : x ∈ frontier (jordanInterior H) := by
        rw [frontier, (jordanInterior_isOpen H).interior_eq]
        exact ⟨hx, hn⟩
      exact hm (hfront x hf)
    have hpath : Continuous (fun r : ℝ => r • x) := continuous_id.smul continuous_const
    have hn : (fun r : ℝ => r • x) ⁻¹' jordanInterior H ∈ 𝓝 (1 : ℝ) :=
      ((jordanInterior_isOpen H).preimage hpath).mem_nhds (by simpa using hxD)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
    have hmem : (1 + r / 2) • x ∈ jordanInterior H := by
      apply hball
      simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have hnorm : ‖(1 + r / 2) • x‖ = (1 + r / 2) * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + r / 2)]
    have hle := hmax (subset_closure hmem)
    change ‖(1 + r / 2) • x‖ ≤ ‖x‖ at hle
    rw [hnorm] at hle
    nlinarith
  intro z hz
  exact (hmax hz).trans hxM

/-- A connected ball avoiding the terminal frontier and containing its
interior origin lies entirely in the terminal Jordan interior. -/
theorem visibleConnector_closedBall_subset_jordanInterior (H : ℂ ≃ₜ ℂ) {M : ℝ}
    (hM : 0 ≤ M) (h0 : (0 : ℂ) ∈ jordanInterior H)
    (hfront : ∀ z ∈ frontier (jordanInterior H), M < ‖z‖) :
    closedBall (0 : ℂ) M ⊆ jordanInterior H := by
  have hconn : IsPreconnected (closedBall (0 : ℂ) M) := (convex_closedBall (0 : ℂ) M).isPreconnected
  have hdisj : Disjoint (closedBall (0 : ℂ) M) (frontier (jordanInterior H)) := by
    apply disjoint_left.mpr
    intro z hz hf
    have hzM : ‖z‖ ≤ M := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact (not_lt_of_ge hzM) (hfront z hf)
  have hside : closedBall (0 : ℂ) M ⊆ jordanInterior H ∨
      closedBall (0 : ℂ) M ⊆ (closure (jordanInterior H))ᶜ := by
    apply hconn.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact disjoint_left.mpr (fun z hz hc => hc (subset_closure hz))
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        apply disjoint_left.mp hdisj hz
        rw [frontier, (jordanInterior_isOpen H).interior_eq]
        exact ⟨hc, hi⟩
  exact hside.resolve_right (fun he => he (mem_closedBall_self hM) (subset_closure h0))

/-- Genuine strict fill nesting follows from actual curve norm bounds and
the terminal origin enclosure; target nesting is not a premise. -/
theorem visibleConnector_jordan_enclosure_of_frontier_norm_bounds
    (Hin Hout : ℂ ≃ₜ ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hin : ∀ z ∈ frontier (jordanInterior Hin), ‖z‖ ≤ M)
    (hout : ∀ z ∈ frontier (jordanInterior Hout), M < ‖z‖)
    (h0 : (0 : ℂ) ∈ jordanInterior Hout) :
    closure (jordanInterior Hin) ⊆ jordanInterior Hout := by
  intro z hz
  apply visibleConnector_closedBall_subset_jordanInterior Hout hM h0 hout
  simpa only [mem_closedBall, dist_zero_right] using visibleConnector_jordan_closure_norm_le Hin hM hin z hz

end
end TightVer401
