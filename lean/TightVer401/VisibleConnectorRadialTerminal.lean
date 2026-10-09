import TightVer401.VisibleConnectorUniformPeriodic

/-! The actual terminal source has positive radial pairing for one uniform
small rotation. The proof uses its rescaled continuous limit, rather than
assuming a terminal geometry or completed connector package. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- This expression extends eta times the actual terminal point through eta=0. -/
def visibleConnectorRescaledTerminalSource (R : ℝ) (p gamma : ℝ → Coord)
    (theta kappa : ℝ → ℝ) (eta s : ℝ) : Coord :=
  eta • p s +
    (visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta eta) s /
      (R * deriv theta s * visibleConnectorActualExcessRatio R kappa eta s)) •
      visibleConnectorShiftedRuling R gamma theta eta s

private theorem radialTerminal_J_unit (t : ℝ) :
    visibleConnectorJ (visibleConnectorUnitDirection t) ⬝ᵥ
      visibleConnectorJ (visibleConnectorUnitDirection t) = 1 := by
  simpa [visibleConnectorUnitDirection,visibleConnectorJ,dotProduct,
    Fin.sum_univ_two,pow_two,add_comm] using Real.cos_sq_add_sin_sq t

/-- The actual nonzero limiting terminal vector. -/
theorem visibleConnector_rescaled_terminal_zero {R : ℝ} {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    {s : ℝ} (hk : kappa s ≠ 0) :
    visibleConnectorRescaledTerminalSource R p gamma theta kappa 0 s =
      -(kappa s * (deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s)) /
        (R * deriv theta s)) •
        visibleConnectorJ (visibleConnectorUnitDirection (theta s)) := by
  unfold visibleConnectorRescaledTerminalSource
  rw [visibleConnector_shifted_A_zero hdecomp s,
    visibleConnector_shifted_ruling_zero hdecomp s]
  simp only [visibleConnectorActualExcessRatio,Real.sinc_zero,mul_one,
    mul_zero,zero_div,zero_mul,sub_zero,zero_smul,zero_add,smul_smul]
  congr 1
  by_cases hd : R * deriv theta s = 0
  · simp [hd]
  · field_simp [hk,hd]
    <;> ring

/-- Away from eta=0 the continuous extension is eta times the SAME actual
terminal point, with the actual C coefficient, not a substitute endpoint. -/
theorem visibleConnector_rescaled_terminal_eq {R : ℝ} {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ} (hgamma : ContDiff ℝ ∞ gamma)
    (htheta : ContDiff ℝ ∞ theta)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    {eta s : ℝ} (heta : eta ≠ 0) :
    visibleConnectorRescaledTerminalSource R p gamma theta kappa eta s =
      eta • (p s + visibleConnectorActualTerminalHeight p gamma
        (visibleConnectorShiftedRuling R gamma theta eta) s •
          visibleConnectorShiftedRuling R gamma theta eta s) := by
  have hdir := visibleConnectorUnitDirection_hasDerivAt
    (((htheta.differentiable (by simp) s).hasDerivAt).sub_const eta)
  have hu : visibleConnectorShiftedDirection theta eta s ⬝ᵥ
      visibleConnectorShiftedDirection theta eta s = 1 := by
    simpa [visibleConnectorShiftedDirection,visibleConnectorUnitDirection,
      dotProduct,Fin.sum_univ_two,pow_two] using Real.cos_sq_add_sin_sq (theta s - eta)
  have hc := visibleConnector_actual_ruling_C_formula (R := R) hgamma hdir hu
  change visibleConnectorC gamma (visibleConnectorShiftedRuling R gamma theta eta) s =
    R * deriv theta s *
      (visibleConnectorJ (gamma s) ⬝ᵥ visibleConnectorShiftedDirection theta eta s - R) at hc
  rw [visibleConnector_actual_excess_factor hdecomp eta s] at hc
  unfold visibleConnectorRescaledTerminalSource visibleConnectorActualTerminalHeight
  rw [smul_add,smul_smul,hc]
  congr 2
  have he : R * deriv theta s * (eta * visibleConnectorActualExcessRatio R kappa eta s) =
      eta * (R * deriv theta s * visibleConnectorActualExcessRatio R kappa eta s) := by ring
  rw [he]
  by_cases hd : R * deriv theta s * visibleConnectorActualExcessRatio R kappa eta s = 0
  · simp [hd]
  · field_simp [heta,hd]

private theorem radialTerminal_curve_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have htrans : HasDerivAt (fun r => f (r + L)) (deriv f (s + L)) s := by
    simpa only [Function.comp_def,id_eq,one_smul] using
      ((hf.differentiable (by simp) (s + L)).hasDerivAt).scomp s
        ((hasDerivAt_id s).add_const L)
  have he := htrans.congr_of_eventuallyEq
    (f₁ := f) (Eventually.of_forall (fun r => (hp r).symm))
  exact he.deriv.symm

/-- Uniform positive radial pairing of the actual terminal source on a compact
trace. This threshold can be intersected with the coefficient threshold, so
the same single actual rotation satisfies both construction requirements. -/
theorem visibleConnector_uniform_actual_terminal_radial_positive
    {R : ℝ} (hR : 0 < R) {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ} {K : Set ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (htheta : ContDiff ℝ ∞ theta) (hkappa : ContDiff ℝ ∞ kappa)
    (hK : IsCompact K)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hk : ∀ s ∈ K, 0 < kappa s)
    (hpv : ∀ s ∈ K, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s ∈ K, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s ∈ K,
      0 < (p s + visibleConnectorActualTerminalHeight p gamma
        (visibleConnectorShiftedRuling R gamma theta eta) s •
          visibleConnectorShiftedRuling R gamma theta eta s) ⬝ᵥ
        (-visibleConnectorJ (visibleConnectorShiftedDirection theta eta s)) := by
  let W : ℝ × ℝ → Coord := fun q =>
    visibleConnectorShiftedRuling R gamma theta q.1 q.2
  let D : ℝ × ℝ → ℝ := fun q =>
    R * deriv theta q.2 * visibleConnectorActualExcessRatio R kappa q.1 q.2
  let Q : ℝ × ℝ → Coord := fun q =>
    visibleConnectorRescaledTerminalSource R p gamma theta kappa q.1 q.2
  let E : ℝ × ℝ → Coord := fun q =>
    -visibleConnectorJ (visibleConnectorShiftedDirection theta q.1 q.2)
  have hpc := hp.continuous
  have hgc := hgamma.continuous
  have htc := htheta.continuous
  have hkc := hkappa.continuous
  have hdpc := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hdtc := (contDiff_infty_iff_deriv.mp htheta).2.continuous
  have hW : Continuous W := by
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp only [W,visibleConnectorShiftedRuling,visibleConnectorActualRuling,
        visibleConnectorShiftedDirection,visibleConnectorUnitDirection,visibleConnectorJ,
        Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
    <;> fun_prop
  have hA : Continuous (fun q : ℝ × ℝ =>
      visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2) := by
    change Continuous (fun q : ℝ × ℝ => -(deriv p q.2 0 * W q 1 - deriv p q.2 1 * W q 0))
    fun_prop
  have hEr : Continuous (fun q : ℝ × ℝ =>
      visibleConnectorActualExcessRatio R kappa q.1 q.2) := by
    unfold visibleConnectorActualExcessRatio
    fun_prop
  have hD : Continuous D := by
    dsimp [D]
    fun_prop
  have hE : Continuous E := by
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp only [E,visibleConnectorShiftedDirection,visibleConnectorUnitDirection,
        visibleConnectorJ,Pi.neg_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    <;> fun_prop
  have hpositive : ∀ᶠ eta in 𝓝 (0 : ℝ), ∀ s ∈ K, 0 < Q (eta,s) ⬝ᵥ E (eta,s) := by
    apply hK.eventually_forall_of_forall_eventually
    intro s hs
    have hDz : D (0,s) ≠ 0 := by
      have hz : 0 < D (0,s) := by
        simpa [D,visibleConnectorActualExcessRatio] using
          mul_pos (mul_pos hR (htpos s hs)) (hk s hs)
      exact hz.ne'
    have hQ : ContinuousAt Q (0,s) := by
      change ContinuousAt (fun q : ℝ × ℝ => q.1 • p q.2 +
        (visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2 /
          D q) • W q) (0,s)
      exact (continuous_fst.continuousAt.smul
        (hpc.comp continuous_snd).continuousAt).add
          ((hA.continuousAt.div hD.continuousAt hDz).smul hW.continuousAt)
    have hdot : ContinuousAt (fun q => Q q ⬝ᵥ E q) (0,s) := by
      simp only [dotProduct,Fin.sum_univ_two]
      exact (((continuous_apply 0).continuousAt.comp hQ).mul
        ((continuous_apply 0).continuousAt.comp hE.continuousAt)).add
          (((continuous_apply 1).continuousAt.comp hQ).mul
            ((continuous_apply 1).continuousAt.comp hE.continuousAt))
    have hz : 0 < Q (0,s) ⬝ᵥ E (0,s) := by
      change 0 < visibleConnectorRescaledTerminalSource R p gamma theta kappa 0 s ⬝ᵥ
        (-visibleConnectorJ (visibleConnectorShiftedDirection theta 0 s))
      rw [visibleConnector_rescaled_terminal_zero hdecomp (hk s hs).ne']
      simp only [visibleConnectorShiftedDirection,sub_zero,smul_dotProduct,smul_eq_mul,
        dotProduct_neg,radialTerminal_J_unit,neg_mul_neg,mul_one]
      simpa only [neg_neg] using
        div_pos (mul_pos (hk s hs) (hpv s hs)) (mul_pos hR (htpos s hs))
    exact hdot.eventually (lt_mem_nhds hz)
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hpositive
  refine ⟨eps,heps,?_⟩
  intro eta heta hetaEps s hs
  have hm : eta ∈ Metric.ball (0 : ℝ) eps := by
    simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos heta] using hetaEps
  have hz := hball hm s hs
  change 0 < visibleConnectorRescaledTerminalSource R p gamma theta kappa eta s ⬝ᵥ
    (-visibleConnectorJ (visibleConnectorShiftedDirection theta eta s)) at hz
  rw [visibleConnector_rescaled_terminal_eq hgamma htheta hdecomp heta.ne',
    smul_dotProduct,smul_eq_mul] at hz
  exact pos_of_mul_pos_right hz heta.le

/-- The compact radial threshold applies to every real period representative
of the SAME actual ruling and terminal point. -/
theorem visibleConnector_periodic_actual_terminal_radial_positive
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (htheta : ContDiff ℝ ∞ theta) (hkappa : ContDiff ℝ ∞ kappa)
    (hpperiod : Periodic p L) (hgperiod : Periodic gamma L)
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hk : ∀ s, 0 < kappa s)
    (hpv : ∀ s, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s,
      0 < (p s + visibleConnectorActualTerminalHeight p gamma
        (visibleConnectorShiftedRuling R gamma theta eta) s •
          visibleConnectorShiftedRuling R gamma theta eta s) ⬝ᵥ
        (-visibleConnectorJ (visibleConnectorShiftedDirection theta eta s)) := by
  obtain ⟨eps,heps,h⟩ := visibleConnector_uniform_actual_terminal_radial_positive
    hR hp hgamma htheta hkappa (K := Icc (0 : ℝ) L) isCompact_Icc hdecomp
      (fun s _ => hk s) (fun s _ => hpv s) (fun s _ => htpos s)
  refine ⟨eps,heps,?_⟩
  intro eta heta hetaEps s
  let e := visibleConnectorShiftedDirection theta eta
  let w := visibleConnectorShiftedRuling R gamma theta eta
  have heperiod : Periodic e L := visibleConnector_shifted_direction_periodic hshift eta
  have hwperiod : Periodic w L := by
    intro r
    change visibleConnectorJ (gamma (r + L)) - R • e (r + L) =
      visibleConnectorJ (gamma r) - R • e r
    rw [hgperiod r,heperiod r]
  have he : ContDiff ℝ ∞ e :=
    visibleConnectorUnitDirection_contDiff.comp (htheta.sub contDiff_const)
  have hw : ContDiff ℝ ∞ w := visibleConnectorActualRuling_contDiff hgamma he
  have hdp := radialTerminal_curve_deriv_periodic hp hpperiod
  have hdg := radialTerminal_curve_deriv_periodic hgamma hgperiod
  have hdw := radialTerminal_curve_deriv_periodic hw hwperiod
  have hA : Periodic (visibleConnectorA p w) L := by
    intro r
    unfold visibleConnectorA
    rw [hdp r,hwperiod r]
  have hB : Periodic (visibleConnectorB gamma w) L := by
    intro r
    unfold visibleConnectorB
    rw [hdg r,hwperiod r]
  have hC : Periodic (visibleConnectorC gamma w) L := by
    intro r
    unfold visibleConnectorC
    rw [hB r,hdw r,hwperiod r]
  have ht : Periodic (visibleConnectorActualTerminalHeight p gamma w) L := by
    intro r
    unfold visibleConnectorActualTerminalHeight
    rw [hA r,hC r]
  let f : ℝ → ℝ := fun r =>
    (p r + visibleConnectorActualTerminalHeight p gamma w r • w r) ⬝ᵥ
      (-visibleConnectorJ (e r))
  have hf : Periodic f L := by
    intro r
    dsimp [f]
    rw [hpperiod r,ht r,hwperiod r,heperiod r]
  obtain ⟨n,hn,_⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico,zero_add] at hn
  have hh := h eta heta hetaEps (s - n • L) ⟨hn.1,hn.2.le⟩
  change 0 < f (s - n • L) at hh
  rw [hf.sub_zsmul_eq n] at hh
  exact hh

/-- Intersect the actual coefficient and radial thresholds once. Every smaller
positive angle then satisfies all four gates on the same periodic ruling. -/
theorem visibleConnector_periodic_actual_coefficients_and_terminal_radial
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (htheta : ContDiff ℝ ∞ theta) (hkappa : ContDiff ℝ ∞ kappa)
    (hpperiod : Periodic p L) (hgperiod : Periodic gamma L)
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hk : ∀ s, 0 < kappa s)
    (hpv : ∀ s, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (hgv : ∀ s, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ
      visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s,
      let w := visibleConnectorShiftedRuling R gamma theta eta
      0 < visibleConnectorA p w s ∧ 0 < visibleConnectorB gamma w s ∧
        0 < visibleConnectorC gamma w s ∧
        0 < (p s + visibleConnectorActualTerminalHeight p gamma w s • w s) ⬝ᵥ
          (-visibleConnectorJ (visibleConnectorShiftedDirection theta eta s)) := by
  obtain ⟨ec,hec,hc⟩ := visibleConnector_uniform_positive_actual_coefficients
    hR hp hgamma htheta hkappa (K := Icc (0 : ℝ) L) isCompact_Icc hdecomp
      (fun s _ => hk s) (fun s _ => hpv s) (fun s _ => hgv s) (fun s _ => htpos s)
  obtain ⟨er,her,hr⟩ := visibleConnector_periodic_actual_terminal_radial_positive
    hR hL hp hgamma htheta hkappa hpperiod hgperiod hshift hdecomp hk hpv htpos
  refine ⟨min ec er,lt_min hec her,?_⟩
  intro eta heta hetaEps s
  have hetaC : eta < ec := hetaEps.trans_le (min_le_left _ _)
  have hetaR : eta < er := hetaEps.trans_le (min_le_right _ _)
  let e := visibleConnectorShiftedDirection theta eta
  let w := visibleConnectorShiftedRuling R gamma theta eta
  have heperiod : Periodic e L := visibleConnector_shifted_direction_periodic hshift eta
  have hwperiod : Periodic w L := by
    intro r
    change visibleConnectorJ (gamma (r + L)) - R • e (r + L) =
      visibleConnectorJ (gamma r) - R • e r
    rw [hgperiod r,heperiod r]
  have he : ContDiff ℝ ∞ e :=
    visibleConnectorUnitDirection_contDiff.comp (htheta.sub contDiff_const)
  have hw : ContDiff ℝ ∞ w := visibleConnectorActualRuling_contDiff hgamma he
  have hdp := radialTerminal_curve_deriv_periodic hp hpperiod
  have hdg := radialTerminal_curve_deriv_periodic hgamma hgperiod
  have hdw := radialTerminal_curve_deriv_periodic hw hwperiod
  have hA : Periodic (visibleConnectorA p w) L := by
    intro r
    unfold visibleConnectorA
    rw [hdp r,hwperiod r]
  have hB : Periodic (visibleConnectorB gamma w) L := by
    intro r
    unfold visibleConnectorB
    rw [hdg r,hwperiod r]
  have hC : Periodic (visibleConnectorC gamma w) L := by
    intro r
    unfold visibleConnectorC
    rw [hB r,hdw r,hwperiod r]
  obtain ⟨n,hn,_⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
  simp only [mem_Ico,zero_add] at hn
  have hs := (hc eta heta hetaC (s - n • L) ⟨hn.1,hn.2.le⟩).2
  change 0 < visibleConnectorA p w (s - n • L) ∧
    0 < visibleConnectorB gamma w (s - n • L) ∧
    0 < visibleConnectorC gamma w (s - n • L) at hs
  rw [hA.sub_zsmul_eq n,hB.sub_zsmul_eq n,hC.sub_zsmul_eq n] at hs
  exact ⟨hs.1,hs.2.1,hs.2.2,hr eta heta hetaR s⟩

end
end TightVer401