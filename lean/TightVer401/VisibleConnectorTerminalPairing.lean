import TightVer401.VisibleConnectorRadialTerminal

/-! Actual terminal first-derivative positivity. We differentiate the rescaled
terminal expression in the curve variable and prove joint continuity of that
actual derivative at zero rotation. No C1 convergence or derivative sign is
assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def visibleConnectorActualTerminalSource (p gamma w : ℝ → Coord) (s : ℝ) : Coord :=
  p s + visibleConnectorActualTerminalHeight p gamma w s • w s

def terminalPairingWDeriv (R : ℝ) (gamma : ℝ → Coord)
    (theta : ℝ → ℝ) (eta s : ℝ) : Coord :=
  visibleConnectorJ (deriv gamma s) -
    R • (deriv theta s • visibleConnectorJ (visibleConnectorShiftedDirection theta eta s))

def terminalPairingDenom (R : ℝ) (theta kappa : ℝ → ℝ) (eta s : ℝ) : ℝ :=
  R * deriv theta s * visibleConnectorActualExcessRatio R kappa eta s

def terminalPairingDenomDeriv (R : ℝ) (theta kappa : ℝ → ℝ)
    (eta s : ℝ) : ℝ :=
  R * deriv (deriv theta) s * visibleConnectorActualExcessRatio R kappa eta s +
    (R * deriv theta s) * (deriv kappa s * Real.sinc eta)

def terminalPairingADeriv (R : ℝ) (p gamma : ℝ → Coord)
    (theta : ℝ → ℝ) (eta s : ℝ) : ℝ :=
  -(visibleConnectorDet (deriv (deriv p) s)
      (visibleConnectorShiftedRuling R gamma theta eta s) +
    visibleConnectorDet (deriv p s) (terminalPairingWDeriv R gamma theta eta s))

def terminalPairingRescaledDeriv (R : ℝ) (p gamma : ℝ → Coord)
    (theta kappa : ℝ → ℝ) (eta s : ℝ) : Coord :=
  eta • deriv p s +
    (visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta eta) s /
      terminalPairingDenom R theta kappa eta s) • terminalPairingWDeriv R gamma theta eta s +
    ((terminalPairingADeriv R p gamma theta eta s * terminalPairingDenom R theta kappa eta s -
      visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta eta) s *
        terminalPairingDenomDeriv R theta kappa eta s) /
      (terminalPairingDenom R theta kappa eta s)^2) •
      visibleConnectorShiftedRuling R gamma theta eta s

private theorem terminalPairing_det_hasDerivAt {v w : ℝ → Coord} {v' w' : Coord} {s : ℝ}
    (hv : HasDerivAt v v' s) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun r => visibleConnectorDet (v r) (w r))
      (visibleConnectorDet v' (w s) + visibleConnectorDet (v s) w') s := by
  have hvi (i : Fin 2) : HasDerivAt (fun r => v r i) (v' i) s := by
    simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt s hv
  have hwi (i : Fin 2) : HasDerivAt (fun r => w r i) (w' i) s := by
    simpa only [Function.comp_def,ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt s hw
  have hd := ((hvi 0).mul (hwi 1)).sub ((hvi 1).mul (hwi 0))
  change HasDerivAt (fun r => v r 0 * w r 1 - v r 1 * w r 0) _ s at hd
  convert hd using 1
  · rfl
  · simp only [visibleConnectorDet]
    ring

set_option backward.isDefEq.respectTransparency true in
theorem terminalPairing_rescaled_hasDerivAt {R : ℝ} {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    (eta s : ℝ) (hD : terminalPairingDenom R theta kappa eta s ≠ 0) :
    HasDerivAt (fun r => visibleConnectorRescaledTerminalSource R p gamma theta kappa eta r)
      (terminalPairingRescaledDeriv R p gamma theta kappa eta s) s := by
  have hpd := (hp.differentiable (by simp) s).hasDerivAt
  have hpp := ((contDiff_infty_iff_deriv.mp hp).2.differentiable (by simp) s).hasDerivAt
  have htd := (ht.differentiable (by simp) s).hasDerivAt
  have htt := ((contDiff_infty_iff_deriv.mp ht).2.differentiable (by simp) s).hasDerivAt
  have hkd := (hk.differentiable (by simp) s).hasDerivAt
  have hwd : HasDerivAt (visibleConnectorShiftedRuling R gamma theta eta)
      (terminalPairingWDeriv R gamma theta eta s) s :=
    (visibleConnectorJ_hasDerivAt ((hg.differentiable (by simp) s).hasDerivAt)).sub
      ((visibleConnectorUnitDirection_hasDerivAt (htd.sub_const eta)).const_smul R)
  have hAd := (terminalPairing_det_hasDerivAt hpp hwd).neg
  change HasDerivAt (visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta eta))
    (terminalPairingADeriv R p gamma theta eta s) s at hAd
  have hEd : HasDerivAt (fun r => visibleConnectorActualExcessRatio R kappa eta r)
      (deriv kappa s * Real.sinc eta) s := by
    simpa only [visibleConnectorActualExcessRatio] using
      (hkd.mul_const (Real.sinc eta)).sub_const (R * eta / 2 * Real.sinc (eta/2)^2)
  have hDd : HasDerivAt (terminalPairingDenom R theta kappa eta)
      (terminalPairingDenomDeriv R theta kappa eta s) s := by
    convert (htt.const_mul R).mul hEd using 1 <;> rfl
  have h := (hpd.const_smul eta).add ((hAd.div hDd hD).smul hwd)
  convert h using 1 <;> first
  | rfl
  | simp [visibleConnectorRescaledTerminalSource,terminalPairingDenom,
      terminalPairingRescaledDeriv,add_assoc]

private theorem terminalPairing_zero_positive {R : ℝ} (hR : 0 < R)
    {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    {s : ℝ} (hkpos : 0 < kappa s)
    (hpv : 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : 0 < deriv theta s) :
    0 < terminalPairingRescaledDeriv R p gamma theta kappa 0 s ⬝ᵥ
      visibleConnectorUnitDirection (theta s) := by
  let lam : ℝ → ℝ := fun r =>
    kappa r * (deriv p r ⬝ᵥ visibleConnectorUnitDirection (theta r)) / (R * deriv theta r)
  have hU : ContDiff ℝ ∞ (fun r => visibleConnectorUnitDirection (theta r)) :=
    visibleConnectorUnitDirection_contDiff.comp ht
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdt := (contDiff_infty_iff_deriv.mp ht).2
  have hnum : ContDiff ℝ ∞ (fun r =>
      kappa r * (deriv p r ⬝ᵥ visibleConnectorUnitDirection (theta r))) := by
    have hkc := hk
    simp only [dotProduct,Fin.sum_univ_two]
    fun_prop
  have hlam : ContDiffAt ℝ ∞ lam s :=
    hnum.contDiffAt.div ((contDiff_const (c := R)).mul hdt).contDiffAt
      (mul_pos hR htpos).ne'
  have hld := (hlam.differentiableAt (by simp)).hasDerivAt
  have hud := visibleConnectorUnitDirection_hasDerivAt
    ((ht.differentiable (by simp) s).hasDerivAt)
  have hjd := visibleConnectorJ_hasDerivAt hud
  have hmodel := hld.neg.smul hjd
  have heq : (fun r => -lam r • visibleConnectorJ (visibleConnectorUnitDirection (theta r)))
      =ᶠ[𝓝 s] (fun r => visibleConnectorRescaledTerminalSource R p gamma theta kappa 0 r) := by
    have he := hk.continuous.continuousAt.eventually (lt_mem_nhds hkpos)
    filter_upwards [he] with r hr
    exact (visibleConnector_rescaled_terminal_zero hdecomp hr.ne').symm
  have hactual := hmodel.congr_of_eventuallyEq heq.symm
  have hDz : terminalPairingDenom R theta kappa 0 s ≠ 0 := by
    simpa [terminalPairingDenom,visibleConnectorActualExcessRatio] using
      (mul_pos (mul_pos hR htpos) hkpos).ne'
  have hq := terminalPairing_rescaled_hasDerivAt hp hg ht hk 0 s hDz
  rw [hq.unique hactual]
  have hunit := Real.cos_sq_add_sin_sq (theta s)
  have hdot :
      ((-lam s) • visibleConnectorJ (deriv theta s •
        visibleConnectorJ (visibleConnectorUnitDirection (theta s))) +
          (-deriv lam s) • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) ⬝ᵥ
        visibleConnectorUnitDirection (theta s) = lam s * deriv theta s := by
    simp only [visibleConnectorJ,visibleConnectorUnitDirection,dotProduct,Fin.sum_univ_two,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
    linear_combination (lam s * deriv theta s) * hunit
  change 0 < (-lam s • visibleConnectorJ (deriv theta s • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) +
    -deriv lam s • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) ⬝ᵥ visibleConnectorUnitDirection (theta s)
  rw [hdot]
  exact mul_pos (div_pos (mul_pos hkpos hpv) (mul_pos hR htpos)) htpos

/-- Actual derivative continuity, proved from the differentiated rescaled
formula. Sinc is only needed continuously in eta: no analytic extension or C1
closeness hypothesis is introduced. -/
theorem visibleConnector_uniform_actual_terminal_direction_pairing
    {R : ℝ} (hR : 0 < R) {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ} {K : Set ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa) (hK : IsCompact K)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hkpos : ∀ s ∈ K, 0 < kappa s)
    (hpv : ∀ s ∈ K, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s ∈ K, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s ∈ K,
      0 < deriv (visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta)) s ⬝ᵥ
        visibleConnectorShiftedDirection theta eta s := by
  let W : ℝ × ℝ → Coord := fun q => visibleConnectorShiftedRuling R gamma theta q.1 q.2
  let Wd : ℝ × ℝ → Coord := fun q => terminalPairingWDeriv R gamma theta q.1 q.2
  let A : ℝ × ℝ → ℝ := fun q =>
    visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2
  let Ad : ℝ × ℝ → ℝ := fun q => terminalPairingADeriv R p gamma theta q.1 q.2
  let D : ℝ × ℝ → ℝ := fun q => terminalPairingDenom R theta kappa q.1 q.2
  let Dd : ℝ × ℝ → ℝ := fun q => terminalPairingDenomDeriv R theta kappa q.1 q.2
  let Qd : ℝ × ℝ → Coord := fun q => terminalPairingRescaledDeriv R p gamma theta kappa q.1 q.2
  let E : ℝ × ℝ → Coord := fun q => visibleConnectorShiftedDirection theta q.1 q.2
  have hpc := hp.continuous
  have hgc := hg.continuous
  have htc := ht.continuous
  have hkc := hk.continuous
  have hdpc := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hdgc := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hdtc := (contDiff_infty_iff_deriv.mp ht).2.continuous
  have hdkc := (contDiff_infty_iff_deriv.mp hk).2.continuous
  have hdppc := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hp).2).2.continuous
  have hdttc := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp ht).2).2.continuous
  have hE : Continuous E := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [E,visibleConnectorShiftedDirection,visibleConnectorUnitDirection,
      Matrix.cons_val_zero,Matrix.cons_val_one] <;> fun_prop
  have hW : Continuous W := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [W,visibleConnectorShiftedRuling,visibleConnectorActualRuling,
      visibleConnectorShiftedDirection,visibleConnectorUnitDirection,visibleConnectorJ,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one] <;> fun_prop
  have hWd : Continuous Wd := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Wd,terminalPairingWDeriv,visibleConnectorJ,
      visibleConnectorShiftedDirection,visibleConnectorUnitDirection,Pi.sub_apply,Pi.smul_apply,
      smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one] <;> fun_prop
  have hA : Continuous A := by
    change Continuous (fun q : ℝ × ℝ => -(deriv p q.2 0 * W q 1 - deriv p q.2 1 * W q 0))
    fun_prop
  have hAd : Continuous Ad := by
    change Continuous (fun q : ℝ × ℝ => -(deriv (deriv p) q.2 0 * W q 1 - deriv (deriv p) q.2 1 * W q 0 +
      (deriv p q.2 0 * Wd q 1 - deriv p q.2 1 * Wd q 0)))
    fun_prop
  have hEr : Continuous (fun q : ℝ × ℝ => visibleConnectorActualExcessRatio R kappa q.1 q.2) := by
    unfold visibleConnectorActualExcessRatio
    fun_prop
  have hD : Continuous D := by
    dsimp [D,terminalPairingDenom]
    fun_prop
  have hDd : Continuous Dd := by
    dsimp [Dd,terminalPairingDenomDeriv]
    fun_prop
  have hevent : ∀ᶠ eta in 𝓝 (0 : ℝ), ∀ s ∈ K,
      0 < D (eta,s) ∧ 0 < Qd (eta,s) ⬝ᵥ E (eta,s) := by
    apply hK.eventually_forall_of_forall_eventually
    intro s hs
    have hDz : 0 < D (0,s) := by
      simpa [D,terminalPairingDenom,visibleConnectorActualExcessRatio] using
        mul_pos (mul_pos hR (htpos s hs)) (hkpos s hs)
    have hQc : ContinuousAt Qd (0,s) := by
      change ContinuousAt (fun q : ℝ × ℝ => q.1 • deriv p q.2 +
        (A q / D q) • Wd q +
          ((Ad q * D q - A q * Dd q) / (D q)^2) • W q) (0,s)
      exact ((continuous_fst.continuousAt.smul (hdpc.comp continuous_snd).continuousAt).add
        ((hA.continuousAt.div hD.continuousAt hDz.ne').smul hWd.continuousAt)).add
          (((hAd.continuousAt.mul hD.continuousAt).sub
            (hA.continuousAt.mul hDd.continuousAt)).div
              (hD.continuousAt.pow 2) (pow_ne_zero 2 hDz.ne') |>.smul hW.continuousAt)
    have hdot : ContinuousAt (fun q => Qd q ⬝ᵥ E q) (0,s) := by
      simp only [dotProduct,Fin.sum_univ_two]
      exact (((continuous_apply 0).continuousAt.comp hQc).mul
        ((continuous_apply 0).continuousAt.comp hE.continuousAt)).add
          (((continuous_apply 1).continuousAt.comp hQc).mul
            ((continuous_apply 1).continuousAt.comp hE.continuousAt))
    have hpos : 0 < Qd (0,s) ⬝ᵥ E (0,s) := by
      simpa only [Qd,E,visibleConnectorShiftedDirection,sub_zero] using
        terminalPairing_zero_positive hR hp hg ht hk hdecomp (hkpos s hs) (hpv s hs) (htpos s hs)
    exact (hD.continuousAt.eventually (lt_mem_nhds hDz)).and
      (hdot.eventually (lt_mem_nhds hpos))
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨eps,heps,?_⟩
  intro eta heta hetaEps s hs
  have hm : eta ∈ Metric.ball (0 : ℝ) eps := by
    simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos heta] using hetaEps
  obtain ⟨hDz,hpos⟩ := hball hm s hs
  have he : ContDiff ℝ ∞ (visibleConnectorShiftedDirection theta eta) :=
    visibleConnectorUnitDirection_contDiff.comp (ht.sub contDiff_const)
  have hw : ContDiff ℝ ∞ (visibleConnectorShiftedRuling R gamma theta eta) :=
    visibleConnectorActualRuling_contDiff hg he
  have hCs : visibleConnectorC gamma (visibleConnectorShiftedRuling R gamma theta eta) s ≠ 0 := by
    have hdir := visibleConnectorUnitDirection_hasDerivAt
      (((ht.differentiable (by simp) s).hasDerivAt).sub_const eta)
    have hu : visibleConnectorShiftedDirection theta eta s ⬝ᵥ
        visibleConnectorShiftedDirection theta eta s = 1 := by
      simpa [visibleConnectorShiftedDirection,visibleConnectorUnitDirection,dotProduct,
        Fin.sum_univ_two,pow_two] using Real.cos_sq_add_sin_sq (theta s - eta)
    have hc := visibleConnector_actual_ruling_C_formula (R := R) hg hdir hu
    change visibleConnectorC gamma (visibleConnectorShiftedRuling R gamma theta eta) s =
      R * deriv theta s *
        (visibleConnectorJ (gamma s) ⬝ᵥ visibleConnectorShiftedDirection theta eta s - R) at hc
    rw [visibleConnector_actual_excess_factor hdecomp eta s] at hc
    have hcD : visibleConnectorC gamma (visibleConnectorShiftedRuling R gamma theta eta) s =
        eta * D (eta,s) := by
      rw [hc]
      dsimp [D,terminalPairingDenom]
      ring
    rw [hcD]
    exact (mul_pos heta hDz).ne'
  have hterm : ContDiffAt ℝ ∞ (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorShiftedRuling R gamma theta eta)) s := by
    exact hp.contDiffAt.add
      (((visibleConnectorA_contDiff hp hw).contDiffAt.div
        (visibleConnectorC_contDiff hg hw).contDiffAt hCs).smul hw.contDiffAt)
  have hdterm := (hterm.differentiableAt (by simp)).hasDerivAt
  have hdscale := hdterm.const_smul eta
  have heq : (fun r => eta • visibleConnectorActualTerminalSource p gamma
      (visibleConnectorShiftedRuling R gamma theta eta) r) =
      (fun r => visibleConnectorRescaledTerminalSource R p gamma theta kappa eta r) := by
    funext r
    exact (visibleConnector_rescaled_terminal_eq hg ht hdecomp heta.ne').symm
  change HasDerivAt (fun r => eta • visibleConnectorActualTerminalSource p gamma
    (visibleConnectorShiftedRuling R gamma theta eta) r) _ s at hdscale
  rw [heq] at hdscale
  have hdactual := terminalPairing_rescaled_hasDerivAt hp hg ht hk eta s hDz.ne'
  have hv := hdactual.unique hdscale
  change 0 < terminalPairingRescaledDeriv R p gamma theta kappa eta s ⬝ᵥ
    visibleConnectorShiftedDirection theta eta s at hpos
  rw [hv,smul_dotProduct,smul_eq_mul] at hpos
  exact pos_of_mul_pos_right hpos heta.le

private theorem terminalPairing_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f L) : Periodic (deriv f) L := by
  intro r
  have hd : HasDerivAt (fun s => f (s + L)) (deriv f (r + L)) r := by
    simpa only [Function.comp_def,id_eq,one_smul] using ((hf.differentiable (by simp) (r + L)).hasDerivAt).scomp r
      ((hasDerivAt_id r).add_const L)
  exact (hd.congr_of_eventuallyEq (f₁ := f)
    (Eventually.of_forall (fun s => (hp s).symm))).deriv.symm

/-- One threshold for the actual coefficients, radial positivity and positive
terminal Hessian trace. Both actual terminal curves are regular. All statements
concern the same shifted ruling at the same eta and every real representative. -/
theorem visibleConnector_periodic_actual_positive_terminal_pair
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
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
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s,
      let e := visibleConnectorShiftedDirection theta eta
      let w := visibleConnectorShiftedRuling R gamma theta eta
      let T := visibleConnectorActualTerminalSource p gamma w
      let Y := fun r => visibleConnectorGradient p gamma w
        (![r,visibleConnectorActualTerminalHeight p gamma w r] : Coord)
      0 < visibleConnectorA p w s ∧ 0 < visibleConnectorB gamma w s ∧
        0 < visibleConnectorC gamma w s ∧ 0 < T s ⬝ᵥ (-visibleConnectorJ (e s)) ∧
        0 < deriv T s ⬝ᵥ deriv Y s ∧ deriv T s ≠ 0 ∧ deriv Y s ≠ 0 := by
  obtain ⟨eb,heb,hb⟩ := visibleConnector_periodic_actual_coefficients_and_terminal_radial
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  obtain ⟨ep,hep,hpderiv⟩ := visibleConnector_uniform_actual_terminal_direction_pairing
    hR hp hg ht hk (K := Icc (0 : ℝ) L) isCompact_Icc hdecomp
      (fun s _ => hkpos s) (fun s _ => hpv s) (fun s _ => htpos s)
  refine ⟨min eb ep,lt_min heb hep,?_⟩
  intro eta heta hetaEps s
  have hetaB := hetaEps.trans_le (min_le_left eb ep)
  have hetaP := hetaEps.trans_le (min_le_right eb ep)
  let e := visibleConnectorShiftedDirection theta eta
  let w := visibleConnectorShiftedRuling R gamma theta eta
  let T := visibleConnectorActualTerminalSource p gamma w
  let Y := fun r => visibleConnectorGradient p gamma w
    (![r,visibleConnectorActualTerminalHeight p gamma w r] : Coord)
  have he : ContDiff ℝ ∞ e :=
    visibleConnectorUnitDirection_contDiff.comp (ht.sub contDiff_const)
  have hw : ContDiff ℝ ∞ w := visibleConnectorActualRuling_contDiff hg he
  have heperiod : Periodic e L := visibleConnector_shifted_direction_periodic hshift eta
  have hwperiod : Periodic w L := by
    intro r
    change visibleConnectorJ (gamma (r + L)) - R • e (r + L) =
      visibleConnectorJ (gamma r) - R • e r
    rw [hgperiod r,heperiod r]
  have hdp := terminalPairing_deriv_periodic hp hpperiod
  have hdg := terminalPairing_deriv_periodic hg hgperiod
  have hdw := terminalPairing_deriv_periodic hw hwperiod
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
  have hheight : ContDiff ℝ ∞ (visibleConnectorActualTerminalHeight p gamma w) :=
    visibleConnectorActualTerminalHeight_contDiff hp hg hw
      (fun r => (hb eta heta hetaB r).2.2.1.ne')
  have hT : ContDiff ℝ ∞ T := hp.add (hheight.smul hw)
  have htperiod : Periodic (visibleConnectorActualTerminalHeight p gamma w) L := by
    intro r
    unfold visibleConnectorActualTerminalHeight
    rw [hA r,hC r]
  have hTperiod : Periodic T L := by
    intro r
    dsimp [T,visibleConnectorActualTerminalSource]
    rw [hpperiod r,htperiod r,hwperiod r]
  have hdTperiod := terminalPairing_deriv_periodic hT hTperiod
  have hdirpair : 0 < deriv T s ⬝ᵥ e s := by
    obtain ⟨n,hn,_⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico,zero_add] at hn
    have hh := hpderiv eta heta hetaP (s - n • L) ⟨hn.1,hn.2.le⟩
    change 0 < deriv T (s - n • L) ⬝ᵥ e (s - n • L) at hh
    rw [hdTperiod.sub_zsmul_eq n,heperiod.sub_zsmul_eq n] at hh
    exact hh
  have hcircle : ∀ r, Y r = -R • visibleConnectorJ (e r) := by
    intro r
    have hu : e r ⬝ᵥ e r = 1 := by
      simpa [e,visibleConnectorShiftedDirection,visibleConnectorUnitDirection,dotProduct,
        Fin.sum_univ_two,pow_two] using Real.cos_sq_add_sin_sq (theta r - eta)
    obtain ⟨ha,hb',hc,hr⟩ := hb eta heta hetaB r
    exact (visibleConnector_actual_ruling_circle_terminal hR hu ha hb' hc).2.2.1
  have hunitderiv := visibleConnectorUnitDirection_hasDerivAt
    (((ht.differentiable (by simp) s).hasDerivAt).sub_const eta)
  have hrot := (visibleConnectorJ_hasDerivAt hunitderiv).const_smul (-R)
  have hY : HasDerivAt Y ((R * deriv theta s) • e s) s := by
    have hrot' : HasDerivAt (fun r => -R • visibleConnectorJ (e r))
        ((R * deriv theta s) • e s) s := by
      have hd : -R • visibleConnectorJ (deriv theta s • visibleConnectorJ (visibleConnectorUnitDirection (theta s - eta))) =
          (R * deriv theta s) • e s := by
        ext i
        fin_cases i <;> simp [e,visibleConnectorShiftedDirection,visibleConnectorJ,visibleConnectorUnitDirection] <;> ring
      rw [hd] at hrot
      exact hrot
    exact hrot'.congr_of_eventuallyEq (Eventually.of_forall hcircle)
  have hpair : 0 < deriv T s ⬝ᵥ deriv Y s := by
    rw [hY.deriv,dotProduct_smul,smul_eq_mul]
    exact mul_pos (mul_pos hR (htpos s)) hdirpair
  obtain ⟨ha,hb',hc,hr⟩ := hb eta heta hetaB s
  refine ⟨ha,hb',hc,hr,hpair,?_,?_⟩
  · intro hz
    have he : deriv T s ⬝ᵥ deriv Y s = 0 := by rw [hz]; simp
    linarith
  · intro hz
    have he : deriv T s ⬝ᵥ deriv Y s = 0 := by rw [hz]; simp
    linarith

end
end TightVer401