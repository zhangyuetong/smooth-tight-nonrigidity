import TightVer401.VisibleConnectorTerminalPairing
import TightVer401.PositiveExitConstructionBalancedTurn
import TightVer401.PositiveAngularLift

/-! The SAME actual terminal ruling is a Jordan curve for a uniformly small
positive rotation. The determinant margin comes from the differentiated
rescaled expression; its turn comes from its explicit positive radial limit.
No terminal embedding, angular phase, or inverse is supplied as a premise. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private def terminalJordanComplex : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)))

private theorem terminalJordanComplex_apply (q : Coord) :
    terminalJordanComplex q = positiveExitComplexPoint q := by
  apply Complex.ext <;> simp [terminalJordanComplex, positiveExitComplexPoint,
    Complex.mul_re, Complex.mul_im]

private theorem terminalJordan_complex_smul (a : ℝ) (q : Coord) :
    positiveExitComplexPoint (a • q) = a • positiveExitComplexPoint q := by
  rw [← terminalJordanComplex_apply, ← terminalJordanComplex_apply]
  exact terminalJordanComplex.map_smul a q

private theorem terminalJordan_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have h := ((hf.differentiable (by simp) (s + L)).hasDerivAt).scomp s
    ((hasDerivAt_id s).add_const L)
  have h' : HasDerivAt (fun r => f (r + L)) (deriv f (s + L)) s := by
    simpa only [Function.comp_def,id_eq,one_smul] using h
  exact (h'.congr_of_eventuallyEq
    (Eventually.of_forall (fun r => (hp r).symm))).deriv.symm

private theorem terminalJordan_det_zero {R : ℝ} (hR : 0 < R)
    {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hkpos : ∀ s, 0 < kappa s) (htpos : ∀ s, 0 < deriv theta s)
    {s : ℝ} (hpv : 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s)) :
    0 < visibleConnectorDet
      (visibleConnectorRescaledTerminalSource R p gamma theta kappa 0 s)
      (terminalPairingRescaledDeriv R p gamma theta kappa 0 s) := by
  let lam : ℝ → ℝ := fun r =>
    kappa r * (deriv p r ⬝ᵥ visibleConnectorUnitDirection (theta r)) /
      (R * deriv theta r)
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdt := (contDiff_infty_iff_deriv.mp ht).2
  have hu : ContDiff ℝ ∞ (fun r => visibleConnectorUnitDirection (theta r)) :=
    visibleConnectorUnitDirection_contDiff.comp ht
  have hnum : ContDiff ℝ ∞ (fun r =>
      kappa r * (deriv p r ⬝ᵥ visibleConnectorUnitDirection (theta r))) := by
    simp only [dotProduct, Fin.sum_univ_two]
    fun_prop
  have hlam : ContDiff ℝ ∞ lam := hnum.div (contDiff_const.mul hdt)
    (fun r => (mul_pos hR (htpos r)).ne')
  have hld := (hlam.differentiable (by simp) s).hasDerivAt
  have hud := visibleConnectorUnitDirection_hasDerivAt
    ((ht.differentiable (by simp) s).hasDerivAt)
  have hdmodel := hld.neg.smul (visibleConnectorJ_hasDerivAt hud)
  have heq : (fun r => -lam r • visibleConnectorJ (visibleConnectorUnitDirection (theta r))) =
      (fun r => visibleConnectorRescaledTerminalSource R p gamma theta kappa 0 r) := by
    funext r
    exact (visibleConnector_rescaled_terminal_zero hdecomp (hkpos r).ne').symm
  change HasDerivAt (fun r => -lam r • visibleConnectorJ
    (visibleConnectorUnitDirection (theta r))) _ s at hdmodel
  rw [heq] at hdmodel
  have hD : terminalPairingDenom R theta kappa 0 s ≠ 0 := by
    simpa [terminalPairingDenom, visibleConnectorActualExcessRatio] using
      (mul_pos (mul_pos hR (htpos s)) (hkpos s)).ne'
  have hactual := terminalPairing_rescaled_hasDerivAt hp hg ht hk 0 s hD
  rw [hactual.unique hdmodel, visibleConnector_rescaled_terminal_zero hdecomp (hkpos s).ne']
  change 0 < visibleConnectorDet (-lam s • visibleConnectorJ
    (visibleConnectorUnitDirection (theta s))) _
  have he : visibleConnectorDet (-lam s • visibleConnectorJ
      (visibleConnectorUnitDirection (theta s)))
      ((-lam s) • visibleConnectorJ (deriv theta s • visibleConnectorJ
        (visibleConnectorUnitDirection (theta s))) +
        (-deriv lam s) • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) =
        lam s ^ 2 * deriv theta s := by
    simp only [visibleConnectorDet, visibleConnectorJ, visibleConnectorUnitDirection,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (lam s ^ 2 * deriv theta s) * Real.cos_sq_add_sin_sq (theta s)
  simp only [Pi.neg_apply]
  rw [he]
  exact mul_pos (sq_pos_of_pos (div_pos (mul_pos (hkpos s) hpv)
    (mul_pos hR (htpos s)))) (htpos s)

/-- A uniform actual determinant and C0 margin for the differentiated rescaled
terminal curve. The requested approximation tolerance is ordinary numerical data. -/
theorem visibleConnector_uniform_rescaled_terminal_det_and_close
    {R : ℝ} (hR : 0 < R) {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hg : ContDiff ℝ ∞ gamma)
    (ht : ContDiff ℝ ∞ theta) (hk : ContDiff ℝ ∞ kappa)
    {K : Set ℝ} (hK : IsCompact K)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hkpos : ∀ s, 0 < kappa s) (htpos : ∀ s, 0 < deriv theta s)
    (hpv : ∀ s ∈ K, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eps > 0, ∀ eta, |eta| < eps → ∀ s ∈ K,
      0 < terminalPairingDenom R theta kappa eta s ∧
      0 < visibleConnectorDet
        (visibleConnectorRescaledTerminalSource R p gamma theta kappa eta s)
        (deriv (visibleConnectorRescaledTerminalSource R p gamma theta kappa eta) s) ∧
      ‖positiveExitComplexPoint
        (visibleConnectorRescaledTerminalSource R p gamma theta kappa eta s) -
        positiveExitComplexPoint
          (visibleConnectorRescaledTerminalSource R p gamma theta kappa 0 s)‖ < epsilon := by
  let W : ℝ × ℝ → Coord := fun q => visibleConnectorShiftedRuling R gamma theta q.1 q.2
  let Wd : ℝ × ℝ → Coord := fun q => terminalPairingWDeriv R gamma theta q.1 q.2
  let A : ℝ × ℝ → ℝ := fun q =>
    visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2
  let Ad : ℝ × ℝ → ℝ := fun q => terminalPairingADeriv R p gamma theta q.1 q.2
  let D : ℝ × ℝ → ℝ := fun q => terminalPairingDenom R theta kappa q.1 q.2
  let Dd : ℝ × ℝ → ℝ := fun q => terminalPairingDenomDeriv R theta kappa q.1 q.2
  let Q : ℝ × ℝ → Coord := fun q =>
    visibleConnectorRescaledTerminalSource R p gamma theta kappa q.1 q.2
  let Qd : ℝ × ℝ → Coord := fun q =>
    terminalPairingRescaledDeriv R p gamma theta kappa q.1 q.2
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
  have hW : Continuous W := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [W, visibleConnectorShiftedRuling, visibleConnectorActualRuling,
      visibleConnectorShiftedDirection, visibleConnectorUnitDirection, visibleConnectorJ,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop
  have hWd : Continuous Wd := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Wd, terminalPairingWDeriv, visibleConnectorJ,
      visibleConnectorShiftedDirection, visibleConnectorUnitDirection, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop
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
  have hD : Continuous D := by dsimp [D, terminalPairingDenom]; fun_prop
  have hDd : Continuous Dd := by dsimp [Dd, terminalPairingDenomDeriv]; fun_prop
  have hQzero : Continuous (fun s => Q (0, s)) := by
    apply continuous_pi
    intro i
    have hd0 (s : ℝ) : D (0, s) ≠ 0 := by
      simpa [D, terminalPairingDenom, visibleConnectorActualExcessRatio] using
        (mul_pos (mul_pos hR (htpos s)) (hkpos s)).ne'
    change Continuous (fun s => (0 : ℝ) * p s i + (A (0,s) / D (0,s)) * W (0,s) i)
    exact (continuous_const.mul ((continuous_apply i).comp hpc)).add
      (((hA.comp (continuous_const.prodMk continuous_id)).div
        (hD.comp (continuous_const.prodMk continuous_id)) hd0).mul
        ((continuous_apply i).comp (hW.comp (continuous_const.prodMk continuous_id))))
  have hevent : ∀ᶠ eta in 𝓝 (0 : ℝ), ∀ s ∈ K,
      0 < D (eta,s) ∧ 0 < visibleConnectorDet (Q (eta,s)) (Qd (eta,s)) ∧
        ‖terminalJordanComplex (Q (eta,s)) - terminalJordanComplex (Q (0,s))‖ < epsilon := by
    apply hK.eventually_forall_of_forall_eventually
    intro s hs
    have hDz : 0 < D (0,s) := by
      simpa [D, terminalPairingDenom, visibleConnectorActualExcessRatio] using
        mul_pos (mul_pos hR (htpos s)) (hkpos s)
    have hQc : ContinuousAt Q (0,s) := by
      change ContinuousAt (fun q : ℝ × ℝ => q.1 • p q.2 + (A q / D q) • W q) (0,s)
      exact (continuous_fst.continuousAt.smul (hpc.comp continuous_snd).continuousAt).add
        ((hA.continuousAt.div hD.continuousAt hDz.ne').smul hW.continuousAt)
    have hQdc : ContinuousAt Qd (0,s) := by
      change ContinuousAt (fun q : ℝ × ℝ => q.1 • deriv p q.2 +
        (A q / D q) • Wd q + ((Ad q * D q - A q * Dd q) / (D q)^2) • W q) (0,s)
      exact ((continuous_fst.continuousAt.smul (hdpc.comp continuous_snd).continuousAt).add
        ((hA.continuousAt.div hD.continuousAt hDz.ne').smul hWd.continuousAt)).add
          (((hAd.continuousAt.mul hD.continuousAt).sub (hA.continuousAt.mul hDd.continuousAt)).div
            (hD.continuousAt.pow 2) (pow_ne_zero 2 hDz.ne') |>.smul hW.continuousAt)
    have hdet : ContinuousAt (fun q => visibleConnectorDet (Q q) (Qd q)) (0,s) := by
      unfold visibleConnectorDet
      exact (((continuous_apply 0).continuousAt.comp hQc).mul
        ((continuous_apply 1).continuousAt.comp hQdc)).sub
          (((continuous_apply 1).continuousAt.comp hQc).mul
            ((continuous_apply 0).continuousAt.comp hQdc))
    have hclose : ContinuousAt (fun q : ℝ × ℝ =>
        ‖terminalJordanComplex (Q q) - terminalJordanComplex (Q (0,q.2))‖) (0,s) :=
      ((terminalJordanComplex.continuous.continuousAt.comp hQc).sub
        ((terminalJordanComplex.continuous.comp hQzero).comp continuous_snd).continuousAt).norm
    have hclose0 : ‖terminalJordanComplex (Q (0,s)) - terminalJordanComplex (Q (0,s))‖ < epsilon :=
      by simpa only [sub_self, norm_zero] using hepsilon
    exact (hD.continuousAt.eventually (lt_mem_nhds hDz)).and
      ((hdet.eventually (lt_mem_nhds
        (terminalJordan_det_zero hR hp hg ht hk hdecomp hkpos htpos (hpv s hs)))).and
          (hclose.eventually (gt_mem_nhds hclose0)))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨eps, heps, ?_⟩
  intro eta heta s hs
  have hm : eta ∈ Metric.ball (0 : ℝ) eps := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using heta
  obtain ⟨hd, hdet, hclose⟩ := hball hm s hs
  have hderiv := (terminalPairing_rescaled_hasDerivAt hp hg ht hk eta s hd.ne').deriv
  refine ⟨hd, ?_, ?_⟩
  · simpa only [Q, Qd, hderiv] using hdet
  · simpa only [Q, terminalJordanComplex_apply] using hclose

/-- The actual smooth positive phase of a regular periodic curve with positive
polar determinant makes its native circle lift an embedding. -/
theorem visibleConnector_positive_det_turn_jordan {f : ℝ → Coord} {L : ℝ}
    (hL : 0 < L) (hf : ContDiff ℝ ∞ f) (hp : Periodic f L)
    (hne : ∀ s, positiveExitComplexTrace f s ≠ 0)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace f) L)
    (hdet : ∀ s, 0 < visibleConnectorDet (f s) (deriv f s)) :
    InjOn f (Ico 0 L) ∧
      Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘ positiveExitComplexTrace f)) := by
  have hc : ContDiff ℝ ∞ (positiveExitComplexTrace f) := by
    simpa only [Function.comp_def, terminalJordanComplex_apply, positiveExitComplexTrace] using
      terminalJordanComplex.contDiff.comp hf
  have hcp : Periodic (positiveExitComplexTrace f) L := by intro s; dsimp [positiveExitComplexTrace]; rw [hp s]
  obtain ⟨phi, hphi, hphase, hshift⟩ := positiveExit_actual_positive_argument_lift hc hcp hne hturn
  let rho : ℝ → ℝ := fun s => ‖positiveExitComplexTrace f s‖
  have hrpos (s : ℝ) : 0 < rho s := norm_pos_iff.mpr (hne s)
  have hr : ContDiff ℝ ∞ rho := by
    have heq : rho = fun s => Real.sqrt ((f s 0)^2 + (f s 1)^2) := by
      funext s
      simp [rho, positiveExitComplexTrace, positiveExitComplexPoint, Complex.norm_def, Complex.normSq_apply, pow_two]
    rw [heq]
    have h0 : ContDiff ℝ ∞ (fun s => f s 0) := (contDiff_apply ℝ ℝ (0 : Fin 2)).comp hf
    have h1 : ContDiff ℝ ∞ (fun s => f s 1) := (contDiff_apply ℝ ℝ (1 : Fin 2)).comp hf
    apply ((h0.pow 2).add (h1.pow 2)).sqrt
    intro s
    have hsq : ‖positiveExitComplexTrace f s‖ ^ 2 ≠ 0 :=
      (sq_pos_of_pos (hrpos s)).ne'
    rw [Complex.sq_norm] at hsq
    simpa only [Complex.normSq_apply, positiveExitComplexTrace, Function.comp_def,
      positiveExitComplexPoint, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero, pow_two] using hsq
  have hrep (s : ℝ) : f s = rho s • visibleConnectorUnitDirection (phi s) := by
    have he := congrArg Subtype.val (hphase s)
    rw [complexCircleDirection_normalized (hne s), Circle.coe_exp, Complex.exp_mul_I] at he
    have hx : (rho s)⁻¹ * f s 0 = Real.cos (phi s) := by
      simpa [rho, positiveExitComplexTrace, positiveExitComplexPoint, Complex.real_smul,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.re he
    have hy : (rho s)⁻¹ * f s 1 = Real.sin (phi s) := by
      simpa [rho, positiveExitComplexTrace, positiveExitComplexPoint, Complex.real_smul,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.im he
    ext i
    fin_cases i
    · change f s 0 = rho s * Real.cos (phi s)
      rw [← hx]; field_simp [(hrpos s).ne']
    · change f s 1 = rho s * Real.sin (phi s)
      rw [← hy]; field_simp [(hrpos s).ne']
  have hphipos (s : ℝ) : 0 < deriv phi s := by
    have hd := ((hr.differentiable (by simp) s).hasDerivAt).smul
      (visibleConnectorUnitDirection_hasDerivAt ((hphi.differentiable (by simp) s).hasDerivAt))
    have hd' := hd.congr_of_eventuallyEq (Eventually.of_forall (fun r => hrep r))
    have he : visibleConnectorDet (f s) (deriv f s) = rho s ^ 2 * deriv phi s := by
      rw [hrep s, hd'.deriv]
      simp only [visibleConnectorDet, visibleConnectorJ, visibleConnectorUnitDirection,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (rho s ^ 2 * deriv phi s) * Real.cos_sq_add_sin_sq (phi s)
    exact pos_of_mul_pos_right (he ▸ hdet s) (sq_nonneg _)
  have hm : StrictMono phi := strictMono_of_deriv_pos hphipos
  have hend : phi L = phi 0 + 2 * Real.pi := by simpa only [zero_add] using hshift 0
  have hmem {s : ℝ} (hs : s ∈ Ico 0 L) : phi s ∈ Ico (phi 0) (phi 0 + 2 * Real.pi) :=
    ⟨hm.monotone hs.1, (hm hs.2).trans_eq hend⟩
  have hic : InjOn (positiveExitComplexTrace f) (Ico 0 L) := by
    intro s hs t ht he
    apply hm.injective
    apply Circle.exp_injOn_Ico (a := phi 0) (b := phi 0 + 2 * Real.pi) (by simp)
      (hmem hs) (hmem ht)
    exact Subtype.ext (congrArg Subtype.val ((hphase s).symm.trans
      ((congrArg complexCircleDirection he).trans (hphase t))))
  letI : Fact (0 < L) := ⟨hL⟩
  refine ⟨fun s hs t ht he => hic hs ht (congrArg positiveExitComplexPoint he),
    periodicComplexCurve_isJordanCurve hc hcp hic⟩

private theorem terminalJordan_direction_pos_scale {z : ℂ} (hz : z ≠ 0)
    {a : ℝ} (ha : 0 < a) : complexCircleDirection (a • z) = complexCircleDirection z := by
  have haz : a • z ≠ 0 := smul_ne_zero ha.ne' hz
  apply Subtype.ext
  rw [complexCircleDirection_normalized haz, complexCircleDirection_normalized hz,
    norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  congr 1
  field_simp [(norm_pos_iff.mpr hz).ne', ha.ne']

/-- The actual terminal of the SAME visible ruling has an actual smooth
periodic Jordan embedding and positive turn, for all sufficiently small positive
rotations chosen before any terminal conclusions are used. -/
theorem visibleConnector_periodic_actual_terminal_jordan
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
    (hgv : ∀ s, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps →
      let T := visibleConnectorActualTerminalSource p gamma
        (visibleConnectorShiftedRuling R gamma theta eta)
      ContDiff ℝ ∞ T ∧ Periodic T L ∧
      (∀ s, positiveExitComplexTrace T s ≠ 0) ∧
      (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
      HasPositiveArgumentTurn (positiveExitComplexTrace T) L ∧ InjOn T (Ico 0 L) ∧
      Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘ positiveExitComplexTrace T)) ∧
      ∃ hperiod : Periodic (positiveExitComplexTrace T) L,
        Topology.IsEmbedding hperiod.lift := by
  let lam : ℝ → ℝ := fun s => kappa s *
    (deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s)) / (R * deriv theta s)
  let Q0 : ℝ → Coord := visibleConnectorRescaledTerminalSource R p gamma theta kappa 0
  let B : ℝ → ℂ := positiveExitComplexTrace Q0
  have hdp := (contDiff_infty_iff_deriv.mp hp).2
  have hdt := (contDiff_infty_iff_deriv.mp ht).2
  have hu := visibleConnectorUnitDirection_contDiff.comp ht
  have hnum : ContDiff ℝ ∞ (fun s => kappa s *
      (deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))) := by
    simp only [dotProduct, Fin.sum_univ_two]
    fun_prop
  have hlam : ContDiff ℝ ∞ lam := hnum.div (contDiff_const.mul hdt)
    (fun s => (mul_pos hR (htpos s)).ne')
  have hlpos (s : ℝ) : 0 < lam s := div_pos (mul_pos (hkpos s) (hpv s)) (mul_pos hR (htpos s))
  have hQ0 (s : ℝ) : Q0 s = -lam s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)) :=
    visibleConnector_rescaled_terminal_zero hdecomp (hkpos s).ne'
  have hB (s : ℝ) : B s = lam s • (Circle.exp (theta s - Real.pi / 2) : ℂ) := by
    dsimp [B, positiveExitComplexTrace]
    rw [hQ0]
    apply Complex.ext <;>
      simp only [positiveExitComplexPoint, visibleConnectorJ,
        visibleConnectorUnitDirection, Circle.coe_exp, Complex.smul_re,
        Complex.smul_im, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        smul_eq_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero,
        Real.cos_sub, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two] <;> ring
  have hQ0smooth : ContDiff ℝ ∞ Q0 := by
    have heq : Q0 = fun s => -lam s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)) := funext hQ0
    rw [heq]
    have hj : ContDiff ℝ ∞ (fun s => visibleConnectorJ (visibleConnectorUnitDirection (theta s))) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · change ContDiff ℝ ∞ (fun s => -Real.sin (theta s))
        exact ht.sin.neg
      · change ContDiff ℝ ∞ (fun s => Real.cos (theta s))
        exact ht.cos
    exact hlam.neg.smul hj
  have hBsmooth : ContDiff ℝ ∞ B := by
    simpa only [B, positiveExitComplexTrace, Function.comp_def, terminalJordanComplex_apply] using
      terminalJordanComplex.contDiff.comp hQ0smooth
  have hBne (s : ℝ) : B s ≠ 0 := by
    rw [hB]
    exact smul_ne_zero (hlpos s).ne' (by exact norm_ne_zero_iff.mp (by simp))
  have hkper : Periodic kappa L := by
    have heper := visibleConnector_shifted_direction_periodic hshift 0
    have hcoef (s : ℝ) : kappa s = -(visibleConnectorJ (gamma s) ⬝ᵥ
        visibleConnectorJ (visibleConnectorUnitDirection (theta s))) := by
      rw [hdecomp s]
      simp only [visibleConnectorJ, visibleConnectorUnitDirection, dotProduct, Fin.sum_univ_two,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -kappa s * Real.cos_sq_add_sin_sq (theta s)
    intro s
    rw [hcoef (s+L), hcoef s, hgperiod s]
    have he : visibleConnectorUnitDirection (theta (s+L)) = visibleConnectorUnitDirection (theta s) := by
      simpa only [visibleConnectorShiftedDirection, sub_zero] using heper s
    rw [he]
  have hdpper := terminalJordan_deriv_periodic hp hpperiod
  have hdtper : Periodic (deriv theta) L := by
    intro s
    have h1 := ((ht.differentiable (by simp) (s+L)).hasDerivAt).comp s ((hasDerivAt_id s).add_const L)
    have h2 := ((ht.differentiable (by simp) s).hasDerivAt).add_const (2*Real.pi)
    have h1' : HasDerivAt (fun r => theta (r+L)) (deriv theta (s+L)) s := by simpa only [Function.comp_def,id_eq,mul_one] using h1
    exact h1'.unique (h2.congr_of_eventuallyEq (Eventually.of_forall (fun r => hshift r)))
  have hlper : Periodic lam L := by
    intro s
    dsimp [lam]
    rw [hkper s, hdpper s, hdtper s]
    have he := visibleConnector_shifted_direction_periodic hshift 0 s
    simpa only [visibleConnectorShiftedDirection, sub_zero] using congrArg
      (fun v => kappa s * (deriv p s ⬝ᵥ v) / (R * deriv theta s)) he
  have hBper : Periodic B L := by
    intro s
    rw [hB (s+L), hB s, hlper s, hshift s]
    have he : Circle.exp (theta s + 2*Real.pi - Real.pi/2) = Circle.exp (theta s - Real.pi/2) := by
      rw [show theta s + 2*Real.pi - Real.pi/2 = theta s - Real.pi/2 + 2*Real.pi by ring, Circle.exp_add]
      simp
    rw [he]
  have hBturn : HasPositiveArgumentTurn B L := by
    refine ⟨fun s => theta s - Real.pi/2, ht.continuous.sub continuous_const, ?_, ?_⟩
    · intro s
      rw [hB s]
      rw [terminalJordan_direction_pos_scale (by exact norm_ne_zero_iff.mp (by simp)) (hlpos s)]
      apply Subtype.ext
      rw [complexCircleDirection_normalized (by exact norm_ne_zero_iff.mp (by simp))]
      simp
    · have hs := hshift 0
      simp only [zero_add] at hs
      linarith
  obtain ⟨epsilon, hepsilon, hturn⟩ := positiveExit_exists_argumentTurn_C0_threshold
    hL hBsmooth hBper hBne hBturn
  obtain ⟨ed, hed, hdetclose⟩ := visibleConnector_uniform_rescaled_terminal_det_and_close
    hR hp hg ht hk (K := Icc (0 : ℝ) L) isCompact_Icc hdecomp hkpos htpos
    (fun s _ => hpv s) hepsilon
  obtain ⟨ec, hec, hcoeff⟩ := visibleConnector_periodic_actual_coefficients_and_terminal_radial
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  refine ⟨min ed ec, lt_min hed hec, ?_⟩
  intro eta heta hetaEps
  dsimp only
  let w := visibleConnectorShiftedRuling R gamma theta eta
  let T := visibleConnectorActualTerminalSource p gamma w
  let Q := visibleConnectorRescaledTerminalSource R p gamma theta kappa eta
  have hetaD : |eta| < ed := by rw [abs_of_pos heta]; exact hetaEps.trans_le (min_le_left _ _)
  have hetaC := hetaEps.trans_le (min_le_right ed ec)
  have he : ContDiff ℝ ∞ (visibleConnectorShiftedDirection theta eta) :=
    visibleConnectorUnitDirection_contDiff.comp (ht.sub contDiff_const)
  have hw : ContDiff ℝ ∞ w := visibleConnectorActualRuling_contDiff hg he
  have hwper : Periodic w L := by
    intro s
    dsimp [w, visibleConnectorShiftedRuling, visibleConnectorActualRuling]
    rw [hgperiod s, visibleConnector_shifted_direction_periodic hshift eta s]
  have hAper : Periodic (visibleConnectorA p w) L := by
    intro s
    unfold visibleConnectorA
    rw [hdpper s, hwper s]
  have hdgper := terminalJordan_deriv_periodic hg hgperiod
  have hdwper := terminalJordan_deriv_periodic hw hwper
  have hBper' : Periodic (visibleConnectorB gamma w) L := by
    intro s
    unfold visibleConnectorB
    rw [hdgper s, hwper s]
  have hCper : Periodic (visibleConnectorC gamma w) L := by
    intro s
    unfold visibleConnectorC
    rw [hBper' s, hdwper s, hwper s]
  have hheight := visibleConnectorActualTerminalHeight_contDiff hp hg hw
    (fun s => (hcoeff eta heta hetaC s).2.2.1.ne')
  have hT : ContDiff ℝ ∞ T := hp.add (hheight.smul hw)
  have hheightper : Periodic (visibleConnectorActualTerminalHeight p gamma w) L := by
    intro s
    unfold visibleConnectorActualTerminalHeight
    rw [hAper s, hCper s]
  have hTp : Periodic T L := by
    intro s
    dsimp [T, visibleConnectorActualTerminalSource]
    rw [hpperiod s, hheightper s, hwper s]
  have hQeq : Q = fun s => eta • T s := by
    funext s
    exact visibleConnector_rescaled_terminal_eq hg ht hdecomp heta.ne'
  have hQ : ContDiff ℝ ∞ Q := by rw [hQeq]; exact (contDiff_const (c := eta)).smul hT
  have hQp : Periodic Q L := by
    intro s
    rw [hQeq]
    change eta • T (s + L) = eta • T s
    rw [hTp s]
  have hdQp := terminalJordan_deriv_periodic hQ hQp
  have hQdet (s : ℝ) : 0 < visibleConnectorDet (Q s) (deriv Q s) := by
    obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico, zero_add] at hn
    have hh := (hdetclose eta hetaD (s-n • L) ⟨hn.1, hn.2.le⟩).2.1
    change 0 < visibleConnectorDet (Q (s-n • L)) (deriv Q (s-n • L)) at hh
    rw [hQp.sub_zsmul_eq n, hdQp.sub_zsmul_eq n] at hh
    exact hh
  have hcQ : ContDiff ℝ ∞ (positiveExitComplexTrace Q) := by
    simpa only [Function.comp_def, terminalJordanComplex_apply, positiveExitComplexTrace] using
      terminalJordanComplex.contDiff.comp hQ
  have hcQp : Periodic (positiveExitComplexTrace Q) L := by intro s; dsimp [positiveExitComplexTrace]; rw [hQp s]
  obtain ⟨hQturn, hQne⟩ := hturn (positiveExitComplexTrace Q) hcQ hcQp
    (fun s hs => (hdetclose eta hetaD s hs).2.2)
  have hcomplexeq (s : ℝ) : positiveExitComplexTrace Q s = eta • positiveExitComplexTrace T s := by
    change positiveExitComplexPoint (Q s) = eta • positiveExitComplexPoint (T s)
    rw [hQeq, terminalJordan_complex_smul]
  have hTne (s : ℝ) : positiveExitComplexTrace T s ≠ 0 := by
    intro hz
    apply hQne s
    rw [hcomplexeq s, hz, smul_zero]
  have hTdet (s : ℝ) : 0 < visibleConnectorDet (T s) (deriv T s) := by
    have hd := ((hT.differentiable (by simp) s).hasDerivAt).const_smul eta
    have hd' : deriv Q s = eta • deriv T s := by rw [hQeq]; exact hd.deriv
    have heq : visibleConnectorDet (Q s) (deriv Q s) = eta^2 * visibleConnectorDet (T s) (deriv T s) := by
      rw [hd', hQeq]
      simp only [visibleConnectorDet, Pi.smul_apply, smul_eq_mul]
      ring
    exact pos_of_mul_pos_right (heq ▸ hQdet s) (sq_nonneg _)
  have hTturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L := by
    obtain ⟨phi, hphi, hproj, hinc⟩ := hQturn
    refine ⟨phi, hphi, ?_, hinc⟩
    intro s
    have hs := hproj s
    rw [hcomplexeq s, terminalJordan_direction_pos_scale (hTne s) heta] at hs
    exact hs
  obtain ⟨hiT, hjT⟩ := visibleConnector_positive_det_turn_jordan hL hT hTp hTne hTturn hTdet
  have hcT : ContDiff ℝ ∞ (positiveExitComplexTrace T) := by
    simpa only [Function.comp_def, terminalJordanComplex_apply, positiveExitComplexTrace] using
      terminalJordanComplex.contDiff.comp hT
  have hcTp : Periodic (positiveExitComplexTrace T) L := by intro s; dsimp [positiveExitComplexTrace]; rw [hTp s]
  have hicT : InjOn (positiveExitComplexTrace T) (Ico 0 L) := by
    intro s hs t ht heq
    apply hiT hs ht
    ext i
    fin_cases i
    · exact congrArg Complex.re heq
    · exact congrArg Complex.im heq
  letI : Fact (0 < L) := ⟨hL⟩
  exact ⟨hT, hTp, hTne, hTdet, hTturn, hiT, hjT,
    hcTp, (periodicComplexCurve_native_embedding hcT hcTp hicT).2⟩

end
end TightVer401
