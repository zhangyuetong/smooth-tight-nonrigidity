import TightVer401.VisibleConnectorTerminalJordan
import TightVer401.PositiveExitConstructionWindingBridge

/-! The SAME actual terminal curve supplies a positive completion boundary
trace after its literal physical-period normalization.  The filling and origin
inclusion are constructed by the certified positive-turn producer.  No filling,
Jordan disk, origin-inside or terminal construction package is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def visibleConnectorTerminalNormalizedTrace (L : ℝ) (T : ℝ → Coord) (t : ℝ) : ℂ :=
  positiveExitComplexTrace T (L * t)

private def terminalPositiveComplex : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)) +
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)))

private theorem terminalPositiveComplex_apply (q : Coord) :
    terminalPositiveComplex q = positiveExitComplexPoint q := by
  apply Complex.ext <;> simp [terminalPositiveComplex, positiveExitComplexPoint,
    Complex.mul_re, Complex.mul_im]

private theorem terminalPositiveComplex_injective : Injective positiveExitComplexPoint := by
  intro p q h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  ext i
  fin_cases i
  · exact hre
  · exact him

/-- The derivative belongs to the actual normalized terminal trace. -/
theorem visibleConnectorTerminalNormalizedTrace_hasDerivAt {L : ℝ} {T : ℝ → Coord}
    (hT : ContDiff ℝ ∞ T) (t : ℝ) :
    HasDerivAt (visibleConnectorTerminalNormalizedTrace L T)
      (L • positiveExitComplexPoint (deriv T (L * t))) t := by
  have hclock : HasDerivAt (fun x : ℝ => L * x) L t := by
    convert! (hasDerivAt_id t).const_mul L using 1 <;> simp
  have hTc := ((hT.differentiable (by simp) (L * t)).hasDerivAt).scomp t hclock
  have hc := terminalPositiveComplex.hasFDerivAt.comp_hasDerivAt t hTc
  convert! hc using 1 <;>
    simp only [visibleConnectorTerminalNormalizedTrace, positiveExitComplexTrace,
      Function.comp_def, map_smul, terminalPositiveComplex_apply] <;> rfl

/-- All ordinary positive-trace inputs are derived at the normalized period.
The determinant supplies regularity; the physical turn is transported by the
literal clock with endpoints 0 and L. -/
theorem visibleConnectorTerminalNormalizedTrace_fields {L : ℝ} (hL : 0 < L)
    {T : ℝ → Coord} (hT : ContDiff ℝ ∞ T) (hperiod : Periodic T L)
    (hne : ∀ s, positiveExitComplexTrace T s ≠ 0)
    (hdet : ∀ s, 0 < visibleConnectorDet (T s) (deriv T s))
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L)
    (hi : InjOn T (Ico 0 L)) :
    ContDiff ℝ ∞ (visibleConnectorTerminalNormalizedTrace L T) ∧
      Periodic (visibleConnectorTerminalNormalizedTrace L T) 1 ∧
      InjOn (visibleConnectorTerminalNormalizedTrace L T) (Ico 0 1) ∧
      (∀ t, deriv (visibleConnectorTerminalNormalizedTrace L T) t ≠ 0) ∧
      (∀ t, visibleConnectorTerminalNormalizedTrace L T t ≠ 0) ∧
      HasPositiveArgumentTurn (visibleConnectorTerminalNormalizedTrace L T) 1 ∧
      range (visibleConnectorTerminalNormalizedTrace L T) = range (positiveExitComplexTrace T) := by
  have hs : ContDiff ℝ ∞ (visibleConnectorTerminalNormalizedTrace L T) := by
    convert! (terminalPositiveComplex.contDiff.comp hT).comp
        ((contDiff_const (c := L)).mul contDiff_id) using 1 <;>
      simp only [visibleConnectorTerminalNormalizedTrace, positiveExitComplexTrace,
        Function.comp_def, terminalPositiveComplex_apply, id_eq] <;> rfl
  have hp : Periodic (visibleConnectorTerminalNormalizedTrace L T) 1 := by
    intro t
    have he : L * (t + 1) = L * t + L := by ring
    simp only [visibleConnectorTerminalNormalizedTrace, positiveExitComplexTrace,
      Function.comp_apply, he, hperiod (L * t)]
  have hic : InjOn (visibleConnectorTerminalNormalizedTrace L T) (Ico 0 1) := by
    intro s hs' t ht' he
    have hsm : L * s ∈ Ico (0 : ℝ) L :=
      ⟨mul_nonneg hL.le hs'.1, by simpa only [mul_one] using mul_lt_mul_of_pos_left hs'.2 hL⟩
    have htm : L * t ∈ Ico (0 : ℝ) L :=
      ⟨mul_nonneg hL.le ht'.1, by simpa only [mul_one] using mul_lt_mul_of_pos_left ht'.2 hL⟩
    have hpoints : T (L * s) = T (L * t) := terminalPositiveComplex_injective he
    have heq := hi hsm htm hpoints
    exact mul_left_cancel₀ hL.ne' heq
  have hreg (t : ℝ) : deriv (visibleConnectorTerminalNormalizedTrace L T) t ≠ 0 := by
    rw [(visibleConnectorTerminalNormalizedTrace_hasDerivAt hT t).deriv]
    apply smul_ne_zero hL.ne'
    intro hzero
    have hdT : deriv T (L * t) = 0 := terminalPositiveComplex_injective
      (hzero.trans (by rfl : (0 : ℂ) = positiveExitComplexPoint (0 : Coord)))
    have hpos := hdet (L * t)
    rw [hdT] at hpos
    have hbad : (0 : ℝ) < 0 := by
      simpa only [visibleConnectorDet, Pi.zero_apply, mul_zero, sub_self] using hpos
    exact lt_irrefl (0 : ℝ) hbad
  have hn (t : ℝ) : visibleConnectorTerminalNormalizedTrace L T t ≠ 0 := hne (L * t)
  have hturn1 : HasPositiveArgumentTurn (visibleConnectorTerminalNormalizedTrace L T) 1 := by
    obtain ⟨phi, hphi, hproj, hinc⟩ := hturn
    refine ⟨fun t => phi (L * t), hphi.comp (continuous_const.mul continuous_id), ?_, ?_⟩
    · intro t
      exact hproj (L * t)
    · simpa only [mul_one, mul_zero] using hinc
  have hrange : range (visibleConnectorTerminalNormalizedTrace L T) =
      range (positiveExitComplexTrace T) := by
    apply Subset.antisymm
    · rintro z ⟨t, rfl⟩
      exact ⟨L * t, rfl⟩
    · rintro z ⟨s, rfl⟩
      refine ⟨s / L, ?_⟩
      have he : L * (s / L) = s := by field_simp [hL.ne'] <;> ring
      simp only [visibleConnectorTerminalNormalizedTrace, he]
  exact ⟨hs, hp, hic, hreg, hn, hturn1, hrange⟩

/-- The certified positive-turn producer constructs ONE actual filling of
the SAME terminal range and its positive winding at every filled point. -/
theorem visibleConnectorTerminal_exists_positive_completion_trace {L : ℝ} (hL : 0 < L)
    {T : ℝ → Coord} (hT : ContDiff ℝ ∞ T) (hperiod : Periodic T L)
    (hne : ∀ s, positiveExitComplexTrace T s ≠ 0)
    (hdet : ∀ s, 0 < visibleConnectorDet (T s) (deriv T s))
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace T) L)
    (hi : InjOn T (Ico 0 L)) :
    ∃ H : ℂ ≃ₜ ℂ,
      DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
      (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 ∧
      range (positiveExitComplexTrace T) = frontier (H '' ball (0 : ℂ) 1) ∧
      HasPositiveArgumentTurn (visibleConnectorTerminalNormalizedTrace L T) 1 ∧
      (∀ t, visibleConnectorTerminalNormalizedTrace L T t ≠ 0) := by
  obtain ⟨hs, hp, hic, hreg, hn, ht, hrange⟩ :=
    visibleConnectorTerminalNormalizedTrace_fields hL hT hperiod hne hdet hturn hi
  obtain ⟨H, hpositive, h0⟩ := positiveExit_positive_turn_exists_completion_trace
    hs hp hic hreg hn ht
  have himage : visibleConnectorTerminalNormalizedTrace L T '' Icc (0 : ℝ) 1 =
      range (visibleConnectorTerminalNormalizedTrace L T) := by
    apply Subset.antisymm (image_subset_range _ _)
    rintro z ⟨t, rfl⟩
    let h1 : 0 < (1 : ℝ) := by norm_num
    refine ⟨toIcoMod h1 0 t, Ico_subset_Icc_self (toIcoMod_mem_Ico' h1 t), ?_⟩
    symm
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul h1 0 t]
    exact hp.zsmul (toIcoDiv h1 0 t) _
  have hboundary := hpositive.2.2.2.2.1
  rw [himage, hrange] at hboundary
  exact ⟨H, hpositive, h0, hboundary, ht, hn⟩

/-- Choose eta once below the actual terminal threshold.  For EVERY such eta
the SAME T admits an actual normalized positive completion trace and filling.
There is no second terminal selection after smoothing or gluing. -/
theorem visibleConnector_periodic_actual_terminal_positive_trace
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
      ∃ H : ℂ ≃ₜ ℂ,
        DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
        (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 ∧
        range (positiveExitComplexTrace T) = frontier (H '' ball (0 : ℂ) 1) ∧
        HasPositiveArgumentTurn (visibleConnectorTerminalNormalizedTrace L T) 1 ∧
        (∀ t, visibleConnectorTerminalNormalizedTrace L T t ≠ 0) := by
  obtain ⟨eps, heps, hterminal⟩ := visibleConnector_periodic_actual_terminal_jordan
    hR hL hp hg ht hk hpperiod hgperiod hshift hdecomp hkpos hpv hgv htpos
  refine ⟨eps, heps, ?_⟩
  intro eta heta hepsEta
  obtain ⟨hT, hperiod, hne, hdet, hturn, hi, _⟩ := hterminal eta heta hepsEta
  exact visibleConnectorTerminal_exists_positive_completion_trace hL hT hperiod hne hdet hturn hi

end
end TightVer401
