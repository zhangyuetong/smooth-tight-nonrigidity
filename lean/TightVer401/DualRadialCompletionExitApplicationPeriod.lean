import TightVer401.PositiveExitConstructionWindingBridge
import TightVer401.DualRadialCompletionTraceInside

/-! Reparameterize the actual exit source and gradient traces by their positive
period. The retained winding bridge constructs their positive fillings; the
clock is surjective, so the original Jordan interiors are unchanged. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

private theorem exitPeriod_complexPoint_eq :
    positiveExitComplexPoint = (seamComplexCoord.symm : Coord → ℂ) := by
  funext p
  apply seamComplexCoord.injective
  rw [seamComplexCoord.apply_symm_apply]
  ext i
  fin_cases i <;> simp [positiveExitComplexPoint, seamComplexCoord_apply]

private theorem exitPeriod_complexPoint_injective : Injective positiveExitComplexPoint := by
  rw [exitPeriod_complexPoint_eq]
  exact seamComplexCoord.symm.injective

private theorem exitPeriod_complexPoint_smooth : ContDiff ℝ ∞ positiveExitComplexPoint := by
  rw [exitPeriod_complexPoint_eq]
  exact seamComplexCoord.symm.contDiff

private theorem exitPeriod_complex_deriv {p : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (L t : ℝ) :
    deriv (fun s => positiveExitComplexTrace p (L*s)) t =
      L • positiveExitComplexPoint (deriv p (L*t)) := by
  have hclock : HasDerivAt (fun s : ℝ => L*s) L t := by
    simpa only [Function.id_def, mul_one] using ((hasDerivAt_id t).const_mul L)
  have hd : HasDerivAt (fun s => p (L*s)) (L • deriv p (L*t)) t :=
    (hp.differentiable (by simp) (L*t)).hasDerivAt.scomp t hclock
  have hc := seamComplexCoord.symm.hasFDerivAt.comp_hasDerivAt t hd
  change deriv (fun s => positiveExitComplexPoint (p (L*s))) t =
    L • positiveExitComplexPoint (deriv p (L*t))
  rw [exitPeriod_complexPoint_eq]
  calc
    deriv (fun s => seamComplexCoord.symm (p (L*s))) t =
        seamComplexCoord.symm (L • deriv p (L*t)) := hc.deriv
    _ = L • seamComplexCoord.symm (deriv p (L*t)) :=
      seamComplexCoord.symm.map_smul L _

/-- The literal clock changes the source derivative by its positive period. -/
theorem dualRadialCompletionExitApplicationPeriod_source_deriv
    {G : Coord → ℝ} {U : Set Coord} {L : ℝ}
    (h : PositiveExitTrace G U L) (t : ℝ) :
    deriv (fun s => positiveExitComplexTrace h.p (L*s)) t =
      L • positiveExitComplexPoint (deriv h.p (L*t)) :=
  exitPeriod_complex_deriv h.p_smooth L t

/-- The literal clock changes the actual gradient derivative by the same period. -/
theorem dualRadialCompletionExitApplicationPeriod_gradient_deriv
    {G : Coord → ℝ} {U : Set Coord} {L : ℝ}
    (h : PositiveExitTrace G U L) (t : ℝ) :
    deriv (fun s => positiveExitComplexTrace h.gamma (L*s)) t =
      L • positiveExitComplexPoint (deriv h.gamma (L*t)) :=
  exitPeriod_complex_deriv h.gamma_smooth L t

/-- No source or gradient points are lost by the surjective positive clock. -/
theorem dualRadialCompletionExitApplicationPeriod_range
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) :
    range (fun t => f (L*t)) = range f := by
  have hs : Surjective (fun t : ℝ => L*t) := by
    intro s
    refine ⟨s/L, ?_⟩
    exact mul_div_cancel₀ s hL.ne'
  exact hs.range_comp f

/-- The actual radian turn has period one after the positive clock change. -/
theorem dualRadialCompletionExitApplicationPeriod_turn
    {f : ℝ → ℂ} {L : ℝ} (hturn : HasPositiveArgumentTurn f L) :
    HasPositiveArgumentTurn (fun t => f (L*t)) 1 := by
  obtain ⟨phi, hphi, hproj, hinc⟩ := hturn
  refine ⟨fun t => phi (L*t), hphi.comp (continuous_const.mul continuous_id),
    fun t => hproj (L*t), ?_⟩
  simpa only [mul_one, mul_zero] using hinc

private theorem exitPeriod_positive_trace {p : ℝ → Coord} {L : ℝ}
    (hL : 0 < L) (hp : ContDiff ℝ ∞ p) (hperiod : Periodic p L)
    (hi : Injective hperiod.lift) (hreg : ∀ t, deriv p t ≠ 0)
    (hne : ∀ t, p t ≠ 0) (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace p) L) :
    ∃ H : ℂ ≃ₜ ℂ,
      DualRadialCompletionPositiveTrace H (fun t => positiveExitComplexTrace p (L*t)) ∧
      (0 : ℂ) ∈ H '' ball (0 : ℂ) 1 := by
  let : Fact (0 < L) := ⟨hL⟩
  have hs : ContDiff ℝ ∞ (fun t => positiveExitComplexTrace p (L*t)) :=
    exitPeriod_complexPoint_smooth.comp (hp.comp (contDiff_const.mul contDiff_id))
  have hper : Periodic (fun t => positiveExitComplexTrace p (L*t)) 1 := by
    intro t
    change positiveExitComplexPoint (p (L*(t+1))) = positiveExitComplexPoint (p (L*t))
    rw [show L*(t+1) = L*t+L by ring, hperiod]
  have hinj : InjOn (fun t => positiveExitComplexTrace p (L*t)) (Ico 0 1) := by
    intro s hs' t ht' he
    have he' : p (L*s) = p (L*t) := exitPeriod_complexPoint_injective he
    have hq : (L*s : AddCircle L) = (L*t : AddCircle L) := by
      apply hi
      simpa only [hperiod.lift_coe] using he'
    have hLs : L*s ∈ Ico (0 : ℝ) L :=
      ⟨mul_nonneg hL.le hs'.1, by nlinarith [hs'.2]⟩
    have hLt : L*t ∈ Ico (0 : ℝ) L :=
      ⟨mul_nonneg hL.le ht'.1, by nlinarith [ht'.2]⟩
    have hreal : L*s = L*t :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := L) (a := 0)
        (by simpa only [zero_add] using hLs)
        (by simpa only [zero_add] using hLt)).mp hq
    exact mul_left_cancel₀ hL.ne' hreal
  have hpointne (t : ℝ) : positiveExitComplexPoint (deriv p (L*t)) ≠ 0 := by
    intro he
    apply hreg (L*t)
    apply exitPeriod_complexPoint_injective
    exact he.trans (by rfl : (0 : ℂ) = positiveExitComplexPoint (0 : Coord))
  have hregular (t : ℝ) : deriv (fun s => positiveExitComplexTrace p (L*s)) t ≠ 0 := by
    rw [exitPeriod_complex_deriv hp L t]
    exact smul_ne_zero hL.ne' (hpointne t)
  have hnonzero (t : ℝ) : positiveExitComplexTrace p (L*t) ≠ 0 := by
    intro he
    apply hne (L*t)
    apply exitPeriod_complexPoint_injective
    exact he.trans (by rfl : (0 : ℂ) = positiveExitComplexPoint (0 : Coord))
  exact positiveExit_positive_turn_exists_completion_trace hs hper hinj hregular hnonzero
    (dualRadialCompletionExitApplicationPeriod_turn hturn)

/-- Positive completion traces for the actual exit loops, with their original
bounded components retained literally. Both fillings use the frozen winding producer. -/
theorem dualRadialCompletionExitApplicationPeriod_positive_traces
    {G : Coord → ℝ} {U : Set Coord} {L : ℝ}
    (h : PositiveExitTrace G U L) :
    ∃ Hp Hg : ℂ ≃ₜ ℂ,
      DualRadialCompletionPositiveTrace Hp (fun t => positiveExitComplexTrace h.p (L*t)) ∧
      DualRadialCompletionPositiveTrace Hg (fun t => positiveExitComplexTrace h.gamma (L*t)) ∧
      (0 : ℂ) ∈ Hp '' ball (0 : ℂ) 1 ∧ (0 : ℂ) ∈ Hg '' ball (0 : ℂ) 1 ∧
      positiveExitInside h.p = seamComplexCoord '' (Hp '' ball (0 : ℂ) 1) ∧
      positiveExitInside h.gamma = seamComplexCoord '' (Hg '' ball (0 : ℂ) 1) := by
  obtain ⟨Hp, hp, hp0⟩ := exitPeriod_positive_trace h.period_pos h.p_smooth
    h.p_periodic h.source_injective h.source_regular h.source_nonzero h.source_turn
  obtain ⟨Hg, hg, hg0⟩ := exitPeriod_positive_trace h.period_pos h.gamma_smooth
    h.gamma_periodic h.gradient_injective h.gradient_regular h.gradient_nonzero h.gradient_turn
  have hpRange : range (positiveExitComplexTrace h.p) = Hp '' sphere (0 : ℂ) 1 := by
    rw [← dualRadialCompletionExitApplicationPeriod_range h.period_pos (positiveExitComplexTrace h.p)]
    exact dualRadialCompletion_positiveTrace_range hp
  have hgRange : range (positiveExitComplexTrace h.gamma) = Hg '' sphere (0 : ℂ) 1 := by
    rw [← dualRadialCompletionExitApplicationPeriod_range h.period_pos (positiveExitComplexTrace h.gamma)]
    exact dualRadialCompletion_positiveTrace_range hg
  exact ⟨Hp, Hg, hp, hg, hp0, hg0,
    dualRadialCompletionTraceInside_eq_of_range hpRange h.source_jordan,
    dualRadialCompletionTraceInside_eq_of_range hgRange h.gradient_jordan⟩

/-- The coordinate dot product is exactly the real inner product in the
existing complex coordinates; no change of Euclidean normalization occurs. -/
theorem dualRadialCompletionExitApplicationPeriod_inner (p q : Coord) :
    inner ℝ (positiveExitComplexPoint p) (positiveExitComplexPoint q) = p ⬝ᵥ q := by
  rw [Complex.inner]
  simp only [positiveExitComplexPoint, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The normalized actual source/gradient tangent pairing remains strictly positive. -/
theorem dualRadialCompletionExitApplicationPeriod_pairing
    {G : Coord → ℝ} {U : Set Coord} {L : ℝ}
    (h : PositiveExitTrace G U L) :
    ∀ t, 0 < inner ℝ
      (deriv (fun s => positiveExitComplexTrace h.p (L*s)) t)
      (deriv (fun s => positiveExitComplexTrace h.gamma (L*s)) t) := by
  intro t
  rw [dualRadialCompletionExitApplicationPeriod_source_deriv h t,
    dualRadialCompletionExitApplicationPeriod_gradient_deriv h t,
    real_inner_smul_left, real_inner_smul_right,
    dualRadialCompletionExitApplicationPeriod_inner]
  exact mul_pos h.period_pos (mul_pos h.period_pos (h.tangent_pairing (L*t)))

/-- The normalized gradient curve is still the actual gradient of the SAME potential. -/
theorem dualRadialCompletionExitApplicationPeriod_actual_gradient
    {G : Coord → ℝ} {U : Set Coord} {L : ℝ}
    (h : PositiveExitTrace G U L) (t : ℝ) :
    positiveExitComplexTrace h.gamma (L*t) =
      positiveExitComplexPoint (planarGradient G (h.p (L*t))) := by
  change positiveExitComplexPoint (h.gamma (L*t)) = _
  rw [h.actual_gradient]
  rfl

end
end TightVer401
