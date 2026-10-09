import TightVer401.DualRadialCompletionReflectionCalculus

/-! The actual reflected dual used by the inner connector call. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The same incoming potential's literal reflected Legendre dual. -/
def dualRadialCompletionIncomingDual (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (q : Coord) : ℝ :=
  planarLegendre G e (dualRadialCompletionReflection q)

/-- Conjugate the existing actual inverse by the existing linear reflection;
this constructs no second inverse or choice of potential. -/
def dualRadialCompletionIncomingChart (e : OpenPartialHomeomorph Coord Coord) :
    OpenPartialHomeomorph Coord Coord :=
  (dualRadialCompletionReflection.toHomeomorph.toOpenPartialHomeomorph.trans e.symm).trans
    dualRadialCompletionReflection.toHomeomorph.toOpenPartialHomeomorph

private theorem incoming_reflection_symm_apply (p : Coord) :
    dualRadialCompletionReflection.symm p = dualRadialCompletionReflection p := by
  apply dualRadialCompletionReflection.injective
  rw [dualRadialCompletionReflection.apply_symm_apply,
    dualRadialCompletionReflection_involutive]

/-- Exact source of the actual reflected dual chart. -/
theorem dualRadialCompletionIncomingChart_source (e : OpenPartialHomeomorph Coord Coord) :
    (dualRadialCompletionIncomingChart e).source = dualRadialCompletionReflection ⁻¹' e.target := by
  simp [dualRadialCompletionIncomingChart]

/-- Exact target of the actual reflected dual chart. -/
theorem dualRadialCompletionIncomingChart_target (e : OpenPartialHomeomorph Coord Coord) :
    (dualRadialCompletionIncomingChart e).target = dualRadialCompletionReflection ⁻¹' e.source := by
  have hs : (dualRadialCompletionReflection.symm : Coord → Coord) =
      dualRadialCompletionReflection := funext incoming_reflection_symm_apply
  simp [dualRadialCompletionIncomingChart, hs]

theorem dualRadialCompletionIncomingChart_apply (e : OpenPartialHomeomorph Coord Coord) (q : Coord) :
    dualRadialCompletionIncomingChart e q =
      dualRadialCompletionReflection (e.symm (dualRadialCompletionReflection q)) := rfl

theorem dualRadialCompletionIncomingChart_symm_apply
    (e : OpenPartialHomeomorph Coord Coord) (q : Coord) :
    (dualRadialCompletionIncomingChart e).symm q =
      dualRadialCompletionReflection (e (dualRadialCompletionReflection q)) := by
  change dualRadialCompletionReflection.symm
    (e (dualRadialCompletionReflection.symm q)) = _
  rw [incoming_reflection_symm_apply, incoming_reflection_symm_apply]

/-- Analytic incoming data of the actual reflected dual, on its actual chart.
No connector, Jordan conclusion, global completion or continued image is assumed. -/
theorem dualRadialCompletionIncoming_dual_data {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord) (hG : ContDiffOn ℝ ∞ G e.source)
    (hneg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (dualRadialCompletionIncomingDual G e)
        (dualRadialCompletionIncomingChart e).source ∧
      (∀ p ∈ (dualRadialCompletionIncomingChart e).source,
        (planarHessian (dualRadialCompletionIncomingDual G e) p).det < 0) ∧
      EqOn (dualRadialCompletionIncomingChart e)
        (planarGradient (dualRadialCompletionIncomingDual G e))
        (dualRadialCompletionIncomingChart e).source ∧
      ContDiffOn ℝ ∞ (dualRadialCompletionIncomingChart e).symm
        (dualRadialCompletionIncomingChart e).target := by
  have hL := planarLegendre_contDiffOn e hG hi
  have hJ : ContDiffOn ℝ ∞ (dualRadialCompletionIncomingDual G e)
      (dualRadialCompletionReflection ⁻¹' e.target) :=
    dualRadialCompletionReflection_contDiffOn hL
  have hE : ContDiffOn ℝ ∞ e e.source :=
    (planarGradient_contDiffOn hG e.open_source).congr heG
  refine ⟨by rw [dualRadialCompletionIncomingChart_source]; exact hJ, ?_, ?_, ?_⟩
  · intro p hp
    rw [dualRadialCompletionIncomingChart_source] at hp
    change (planarHessian (fun q => planarLegendre G e (dualRadialCompletionReflection q)) p).det < 0
    rw [dualRadialCompletionReflection_hessian_det hL e.open_target hp]
    exact planarLegendre_saddle e hG hi heG hp (hneg _ (e.map_target hp))
  · intro p hp
    rw [dualRadialCompletionIncomingChart_source] at hp
    rw [dualRadialCompletionIncomingChart_apply]
    change _ = planarGradient (fun q => planarLegendre G e (dualRadialCompletionReflection q)) p
    rw [dualRadialCompletionReflection_gradient
      ((hL.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)),
      planarLegendre_gradient e hG hi heG hp]
  · rw [dualRadialCompletionIncomingChart_target]
    have hComp : ContDiffOn ℝ ∞ (fun q => e (dualRadialCompletionReflection q))
        (dualRadialCompletionReflection ⁻¹' e.source) :=
      hE.comp dualRadialCompletionReflection.contDiff.contDiffOn (fun _ hq => hq)
    exact (dualRadialCompletionReflection.contDiff.comp_contDiffOn hComp).congr
      (fun q _ => dualRadialCompletionIncomingChart_symm_apply e q)

private theorem incoming_reverse_reflect_hasDerivAt {p : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (s : ℝ) :
    HasDerivAt (fun t => dualRadialCompletionReflection (p (-t)))
      (-dualRadialCompletionReflection (deriv p (-s))) s := by
  have hneg := (hp.differentiable (by simp) (-s)).hasDerivAt.scomp s (hasDerivAt_neg s)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun t => p (-t) 0) (-deriv p (-s) 0) s
    have hd := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hneg
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, neg_one_smul, Pi.neg_apply] using hd
  · change HasDerivAt (fun t => -(p (-t) 1)) (-(-(deriv p (-s) 1))) s
    have hd : HasDerivAt (fun t : ℝ => p (-t) 1) (-deriv p (-s) 1) s := by
      have hproj := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hneg
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, neg_one_smul, Pi.neg_apply] using hproj
    have hscalar := (hasDerivAt_neg (p (-s) 1)).comp s hd
    simpa only [Function.comp_def, neg_mul, one_mul, neg_neg] using hscalar

private theorem incoming_reverse_reflect_periodic {p : ℝ → Coord} {L : ℝ}
    (hp : Function.Periodic p L) :
    Function.Periodic (fun t => dualRadialCompletionReflection (p (-t))) L := by
  intro t
  change dualRadialCompletionReflection (p (-(t + L))) = dualRadialCompletionReflection (p (-t))
  rw [show -(t + L) = -t - L by ring, hp.sub_eq]

/-- Actual swapped, reflected and reversed physical traces for the inner
connector. Smoothness, periodicity, source membership, actual gradient and
positive tangent pairing are derived from the ordinary incoming traces. -/
theorem dualRadialCompletionIncoming_reflected_traces {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord) (hG : ContDiffOn ℝ ∞ G e.source)
    (heG : ∀ q ∈ e.source, e q = planarGradient G q)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {p gamma : ℝ → Coord} {L : ℝ} (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (hpPeriod : Function.Periodic p L) (hgammaPeriod : Function.Periodic gamma L)
    (hSource : ∀ s, p s ∈ e.source) (hActual : ∀ s, e (p s) = gamma s)
    (hPairing : ∀ s, 0 < deriv p s ⬝ᵥ deriv gamma s) :
    ContDiff ℝ ∞ (fun s => dualRadialCompletionReflection (gamma (-s))) ∧
      ContDiff ℝ ∞ (fun s => dualRadialCompletionReflection (p (-s))) ∧
      Function.Periodic (fun s => dualRadialCompletionReflection (gamma (-s))) L ∧
      Function.Periodic (fun s => dualRadialCompletionReflection (p (-s))) L ∧
      (∀ s, dualRadialCompletionReflection (gamma (-s)) ∈
        (dualRadialCompletionIncomingChart e).source) ∧
      (∀ s, planarGradient (dualRadialCompletionIncomingDual G e)
        (dualRadialCompletionReflection (gamma (-s))) = dualRadialCompletionReflection (p (-s))) ∧
      ∀ s, 0 < deriv (fun t => dualRadialCompletionReflection (gamma (-t))) s ⬝ᵥ
        deriv (fun t => dualRadialCompletionReflection (p (-t))) s := by
  have hTarget (s : ℝ) : gamma s ∈ e.target := by
    rw [← hActual s]
    exact e.map_source (hSource s)
  have hL := planarLegendre_contDiffOn e hG hi
  refine ⟨dualRadialCompletionReflection.contDiff.comp (hgamma.comp contDiff_neg),
    dualRadialCompletionReflection.contDiff.comp (hp.comp contDiff_neg),
    incoming_reverse_reflect_periodic hgammaPeriod, incoming_reverse_reflect_periodic hpPeriod,
    ?_, ?_, ?_⟩
  · intro s
    rw [dualRadialCompletionIncomingChart_source]
    change dualRadialCompletionReflection (dualRadialCompletionReflection (gamma (-s))) ∈ e.target
    rw [dualRadialCompletionReflection_involutive]
    exact hTarget (-s)
  · intro s
    change planarGradient (fun q => planarLegendre G e (dualRadialCompletionReflection q))
      (dualRadialCompletionReflection (gamma (-s))) = _
    rw [dualRadialCompletionReflection_gradient
      (p := dualRadialCompletionReflection (gamma (-s)))
      ((hL.contDiffAt (e.open_target.mem_nhds (by rw [dualRadialCompletionReflection_involutive]; exact hTarget (-s)))).differentiableAt
        (by simp)), dualRadialCompletionReflection_involutive,
      planarLegendre_gradient e hG hi heG (hTarget (-s)), ← hActual (-s), e.left_inv (hSource (-s))]
  · intro s
    rw [(incoming_reverse_reflect_hasDerivAt hgamma s).deriv,
      (incoming_reverse_reflect_hasDerivAt hp s).deriv]
    have hDot : (-dualRadialCompletionReflection (deriv gamma (-s))) ⬝ᵥ
        (-dualRadialCompletionReflection (deriv p (-s))) = deriv gamma (-s) ⬝ᵥ deriv p (-s) := by
      rw [dotProduct_neg, neg_dotProduct, neg_neg, dualRadialCompletionReflection_dot]
    rw [hDot, dotProduct_comm]
    exact hPairing (-s)

/-- Exact coordinate identification with the complex reflection used by the
ordinary visibility inputs; applying it at -s gives corrugatedReverseReflect. -/
theorem dualRadialCompletionIncoming_complex_reflection (z : ℂ) :
    dualRadialCompletionReflection (seamComplexCoord z) = seamComplexCoord (conj z) := by
  simp [seamComplexCoord_apply]

end
end TightVer401
