import TightVer401.DualRadialCompletionExitApplicationPeriod
import TightVer401.CorrugatedSeedFrameVisibility
import TightVer401.AnnularDegreeGlobal

/-! Transport the SAME actual exit interiors and visibility through the
positive period clock. No new Jordan or winding construction is introduced. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology RealInnerProductSpace ComplexConjugate

theorem dualRadialCompletionExitApplication_coord_complex (p : Coord) :
    seamComplexCoord (positiveExitComplexPoint p) = p := by
  ext i
  fin_cases i <;> simp [positiveExitComplexPoint, seamComplexCoord_apply]

theorem dualRadialCompletionExitApplication_complex_trace_smooth
    {p : ℝ → Coord} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (positiveExitComplexTrace p) := by
  have he : positiveExitComplexTrace p = seamComplexCoord.symm ∘ p := by
    funext t
    apply Complex.ext <;> rfl
  rw [he]
  exact seamComplexCoord.symm.contDiff.comp hp

theorem dualRadialCompletionExitApplication_nested
    {Ho Hi : ℂ ≃ₜ ℂ} {O I : Set Coord}
    (hO : O = seamComplexCoord '' (Ho '' ball (0 : ℂ) 1))
    (hI : I = seamComplexCoord '' (Hi '' ball (0 : ℂ) 1))
    (hn : closure I ⊆ O) :
    closure (Hi '' ball (0 : ℂ) 1) ⊆ Ho '' ball (0 : ℂ) 1 := by
  intro z hz
  have hp : seamComplexCoord z ∈ closure I := by
    rw [hI, ← seamComplexCoord.image_closure]
    exact mem_image_of_mem _ hz
  have ho := hn hp
  rw [hO] at ho
  obtain ⟨w, hw, he⟩ := ho
  exact seamComplexCoord.injective he ▸ hw

theorem dualRadialCompletionExitApplication_annulus
    {Ho Hi : ℂ ≃ₜ ℂ} {O I : Set Coord}
    (hO : O = seamComplexCoord '' (Ho '' ball (0 : ℂ) 1))
    (hI : I = seamComplexCoord '' (Hi '' ball (0 : ℂ) 1)) :
    O \ closure I = annularCoordJordanInterior Ho Hi := by
  rw [hO, hI, ← seamComplexCoord.image_closure]
  change (seamComplexCoord '' (Ho '' ball (0 : ℂ) 1)) \
      (seamComplexCoord '' closure (Hi '' ball (0 : ℂ) 1)) =
    seamComplexCoord '' ((Ho '' ball (0 : ℂ) 1) \ closure (Hi '' ball (0 : ℂ) 1))
  ext q
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hq⟩
    exact ⟨z, ⟨hz, fun hi => hq ⟨z, hi, rfl⟩⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hi⟩, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, he⟩
    exact hi (seamComplexCoord.injective he ▸ hw)

theorem dualRadialCompletionExitApplication_outer_visibility
    {G : Coord → ℝ} {U : Set Coord} {L R : ℝ}
    (h : PositiveExitTrace G U L)
    (hv : ComplexVisiblePair R (positiveExitComplexTrace h.p)
      (fun t => Complex.I * positiveExitComplexTrace h.gamma t)) :
    ComplexVisiblePair R (fun t => positiveExitComplexTrace h.p (L*t))
      (fun t => Complex.I * positiveExitComplexTrace h.gamma (L*t)) := by
  have hp := dualRadialCompletionExitApplication_complex_trace_smooth h.p_smooth
  have hg := dualRadialCompletionExitApplication_complex_trace_smooth h.gamma_smooth
  have hclock (t : ℝ) : HasDerivAt (fun s : ℝ => L*s) L t := by
    simpa only [Function.id_def, mul_one] using (hasDerivAt_id t).const_mul L
  exact hv.comp (ψ := fun t : ℝ => L*t) (hp.differentiable (by simp))
    ((contDiff_const.mul hg).differentiable (by simp))
    (fun t => (hclock t).differentiableAt)
    (fun t => by rw [(hclock t).deriv]; exact h.period_pos)

theorem dualRadialCompletionExitApplication_inner_visibility
    {G : Coord → ℝ} {U : Set Coord} {L R : ℝ}
    (h : PositiveExitTrace G U L)
    (hv : ComplexVisiblePair R (corrugatedReverseReflect (positiveExitComplexTrace h.gamma))
      (fun t => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace h.p) t)) :
    ComplexVisiblePair R
      (corrugatedReverseReflect (fun t => positiveExitComplexTrace h.gamma (L*t)))
      (fun t => Complex.I * corrugatedReverseReflect
        (fun s => positiveExitComplexTrace h.p (L*s)) t) := by
  have hp := dualRadialCompletionExitApplication_complex_trace_smooth h.p_smooth
  have hg := dualRadialCompletionExitApplication_complex_trace_smooth h.gamma_smooth
  have hclock (t : ℝ) : HasDerivAt (fun s : ℝ => L*s) L t := by
    simpa only [Function.id_def, mul_one] using (hasDerivAt_id t).const_mul L
  have hc := hv.comp (ψ := fun t : ℝ => L*t)
    ((corrugatedReverseReflect_contDiff hg).differentiable (by simp))
    ((contDiff_const.mul (corrugatedReverseReflect_contDiff hp)).differentiable (by simp))
    (fun t => (hclock t).differentiableAt)
    (fun t => by rw [(hclock t).deriv]; exact h.period_pos)
  have heG : corrugatedReverseReflect
      (fun t => positiveExitComplexTrace h.gamma (L*t)) =
      corrugatedReverseReflect (positiveExitComplexTrace h.gamma) ∘ (fun t => L*t) := by
    funext t
    change conj (positiveExitComplexTrace h.gamma (L*(-t))) =
      conj (positiveExitComplexTrace h.gamma (-(L*t)))
    rw [mul_neg]
  have heP : corrugatedReverseReflect
      (fun t => positiveExitComplexTrace h.p (L*t)) =
      corrugatedReverseReflect (positiveExitComplexTrace h.p) ∘ (fun t => L*t) := by
    funext t
    change conj (positiveExitComplexTrace h.p (L*(-t))) =
      conj (positiveExitComplexTrace h.p (-(L*t)))
    rw [mul_neg]
  rw [heG, heP]
  exact hc

end
end TightVer401
