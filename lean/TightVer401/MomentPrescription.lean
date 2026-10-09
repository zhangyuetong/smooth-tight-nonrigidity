import TightVer401.MomentPrescriptionPositive

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem finite_moment_period_prescription {m : ℕ} (L : ℝ) [Fact (0 < L)]
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) (g b : AddCircle L → ℝ)
    (hf : Continuous f) (hfSmooth : ContDiff ℝ ∞ (f ∘ periodProjection L))
    (hg : Continuous g) (hb : ContDiff ℝ ∞ (b ∘ periodProjection L))
    (hbpos : ∀ q, 0 < b q) (hgpos : ∃ q, 0 < g q) (hgneg : ∃ q, g q < 0)
    (B : ℝ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    letI := periodCircleChartedSpace L
    ∃ A : AddCircle L → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧
      (∀ q, 0 < A q) ∧
      (∫ r in 0..L, ‖A (periodProjection L r) - b (periodProjection L r)‖) < η ∧
      (∫ r in 0..L, A (periodProjection L r) • f (periodProjection L r)) =
        (∫ r in 0..L, b (periodProjection L r) • f (periodProjection L r)) ∧
      (∫ r in 0..L, g (periodProjection L r) / Real.sqrt (A (periodProjection L r))) = B ∧
      ∃ centers radii : Fin (Module.finrank ℝ (circleMomentSpan L f) + 1) → ℝ,
        (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
        Function.support (fun q => A q - b q) ⊆
          ⋃ j, periodProjection L '' Icc (centers j - radii j) (centers j + radii j) := by
  letI := periodCircleChartedSpace L
  by_cases hB : momentNonlinearPeriod (b ∘ periodProjection L) (g ∘ periodProjection L) L ≤ B
  · exact momentPrescription_circle_above L f g b hf hfSmooth hg hb hbpos hgpos hη hε hB
  · have hnegpos : ∃ q, 0 < (-g) q := by
      obtain ⟨q, hq⟩ := hgneg
      exact ⟨q, neg_pos.mpr hq⟩
    have hnegB : momentNonlinearPeriod (b ∘ periodProjection L) ((-g) ∘ periodProjection L) L ≤ -B := by
      change momentNonlinearPeriod (b ∘ periodProjection L) (-(g ∘ periodProjection L)) L ≤ -B
      rw [momentDivergence_period_neg]
      linarith
    obtain ⟨A, hA, hApos, hsmall, hmoment, htarget, harcs⟩ :=
      momentPrescription_circle_above L f (-g) b hf hfSmooth hg.neg hb hbpos hnegpos hη hε hnegB
    refine ⟨A, hA, hApos, hsmall, hmoment, ?_, harcs⟩
    have hn : momentNonlinearPeriod (A ∘ periodProjection L) (-(g ∘ periodProjection L)) L = -B := htarget
    rw [momentDivergence_period_neg] at hn
    change momentNonlinearPeriod (A ∘ periodProjection L) (g ∘ periodProjection L) L = B
    linarith

end
end TightVer401

