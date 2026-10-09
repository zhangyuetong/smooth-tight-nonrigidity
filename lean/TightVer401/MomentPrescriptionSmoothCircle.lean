import TightVer401.MomentPrescription
import TightVer401.PeriodCircleInstances

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold

theorem finite_moment_period_prescription_smooth_circle {m : ℕ}
    (L : ℝ) [Fact (0 < L)]
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) (g b : AddCircle L → ℝ)
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g)
    (hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ b)
    (hbpos : ∀ q, 0 < b q) (hgpos : ∃ q, 0 < g q) (hgneg : ∃ q, g q < 0)
    (B : ℝ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
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
  exact finite_moment_period_prescription L f g b hf.continuous
    (hf.comp (periodProjection_contMDiff L)).contDiff hg.continuous
    (hb.comp (periodProjection_contMDiff L)).contDiff hbpos hgpos hgneg B hη hε

end
end TightVer401
