import TightVer401.CurveL1StabilityImmersion

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_speedCurve_L1_smooth_embedding_threshold (L : ℝ) [Fact (0 < L)]
    (P : ℝ → E) (hP : ContDiff ℝ ∞ P) (hPL : Function.Periodic P L)
    (hne : ∀ x, P x ≠ 0) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbL : Function.Periodic b L) (hbpos : ∀ x, 0 < b x)
    (hbclose : (∫ x in 0..L, b x • P x) = 0)
    (hbinj : Set.InjOn (speedCurve b P) (Ico 0 L)) :
    ∃ η > 0, ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a L →
      (∀ x, 0 < a x) → (∫ x in 0..L, a x • P x) = 0 →
      (∫ x in 0..L, |a x - b x|) < η →
      ∃ C : AddCircle L → E, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ C ∧
        Topology.IsEmbedding C ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) C q)) ∧
        (∀ x, C (periodProjection L x) = speedCurve a P x) ∧
        Set.InjOn (speedCurve a P) (Ico 0 L) := by
  obtain ⟨η, hη, hthreshold⟩ := exists_speedCurve_L1_embedding_threshold L P hP hPL hne b hb hbL hbpos hbclose hbinj
  refine ⟨η, hη, fun a ha haL hapos haclose hsmall => ?_⟩
  obtain ⟨C, hC, hemb, hrep, hi⟩ := hthreshold a ha haL hapos haclose hsmall
  have hp := speedCurve_periodic ha.continuous hP.continuous haL hPL haclose
  have hCeq : C = hp.lift := periodicLift_unique hp C hrep
  refine ⟨C, hC, hemb, ?_, hrep, hi⟩
  intro q
  rw [hCeq]
  exact speedCurve_circle_mfderiv_injective ha hP hapos hne hp q

end
end TightVer401
