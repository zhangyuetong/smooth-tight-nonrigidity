import TightVer401.MomentControlCircle

namespace TightVer401
noncomputable section
open Set MeasureTheory

theorem circleMomentSpan_finrank_le {m : ℕ} (L : ℝ)
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) :
    Module.finrank ℝ (circleMomentSpan L f) ≤ m := by
  simpa only [finrank_euclideanSpace_fin] using (circleMomentSpan L f).finrank_le

theorem circleMomentSpan_finrank_zero_iff {m : ℕ} (L : ℝ)
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) :
    Module.finrank ℝ (circleMomentSpan L f) = 0 ↔ ∀ q, f q = 0 := by
  rw [Submodule.finrank_eq_zero]
  constructor
  · intro h q
    have hmem : f q ∈ circleMomentSpan L f := Submodule.subset_span (mem_range_self q)
    rw [h] at hmem
    simpa using hmem
  · intro hf
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      simpa using hf q
    · exact bot_le

theorem circleControlMoment_eq_zero_of_finrank_zero {m : ℕ} (L : ℝ)
    (f : AddCircle L → EuclideanSpace ℝ (Fin m))
    (hd : Module.finrank ℝ (circleMomentSpan L f) = 0) (ψ : AddCircle L → ℝ) :
    circleControlMoment L f ψ = 0 := by
  have hf := (circleMomentSpan_finrank_zero_iff L f).mp hd
  simp [circleControlMoment, hf]

theorem representative_weighted_moment_eq_zero_of_finrank_zero {m : ℕ} (L : ℝ)
    (f : AddCircle L → EuclideanSpace ℝ (Fin m))
    (hd : Module.finrank ℝ (circleMomentSpan L f) = 0) (a : ℝ → ℝ) :
    (∫ s in 0..L, a s • f (periodProjection L s)) = 0 := by
  have hf := (circleMomentSpan_finrank_zero_iff L f).mp hd
  simp [hf]

theorem circleMomentSpan_finrank_pos_iff {m : ℕ} (L : ℝ)
    (f : AddCircle L → EuclideanSpace ℝ (Fin m)) :
    0 < Module.finrank ℝ (circleMomentSpan L f) ↔ ∃ q, f q ≠ 0 := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, circleMomentSpan_finrank_zero_iff, not_forall]

end
end TightVer401
