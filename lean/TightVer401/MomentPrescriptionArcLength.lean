import TightVer401.MomentPrescriptionSupport

namespace TightVer401
noncomputable section
open Set

theorem momentPrescription_total_arc_length {n : ℕ} {radii : Fin (n + 1) → ℝ}
    {ε : ℝ} (hwidth : ∀ j, 2 * radii j < ε / (n + 1 : ℝ)) :
    (∑ j, 2 * radii j) < ε := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  calc
    (∑ j, 2 * radii j) < ∑ _j : Fin (n + 1), ε / (n + 1 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hwidth j)
    _ = ε := by simp; field_simp

theorem momentPrescription_circle_arcs_total {n : ℕ} (L : ℝ)
    {A b χ : AddCircle L → ℝ} {Ψ : Fin n → AddCircle L → ℝ} {ε : ℝ}
    (hsupport : Function.support (fun q => A q - b q) ⊆
      Function.support χ ∪ ⋃ j, Function.support (Ψ j))
    (hχ : ∃ c r : ℝ, 0 ≤ r ∧ 2 * r < ε / (n + 1 : ℝ) ∧
      Function.support χ ⊆ periodProjection L '' Icc (c - r) (c + r))
    (hΨ : ∀ j, ∃ c r : ℝ, 0 ≤ r ∧ 2 * r < ε / (n + 1 : ℝ) ∧
      Function.support (Ψ j) ⊆ periodProjection L '' Icc (c - r) (c + r)) :
    ∃ centers radii : Fin (n + 1) → ℝ,
      (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
      Function.support (fun q => A q - b q) ⊆
        ⋃ j, periodProjection L '' Icc (centers j - radii j) (centers j + radii j) := by
  obtain ⟨centers, radii, hwidth, hs⟩ :=
    momentPrescription_circle_short_arcs L hsupport hχ hΨ
  exact ⟨centers, radii, fun j => (hwidth j).1,
    momentPrescription_total_arc_length (fun j => (hwidth j).2), hs⟩

end
end TightVer401
