import TightVer401.MomentPrescriptionPath
import TightVer401.PeriodCircle

namespace TightVer401
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

theorem momentPrescription_circle_support {n : ℕ} (L : ℝ)
    {A b χ : AddCircle L → ℝ} {Ψ : Fin n → AddCircle L → ℝ} {a : ℝ → ℝ}
    (hA : ∀ r, A (periodProjection L r) = a r)
    (hreal : Function.support (fun r => a r - b (periodProjection L r)) ⊆
      Function.support (χ ∘ periodProjection L) ∪
        ⋃ j, Function.support (Ψ j ∘ periodProjection L)) :
    Function.support (fun q => A q - b q) ⊆ Function.support χ ∪ ⋃ j, Function.support (Ψ j) := by
  intro q hq
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective q
  have hr' : periodProjection L r = q := hr
  have hrealmem : r ∈ Function.support (fun r => a r - b (periodProjection L r)) := by
    change a r - b (periodProjection L r) ≠ 0
    rw [← hA r, hr']
    exact hq
  rcases hreal hrealmem with hχ | hΨ
  · left
    change χ q ≠ 0
    change χ (periodProjection L r) ≠ 0 at hχ
    rwa [hr'] at hχ
  · right
    obtain ⟨j, hj⟩ := mem_iUnion.mp hΨ
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change Ψ j q ≠ 0
    change Ψ j (periodProjection L r) ≠ 0 at hj
    rwa [hr'] at hj

theorem momentPrescription_circle_short_arcs {n : ℕ} (L : ℝ)
    {A b χ : AddCircle L → ℝ} {Ψ : Fin n → AddCircle L → ℝ} {ε : ℝ}
    (hsupport : Function.support (fun q => A q - b q) ⊆
      Function.support χ ∪ ⋃ j, Function.support (Ψ j))
    (hχ : ∃ c r : ℝ, 0 ≤ r ∧ 2 * r < ε ∧
      Function.support χ ⊆ periodProjection L '' Icc (c - r) (c + r))
    (hΨ : ∀ j, ∃ c r : ℝ, 0 ≤ r ∧ 2 * r < ε ∧
      Function.support (Ψ j) ⊆ periodProjection L '' Icc (c - r) (c + r)) :
    ∃ centers radii : Fin (n + 1) → ℝ,
      (∀ j, 0 ≤ radii j ∧ 2 * radii j < ε) ∧
      Function.support (fun q => A q - b q) ⊆
        ⋃ j, periodProjection L '' Icc (centers j - radii j) (centers j + radii j) := by
  classical
  obtain ⟨c₀, r₀, hr₀, hε₀, hχsupp⟩ := hχ
  choose c r hr hε hs using hΨ
  let centers : Fin (n + 1) → ℝ := Fin.cons c₀ c
  let radii : Fin (n + 1) → ℝ := Fin.cons r₀ r
  refine ⟨centers, radii, ?_, ?_⟩
  · intro j
    refine Fin.cases ⟨hr₀, hε₀⟩ (fun i => ⟨hr i, hε i⟩) j
  · intro q hq
    rcases hsupport hq with hχq | hΨq
    · exact mem_iUnion.mpr ⟨0, hχsupp hχq⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hΨq
      exact mem_iUnion.mpr ⟨j.succ, hs j hj⟩

end
end TightVer401
