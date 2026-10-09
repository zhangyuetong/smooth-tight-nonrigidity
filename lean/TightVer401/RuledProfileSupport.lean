import TightVer401.RuledProfileApplication
import TightVer401.RuledCompactLevels
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Support of the displayed vector-valued profile on a compact parameter
circle and a one-sided band. The derivative of F has no larger support. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set

def bandProfile {A : Type*} (k τ ρ W : A → ℝ) (F : ℝ → ℝ)
    (T n : A → Ambient) {b : ℝ} : A × Ioo (0 : ℝ) b → Ambient := fun p =>
  let u : ℝ := p.2
  let v := 1 / (ρ p.1 * u) - W p.1
  (τ p.1 * u / (2 * ρ p.1) * deriv F v) • T p.1 +
    (u * F v - (1 - k p.1 * u) / (2 * ρ p.1) * deriv F v) • n p.1

theorem bandProfile_zero_off_profile_support {A : Type*}
    {k τ ρ W : A → ℝ} {F : ℝ → ℝ} {T n : A → Ambient} {b : ℝ}
    {p : A × Ioo (0 : ℝ) b}
    (hv : 1 / (ρ p.1 * (p.2 : ℝ)) - W p.1 ∉ tsupport F) :
    bandProfile k τ ρ W F T n p = 0 := by
  have hval := image_eq_zero_of_notMem_tsupport hv
  have hder := deriv_of_notMem_tsupport hv
  simp only [bandProfile, hval, hder, mul_zero, sub_zero, zero_smul, add_zero]

theorem bandProfile_hasCompactSupport
    {A : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]
    {k τ ρ W : A → ℝ} {F : ℝ → ℝ} {T n : A → Ambient} {b : ℝ}
    (hρ : Continuous ρ) (hW : Continuous W) (hρpos : ∀ a, 0 < ρ a) (hb : 0 < b)
    (hF : HasCompactSupport F)
    (hlevels : ∀ a, ∀ c ∈ tsupport F, 1 / (ρ a * b) - W a < c) :
    HasCompactSupport (bandProfile k τ ρ W F T n (b := b)) := by
  apply compact_support_of_compact_leaf_levels hρ hW hρpos hb hF hlevels
  intro p hp
  exact bandProfile_zero_off_profile_support hp

theorem bandProfile_real_lift {k τ ρ W F : ℝ → ℝ} {T n : ℝ → Ambient} {b : ℝ}
    (p : ℝ × Ioo (0 : ℝ) b) :
    bandProfile k τ ρ W F T n p =
      ruledProfileField k τ ρ W F T n (![p.1, (p.2 : ℝ)] : Coord) := by
  rfl

end
end TightVer401
