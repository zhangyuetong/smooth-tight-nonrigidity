import TightVer401.RuledProfileSupport
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! A nonzero smooth compact profile exists above every real cutoff. The
scalar bump is the same Mathlib construction used in OpenAI's localized bumps. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set Metric
open scoped ContDiff

theorem exists_nonzero_compact_profile_above (c : ℝ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Ioi c ∧ F (c + 2) = 1 := by
  let φ : ContDiffBump (c + 2) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, ?_⟩
  · intro t ht
    rw [φ.tsupport_eq] at ht
    change dist t (c + 2) ≤ 1 at ht
    rw [Real.dist_eq] at ht
    have hh := (abs_le.mp ht).1
    change c < t
    linarith
  · exact φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)

theorem ruled_profile_nonzero_of_value
    {k τ ρ W F : ℝ → ℝ} {T E n : ℝ → Ambient} {p : Coord}
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : τ (p 0) ≠ 0) (hu : p 1 ≠ 0) (hF : F (ruledFirstIntegral ρ W p) ≠ 0) :
    ruledProfileField k τ ρ W F T n p ≠ 0 := by
  intro hz
  have he := ruled_profile_potential (k := k) (τ := τ) (ρ := ρ) (W := W) (F := F) hf
  rw [hz, inner_zero_left] at he
  exact (mul_ne_zero (mul_ne_zero hτ (pow_ne_zero 2 hu)) hF) he.symm

end
end TightVer401
