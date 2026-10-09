import TightVer401.RuledProfileStrain
import TightVer401.RuledLeaves

/-! The profile is recovered from the actual vector field, so the profile
parametrization is injective on all complete leaf levels in the band. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def ruledProfileField (k τ ρ W F : ℝ → ℝ) (T n : ℝ → Ambient) : Coord → Ambient :=
  ruledBending (ruledProfileAlpha τ ρ W F) (ruledProfileBeta k ρ W F) T n

theorem ruled_profile_potential
    {k τ ρ W F : ℝ → ℝ} {T E n : ℝ → Ambient} {p : Coord}
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    inner ℝ (ruledProfileField k τ ρ W F T n p)
      ((1 - k (p 0) * p 1) • T (p 0) + (τ (p 0) * p 1) • n (p 0)) =
        τ (p 0) * (p 1)^2 * F (ruledFirstIntegral ρ W p) := by
  rcases hf with ⟨hTT, _, hnn, _, hTn, _⟩
  have hnT : inner ℝ (n (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTn]
  simp only [ruledProfileField, ruledBending, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hTT, hnn, hTn, hnT,
    mul_zero, mul_one, zero_add, add_zero]
  dsimp only [ruledProfileAlpha, ruledProfileBeta]
  simp only [div_eq_mul_inv]
  ring

theorem ruled_profile_value_of_field_eq
    {k τ ρ W F G : ℝ → ℝ} {T E n : ℝ → Ambient} {p : Coord}
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : τ (p 0) ≠ 0) (hu : p 1 ≠ 0)
    (he : ruledProfileField k τ ρ W F T n p = ruledProfileField k τ ρ W G T n p) :
    F (ruledFirstIntegral ρ W p) = G (ruledFirstIntegral ρ W p) := by
  have h := congrArg (fun v : Ambient => inner ℝ v
    ((1 - k (p 0) * p 1) • T (p 0) + (τ (p 0) * p 1) • n (p 0))) he
  rw [ruled_profile_potential hf, ruled_profile_potential hf] at h
  exact (mul_left_cancel₀ (mul_ne_zero hτ (pow_ne_zero 2 hu))) h

theorem ruled_profile_unique_at_leaf_level
    {k τ ρ W F G : ℝ → ℝ} {T E n : ℝ → Ambient} {s c b : ℝ}
    (hf : IsOrthonormalFrame (T s) (E s) (n s))
    (hτ : τ s ≠ 0) (hρ : 0 < ρ s) (hb : 0 < b)
    (hc : 1 / (ρ s * b) - W s < c)
    (he : ∀ u ∈ Set.Ioo 0 b,
      ruledProfileField k τ ρ W F T n (![s, u] : Coord) =
        ruledProfileField k τ ρ W G T n (![s, u] : Coord)) : F c = G c := by
  let u := ruledLeaf ρ W c s
  have hu : u ∈ Set.Ioo 0 b := ruledLeaf_in_band hρ hb hc
  have hcw : c + W s ≠ 0 := by
    have hi := one_div_pos.mpr (mul_pos hρ hb)
    linarith
  have hv : ruledFirstIntegral ρ W (![s, u] : Coord) = c :=
    ruledLeaf_first_integral (ne_of_gt hρ) hcw
  have hf' : IsOrthonormalFrame (T ((![s, u] : Coord) 0))
      (E ((![s, u] : Coord) 0)) (n ((![s, u] : Coord) 0)) := by simpa using hf
  have hτ' : τ ((![s, u] : Coord) 0) ≠ 0 := by simpa using hτ
  have hu' : (![s, u] : Coord) 1 ≠ 0 := by simpa using ne_of_gt hu.1
  have h := ruled_profile_value_of_field_eq hf' hτ' hu' (he u hu)
  simpa only [hv] using h

end
end TightVer401
