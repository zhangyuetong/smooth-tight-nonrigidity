import TightVer401.PotentialNecessity
import TightVer401.RuledPotentialRecovery

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem ruledBending_projections {α β : Coord → ℝ} {T E n : ℝ → Ambient} {p : Coord}
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    inner ℝ (ruledBending α β T n p) (T (p 0)) = α p ∧
    inner ℝ (ruledBending α β T n p) (n (p 0)) = β p := by
  rcases hf with ⟨hTT, _, hnn, _, hTn, _⟩
  have hnT : inner ℝ (n (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTn]
  simp only [ruledBending, inner_add_left, real_inner_smul_left, hTT, hnn, hTn, hnT,
    mul_one, mul_zero, add_zero, zero_add, and_self]

theorem ruledPotential_zero_of_bending_zero {k τ : ℝ → ℝ} {α β : Coord → ℝ}
    {T E n : ℝ → Ambient} {p : Coord}
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hy : ruledBending α β T n p = 0) : ruledPotential k τ α β p = 0 := by
  obtain ⟨ha, hb⟩ := ruledBending_projections (α := α) (β := β) hf
  rw [hy, inner_zero_left] at ha hb
  simp [ruledPotential, ha.symm, hb.symm]

theorem supported_ruled_bending_period_zero
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {α β : Coord → ℝ} {L lower upper : ℝ}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : ∀ s, HasDerivAt T (k s • E s) s)
    (hn : ∀ s, HasDerivAt n (-τ s • E s) s)
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hαL : ∀ s u, α (![s + L, u] : Coord) = α (![s, u] : Coord))
    (hβL : ∀ s u, β (![s + L, u] : Coord) = β (![s, u] : Coord))
    (hα : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ α p)
    (hβ : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ β p)
    (hf : ∀ s, IsOrthonormalFrame (T s) (E s) (n s))
    (hstrain : ∀ p : Coord, 0 < p 1 → ∀ i j : Fin 2,
      strain (ruledMap γ E) (ruledBending α β T n) p i j = 0)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsupportLower : ∀ p : Coord, p 1 < lower → ruledBending α β T n p = 0)
    (hsupportUpper : ∀ p : Coord, upper < p 1 → ruledBending α β T n p = 0)
    {p : Coord} (hp : 0 < p 1) (hne : ruledBending α β T n p ≠ 0) :
    (∫ r in 0..L, ruledPeriodCoefficient k τ r) = 0 := by
  have hmix (q : Coord) (hq : 0 < q 1) :
      (1 - k (q 0) * q 1) * coordPartial 1 α q +
      τ (q 0) * q 1 * coordPartial 1 β q + k (q 0) * α q - τ (q 0) * β q = 0 := by
    obtain ⟨_, hm, _⟩ := ruled_strain_equations (hγ (q 0)) (hE (q 0)) (hT (q 0))
      (hn (q 0)) (hα q hq) (hβ q hq) (hf (q 0))
    exact hm.symm.trans (hstrain q hq 0 1)
  obtain ⟨q, hq, hPq⟩ := ruledPotential_nonzero_of_bending hk hτ hτ0 hα hβ hmix hp hne
  apply ruled_potential_period_necessity (P := ruledPotential k τ α β)
    hk hτ hτ0 hkL hτL hlower hupper
  · intro r hr
    exact ruledPotential_differentiableAt (hk.differentiable (by simp) (r 0))
      (hτ.differentiable (by simp) (r 0)) (hα r hr) (hβ r hr)
  · intro r hr
    exact ruledPotential_zero_of_bending_zero (hf (r 0)) (hsupportLower r hr)
  · intro r hr
    exact ruledPotential_zero_of_bending_zero (hf (r 0)) (hsupportUpper r hr)
  · intro s u
    simp [ruledPotential, hkL s, hτL s, hαL s u, hβL s u]
  · intro r hr
    exact ruledPotential_transport_of_zero_strain (hγ (r 0)) (hE (r 0)) (hT (r 0)) (hn (r 0))
      (hk.differentiable (by simp) (r 0)).hasDerivAt
      (hτ.differentiable (by simp) (r 0)).hasDerivAt (hτ0 (r 0))
      (hα r hr) (hβ r hr) (hf (r 0)) (hstrain r hr 0 0) (hstrain r hr 0 1)
  · exact hq
  · exact hPq

end
end TightVer401
