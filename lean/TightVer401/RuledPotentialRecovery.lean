import TightVer401.RuledPotentialPDE

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem ruledPotential_reconstruction {k τ : ℝ → ℝ} {α β : Coord → ℝ} {p : Coord} {ks τs : ℝ}
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0)) (hτ0 : τ (p 0) ≠ 0)
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p)
    (hmix : (1 - k (p 0) * p 1) * coordPartial 1 α p +
      τ (p 0) * p 1 * coordPartial 1 β p + k (p 0) * α p - τ (p 0) * β p = 0) :
    α p = ruledPotential k τ α β p - p 1 * coordPartial 1 (ruledPotential k τ α β) p / 2 ∧
    β p = (k (p 0) * ruledPotential k τ α β p +
      (1 - k (p 0) * p 1) * coordPartial 1 (ruledPotential k τ α β) p / 2) / τ (p 0) := by
  rw [ruledPotential_partial hk hτ hα hβ 1]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
    zero_mul, one_mul, add_zero]
  dsimp only [ruledPotential]
  convert! ruled_reconstruction_from_mixed_strain hτ0 hmix using 1 <;> ring

theorem ruledPotential_nonzero_of_bending {k τ : ℝ → ℝ} {α β : Coord → ℝ}
    {T n : ℝ → Ambient} (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ)
    (hτ0 : ∀ s, τ s ≠ 0)
    (hα : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ α p)
    (hβ : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ β p)
    (hmix : ∀ p : Coord, 0 < p 1 → (1 - k (p 0) * p 1) * coordPartial 1 α p +
      τ (p 0) * p 1 * coordPartial 1 β p + k (p 0) * α p - τ (p 0) * β p = 0)
    {p : Coord} (hp : 0 < p 1) (hne : ruledBending α β T n p ≠ 0) :
    ∃ q : Coord, 0 < q 1 ∧ ruledPotential k τ α β q ≠ 0 := by
  by_contra! hz
  have he : ruledPotential k τ α β =ᶠ[𝓝 p] (fun _ => 0) := by
    have hpos : ∀ᶠ q : Coord in 𝓝 p, 0 < q 1 :=
      continuousAt_const.eventually_lt (continuous_apply 1).continuousAt hp
    filter_upwards [hpos] with q hq
    exact hz q hq
  have hd : coordPartial 1 (ruledPotential k τ α β) p = 0 := by
    have hc : fderiv ℝ (fun _ : Coord => (0 : ℝ)) p = 0 :=
      (hasFDerivAt_const (c := (0 : ℝ)) p).fderiv
    simp [coordPartial, he.fderiv_eq (𝕜 := ℝ), hc]
  obtain ⟨ha, hb⟩ := ruledPotential_reconstruction
    (hk.differentiable (by simp) (p 0)).hasDerivAt
    (hτ.differentiable (by simp) (p 0)).hasDerivAt (hτ0 _) (hα p hp) (hβ p hp) (hmix p hp)
  rw [hz p hp, hd] at ha hb
  have ha0 : α p = 0 := by simpa using ha
  have hb0 : β p = 0 := by simpa using hb
  exact hne (by simp [ruledBending, ha0, hb0])

end
end TightVer401
