import TightVer401.RuledStrain
import TightVer401.CharacteristicTransport

/-! The scalar reconstruction and transport identities following the checked
strain reduction, and the actual profile derivative used to recover y_F. -/
namespace TightVer401
noncomputable section

theorem ruled_reconstruction_from_mixed_strain
    {k τ u α β αu βu : ℝ} (hτ : τ ≠ 0)
    (hmix : (1 - k * u) * αu + τ * u * βu + k * α - τ * β = 0) :
    let p := (1 - k * u) * α + τ * u * β
    let pu := -k * α + (1 - k * u) * αu + τ * β + τ * u * βu
    α = p - u * pu / 2 ∧ β = (k * p + (1 - k * u) * pu / 2) / τ := by
  dsimp
  have hpu : -k * α + (1 - k * u) * αu + τ * β + τ * u * βu =
      2 * (τ * β - k * α) := by linarith
  rw [hpu]
  constructor
  · ring
  · apply (eq_div_iff hτ).mpr
    ring

theorem ruled_transport_from_zero_strain
    {k τ ks τs u α β αs βs αu βu : ℝ} (hτ : τ ≠ 0)
    (hss : (1 - k * u) * αs + τ * u * βs = 0)
    (hmix : (1 - k * u) * αu + τ * u * βu + k * α - τ * β = 0) :
    let p := (1 - k * u) * α + τ * u * β
    let pu := -k * α + (1 - k * u) * αu + τ * β + τ * u * βu
    let ps := -ks * u * α + (1 - k * u) * αs + τs * u * β + τ * u * βs
    let lam := τs / τ
    let D := ks - k * lam
    ps - u / 2 * (lam + u * D) * pu = -u * D * p := by
  dsimp
  have hpu : -k * α + (1 - k * u) * αu + τ * β + τ * u * βu =
      2 * (τ * β - k * α) := by linarith
  have hps : -ks * u * α + (1 - k * u) * αs + τs * u * β + τ * u * βs =
      -ks * u * α + τs * u * β := by linarith
  rw [hpu, hps]
  field_simp
  <;> ring

theorem ruled_profile_potential_hasDerivAt
    {F : ℝ → ℝ} {τ ρ ω u f' : ℝ} (hρ : ρ ≠ 0) (hu : u ≠ 0)
    (hF : HasDerivAt F f' (1 / (ρ * u) - ω)) :
    HasDerivAt (fun v => τ * v^2 * F (1 / (ρ * v) - ω))
      (2 * τ * u * F (1 / (ρ * u) - ω) - τ / ρ * f') u := by
  have hdv : HasDerivAt (fun v : ℝ => 1 / (ρ * v) - ω) (-1 / (ρ * u^2)) u := by
    have hi : HasDerivAt (fun v : ℝ => (ρ * v)⁻¹) (-ρ / (ρ * u)^2) u :=
      (hasDerivAt_const_mul ρ).inv (mul_ne_zero hρ hu)
    convert! hi.sub_const ω using 1
    · funext v
      simp [one_div]
    · field_simp
      <;> ring
  have hdF := hF.comp u hdv
  have hdpoly : HasDerivAt (fun v : ℝ => τ * v^2) (τ * (2 * u)) u := by
    convert! ((hasDerivAt_id u).pow 2).const_mul τ using 1
    simp
  convert! hdpoly.mul hdF using 1
  simp only [Function.comp_apply]
  field_simp
  <;> ring

theorem ruled_profile_reconstruction
    {k τ ρ u f f' : ℝ} (hτ : τ ≠ 0) (hρ : ρ ≠ 0) :
    let p := τ * u^2 * f
    let pu := 2 * τ * u * f - τ / ρ * f'
    p - u * pu / 2 = τ * u / (2 * ρ) * f' ∧
    (k * p + (1 - k * u) * pu / 2) / τ =
      u * f - (1 - k * u) / (2 * ρ) * f' := by
  dsimp
  constructor <;> field_simp <;> ring

end
end TightVer401
