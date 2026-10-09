import TightVer401.CharacteristicTransport

/-! A first integral regular across the central characteristic. The reciprocal
coordinate is used only away from the center; the fraction here is smooth at
u = 0 whenever its denominator is nonzero. -/
namespace TightVer401
noncomputable section

def regularCoordinate (ρ ω u : ℝ) : ℝ := ρ * u / (1 - ρ * u * ω)

theorem regularCoordinate_transverse_derivative (ρ ω : ℝ) :
    HasDerivAt (regularCoordinate ρ ω) ρ 0 := by
  have hn : HasDerivAt (fun u : ℝ => ρ * u) ρ 0 := hasDerivAt_const_mul ρ
  have hd : HasDerivAt (fun u : ℝ => 1 - ρ * u * ω) (-ρ * ω) 0 := by
    have h : HasDerivAt (fun u : ℝ => 1 + (-ρ * ω) * u) (-ρ * ω) 0 :=
      (hasDerivAt_const_mul (-ρ * ω)).const_add 1
    convert! h using 1
    funext u
    ring
  convert! hn.fun_div hd (by simp) using 1
  simp

theorem regularCoordinate_characteristic_derivative
    {ρ u ω : ℝ → ℝ} {s lam D c : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ s / 2) s)
    (hu : HasDerivAt u (-(u s / 2) * (lam + u s * D)) s)
    (hω : HasDerivAt ω (D / (2 * ρ s) - c) s)
    (hρ0 : ρ s ≠ 0) (hd : 1 - ρ s * u s * ω s ≠ 0) :
    HasDerivAt (fun t => regularCoordinate (ρ t) (ω t) (u t))
      (-c * (regularCoordinate (ρ s) (ω s) (u s))^2) s := by
  have hn := hρ.mul hu
  have hden := (hn.mul hω).neg.const_add 1
  convert! hn.div hden hd using 1
  unfold regularCoordinate
  simp only [Pi.mul_apply, Pi.neg_apply, ← sub_eq_add_neg]
  field_simp [hρ0, hd]
  <;> ring

end
end TightVer401
