import TightVer401.ReturnMap
import Mathlib.Analysis.Calculus.MeanValue

/-! The principal-normal characteristic equation is integrated using actual
one-variable derivatives. Inputs are the displayed scalar ODEs, rather than
an assumed return map or an assumed first integral. -/
namespace TightVer401
noncomputable section

theorem reciprocal_characteristic_derivative
    {ρ u : ℝ → ℝ} {s lam D : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ s / 2) s)
    (hu : HasDerivAt u (-(u s / 2) * (lam + u s * D)) s)
    (hρ0 : ρ s ≠ 0) (hu0 : u s ≠ 0) :
    HasDerivAt (fun t => 1 / (ρ t * u t)) (D / (2 * ρ s)) s := by
  convert! (hρ.mul hu).inv (mul_ne_zero hρ0 hu0) using 1
  · ext t
    simp [one_div]
  · field_simp
    <;> simp only [Pi.mul_apply, Pi.pow_apply]
    <;> ring

theorem characteristic_first_integral_derivative
    {ρ u ω : ℝ → ℝ} {s lam D : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ s / 2) s)
    (hu : HasDerivAt u (-(u s / 2) * (lam + u s * D)) s)
    (hω : HasDerivAt ω (D / (2 * ρ s)) s)
    (hρ0 : ρ s ≠ 0) (hu0 : u s ≠ 0) :
    HasDerivAt (fun t => 1 / (ρ t * u t) - ω t) 0 s := by
  convert! (reciprocal_characteristic_derivative hρ hu hρ0 hu0).fun_sub hω using 1
  ring

theorem characteristic_first_integral_constant
    {ρ u ω lam D : ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hc : IsPreconnected J)
    (hρ : ∀ s ∈ J, HasDerivAt ρ (lam s * ρ s / 2) s)
    (hu : ∀ s ∈ J, HasDerivAt u (-(u s / 2) * (lam s + u s * D s)) s)
    (hω : ∀ s ∈ J, HasDerivAt ω (D s / (2 * ρ s)) s)
    (hρ0 : ∀ s ∈ J, ρ s ≠ 0) (hu0 : ∀ s ∈ J, u s ≠ 0)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    1 / (ρ s * u s) - ω s = 1 / (ρ t * u t) - ω t := by
  have hd (r) (hr : r ∈ J) := characteristic_first_integral_derivative
    (hρ r hr) (hu r hr) (hω r hr) (hρ0 r hr) (hu0 r hr)
  exact hJ.is_const_of_deriv_eq_zero hc
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

theorem principal_return_of_reciprocal_increment
    {r u₀ u₁ I : ℝ} (hr : r ≠ 0) (h₀ : u₀ ≠ 0) (h₁ : u₁ ≠ 0)
    (h : 1 / (r * u₁) = 1 / (r * u₀) + I) :
    u₁ = projectiveReturn (r * I) u₀ := by
  have he : u₀ = u₁ * (1 + r * I * u₀) := by
    field_simp at h
    nlinarith [h]
  have hn : 1 + r * I * u₀ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact h₀ he
  exact (eq_div_iff hn).mpr he.symm

theorem transport_weight_derivative
    {τ u p : ℝ → ℝ} {s lam D : ℝ}
    (hτ : HasDerivAt τ (lam * τ s) s)
    (hu : HasDerivAt u (-(u s / 2) * (lam + u s * D)) s)
    (hp : HasDerivAt p (-u s * D * p s) s)
    (hτ0 : τ s ≠ 0) (hu0 : u s ≠ 0) :
    HasDerivAt (fun t => p t / (τ t * (u t)^2)) 0 s := by
  convert! hp.fun_div (hτ.mul (hu.pow 2)) (mul_ne_zero hτ0 (pow_ne_zero 2 hu0)) using 1
  field_simp
  <;> simp only [Pi.mul_apply, Pi.pow_apply]
  <;> ring

theorem principal_return_of_characteristic
    {ρ u ω lam D : ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hc : IsPreconnected J)
    (hρ : ∀ s ∈ J, HasDerivAt ρ (lam s * ρ s / 2) s)
    (hu : ∀ s ∈ J, HasDerivAt u (-(u s / 2) * (lam s + u s * D s)) s)
    (hω : ∀ s ∈ J, HasDerivAt ω (D s / (2 * ρ s)) s)
    (hρ0 : ∀ s ∈ J, ρ s ≠ 0) (hu0 : ∀ s ∈ J, u s ≠ 0)
    {s t I : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hperiod : ρ t = ρ s) (hincrement : ω t - ω s = I) :
    u t = projectiveReturn (ρ s * I) (u s) := by
  have h := characteristic_first_integral_constant hJ hc hρ hu hω hρ0 hu0 hs ht
  rw [hperiod] at h
  apply principal_return_of_reciprocal_increment (hρ0 s hs) (hu0 s hs) (hu0 t ht)
  linarith

/- Compact-support necessity reduces to this ordinary bounded-orbit fact. -/
theorem bounded_additive_orbit_period_zero {r : ℕ → ℝ} {I C : ℝ}
    (hstep : ∀ n, r (n + 1) = r n + I) (hbound : ∀ n, |r n| ≤ C) : I = 0 := by
  have hform (n : ℕ) : r n = r 0 + n * I := by
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih]; push_cast; ring
  by_contra hn
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · obtain ⟨n, hN⟩ := exists_nat_gt ((C + r 0) / (-I))
    have hm := (div_lt_iff₀ (neg_pos.mpr hneg)).mp hN
    have hb := (abs_le.mp (hbound n)).1
    rw [hform] at hb
    nlinarith
  · obtain ⟨n, hN⟩ := exists_nat_gt ((C - r 0) / I)
    have hm := (div_lt_iff₀ hpos).mp hN
    have hb := (abs_le.mp (hbound n)).2
    rw [hform] at hb
    nlinarith

end
end TightVer401
