import TightVer401.CharacteristicTransport
import TightVer401.ProjectiveJets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Integration of the scalar Riccati characteristic equation, using actual
derivatives and a primitive for q₂ exp(A). The zero-free solution domain is
explicit. Establishing its geometric inputs is a separate ruled-band step. -/
namespace TightVer401
noncomputable section

theorem riccati_reciprocal_derivative
    {A u : ℝ → ℝ} {s q₁ q₂ : ℝ}
    (hA : HasDerivAt A q₁ s)
    (hu : HasDerivAt u (q₁ * u s + q₂ * (u s)^2) s)
    (hu0 : u s ≠ 0) :
    HasDerivAt (fun t => Real.exp (A t) / u t) (-q₂ * Real.exp (A s)) s := by
  convert! hA.exp.fun_div hu hu0 using 1
  field_simp
  <;> ring

theorem riccati_first_integral_derivative
    {A u V : ℝ → ℝ} {s q₁ q₂ : ℝ}
    (hA : HasDerivAt A q₁ s)
    (hu : HasDerivAt u (q₁ * u s + q₂ * (u s)^2) s)
    (hV : HasDerivAt V (q₂ * Real.exp (A s)) s)
    (hu0 : u s ≠ 0) :
    HasDerivAt (fun t => Real.exp (A t) / u t + V t) 0 s := by
  convert! (riccati_reciprocal_derivative hA hu hu0).fun_add hV using 1
  ring

theorem riccati_return_of_characteristic
    {A u V q₁ q₂ : ℝ → ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hc : IsPreconnected J)
    (hA : ∀ t ∈ J, HasDerivAt A (q₁ t) t)
    (hu : ∀ t ∈ J, HasDerivAt u (q₁ t * u t + q₂ t * (u t)^2) t)
    (hV : ∀ t ∈ J, HasDerivAt V (q₂ t * Real.exp (A t)) t)
    (hu0 : ∀ t ∈ J, u t ≠ 0)
    (h0 : (0 : ℝ) ∈ J) {L : ℝ} (hL : L ∈ J)
    (hA0 : A 0 = 0) (hV0 : V 0 = 0) :
    u L = mobiusReturn (Real.exp (A L)) (V L) (u 0) := by
  have hd (t) (ht : t ∈ J) := riccati_first_integral_derivative
    (hA t ht) (hu t ht) (hV t ht) (hu0 t ht)
  have h := hJ.is_const_of_deriv_eq_zero hc
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) h0 hL
  simp only [hA0, hV0, Real.exp_zero, add_zero] at h
  have he : u L * (1 - V L * u 0) = Real.exp (A L) * u 0 := by
    field_simp [hu0 0 h0, hu0 L hL] at h
    nlinarith [h]
  have hp : 1 - V L * u 0 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact mul_ne_zero (Real.exp_ne_zero _) (hu0 0 h0) he.symm
  exact (eq_div_iff hp).mpr he

end
end TightVer401
