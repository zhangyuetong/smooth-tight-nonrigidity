import TightVer401.PositiveExitConstructionLevels

/-! Positive initial-value derivative of the SAME original characteristic
flow. This produces the actual transverse orientation factor, independently
of a selected graph or an assumed annulus Jacobian. Cartesian Gauss projection
and full raw-annulus orientation remain separate obligations. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Differentiate the actual principal trajectory in its initial value,
with the starting and terminal phases held fixed. -/
theorem positiveExit_selectedSourceGeometry_trajectory_initialValue_hasDerivAt
    (ρ W : ℝ → ℝ) (s t v : ℝ) (hρt : ρ t ≠ 0)
    (hd : 1 + ρ s * v * (W t - W s) ≠ 0) :
    HasDerivAt (fun u => principalTrajectory ρ W s u t)
      (ρ s / (ρ t * (1 + ρ s * v * (W t - W s))^2)) v := by
  have hn := (hasDerivAt_id v).const_mul (ρ s)
  have hden := (((hasDerivAt_const v (1 : ℝ)).add
    (((hasDerivAt_id v).const_mul (ρ s)).mul_const (W t - W s))).const_mul (ρ t))
  convert! hn.div hden (mul_ne_zero hρt hd) using 1 <;>
    simp only [principalTrajectory, id_eq, Pi.add_apply] <;>
    field_simp [hρt, hd] <;> ring

/-- Positivity of the original rho factors forces a strictly positive
initial-value derivative wherever the actual denominator is nonzero. -/
theorem positiveExit_selectedSourceGeometry_trajectory_initialValue_deriv_pos
    (ρ W : ℝ → ℝ) (s t v : ℝ) (hρs : 0 < ρ s) (hρt : 0 < ρ t)
    (hd : 1 + ρ s * v * (W t - W s) ≠ 0) :
    deriv (fun u => principalTrajectory ρ W s u t) v =
      ρ s / (ρ t * (1 + ρ s * v * (W t - W s))^2) ∧
    0 < deriv (fun u => principalTrajectory ρ W s u t) v := by
  have he := (positiveExit_selectedSourceGeometry_trajectory_initialValue_hasDerivAt
    ρ W s t v hρt.ne' hd).deriv
  refine ⟨he, ?_⟩
  rw [he]
  exact div_pos hρs (mul_pos hρt (sq_pos_of_ne_zero hd))

/-- The SAME original ruled flow has a positive transverse derivative
throughout its actual complete initial interval. In-band containment produces
its denominator condition; no orientation package is assumed. -/
theorem positiveExit_selectedSourceGeometry_ruledFlow_initialValue_deriv_pos
    {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) δ) (t : ℝ) :
    HasDerivAt
      (fun u => principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t)
      (ruledRho d.τ 0 / (ruledRho d.τ t *
        (1 + ruledRho d.τ 0 * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ 0))^2)) v ∧
    0 < deriv
      (fun u => principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t) v := by
  have hρ0 := ruledRho_pos (d.torsion_ne_zero 0)
  have hρt := ruledRho_pos (d.torsion_ne_zero t)
  have hd := positiveExit_trajectory_denominator_ne_zero d hinside hv t
  exact ⟨positiveExit_selectedSourceGeometry_trajectory_initialValue_hasDerivAt
      (ruledRho d.τ) (ruledOmega d.k d.τ) 0 t v hρt.ne' hd,
    (positiveExit_selectedSourceGeometry_trajectory_initialValue_deriv_pos
      (ruledRho d.τ) (ruledOmega d.k d.τ) 0 t v hρ0 hρt hd).2⟩

end
end TightVer401

