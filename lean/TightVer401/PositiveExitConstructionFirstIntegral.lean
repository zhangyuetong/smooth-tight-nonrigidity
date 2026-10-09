import TightVer401.PositiveExitConstructionLevels
import TightVer401.RuledProfiles
import TightVer401.AdvectionTransport
import TightVer401.IdentityBandCentralSupportInterior

/-! The actual raw first integral and nonruling null direction of the same
ruled identity band. Reciprocal coordinate derivatives and actual second
form coefficients are specialized from the retained calculus. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The retained reciprocal first integral with the actual frame coefficients. -/
abbrev positiveExitRawFirstIntegral {T : ℝ} (d : PeriodicRuledFrame T) : Coord → ℝ :=
  ruledFirstIntegral (ruledRho d.τ) (ruledOmega d.k d.τ)

/-- The actual nonruling characteristic tangent, with first coordinate one. -/
def positiveExitRawNullDirection {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord) : Coord :=
  ![1, -(q 1 / 2) * (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0))]

private theorem positiveExit_firstIntegral_derivative_data {T : ℝ}
    (d : PeriodicRuledFrame T) (q : Coord) :
    HasDerivAt (ruledRho d.τ)
      (ruledLambda d.τ (q 0) * ruledRho d.τ (q 0) / 2) (q 0) ∧
    HasDerivAt (ruledOmega d.k d.τ)
      (ruledD d.k d.τ (q 0) / (2 * ruledRho d.τ (q 0))) (q 0) := by
  constructor
  · simpa only [ruledLambda] using ruledRho_hasDerivAt
      (d.smooth_τ.differentiable (by simp) (q 0)).hasDerivAt (d.torsion_ne_zero (q 0))
  · exact ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero (q 0)

theorem positiveExitRawFirstIntegral_contDiffOn {T : ℝ} (d : PeriodicRuledFrame T) :
    ContDiffOn ℝ ∞ (positiveExitRawFirstIntegral d) {q : Coord | 0 < q 1} := by
  have hρ := (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero).comp (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hω := (rawPrimitive_contDiff
    (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero)).comp
      (contDiff_apply ℝ ℝ (0 : Fin 2))
  exact (contDiffOn_const.div (hρ.contDiffOn.mul (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffOn)
    (fun q hq => mul_ne_zero (ruledRho_pos (d.torsion_ne_zero (q 0))).ne' hq.ne')).sub hω.contDiffOn

/-- The actual zero balance makes the raw first integral periodic at every height. -/
theorem positiveExitRawFirstIntegral_periodic {T : ℝ} (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (u : ℝ) :
    Function.Periodic (fun r => positiveExitRawFirstIntegral d (![r, u] : Coord)) T := by
  intro r
  simp only [positiveExitRawFirstIntegral, ruledFirstIntegral, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, (ruledRho_periodic d.period_τ) r,
    (periodicRuledFrame_omega_periodic d hb) r]

/-- Exact actual first-coordinate and transverse derivatives. -/
theorem positiveExitRawFirstIntegral_partials {T : ℝ} (d : PeriodicRuledFrame T)
    (q : Coord) (hq : 0 < q 1) :
    coordPartial 0 (positiveExitRawFirstIntegral d) q =
      -(ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)) /
        (2 * ruledRho d.τ (q 0) * q 1) ∧
    coordPartial 1 (positiveExitRawFirstIntegral d) q =
      -1 / (ruledRho d.τ (q 0) * (q 1)^2) := by
  obtain ⟨hρ, hω⟩ := positiveExit_firstIntegral_derivative_data d q
  have hρ0 := (ruledRho_pos (d.torsion_ne_zero (q 0))).ne'
  constructor
  · simpa using ruledFirstIntegral_partial hρ hω hρ0 hq.ne' 0
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ruledFirstIntegral_partial hρ hω hρ0 hq.ne' 1

/-- In particular the first integral is a regular transverse coordinate. -/
theorem positiveExitRawFirstIntegral_partial1_neg {T : ℝ} (d : PeriodicRuledFrame T)
    (q : Coord) (hq : 0 < q 1) : coordPartial 1 (positiveExitRawFirstIntegral d) q < 0 := by
  rw [(positiveExitRawFirstIntegral_partials d q hq).2]
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos (ruledRho_pos (d.torsion_ne_zero (q 0))) (pow_pos hq 2))

theorem positiveExitRawFirstIntegral_partial1_ne_zero {T : ℝ} (d : PeriodicRuledFrame T)
    (q : Coord) (hq : 0 < q 1) : coordPartial 1 (positiveExitRawFirstIntegral d) q ≠ 0 :=
  (positiveExitRawFirstIntegral_partial1_neg d q hq).ne
/-- The actual scalar differential annihilates the actual nonruling null direction. -/
theorem positiveExitRawFirstIntegral_annihilates_null {T : ℝ}
    (d : PeriodicRuledFrame T) (q : Coord) (hq : 0 < q 1) :
    fderiv ℝ (positiveExitRawFirstIntegral d) q (positiveExitRawNullDirection d q) = 0 := by
  rw [fderiv_two_scalar_coordinates,
    (positiveExitRawFirstIntegral_partials d q hq).1,
    (positiveExitRawFirstIntegral_partials d q hq).2]
  simp only [positiveExitRawNullDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, one_mul]
  have hρ0 := (ruledRho_pos (d.torsion_ne_zero (q 0))).ne'
  field_simp [hρ0, hq.ne']
  <;> ring

/-- This null direction is an actual asymptotic tangent of the actual ruled
immersion, expressed using its actual ambient Gauss differential. -/
theorem positiveExitRawNullDirection_actual_pairing {T : ℝ}
    (d : PeriodicRuledFrame T) (q : Coord) :
    inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) q (positiveExitRawNullDirection d q))
      (fderiv ℝ d.rawGaussMap q (positiveExitRawNullDirection d q)) = 0 := by
  rw [identityBand_interior_differential_pairing]
  simp only [positiveExitRawNullDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, mul_one, one_mul]
  have hz : q 1 * d.τ (q 0) *
      (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)) +
      d.τ (q 0) * (-(q 1 / 2) *
        (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0)) +
        -(q 1 / 2) * (ruledLambda d.τ (q 0) + q 1 * ruledD d.k d.τ (q 0))) = 0 := by ring
  rw [hz]
  simp

/-- Native and raw label definitions agree on actual quotient representatives. -/
theorem positiveExitRawFirstIntegral_native_label {T w : ℝ} (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (r : ℝ) (u : Ioo (0 : ℝ) w) :
    positiveExitRawFirstIntegral d (![r, (u : ℝ)] : Coord) =
      positiveExitLevel d hb (periodProjection T r, u) := by
  change 1 / (ruledRho d.τ r * (u : ℝ)) - ruledOmega d.k d.τ r =
    1 / ((ruledRho_periodic d.period_τ).lift (r : AddCircle T) * (u : ℝ)) -
      (periodicRuledFrame_omega_periodic d hb).lift (r : AddCircle T)
  simp only [Function.Periodic.lift_coe]

/-- The same actual selected complete trajectory lies in one level, with its
label derived from its actual initial height. -/
theorem positiveExitRawFirstIntegral_trajectory {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) δ) (t : ℝ) :
    positiveExitRawFirstIntegral d
      (![t, principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t] : Coord) =
        1 / (ruledRho d.τ 0 * u) - ruledOmega d.k d.τ 0 := by
  exact positiveExit_trajectory_first_integral d hinside hu t

end
end TightVer401
