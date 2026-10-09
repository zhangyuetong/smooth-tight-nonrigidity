import TightVer401.QuadraticRadialFillingUnitTurn

/-! Every actual point inside a round circle has an actual continuous
normalized argument lift with one positive turn around that circle. -/
namespace TightVer401
noncomputable section
open Set Function ComplexConjugate
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Rotate the actual translated circle into its outward radial frame. -/
def quadraticRadialFillingRoundRotatedTrace (R : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  (circleMap 0 R s - z) * conj (circleMap 0 1 s)

/-- An explicit actual direction lift of the translated round circle. -/
def quadraticRadialFillingRoundDirectionLift (R : ℝ) (z : ℂ) (s : ℝ) : ℝ :=
  s + Complex.arg (quadraticRadialFillingRoundRotatedTrace R z s)

theorem quadraticRadialFillingRoundRotatedTrace_eq (R : ℝ) (z : ℂ) (s : ℝ) :
    quadraticRadialFillingRoundRotatedTrace R z s =
      (R : ℂ) - z * conj (circleMap 0 1 s) := by
  have hr : circleMap 0 R s * conj (circleMap 0 1 s) = (R : ℂ) := by
    rw [conj_circleMap_zero, circleMap_zero_mul]
    simp [circleMap]
  unfold quadraticRadialFillingRoundRotatedTrace
  rw [sub_mul, hr]

/-- The entire rotated trace lies in the actual right half-plane, from the
ordinary physical inequality that the point lies strictly inside the circle. -/
theorem quadraticRadialFillingRoundRotatedTrace_re_pos
    {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) (s : ℝ) :
    0 < (quadraticRadialFillingRoundRotatedTrace R z s).re := by
  have hb : (z * conj (circleMap 0 1 s)).re ≤ ‖z‖ := by
    simpa only [norm_mul, Complex.norm_conj, norm_circleMap_zero, abs_one, mul_one] using
      Complex.re_le_norm (z * conj (circleMap 0 1 s))
  rw [quadraticRadialFillingRoundRotatedTrace_eq, Complex.sub_re, Complex.ofReal_re]
  linarith

theorem quadraticRadialFillingRoundRotatedTrace_periodic (R : ℝ) (z : ℂ) :
    Function.Periodic (quadraticRadialFillingRoundRotatedTrace R z) (2 * Real.pi) := by
  intro s
  unfold quadraticRadialFillingRoundRotatedTrace
  rw [periodic_circleMap 0 R s, periodic_circleMap 0 1 s]

/-- Right-half-plane membership supplies continuity of the explicit
ordinary real argument, without a supplied continuous angle branch. -/
theorem quadraticRadialFillingRoundDirectionLift_continuous
    {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) :
    Continuous (quadraticRadialFillingRoundDirectionLift R z) := by
  have hq : Continuous (quadraticRadialFillingRoundRotatedTrace R z) :=
    ((quadraticRadialFillingCircle_contDiff R).continuous.sub continuous_const).mul
      (Complex.continuous_conj.comp (quadraticRadialFillingCircle_contDiff 1).continuous)
  apply continuous_id.add
  apply continuous_iff_continuousAt.mpr
  intro s
  have hs : quadraticRadialFillingRoundRotatedTrace R z s ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr
      (Or.inl (quadraticRadialFillingRoundRotatedTrace_re_pos hz s))
  exact (Complex.continuousAt_arg hs).comp hq.continuousAt

/-- Actual unit-circle rotation proves that the constructed real angle
projects to the actual direction of the translated source circle. -/
theorem quadraticRadialFillingRoundDirectionLift_projects
    {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) (s : ℝ) :
    complexCircleDirection (circleMap 0 R s - z) =
      Circle.exp (quadraticRadialFillingRoundDirectionLift R z s) := by
  let w := circleMap 0 R s - z
  let q := quadraticRadialFillingRoundRotatedTrace R z s
  have hqne : q ≠ 0 := by
    have hp : 0 < q.re := quadraticRadialFillingRoundRotatedTrace_re_pos hz s
    intro he
    simpa [he] using hp
  have hwne : w ≠ 0 := by
    intro he
    apply hqne
    change (circleMap 0 R s - z) * conj (circleMap 0 1 s) = 0
    change w * conj (circleMap 0 1 s) = 0
    rw [he, zero_mul]
  have hn : ‖q‖ = ‖w‖ := by
    simp [q, w, quadraticRadialFillingRoundRotatedTrace, norm_mul]
  have hr : q * circleMap 0 1 s = w := by
    have he : conj (circleMap 0 1 s) * circleMap 0 1 s = 1 := by
      rw [conj_circleMap_zero, circleMap_zero_mul]
      simp [circleMap]
    dsimp [q, quadraticRadialFillingRoundRotatedTrace]
    rw [mul_assoc, he, mul_one]
  have hqe : Complex.exp ((Complex.arg q : ℂ) * Complex.I) = ‖q‖⁻¹ • q :=
    (complexCircleDirection_coe q).symm.trans (complexCircleDirection_normalized hqne)
  apply complexCircleDirection_eq_of_exp hwne
  change Complex.exp (((s + Complex.arg q : ℝ) : ℂ) * Complex.I) = ‖w‖⁻¹ • w
  calc
    _ = circleMap 0 1 s * Complex.exp ((Complex.arg q : ℂ) * Complex.I) := by
      simp only [Complex.ofReal_add, add_mul, Complex.exp_add, circleMap_zero,
        Complex.ofReal_one, one_mul]
    _ = ‖q‖⁻¹ • (q * circleMap 0 1 s) := by
      rw [hqe, Complex.real_smul, Complex.real_smul]
      ring
    _ = ‖w‖⁻¹ • w := by rw [hr, hn]

theorem quadraticRadialFillingRoundDirectionLift_turn (R : ℝ) (z : ℂ) :
    quadraticRadialFillingRoundDirectionLift R z (2 * Real.pi) =
      quadraticRadialFillingRoundDirectionLift R z 0 + 2 * Real.pi := by
  have hp := quadraticRadialFillingRoundRotatedTrace_periodic R z 0
  simp only [zero_add] at hp
  unfold quadraticRadialFillingRoundDirectionLift
  rw [hp]
  ring

/-- Construct the normalized argument lift and its exact one-turn endpoint
equality for each ordinary actual point strictly inside the round circle. -/
theorem quadraticRadialFillingRound_exists_normalized_argument_unit_turn
    {R : ℝ} (_hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    ∃ u : C(unitInterval, ℝ),
      (∀ t : unitInterval,
        normalizedArgument (circleMap 0 R (2 * Real.pi * (t : ℝ)) - z) =
          (u t : UnitAddCircle)) ∧
      u 1 = u 0 + 1 :=
  quadraticRadialFilling_exists_normalized_argument_unit_turn
    (quadraticRadialFillingRoundDirectionLift_continuous hz)
    (quadraticRadialFillingRoundDirectionLift_projects hz)
    (quadraticRadialFillingRoundDirectionLift_turn R z)

end
end TightVer401
