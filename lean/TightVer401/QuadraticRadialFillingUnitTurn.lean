import TightVer401.QuadraticRadialFillingGradientWinding
import OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic

/-! The actual radial-positive gradient direction gives a normalized
period-one argument lift with endpoint increase exactly one. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual circle direction agreement gives argument agreement in the
period-one quotient, using the actual period-rescaling equivalence. -/
theorem quadraticRadialFilling_normalizedArgument_of_direction
    {z : ℂ} {φ : ℝ} (hφ : complexCircleDirection z = Circle.exp φ) :
    normalizedArgument z = ((φ / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
  have hexp : AddCircle.toCircle (T := 2 * Real.pi) (φ : AddCircle (2 * Real.pi)) =
      Circle.exp φ := by
    rw [AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul]
  have hangle : (Complex.arg z : AddCircle (2 * Real.pi)) =
      (φ : AddCircle (2 * Real.pi)) := by
    apply AddCircle.injective_toCircle Real.two_pi_pos.ne'
    exact hφ.trans hexp.symm
  unfold normalizedArgument
  change AddCircle.equivAddCircle (2 * Real.pi) 1 Real.two_pi_pos.ne' one_ne_zero
    (Complex.arg z : AddCircle (2 * Real.pi)) =
    ((φ / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [hangle, AddCircle.equivAddCircle_apply_mk]
  simp only [mul_one, div_eq_mul_inv]

/-- Rescaling an actual continuous real direction lift constructs its
continuous normalized argument lift on the actual unit interval. -/
theorem quadraticRadialFilling_exists_normalized_argument_unit_turn
    {γ : ℝ → ℂ} {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hproj : ∀ s, complexCircleDirection (γ s) = Circle.exp (φ s))
    (hturn : φ (2 * Real.pi) = φ 0 + 2 * Real.pi) :
    ∃ u : C(unitInterval, ℝ),
      (∀ t : unitInterval,
        normalizedArgument (γ (2 * Real.pi * (t : ℝ))) = (u t : UnitAddCircle)) ∧
      u 1 = u 0 + 1 := by
  have ht : Continuous (fun t : unitInterval => 2 * Real.pi * (t : ℝ)) :=
    continuous_const.mul continuous_subtype_val
  let u : C(unitInterval, ℝ) :=
    ⟨fun t => φ (2 * Real.pi * (t : ℝ)) / (2 * Real.pi),
      (hφ.comp ht).div_const (2 * Real.pi)⟩
  refine ⟨u, ?_, ?_⟩
  · intro t
    exact quadraticRadialFilling_normalizedArgument_of_direction
      (hproj (2 * Real.pi * (t : ℝ)))
  · change φ (2 * Real.pi * (1 : ℝ)) / (2 * Real.pi) =
      φ (2 * Real.pi * (0 : ℝ)) / (2 * Real.pi) + 1
    rw [mul_one, mul_zero, hturn, add_div, div_self Real.two_pi_pos.ne']

/-- Smooth actual incoming circle data and positive physical radial pairing
produce the actual gradient's normalized argument lift and its one-turn
endpoint equality, without supplied winding or normalized increment. -/
theorem quadraticRadialFillingGradient_exists_normalized_argument_unit_turn
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U)
    (hpos : ∀ s, 0 < quadraticRadialFillingGradientTrace F R s ⬝ᵥ
      ![Real.cos s, Real.sin s]) :
    ∃ u : C(unitInterval, ℝ),
      (∀ t : unitInterval,
        normalizedArgument
          (quadraticRadialFillingGradientComplexTrace F R (2 * Real.pi * (t : ℝ))) =
            (u t : UnitAddCircle)) ∧
      u 1 = u 0 + 1 :=
  quadraticRadialFilling_exists_normalized_argument_unit_turn
    (quadraticRadialFillingGradientDirectionLift_continuous hR hU hF hCircleU hpos)
    (quadraticRadialFillingGradientDirectionLift_projects hpos)
    (quadraticRadialFillingGradientDirectionLift_turn F R)

end
end TightVer401
