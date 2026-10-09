import TightVer401.FermiNormalGeometry
import TightVer401.SphereSupportTensor
import TightVer401.ScalarCoordinateCalculus

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

def fermiMetric (h : Coord → ℝ) : MetricField :=
  fun p => !![h p ^ 2, 0; 0, 1]

theorem fermiNormalMap_inducedMetric {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) :
    inducedMetric (fermiNormalMap ζ) = fermiMetric (fermiNormalScale (normalLoopCurvature ζ)) := by
  funext p
  exact fermiNormalMap_metric hζ hunit hspeed p

theorem fermiMetric_inverse {h : Coord → ℝ} {p : Coord} (hp : h p ≠ 0) :
    inverseMetric (fermiMetric h) p = !![(h p ^ 2)⁻¹, 0; 0, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiMetric, Matrix.mul_apply, Fin.sum_univ_two, hp]

theorem fermiMetric_partials {h : Coord → ℝ} {p : Coord}
    (hh : DifferentiableAt ℝ h p) (k : Fin 2) :
    coordPartial k (fun q => fermiMetric h q 0 0) p =
        2 * h p * coordPartial k h p ∧
    coordPartial k (fun q => fermiMetric h q 0 1) p = 0 ∧
    coordPartial k (fun q => fermiMetric h q 1 0) p = 0 ∧
    coordPartial k (fun q => fermiMetric h q 1 1) p = 0 := by
  constructor
  · change coordPartial k (fun q => h q ^ 2) p = _
    have he : (fun q => h q ^ 2) = (fun q => h q * h q) := by
      funext q
      ring
    rw [he, coordPartial_scalar_mul hh hh]
    ring
  · constructor
    · exact coordPartial_scalar_const 0 p k
    · constructor
      · exact coordPartial_scalar_const 0 p k
      · exact coordPartial_scalar_const 1 p k

theorem fermiMetric_christoffel {h : Coord → ℝ} {p : Coord}
    (hh : DifferentiableAt ℝ h p) (hp : h p ≠ 0) :
    christoffel (fermiMetric h) 0 0 0 p = coordPartial 0 h p / h p ∧
    christoffel (fermiMetric h) 0 0 1 p = coordPartial 1 h p / h p ∧
    christoffel (fermiMetric h) 0 1 0 p = coordPartial 1 h p / h p ∧
    christoffel (fermiMetric h) 0 1 1 p = 0 ∧
    christoffel (fermiMetric h) 1 0 0 p = -h p * coordPartial 1 h p ∧
    christoffel (fermiMetric h) 1 0 1 p = 0 ∧
    christoffel (fermiMetric h) 1 1 0 p = 0 ∧
    christoffel (fermiMetric h) 1 1 1 p = 0 := by
  have h0 := fermiMetric_partials hh (0 : Fin 2)
  have h1 := fermiMetric_partials hh (1 : Fin 2)
  simp only [christoffel, fermiMetric_inverse hp, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    h0.1, h0.2.1, h0.2.2.1, h0.2.2.2,
    h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
  repeat' constructor
  all_goals field_simp [hp]
  all_goals ring

theorem fermiMetric_support_entries {h H : Coord → ℝ} {p : Coord}
    (hh : DifferentiableAt ℝ h p) (hp : h p ≠ 0) :
    sphereSupportTensor (fermiMetric h) H p 0 0 =
      coordPartial 0 (coordPartial 0 H) p - coordPartial 0 h p / h p * coordPartial 0 H p +
        h p * coordPartial 1 h p * coordPartial 1 H p + H p * h p ^ 2 ∧
    sphereSupportTensor (fermiMetric h) H p 0 1 =
      coordPartial 0 (coordPartial 1 H) p - coordPartial 1 h p / h p * coordPartial 0 H p ∧
    sphereSupportTensor (fermiMetric h) H p 1 1 =
      coordPartial 1 (coordPartial 1 H) p + H p := by
  have hc := fermiMetric_christoffel hh hp
  simp only [sphereSupportTensor, covHessian, Fin.sum_univ_two,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, fermiMetric,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    zero_mul, add_zero, zero_add, mul_zero, mul_one]
  constructor
  · ring
  · simp

end
end TightVer401
