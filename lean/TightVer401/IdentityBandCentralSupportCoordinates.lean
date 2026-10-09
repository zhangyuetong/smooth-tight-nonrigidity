import TightVer401.NormalLoopCentralSupport

/-! Actual central ruled-germ pairings for the corrected-speed identity band.
The central point has height zero and need not lie in a positive-height band.
These identities do not assert a global support potential or an exit curve. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- In the actual ruled germ, arbitrary central Gauss-frame directions have
the pairing of the manuscript's support tensor [[0,a],[a,0]]. Only the actual
frame's pointwise speed/torsion identity is needed. -/
theorem identityBand_central_differential_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {a : ℝ} (ha : a ≠ 0)
    (hτ : d.τ s = -a⁻¹) (v w : Coord) :
    inner ℝ (fderiv ℝ (ruledMap d.γ d.E) (![s, 0] : Coord) (a • v))
      (fderiv ℝ d.rawGaussMap (![s, 0] : Coord) (a • w)) =
      a * (v 0 * w 1 + v 1 * w 0) := by
  have hTT := (d.orthonormal s).1
  have hEE := (d.orthonormal s).2.1
  have hTE := (d.orthonormal s).2.2.2.1
  have hET : inner ℝ (d.E s) (d.T s) = 0 := by
    rw [real_inner_comm]
    exact hTE
  rw [fderiv_two_coordinates, fderiv_two_coordinates,
    (periodicRuledFrame_ruledMap_central_partials d s).1,
    (periodicRuledFrame_ruledMap_central_partials d s).2,
    periodicRuledFrame_rawGaussMap_central_partial_s,
    periodicRuledFrame_rawGaussMap_central_partial_u]
  simp only [Pi.smul_apply, smul_eq_mul, hτ, neg_neg, smul_smul,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hTT, hEE, hTE, hET, mul_zero, mul_one, zero_add, add_zero]
  field_simp [ha] <;> ring

/-- The retained positive corrected speed gives the positive mixed entry
from actual derivatives, independently of the Gauss-image inverse. -/
theorem identityBand_central_mixed_pairing_pos {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {a : ℝ} (ha : 0 < a)
    (hτ : d.τ s = -a⁻¹) :
    inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) (![s, 0] : Coord)
        (a • (Pi.single 0 1 : Coord)))
      (fderiv ℝ d.rawGaussMap (![s, 0] : Coord)
        (a • (Pi.single 1 1 : Coord))) = a ∧ 0 < a := by
  refine ⟨?_, ha⟩
  simpa using identityBand_central_differential_pairing d s ha.ne' hτ
    (Pi.single 0 1 : Coord) (Pi.single 1 1 : Coord)

/-- A positive transverse tilt of the central tangent is a positive,
noncharacteristic tensor direction. This is a pointwise direction result;
it does not construct a closed positive exit curve. -/
theorem identityBand_central_positive_transverse_pairing {L : ℝ}
    (d : PeriodicRuledFrame L) (s : ℝ) {a t : ℝ} (ha : 0 < a)
    (hτ : d.τ s = -a⁻¹) (ht : 0 < t) :
    inner ℝ (fderiv ℝ (ruledMap d.γ d.E) (![s, 0] : Coord) (a • ![1, t]))
      (fderiv ℝ d.rawGaussMap (![s, 0] : Coord) (a • ![1, t])) = 2 * a * t ∧
      0 < inner ℝ
        (fderiv ℝ (ruledMap d.γ d.E) (![s, 0] : Coord) (a • ![1, t]))
        (fderiv ℝ d.rawGaussMap (![s, 0] : Coord) (a • ![1, t])) := by
  have heq : inner ℝ
      (fderiv ℝ (ruledMap d.γ d.E) (![s, 0] : Coord) (a • ![1, t]))
      (fderiv ℝ d.rawGaussMap (![s, 0] : Coord) (a • ![1, t])) = 2 * a * t := by
    rw [identityBand_central_differential_pairing d s ha.ne' hτ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  exact mul_pos (mul_pos (by norm_num) ha) ht

end
end TightVer401
