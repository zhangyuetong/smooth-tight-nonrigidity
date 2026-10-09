import TightVer401.SphereSupportDifferential

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

def sphereSupportTensor (g : MetricField) (H : Coord → ℝ) : MetricField :=
  fun p => covHessian g H p + H p • g p

def sphereTangentLift (g : MetricField) (Q : Coord → Ambient) (p : Coord) (a : Coord) : Ambient :=
  ∑ i, ((g p)⁻¹ *ᵥ a) i • coordPartial i Q p

theorem sphereTangentLift_pairing {g : MetricField} {Q : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U) {p : Coord} (hp : p ∈ U)
    (a : Coord) (j : Fin 2) :
    inner ℝ (sphereTangentLift g Q p a) (coordPartial j Q p) = a j := by
  have hind (i j : Fin 2) : inner ℝ (coordPartial i Q p) (coordPartial j Q p) = g p i j :=
    congrFun (congrFun (inducedMetric_eq_of_isometric hQ hp) i) j
  have he : g p *ᵥ ((g p)⁻¹ *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit), Matrix.one_mulVec]
  have hj := congrFun he j
  simp only [sphereTangentLift, sum_inner, real_inner_smul_left, hind, metric_coeff_symm hg hp]
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using hj

theorem sphereTangentLift_normal_pairing {g : MetricField} {Q : Coord → Ambient} {U : Set Coord}
    (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (a : Coord) :
    inner ℝ (sphereTangentLift g Q p a) (Q p) = 0 := by
  have horth (i : Fin 2) : inner ℝ (coordPartial i Q p) (Q p) = 0 :=
    sphere_differential_orthogonal hQ hU hp hunit _
  simp only [sphereTangentLift, sum_inner, real_inner_smul_left, horth, mul_zero, Finset.sum_const_zero]

theorem sphereSupportMap_differential {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (i : Fin 2) :
    coordPartial i (sphereSupportMap g Q H) p =
      sphereTangentLift g Q p (sphereSupportTensor g H p i) := by
  let a := coordPartial i (sphereSupportMap g Q H) p
  let b := sphereTangentLift g Q p (sphereSupportTensor g H p i)
  have hwt (j : Fin 2) : inner ℝ (coordPartial j Q p) (a - b) = 0 := by
    rw [real_inner_comm, inner_sub_left]
    have ha := (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit i j).2
    have hb := sphereTangentLift_pairing hg hQ hp (sphereSupportTensor g H p i) j
    change inner ℝ a (coordPartial j Q p) = sphereSupportTensor g H p i j at ha
    rw [ha, hb]
    exact sub_self _
  have hn : inner ℝ (Q p) (a - b) = 0 := by
    rw [real_inner_comm, inner_sub_left,
      (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit i i).1,
      sphereTangentLift_normal_pairing hQ.1 hU hp hunit]
    exact sub_self _
  have heq := normal_eq_inner_smul_of_independent_tangents
    (fun j => coordPartial j Q p) (isometric_tangents_independent hg hQ hp) (Q p) (a - b)
    (hunit p hp) (fun j => sphere_differential_orthogonal hQ.1 hU hp hunit _) hwt
  rw [hn, zero_smul] at heq
  exact sub_eq_zero.mp heq

end
end TightVer401
