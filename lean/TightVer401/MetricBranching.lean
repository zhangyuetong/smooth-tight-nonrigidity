import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric
import Mathlib.Tactic.Ring

/-! The exact metric identities in ver401, using the OpenAI surface definitions.
The derivatives in these statements are actual Fréchet derivatives.
-/
namespace TightVer401

noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
open scoped BigOperators

def strain (X y : Coord → Ambient) (p : Coord) (i j : Fin 2) : ℝ :=
  inner ℝ (coordPartial i X p) (coordPartial j y p) +
  inner ℝ (coordPartial i y p) (coordPartial j X p)

def IsInfinitesimalBendingOn (X y : Coord → Ambient) (U : Set Coord) : Prop :=
  ContDiffOn ℝ ∞ y U ∧ ∀ p ∈ U, ∀ i j, strain X y p i j = 0

theorem metric_quadratic {X y : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) (hy : DifferentiableAt ℝ y p) (i j : Fin 2) :
    inducedMetric (fun q => X q + y q) p i j =
      inducedMetric X p i j + strain X y p i j + inducedMetric y p i j := by
  simp only [inducedMetric, strain, coordPartial, fderiv_fun_add hX hy,
    add_apply, inner_add_left, inner_add_right]
  ring

theorem metric_sub_quadratic {X y : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) (hy : DifferentiableAt ℝ y p) (i j : Fin 2) :
    inducedMetric (fun q => X q - y q) p i j =
      inducedMetric X p i j - strain X y p i j + inducedMetric y p i j := by
  simp only [inducedMetric, strain, coordPartial, fderiv_fun_sub hX hy,
    sub_apply, inner_sub_left, inner_sub_right]
  ring

theorem exact_sign_pair {X y : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hy : IsInfinitesimalBendingOn X y U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    inducedMetric (fun q => X q + y q) p = inducedMetric (fun q => X q - y q) p := by
  have hdX := ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdy := ((hy.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  ext i j
  rw [metric_quadratic hdX hdy, metric_sub_quadratic hdX hdy, hy.2 p hp]
  simp

theorem metric_pair_common {X y : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hy : IsInfinitesimalBendingOn X y U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    inducedMetric (fun q => X q + y q) p = inducedMetric X p + inducedMetric y p := by
  have hdX := ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdy := ((hy.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  ext i j
  rw [metric_quadratic hdX hdy, hy.2 p hp]
  simp

theorem mixed_derivatives_zero_of_disjoint_supports
    {y z : Coord → Ambient} (h : Disjoint (tsupport y) (tsupport z))
    (p : Coord) (i j : Fin 2) :
    inner ℝ (coordPartial i y p) (coordPartial j z p) = 0 := by
  by_cases hp : p ∈ tsupport y
  · have hz : p ∉ tsupport z := fun hz => Set.disjoint_left.mp h hp hz
    simp [coordPartial, fderiv_of_notMem_tsupport ℝ hz]
  · simp [coordPartial, fderiv_of_notMem_tsupport ℝ hp]

theorem coordPartial_finite_linear {m : ℕ} {Y : Fin m → Coord → Ambient}
    {p : Coord} (hY : ∀ k, DifferentiableAt ℝ (Y k) p)
    (c : Fin m → ℝ) (i : Fin 2) :
    coordPartial i (fun q => ∑ k, c k • Y k q) p =
      ∑ k, c k • coordPartial i (Y k) p := by
  have hs (k) : DifferentiableAt ℝ (fun q => c k • Y k q) p := by
    exact (hY k).fun_const_smul (c k)
  unfold coordPartial
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun k q => c k • Y k q) (fun k _ => hs k)]
  simp only [sum_apply, fderiv_fun_const_smul (hY _) _, smul_apply]

theorem finite_quadratic_diagonal {m : ℕ} {Y : Fin m → Coord → Ambient}
    {p : Coord} (hY : ∀ k, DifferentiableAt ℝ (Y k) p)
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (c : Fin m → ℝ) (i j : Fin 2) :
    inducedMetric (fun q => ∑ k, c k • Y k q) p i j =
      ∑ k, (c k)^2 * inducedMetric (Y k) p i j := by
  classical
  simp only [inducedMetric, coordPartial_finite_linear hY, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single k]
  · ring
  · intro l _ hl
    rw [mixed_derivatives_zero_of_disjoint_supports (hdisj l k hl)]
    ring
  · simp

theorem strain_finite_linear {m : ℕ} {X : Coord → Ambient}
    {Y : Fin m → Coord → Ambient} {p : Coord}
    (hY : ∀ k, DifferentiableAt ℝ (Y k) p)
    (c : Fin m → ℝ) (i j : Fin 2) :
    strain X (fun q => ∑ k, c k • Y k q) p i j =
      ∑ k, c k * strain X (Y k) p i j := by
  simp only [strain, coordPartial_finite_linear hY, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/- This proves the finite formula of thm:branch. The infinite-series passage,
embedding, tightness and noncongruence are separate targets. -/
theorem finite_sign_metric {m : ℕ} {X : Coord → Ambient}
    {Y : Fin m → Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U)
    (hY : ∀ k, IsInfinitesimalBendingOn X (Y k) U)
    (hdisj : ∀ k l, k ≠ l → Disjoint (tsupport (Y k)) (tsupport (Y l)))
    (hU : IsOpen U) (a ε : Fin m → ℝ) (hε : ∀ k, (ε k)^2 = 1)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    inducedMetric (fun q => X q + ∑ k, (ε k * a k) • Y k q) p i j =
      inducedMetric X p i j + ∑ k, (a k)^2 * inducedMetric (Y k) p i j := by
  have hdX := ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdY (k) : DifferentiableAt ℝ (Y k) p :=
    (((hY k).1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdSum : DifferentiableAt ℝ (fun q => ∑ k, (ε k * a k) • Y k q) p := by
    apply DifferentiableAt.fun_sum
    intro k _
    exact (hdY k).fun_const_smul (ε k * a k)
  rw [metric_quadratic hdX hdSum, strain_finite_linear hdY,
    finite_quadratic_diagonal hdY hdisj]
  simp only [(hY _).2 p hp, mul_zero, Finset.sum_const_zero, add_zero,
    mul_pow, hε, one_mul]

end
end TightVer401
