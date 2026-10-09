import TightVer401.QuadraticRadialFillingBoundary
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform actual radial neighborhoods of the incoming boundary circle. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry
open scoped Topology

theorem quadraticRadialFilling_radius_smul (a : ℝ) (x : Coord) :
    planarRadius (a • x) = |a| * planarRadius x := by
  unfold planarRadius
  simp only [Pi.smul_apply, smul_eq_mul]
  have hs : (a * x 0) ^ 2 + (a * x 1) ^ 2 =
      a ^ 2 * (x 0 ^ 2 + x 1 ^ 2) := by ring
  rw [hs, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

def quadraticRadialFillingProjectToRadius (R : ℝ) (x : Coord) : Coord :=
  (R / planarRadius x) • x

theorem quadraticRadialFilling_projectToRadius_mem {R : ℝ} (hR : 0 < R)
    {x : Coord} (hx : 0 < planarRadius x) :
    quadraticRadialFillingProjectToRadius R x ∈ quadraticRadialFillingRadiusLevel R := by
  change planarRadius ((R / planarRadius x) • x) = R
  rw [quadraticRadialFilling_radius_smul, abs_of_pos (div_pos hR hx)]
  exact div_mul_cancel₀ R hx.ne'

/-- Radial projection moves a point by at most its physical radial error in
the actual coordinate metric; no equality of coordinate and L2 norms is used. -/
theorem quadraticRadialFilling_dist_projectToRadius_le (R : ℝ)
    {x : Coord} (hx : 0 < planarRadius x) :
    dist x (quadraticRadialFillingProjectToRadius R x) ≤ |planarRadius x - R| := by
  apply (dist_pi_le_iff (abs_nonneg (planarRadius x - R))).mpr
  intro i
  change dist (x i) ((R / planarRadius x) * x i) ≤ _
  rw [Real.dist_eq]
  calc
    |x i - R / planarRadius x * x i| =
        |1 - R / planarRadius x| * |x i| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |1 - R / planarRadius x| * planarRadius x :=
      mul_le_mul_of_nonneg_left
        (quadraticRadialFilling_abs_coord_le_radius x i) (abs_nonneg _)
    _ = |(1 - R / planarRadius x) * planarRadius x| := by
      rw [abs_mul, abs_of_pos hx]
    _ = |planarRadius x - R| := by
      congr 1
      field_simp [hx.ne']

/-- Every open neighborhood of the actual positive radius circle contains a
uniform radial collar, derived from compactness rather than supplied as data. -/
theorem quadraticRadialFilling_exists_radial_collar
    {R : ℝ} (hR : 0 < R) {U : Set Coord} (hU : IsOpen U)
    (hCircleU : quadraticRadialFillingRadiusLevel R ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∀ x : Coord, |planarRadius x - R| < δ → x ∈ U := by
  obtain ⟨d, hd, hthick⟩ :=
    (quadraticRadialFilling_radiusLevel_isCompact R).exists_thickening_subset_open hU hCircleU
  let δ := min d (R / 2)
  have hδ : 0 < δ := lt_min hd (half_pos hR)
  have hδR : δ < R := (min_le_right d (R / 2)).trans_lt (half_lt_self hR)
  refine ⟨δ, hδ, hδR, ?_⟩
  intro x hx
  have hrad : 0 < planarRadius x := by
    have hh := (abs_lt.mp hx).1
    linarith
  apply hthick
  apply mem_thickening_iff.mpr
  refine ⟨quadraticRadialFillingProjectToRadius R x,
    quadraticRadialFilling_projectToRadius_mem hR hrad, ?_⟩
  exact (quadraticRadialFilling_dist_projectToRadius_le R hrad).trans_lt
    (hx.trans_le (min_le_left d (R / 2)))

end
end TightVer401
