import TightVer401.AngularDescentCharts
import TightVer401.PeriodicComplexJordan
import TightVer401.SeamTubeBoundary
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Actual round-circle geometry for the relative saddle smoothing application.
The positive normal coordinate of this counterclockwise circle points inward. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual once-traversed standard circle, with real angle parameter. -/
def quadraticRadialFillingCircle (R : ℝ) : ℝ → ℂ := circleMap 0 R

theorem quadraticRadialFillingCircle_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (quadraticRadialFillingCircle R) := contDiff_circleMap 0 R

theorem quadraticRadialFillingCircle_periodic (R : ℝ) :
    Function.Periodic (quadraticRadialFillingCircle R) (2 * Real.pi) :=
  periodic_circleMap 0 R

theorem quadraticRadialFillingCircle_deriv (R s : ℝ) :
    deriv (quadraticRadialFillingCircle R) s = quadraticRadialFillingCircle R s * Complex.I :=
  (hasDerivAt_circleMap 0 R s).deriv

theorem quadraticRadialFillingCircle_regular {R : ℝ} (hR : 0 < R) (s : ℝ) :
    deriv (quadraticRadialFillingCircle R) s ≠ 0 := by
  rw [quadraticRadialFillingCircle_deriv]
  exact mul_ne_zero (circleMap_ne_center hR.ne') Complex.I_ne_zero

theorem quadraticRadialFillingCircle_injOn {R : ℝ} (hR : 0 < R) :
    InjOn (quadraticRadialFillingCircle R) (Ico 0 (2 * Real.pi)) :=
  injOn_circleMap_of_abs_sub_le' hR.ne' (by simp)

theorem quadraticRadialFillingCircle_lift_injective {R : ℝ} (hR : 0 < R) :
    Function.Injective (quadraticRadialFillingCircle_periodic R).lift := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  exact periodicComplexCurve_lift_injective (quadraticRadialFillingCircle_periodic R)
    (quadraticRadialFillingCircle_injOn hR)

theorem quadraticRadialFillingCircle_coord (R s : ℝ) :
    seamComplexCoord (quadraticRadialFillingCircle R s) = saddlePolarChart ![R,s] := by
  rw [seamComplexCoord_apply]
  ext i
  fin_cases i <;>
    simp [quadraticRadialFillingCircle, saddlePolarChart, circleMap_zero_re, circleMap_zero_im]

theorem quadraticRadialFillingComplex_coord (z : ℂ) :
    angularDescentComplex (seamComplexCoord z) = z := by
  apply Complex.ext <;> simp [angularDescentComplex, seamComplexCoord_apply]

theorem quadraticRadialFillingCoord_complex (x : Coord) :
    seamComplexCoord (angularDescentComplex x) = x := by
  rw [seamComplexCoord_apply]
  ext i
  fin_cases i <;> simp [angularDescentComplex]

theorem quadraticRadialFillingRadius_complex (z : ℂ) :
    planarRadius (seamComplexCoord z) = ‖z‖ := by
  rw [← angularDescentComplex_norm, quadraticRadialFillingComplex_coord]

theorem quadraticRadialFillingRadius_continuous : Continuous planarRadius := by
  simpa only [angularDescentComplex_norm] using angularDescentComplex_contDiff.continuous.norm

/-- The actual quotient-circle seam is exactly the Cartesian radius-R circle. -/
theorem quadraticRadialFillingCircle_seam {R : ℝ} (hR : 0 < R) :
    seamNormalSeam (quadraticRadialFillingCircle R) (quadraticRadialFillingCircle_periodic R) =
      {x : Coord | planarRadius x = R} := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
    change planarRadius (seamNormalNative (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) (periodProjection (2 * Real.pi) s,0)) = R
    rw [seamNormalNative_coe, seamNormalCoordinates_central,
      quadraticRadialFillingRadius_complex]
    simp [quadraticRadialFillingCircle, norm_circleMap_zero, abs_of_pos hR]
  · intro hx
    change planarRadius x = R at hx
    have hz : angularDescentComplex x ∈ Set.range (circleMap 0 R) := by
      rw [range_circleMap]
      simpa only [Metric.mem_sphere, dist_zero_right, angularDescentComplex_norm,
        abs_of_pos hR] using hx
    obtain ⟨s,hs⟩ := hz
    refine ⟨periodProjection (2 * Real.pi) s, ?_⟩
    change seamNormalNative (quadraticRadialFillingCircle R)
      (quadraticRadialFillingCircle_periodic R) (periodProjection (2 * Real.pi) s,0) = x
    rw [seamNormalNative_coe, seamNormalCoordinates_central]
    change seamComplexCoord (circleMap 0 R s) = x
    rw [hs, quadraticRadialFillingCoord_complex]

/-- No additional boundary is introduced by choosing the radial inner side. -/
theorem quadraticRadialFillingCircle_frontier {R : ℝ} (hR : 0 < R) :
    frontier {x : Coord | planarRadius x < R} ⊆
      seamNormalSeam (quadraticRadialFillingCircle R) (quadraticRadialFillingCircle_periodic R) := by
  rw [quadraticRadialFillingCircle_seam hR]
  exact frontier_lt_subset_eq quadraticRadialFillingRadius_continuous continuous_const

/-- The unnormalized left-normal coordinate is inward for the standard circle. -/
theorem quadraticRadialFillingCircle_normal (R s t : ℝ) :
    seamNormalCoordinates (quadraticRadialFillingCircle R) ![s,t] =
      saddlePolarChart ![R * (1-t),s] := by
  change seamComplexCoord (quadraticRadialFillingCircle R s +
    t • (Complex.I * deriv (quadraticRadialFillingCircle R) s)) = _
  rw [quadraticRadialFillingCircle_deriv]
  have hn : Complex.I * (quadraticRadialFillingCircle R s * Complex.I) =
      -quadraticRadialFillingCircle R s := by
    calc
      _ = quadraticRadialFillingCircle R s * (Complex.I * Complex.I) := by ring
      _ = _ := by simp
  have he : quadraticRadialFillingCircle R s + t • (-quadraticRadialFillingCircle R s) =
      (1-t) • quadraticRadialFillingCircle R s := by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hn, he, map_smul, quadraticRadialFillingCircle_coord]
  ext i
  fin_cases i <;> simp [saddlePolarChart] <;> ring

/-- The absolute-value ambiguity in radius disappears on a genuine narrow collar. -/
theorem quadraticRadialFillingCircle_normal_radius {R : ℝ} (hR : 0 < R)
    (s t : ℝ) (ht : |t| < (1:ℝ)/2) :
    planarRadius (seamNormalCoordinates (quadraticRadialFillingCircle R) ![s,t]) = R * (1-t) := by
  rw [quadraticRadialFillingCircle_normal]
  apply angularDescent_radius_polar
  have ht' := (abs_lt.mp ht).2
  change 0 < R * (1-t)
  exact mul_pos hR (by linarith)

/-- Positive normal coordinate is exactly the filler side. -/
theorem quadraticRadialFillingCircle_normal_side {R : ℝ} (hR : 0 < R)
    (s t : ℝ) (ht : |t| < (1:ℝ)/2) :
    seamNormalCoordinates (quadraticRadialFillingCircle R) ![s,t] ∈
      {x : Coord | planarRadius x < R} ↔ 0 < t := by
  change planarRadius (seamNormalCoordinates (quadraticRadialFillingCircle R) ![s,t]) < R ↔ 0 < t
  rw [quadraticRadialFillingCircle_normal_radius hR s t ht]
  constructor <;> intro h <;> nlinarith

end
end TightVer401
