import TightVer401.QuadraticRadialFillingGradientJordan
import TightVer401.ComplexCircleDirection

/-! Positive radial pairing gives an actual direction lift of the gradient
circle with increase exactly two pi. Its genuine Jordan filling contains zero. -/
namespace TightVer401
noncomputable section
open Set Function ComplexConjugate OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Rotate the actual gradient into the outward radial frame. -/
def quadraticRadialFillingGradientRotatedTrace (F : Coord → ℝ) (R s : ℝ) : ℂ :=
  quadraticRadialFillingGradientComplexTrace F R s *
    conj (circleMap 0 1 s)

/-- An explicit real direction lift, rather than an assumed winding value. -/
def quadraticRadialFillingGradientDirectionLift (F : Coord → ℝ) (R s : ℝ) : ℝ :=
  s + Complex.arg (quadraticRadialFillingGradientRotatedTrace F R s)

theorem quadraticRadialFillingGradientRotatedTrace_re (F : Coord → ℝ) (R s : ℝ) :
    (quadraticRadialFillingGradientRotatedTrace F R s).re =
      quadraticRadialFillingGradientTrace F R s ⬝ᵥ ![Real.cos s,Real.sin s] := by
  simp [quadraticRadialFillingGradientRotatedTrace,
    quadraticRadialFillingGradientComplexTrace, angularDescentComplex,
    Complex.mul_re, circleMap_zero_re, circleMap_zero_im, dotProduct, Fin.sum_univ_two]

theorem quadraticRadialFillingGradientRotatedTrace_periodic (F : Coord → ℝ) (R : ℝ) :
    Function.Periodic (quadraticRadialFillingGradientRotatedTrace F R) (2 * Real.pi) := by
  intro s
  unfold quadraticRadialFillingGradientRotatedTrace
  rw [quadraticRadialFillingGradientComplexTrace_periodic F R s,
    periodic_circleMap 0 1 s]

theorem quadraticRadialFillingGradientComplexTrace_ne_zero
    {F : Coord → ℝ} {R : ℝ}
    (hpos : ∀ s, 0 < quadraticRadialFillingGradientTrace F R s ⬝ᵥ
      ![Real.cos s,Real.sin s]) (s : ℝ) :
    quadraticRadialFillingGradientComplexTrace F R s ≠ 0 := by
  intro hz
  have hp := hpos s
  rw [← quadraticRadialFillingGradientRotatedTrace_re] at hp
  simp [quadraticRadialFillingGradientRotatedTrace, hz] at hp

/-- Actual positive radial pairing places the rotated gradient in a domain
with a continuous ordinary argument. -/
theorem quadraticRadialFillingGradientDirectionLift_continuous
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U)
    (hpos : ∀ s, 0 < quadraticRadialFillingGradientTrace F R s ⬝ᵥ
      ![Real.cos s,Real.sin s]) :
    Continuous (quadraticRadialFillingGradientDirectionLift F R) := by
  have hq : Continuous (quadraticRadialFillingGradientRotatedTrace F R) :=
    (quadraticRadialFillingGradientComplexTrace_contDiff hR hU hF hCircleU).continuous.mul
      (Complex.continuous_conj.comp (quadraticRadialFillingCircle_contDiff 1).continuous)
  apply continuous_id.add
  apply continuous_iff_continuousAt.mpr
  intro s
  have hs : quadraticRadialFillingGradientRotatedTrace F R s ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr
      (Or.inl (by rw [quadraticRadialFillingGradientRotatedTrace_re]; exact hpos s))
  exact (Complex.continuousAt_arg hs).comp hq.continuousAt

/-- The lifted direction comes from the actual normalized complex gradient. -/
theorem quadraticRadialFillingGradientDirectionLift_projects
    {F : Coord → ℝ} {R : ℝ}
    (hpos : ∀ s, 0 < quadraticRadialFillingGradientTrace F R s ⬝ᵥ
      ![Real.cos s,Real.sin s]) (s : ℝ) :
    complexCircleDirection (quadraticRadialFillingGradientComplexTrace F R s) =
      Circle.exp (quadraticRadialFillingGradientDirectionLift F R s) := by
  let z := quadraticRadialFillingGradientComplexTrace F R s
  let q := quadraticRadialFillingGradientRotatedTrace F R s
  have hzne : z ≠ 0 := quadraticRadialFillingGradientComplexTrace_ne_zero hpos s
  have hqne : q ≠ 0 := by
    have hp : 0 < q.re := by
      dsimp [q]
      rw [quadraticRadialFillingGradientRotatedTrace_re]
      exact hpos s
    intro he
    simpa [he] using hp
  have hn : ‖q‖ = ‖z‖ := by
    simp [q, z, quadraticRadialFillingGradientRotatedTrace, norm_mul]
  have hr : q * circleMap 0 1 s = z := by
    have he : conj (circleMap 0 1 s) * circleMap 0 1 s = 1 := by
      rw [conj_circleMap_zero, circleMap_zero_mul]
      simp [circleMap]
    dsimp [q, quadraticRadialFillingGradientRotatedTrace]
    rw [mul_assoc, he, mul_one]
  have hqe : Complex.exp ((Complex.arg q : ℂ) * Complex.I) = ‖q‖⁻¹ • q :=
    (complexCircleDirection_coe q).symm.trans (complexCircleDirection_normalized hqne)
  apply complexCircleDirection_eq_of_exp hzne
  change Complex.exp (((s + Complex.arg q : ℝ) : ℂ) * Complex.I) = ‖z‖⁻¹ • z
  calc
    _ = circleMap 0 1 s * Complex.exp ((Complex.arg q : ℂ) * Complex.I) := by
      simp only [Complex.ofReal_add, add_mul, Complex.exp_add, circleMap_zero,
        Complex.ofReal_one, one_mul]
    _ = ‖q‖⁻¹ • (q * circleMap 0 1 s) := by
      rw [hqe, Complex.real_smul, Complex.real_smul]
      ring
    _ = ‖z‖⁻¹ • z := by rw [hr, hn]

theorem quadraticRadialFillingGradientDirectionLift_turn (F : Coord → ℝ) (R : ℝ) :
    quadraticRadialFillingGradientDirectionLift F R (2 * Real.pi) =
      quadraticRadialFillingGradientDirectionLift F R 0 + 2 * Real.pi := by
  have hp := quadraticRadialFillingGradientRotatedTrace_periodic F R 0
  simp only [zero_add] at hp
  unfold quadraticRadialFillingGradientDirectionLift
  rw [hp]
  ring

/-- Positive radial derivative forces the origin into the genuine Jordan
filling of the actual gradient boundary. No degree or winding premise is used. -/
theorem quadraticRadialFillingGradient_origin_inside
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord} {H : ℂ ≃ₜ ℂ}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U)
    (hpos : ∀ s, 0 < quadraticRadialFillingGradientTrace F R s ⬝ᵥ
      ![Real.cos s,Real.sin s])
    (hboundary : range (quadraticRadialFillingGradientComplexTrace F R) =
      H '' Metric.sphere (0 : ℂ) 1) :
    (0 : ℂ) ∈ H '' Metric.ball (0 : ℂ) 1 := by
  apply winding_origin_inside complexCircleDirection_continuousOn
    (quadraticRadialFillingGradientComplexTrace_contDiff hR hU hF hCircleU).continuous
    (quadraticRadialFillingGradientDirectionLift_continuous hR hU hF hCircleU hpos)
    hboundary (quadraticRadialFillingGradientComplexTrace_ne_zero hpos)
    (by simpa only [zero_add] using
      quadraticRadialFillingGradientComplexTrace_periodic F R 0)
    (quadraticRadialFillingGradientDirectionLift_projects hpos)
  rw [quadraticRadialFillingGradientDirectionLift_turn]
  exact ne_of_gt (lt_add_of_pos_right _ Real.two_pi_pos)

end
end TightVer401

