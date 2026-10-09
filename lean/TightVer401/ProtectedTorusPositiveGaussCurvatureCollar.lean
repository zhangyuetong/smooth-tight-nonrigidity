import TightVer401.ProtectedTorusPositiveGaussCurvatureReparam
import TightVer401.ParabolicConvexClosureBoundary

/-! Actual parabolic collar curvature at the zero transverse parameter.
The actual first form is positive there although the height derivative
vanishes. The normal is the actual axis vector, and the angular column of
the actual second fundamental form vanishes. Thus the retained Gauss
equation gives curvature zero. No seam-curvature value is an input.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def protectedTorusPositiveGaussScalarCoordinates (s : ℝ) (b : ℝ → ℝ) (q : Coord) : Coord :=
  ![s + q 0, b (q 1)]

theorem protectedTorusPositiveGaussScalarCoordinates_contDiff (s : ℝ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (protectedTorusPositiveGaussScalarCoordinates s b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : Coord => s + q 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : Coord => b (q 1))
    exact hb.comp (contDiff_apply ℝ ℝ 1)

theorem protectedTorusPositiveGaussScalarCoordinates_fderiv (s : ℝ) {b : ℝ → ℝ}
    {b' : ℝ} {q : Coord} (hb : HasDerivAt b b' (q 1)) (v : Coord) :
    fderiv ℝ (protectedTorusPositiveGaussScalarCoordinates s b) q v = ![v 0, b' * v 1] := by
  let L : Fin 2 → Coord →L[ℝ] ℝ := fun i =>
    if i = 0 then ContinuousLinearMap.proj (R := ℝ) 0
    else b' • ContinuousLinearMap.proj (R := ℝ) 1
  have hd : HasFDerivAt (protectedTorusPositiveGaussScalarCoordinates s b)
      (ContinuousLinearMap.pi L) q := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [protectedTorusPositiveGaussScalarCoordinates, L] using
        (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) q).const_add s
    · change HasFDerivAt (fun x : Coord => b (x 1))
        (b' • ContinuousLinearMap.proj (R := ℝ) 1) q
      convert! hb.comp_hasFDerivAt q
        (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) q) using 1 <;> rfl
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [L, ContinuousLinearMap.pi_apply]

theorem protectedTorusPositiveGaussScalarCoordinates_regular (s : ℝ) {b : ℝ → ℝ}
    {b' : ℝ} {q : Coord} (hb : HasDerivAt b b' (q 1)) (hb' : b' ≠ 0) :
    Function.Injective (fderiv ℝ (protectedTorusPositiveGaussScalarCoordinates s b) q) := by
  intro v w he
  rw [protectedTorusPositiveGaussScalarCoordinates_fderiv s hb,
    protectedTorusPositiveGaussScalarCoordinates_fderiv s hb] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change v 0 = w 0 at h0
  change b' * v 1 = b' * w 1 at h1
  ext i
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ hb' h1

/-- The actual polynomial collar has zero curvature at its regular boundary
circle, derived from first/second derivatives and the retained Gauss equation. -/
theorem protectedTorusPositiveGauss_collar_curvature_zero {RN mu : ℝ}
    (hRN : RN ≠ 0) (hmu : mu ≠ 0) (σ h : ℝ) {p : Coord} (hp : p 1 = 0) :
    gaussianCurvature (inducedMetric (parabolicConvexClosureCollar σ RN mu h)) p = 0 := by
  let X := parabolicConvexClosureCollar σ RN mu h
  let U : Set Coord := {q | RN + mu * q 1 ≠ 0}
  have hU : IsOpen U := by
    change IsOpen ((fun q : Coord => RN + mu * q 1) ⁻¹' ({0}ᶜ : Set ℝ))
    exact isClosed_singleton.isOpen_compl.preimage
      (continuous_const.add (continuous_const.mul (continuous_apply 1)))
  have hX : ContDiffOn ℝ ∞ X U := (parabolicConvexClosureCollar_contDiff σ RN mu h).contDiffOn
  have hpU : p ∈ U := by simpa [U, hp] using hRN
  have hi : ∀ q ∈ U, Function.Injective (fderiv ℝ X q) :=
    fun q hq => parabolicConvexClosureCollar_differential_injective hmu hq
  have hg := inducedMetric_smoothPositiveOn hX hU hi
  rcases revolution_frame (p 0) with ⟨_, _, hzz, _, hrz, haz⟩
  have hn : IsUnitNormalAt X revolutionAxis p := by
    refine ⟨hzz, fun v => ?_⟩
    rw [fderiv_two_coordinates, parabolicConvexClosureCollar_partial_theta,
      parabolicConvexClosureCollar_partial_radial]
    simp only [hp, mul_zero, zero_smul, sub_zero, add_zero, inner_add_left, inner_sub_left,
      real_inner_smul_left, haz, hrz, mul_zero, zero_add]
  have hheight : height X revolutionAxis =
      (fun q : Coord => σ * (h - mu * (q 1)^2 / 2)) := by
    funext q
    rcases revolution_frame (q 0) with ⟨_, _, hz, _, hr, _⟩
    simp only [height, X, parabolicConvexClosureCollar, inner_add_left,
      real_inner_smul_left, hr, hz, mul_zero, mul_one, zero_add]
  have hzero : coordPartial 0 (height X revolutionAxis) = (fun _ : Coord => (0 : ℝ)) := by
    funext q
    let f : ℝ → ℝ := fun t => σ * (h - mu * t^2 / 2)
    have hf : DifferentiableAt ℝ f (q 1) := by dsimp [f]; fun_prop
    have hd := hf.hasFDerivAt.comp q (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) q)
    rw [hheight]
    change fderiv ℝ (f ∘ (fun q : Coord => q 1)) q (Pi.single 0 1) = 0
    rw [hd.fderiv]
    change fderiv ℝ f (q 1) ((Pi.single 0 (1 : ℝ) : Coord) 1) = 0
    simp
  have hS (i : Fin 2) : secondFundamental X revolutionAxis p i 0 = 0 := by
    calc
      secondFundamental X revolutionAxis p i 0 =
          coordPartial i (coordPartial 0 (height X revolutionAxis)) p :=
        (second_partial_height hX hU hpU revolutionAxis i 0).symm
      _ = 0 := by rw [hzero]; simp [coordPartial]
  rw [curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hX)
    hU hpU hn]
  simp only [Matrix.det_fin_two, hS, zero_mul, mul_zero, sub_self, zero_div]

end
end TightVer401
