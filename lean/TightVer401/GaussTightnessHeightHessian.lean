import TightVer401.HeightTightnessSecondDerivative
import TightVer401.SurfaceMetric

/-! The actual height second fundamental form at a local maximum is
negative semidefinite. Smoothness is required only on the SAME open chart
domain, so this leaf applies directly to native torus chart representatives.
Final consumer: `classicalPositiveGaussTightness_proved`. -/

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem heightHessian_scalar_fderiv_two (H : Coord → ℝ) (p v : Coord) :
    fderiv ℝ H p v = v 0 * coordPartial 0 H p + v 1 * coordPartial 1 H p := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  calc
    fderiv ℝ H p v = fderiv ℝ H p
        (v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord)) := congrArg _ hv
    _ = _ := by simp [coordPartial]

private theorem heightHessian_affine_hasDeriv (p v : Coord) (t : ℝ) :
    HasDerivAt (fun s : ℝ => p + s • v) v t := by
  have hd : HasDerivAt ((fun _ : ℝ => p) + fun s : ℝ => s • v)
      ((0 : Coord) + (1 : ℝ) • v) t :=
    (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const v)
  change HasDerivAt ((fun _ : ℝ => p) + fun s : ℝ => s • v) v t
  simpa only [zero_add, one_smul] using hd

/-- The actual second derivative of an affine slice is the coordinate
Hessian quadratic form, with only local smoothness near the slice center. -/
theorem gaussTightness_slice_secondDeriv
    {H : Coord → ℝ} {U : Set Coord} (hH : ContDiffOn ℝ ∞ H U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (v : Coord) :
    deriv (deriv (fun t : ℝ => H (p + t • v))) 0 =
      v ⬝ᵥ (((fun i j : Fin 2 => coordPartial i (coordPartial j H) p) :
        Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v) := by
  let φ : ℝ → Coord := fun t => p + t • v
  have hφ (t : ℝ) : HasDerivAt φ v t := heightHessian_affine_hasDeriv p v t
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ U :=
    (hφ 0).continuousAt (by simpa [φ] using hU.mem_nhds hp)
  have hfirst : deriv (fun t => H (φ t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => v 0 * coordPartial 0 H (φ t) + v 1 * coordPartial 1 H (φ t)) := by
    filter_upwards [hmem] with t ht
    have hdH : DifferentiableAt ℝ H (φ t) :=
      ((hH (φ t) ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
    have hs : HasDerivAt (fun s => H (φ s)) (fderiv ℝ H (φ t) v) t := by
      simpa only [Function.comp_def] using hdH.hasFDerivAt.comp_hasDerivAt t (hφ t)
    rw [hs.deriv, heightHessian_scalar_fderiv_two]
  have hpart (j : Fin 2) : HasDerivAt (fun t => coordPartial j H (φ t))
      (fderiv ℝ (coordPartial j H) p v) 0 := by
    have hd : DifferentiableAt ℝ (coordPartial j H) p :=
      (((partial_contDiffOn hH hU j) p hp).contDiffAt
        (hU.mem_nhds hp)).differentiableAt (by simp)
    have hdφ : HasFDerivAt (coordPartial j H) (fderiv ℝ (coordPartial j H) p) (φ 0) := by
      simpa [φ] using hd.hasFDerivAt
    simpa only [Function.comp_def] using hdφ.comp_hasDerivAt 0 (hφ 0)
  have hsum : HasDerivAt
      (fun t => v 0 * coordPartial 0 H (φ t) + v 1 * coordPartial 1 H (φ t))
      (v 0 * fderiv ℝ (coordPartial 0 H) p v +
        v 1 * fderiv ℝ (coordPartial 1 H) p v) 0 := by
    convert! ((hpart 0).const_mul (v 0)).add ((hpart 1).const_mul (v 1)) using 1 <;> rfl
  change deriv (deriv (fun t => H (φ t))) 0 = _
  rw [hfirst.deriv_eq, hsum.deriv,
    heightHessian_scalar_fderiv_two, heightHessian_scalar_fderiv_two]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Every affine height slice through an actual coordinate local maximum
has nonpositive second derivative; this is exactly the second-form quadratic
expression for the SAME surface and height direction. -/
theorem gaussTightness_localMax_height_secondForm_nonpos
    {F : Coord → Ambient} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (w : Ambient)
    (hmax : IsLocalMax (height F w) p) (v : Coord) :
    v ⬝ᵥ (secondFundamental F w p *ᵥ v) ≤ 0 := by
  have hh : ContDiffOn ℝ ∞ (height F w) U := height_smooth hF w
  have hφ : HasDerivAt (fun t : ℝ => p + t • v) v 0 :=
    heightHessian_affine_hasDeriv p v 0
  have hmaxφ : IsLocalMax (fun t : ℝ => height F w (p + t • v)) 0 := by
    have hm : IsLocalMax (height F w) (p + (0 : ℝ) • v) := by simpa using hmax
    simpa only [Function.comp_def] using
      hm.comp_continuous (g := fun t : ℝ => p + t • v) (b := 0) hφ.continuousAt
  have hc : ContinuousAt (fun t : ℝ => height F w (p + t • v)) 0 := by
    have hcH : ContinuousAt (height F w) p :=
      ((hh p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
    have hcHφ : ContinuousAt (height F w) (p + (0 : ℝ) • v) := by simpa using hcH
    exact hcHφ.comp (f := fun t : ℝ => p + t • v) (x := 0) hφ.continuousAt
  have hle := localMax_secondDeriv_nonpos hmaxφ hc
  rw [gaussTightness_slice_secondDeriv hh hU hp v] at hle
  have hmatrix : ((fun i j : Fin 2 => coordPartial i (coordPartial j (height F w)) p) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      secondFundamental F w p := by
    ext i j
    exact second_partial_height hF hU hp w i j
  rwa [hmatrix] at hle

end
end TightVer401
