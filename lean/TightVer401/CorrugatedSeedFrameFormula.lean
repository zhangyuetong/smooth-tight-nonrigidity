import TightVer401.CorrugatedSeedSpatial
import TightVer401.CorrugatedSeedSphereReparam

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace

def corrugatedNormalNumerator (z v : ℂ) : Ambient :=
  WithLp.toLp 2 ![v.im, -v.re, -corrugatedSeedPlaneDet z v]
def corrugatedSeedInitialSpeed (N : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  corrugatedSeedMultiplier (corrugatedSeedRoot N) N (ψ r) *
    (planarWeight (corrugatedComplexCoord (corrugatedSeedBeta N (ψ r))))^2

theorem corrugatedComplex_comp_deriv {f : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ) (r : ℝ) :
    deriv (f ∘ ψ) r = deriv ψ r • deriv f (ψ r) :=
  ((hf (ψ r)).hasDerivAt.scomp r (hψ r).hasDerivAt).deriv

theorem corrugatedNormalNumerator_smul (a : ℝ) (z v : ℂ) :
    corrugatedNormalNumerator z (a • v) = a • corrugatedNormalNumerator z v := by
  ext i
  fin_cases i
  · simp [corrugatedNormalNumerator, Complex.real_smul, Complex.mul_im]
  · simp [corrugatedNormalNumerator, Complex.real_smul, Complex.mul_re]
  · simp [corrugatedNormalNumerator, corrugatedSeedPlaneDet, Complex.real_smul,
      Complex.mul_re, Complex.mul_im]
    ring

theorem corrugatedScaledHomogeneous_normal (a b : ℝ) (z v : ℂ) :
    -ambientCross (a • corrugatedHomogeneous z)
      (b • corrugatedHomogeneous z + a • corrugatedHorizontal v) =
      a^2 • corrugatedNormalNumerator z v := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply, corrugatedHomogeneous,
    corrugatedHorizontal, corrugatedNormalNumerator, corrugatedSeedPlaneDet] <;> ring

theorem corrugatedSeedSphere_tangent (N t : ℝ) :
    normalLoopTangent (corrugatedSeedSphere N) t =
      (corrugatedSeedSphereScale N t)^2 •
        corrugatedNormalNumerator (corrugatedSeedBeta N t) (deriv (corrugatedSeedBeta N) t) := by
  have he : corrugatedSeedSphere N =
      fun s => corrugatedSeedSphereScale N s • corrugatedHomogeneous (corrugatedSeedBeta N s) :=
    funext (corrugatedSeedSphere_eq_scaled N)
  unfold normalLoopTangent normalLoopP
  rw [he, corrugatedScaledHomogeneous_deriv
    ((corrugatedSeedSphereScale_contDiff N).differentiable (by simp))
    ((corrugatedSeedBeta_contDiff N).differentiable (by simp))]
  exact corrugatedScaledHomogeneous_normal _ _ _ _

theorem normalLoopTangent_comp {ζ : ℝ → Ambient} {ψ : ℝ → ℝ}
    (hζ : Differentiable ℝ ζ) (hψ : Differentiable ℝ ψ) (r : ℝ) :
    normalLoopTangent (ζ ∘ ψ) r = deriv ψ r • normalLoopTangent ζ (ψ r) := by
  unfold normalLoopTangent normalLoopP
  rw [sphericalCurve_comp_deriv hζ hψ]
  simp only [Function.comp_apply, normalLoopCross_smul_right, smul_neg]

theorem corrugatedSeedFrame_tangent {N : ℝ} {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (r : ℝ) :
    normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r =
      (corrugatedSeedSphereScale N (ψ r))^2 •
        corrugatedNormalNumerator (corrugatedSeedBeta N (ψ r))
          (deriv (corrugatedSeedBeta N ∘ ψ) r) := by
  rw [normalLoopTangent_comp ((corrugatedSeedSphere_contDiff N).differentiable (by simp)) hψ,
    corrugatedSeedSphere_tangent,
    corrugatedComplex_comp_deriv ((corrugatedSeedBeta_contDiff N).differentiable (by simp)) hψ,
    corrugatedNormalNumerator_smul, smul_smul, smul_smul]
  congr 1
  ring

theorem corrugatedSeedSpatial_deriv_base {N : ℝ} (hN : 1 < N) (t : ℝ) :
    deriv (corrugatedSeedSpatial N) t =
      corrugatedSeedMultiplier (corrugatedSeedRoot N) N t •
        corrugatedNormalNumerator (corrugatedSeedBeta N t) (deriv (corrugatedSeedBeta N) t) := by
  rw [(corrugatedSeedSpatial_hasDerivAt N t).deriv]
  unfold corrugatedSeedVerticalDensity
  rw [corrugatedSeedPartner_deriv hN, Complex.real_smul, corrugatedSeedPlaneDet_real_mul]
  ext i
  fin_cases i <;>
    simp [corrugatedNormalNumerator, Complex.mul_re, Complex.mul_im]

theorem corrugatedSeedSpatial_frame_deriv {N : ℝ} (hN : 1 < N) {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (r : ℝ) :
    deriv (corrugatedSeedSpatial N ∘ ψ) r =
      corrugatedSeedInitialSpeed N ψ r • normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r := by
  rw [sphericalCurve_comp_deriv ((corrugatedSeedSpatial_contDiff N).differentiable (by simp)) hψ,
    corrugatedSeedSpatial_deriv_base hN, corrugatedSeedFrame_tangent hψ,
    corrugatedComplex_comp_deriv ((corrugatedSeedBeta_contDiff N).differentiable (by simp)) hψ,
    corrugatedNormalNumerator_smul]
  simp only [smul_smul, corrugatedSeedInitialSpeed, corrugatedSeedSphereScale]
  have hw := planarWeight_pos (corrugatedComplexCoord (corrugatedSeedBeta N (ψ r)))
  congr 1
  field_simp

theorem corrugatedSeedInitialSpeed_pos (N : ℝ) (ψ : ℝ → ℝ) (r : ℝ) :
    0 < corrugatedSeedInitialSpeed N ψ r :=
  mul_pos (corrugatedSeedMultiplier_pos _ _ _) (pow_pos (planarWeight_pos _) _)

theorem corrugatedSeedInitialSpeed_contDiff (N : ℝ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (corrugatedSeedInitialSpeed N ψ) := by
  exact ((corrugatedSeedMultiplier_contDiff _ _).comp hψ).mul
    ((gnomonicWeight_contDiff.comp (corrugatedComplexCoord_contDiff.comp
      ((corrugatedSeedBeta_contDiff N).comp hψ))).pow 2)

theorem corrugatedSeedFrame_vertical_nonzero {N : ℝ} (hN : 1 < N) {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (hz : ψ 0 = 0) (hp : 0 < deriv ψ 0) :
    normalLoopTangent (corrugatedSeedSphere N ∘ ψ) 0 2 < 0 := by
  rw [normalLoopTangent_comp ((corrugatedSeedSphere_contDiff N).differentiable (by simp)) hψ,
    hz, corrugatedSeedSphere_tangent]
  change deriv ψ 0 * ((corrugatedSeedSphereScale N 0)^2 *
    -corrugatedSeedPlaneDet (corrugatedSeedBeta N 0) (deriv (corrugatedSeedBeta N) 0)) < 0
  rw [corrugatedSeedBeta_deriv (ne_of_gt (by linarith : 0 < N)), corrugatedSeedBeta_tangent_det]
  norm_num [corrugatedSeedRadius]
  have hs : 0 < (corrugatedSeedSphereScale N 0)^2 := pow_pos (corrugatedSeedSphereScale_pos N 0) 2
  nlinarith [mul_pos hp hs]

end
end TightVer401
