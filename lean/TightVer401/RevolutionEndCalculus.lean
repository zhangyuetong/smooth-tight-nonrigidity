import TightVer401.ScalarCoordinateCalculus
import TightVer401.SurfaceMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def revolutionRadial (θ : ℝ) : Ambient := WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0]
def revolutionAngular (θ : ℝ) : Ambient := WithLp.toLp 2 ![-Real.sin θ, Real.cos θ, 0]
def revolutionAxis : Ambient := WithLp.toLp 2 ![0, 0, 1]
def revolutionEnd (q : ℝ → ℝ) (p : Coord) : Ambient :=
  q (p 1) • revolutionRadial (p 0) + p 1 • revolutionAxis

theorem revolutionRadial_hasDerivAt (θ : ℝ) : HasDerivAt revolutionRadial (revolutionAngular θ) θ := by
  let Φ : ℝ → Fin 3 → ℝ := fun t => ![Real.cos t, Real.sin t, 0]
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hΦ : HasDerivAt Φ ![-Real.sin θ, Real.cos θ, 0] θ := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact Real.hasDerivAt_cos θ
    · exact Real.hasDerivAt_sin θ
    · exact hasDerivAt_const θ 0
  exact E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ hΦ

theorem revolutionAngular_hasDerivAt (θ : ℝ) : HasDerivAt revolutionAngular (-revolutionRadial θ) θ := by
  let Φ : ℝ → Fin 3 → ℝ := fun t => ![-Real.sin t, Real.cos t, 0]
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hΦ : HasDerivAt Φ ![-Real.cos θ, -Real.sin θ, 0] θ := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact (Real.hasDerivAt_sin θ).neg
    · exact Real.hasDerivAt_cos θ
    · exact hasDerivAt_const θ 0
  convert! E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ hΦ using 1
  ext j
  fin_cases j <;> simp [E, revolutionRadial]

theorem revolutionRadial_contDiff : ContDiff ℝ ∞ revolutionRadial := by
  have hΦ : ContDiff ℝ ∞ (fun t : ℝ => ![Real.cos t, Real.sin t, (0 : ℝ)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact Real.contDiff_cos
    · exact Real.contDiff_sin
    · exact contDiff_const
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hΦ

theorem revolutionAngular_contDiff : ContDiff ℝ ∞ revolutionAngular := by
  have hΦ : ContDiff ℝ ∞ (fun t : ℝ => ![-Real.sin t, Real.cos t, (0 : ℝ)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact Real.contDiff_sin.neg
    · exact Real.contDiff_cos
    · exact contDiff_const
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hΦ

theorem revolution_frame (θ : ℝ) : IsOrthonormalFrame (revolutionRadial θ) (revolutionAngular θ) revolutionAxis := by
  unfold IsOrthonormalFrame revolutionRadial revolutionAngular revolutionAxis
  simp only [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_succ]
  constructor
  · nlinarith [Real.sin_sq_add_cos_sq θ]
  · constructor
    · nlinarith [Real.sin_sq_add_cos_sq θ]
    · ring

theorem revolutionEnd_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (revolutionEnd q) := by
  have h0 : ContDiff ℝ ∞ (fun p : Coord => p 0) := contDiff_apply ℝ ℝ 0
  have h1 : ContDiff ℝ ∞ (fun p : Coord => p 1) := contDiff_apply ℝ ℝ 1
  exact ((hq.comp h1).smul (revolutionRadial_contDiff.comp h0)).add (h1.smul contDiff_const)

theorem revolutionEnd_partial {q : ℝ → ℝ} {p : Coord} {q₁ : ℝ}
    (hq : HasDerivAt q q₁ (p 1)) (i : Fin 2) :
    coordPartial i (revolutionEnd q) p =
      ((Pi.single i (1 : ℝ) : Coord) 1 * q₁) • revolutionRadial (p 0) +
      (q (p 1) * (Pi.single i (1 : ℝ) : Coord) 0) • revolutionAngular (p 0) +
      ((Pi.single i (1 : ℝ) : Coord) 1) • revolutionAxis := by
  have hqz := hq.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have he := (revolutionRadial_hasDerivAt (p 0)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hz := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hd := (hqz.smul he).add (hz.smul (hasFDerivAt_const (c := revolutionAxis) p))
  change HasFDerivAt (revolutionEnd q) _ p at hd
  rw [coordPartial, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply,
    zero_apply, smul_zero, zero_add, smul_smul, Function.comp_apply]
  module

theorem revolutionEnd_partial_theta {q : ℝ → ℝ} {p : Coord} {q₁ : ℝ}
    (hq : HasDerivAt q q₁ (p 1)) :
    coordPartial 0 (revolutionEnd q) p = q (p 1) • revolutionAngular (p 0) := by
  simpa using revolutionEnd_partial hq 0

theorem revolutionEnd_partial_height {q : ℝ → ℝ} {p : Coord} {q₁ : ℝ}
    (hq : HasDerivAt q q₁ (p 1)) :
    coordPartial 1 (revolutionEnd q) p = q₁ • revolutionRadial (p 0) + revolutionAxis := by
  simpa using revolutionEnd_partial hq 1

end
end TightVer401
