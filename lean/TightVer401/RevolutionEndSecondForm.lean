import TightVer401.RevolutionEndGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem revolution_curve_product_partial {a : ℝ → ℝ} {V : ℝ → Ambient}
    {a₁ : ℝ} {V₁ : Ambient} {p : Coord}
    (ha : HasDerivAt a a₁ (p 1)) (hV : HasDerivAt V V₁ (p 0)) (i : Fin 2) :
    coordPartial i (fun z : Coord => a (z 1) • V (z 0)) p =
      ((Pi.single i (1 : ℝ) : Coord) 1 * a₁) • V (p 0) +
        (a (p 1) * (Pi.single i (1 : ℝ) : Coord) 0) • V₁ := by
  have ha' := ha.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have hV' := hV.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hd := ha'.smul hV'
  change HasFDerivAt (fun z : Coord => a (z 1) • V (z 0)) _ p at hd
  rw [coordPartial, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply,
    smul_smul, Function.comp_apply]
  module

theorem revolutionEnd_second_theta {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    coordPartial 0 (coordPartial 0 (revolutionEnd q)) p =
      (-q (p 1)) • revolutionRadial (p 0) := by
  have hfun : coordPartial 0 (revolutionEnd q) = fun z => q (z 1) • revolutionAngular (z 0) := by
    funext z
    exact revolutionEnd_partial_theta (hq.differentiable (by simp) (z 1)).hasDerivAt
  rw [hfun, revolution_curve_product_partial
    (hq.differentiable (by simp) (p 1)).hasDerivAt (revolutionAngular_hasDerivAt (p 0))]
  simp

theorem revolutionEnd_second_mixed {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    coordPartial 1 (coordPartial 0 (revolutionEnd q)) p =
      deriv q (p 1) • revolutionAngular (p 0) := by
  have hfun : coordPartial 0 (revolutionEnd q) = fun z => q (z 1) • revolutionAngular (z 0) := by
    funext z
    exact revolutionEnd_partial_theta (hq.differentiable (by simp) (z 1)).hasDerivAt
  rw [hfun, revolution_curve_product_partial
    (hq.differentiable (by simp) (p 1)).hasDerivAt (revolutionAngular_hasDerivAt (p 0))]
  simp

theorem revolutionEnd_second_height {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    coordPartial 1 (coordPartial 1 (revolutionEnd q)) p =
      deriv (deriv q) (p 1) • revolutionRadial (p 0) := by
  have hfun : coordPartial 1 (revolutionEnd q) = fun z => deriv q (z 1) • revolutionRadial (z 0) + revolutionAxis := by
    funext z
    exact revolutionEnd_partial_height (hq.differentiable (by simp) (z 1)).hasDerivAt
  have hqd := (contDiff_infty_iff_deriv.mp hq).2
  have hprod : DifferentiableAt ℝ (fun z : Coord => deriv q (z 1) • revolutionRadial (z 0)) p :=
    ((hqd.comp (contDiff_apply ℝ ℝ 1)).smul (revolutionRadial_contDiff.comp (contDiff_apply ℝ ℝ 0))).differentiable (by simp) p
  have hc : fderiv ℝ (fun _ : Coord => revolutionAxis) p = 0 :=
    (hasFDerivAt_const (c := revolutionAxis) p).fderiv
  rw [hfun]
  simp only [coordPartial, fderiv_fun_add hprod (differentiableAt_const (c := revolutionAxis)),
    add_apply, hc, zero_apply, add_zero]
  change coordPartial 1 (fun z : Coord => deriv q (z 1) • revolutionRadial (z 0)) p = _
  rw [revolution_curve_product_partial
    (hqd.differentiable (by simp) (p 1)).hasDerivAt (revolutionRadial_hasDerivAt (p 0))]
  simp

theorem revolutionEnd_secondFundamental {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    secondFundamental (revolutionEnd q) (revolutionEndNormal q p) p =
      ![![q (p 1) / revolutionWeight (deriv q (p 1)), 0],
        ![0, -deriv (deriv q) (p 1) / revolutionWeight (deriv q (p 1))]] := by
  rcases revolution_frame (p 0) with ⟨hrr, _, _, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hra]
  have hcomm := coordPartial_comm (revolutionEnd_contDiff hq).contDiffOn isOpen_univ (mem_univ p) 0 1
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (coordPartial 0 (coordPartial 0 (revolutionEnd q)) p) (revolutionEndNormal q p) = q (p 1) / revolutionWeight (deriv q (p 1))
    rw [revolutionEnd_second_theta hq]
    simp only [revolutionEndNormal, inner_add_right, real_inner_smul_left, real_inner_smul_right, hrr, hrz]
    simp <;> ring
  · change inner ℝ (coordPartial 0 (coordPartial 1 (revolutionEnd q)) p) (revolutionEndNormal q p) = 0
    rw [hcomm, revolutionEnd_second_mixed hq]
    simp [revolutionEndNormal, inner_add_right, real_inner_smul_left, real_inner_smul_right, har, haz]
  · change inner ℝ (coordPartial 1 (coordPartial 0 (revolutionEnd q)) p) (revolutionEndNormal q p) = 0
    rw [revolutionEnd_second_mixed hq]
    simp [revolutionEndNormal, inner_add_right, real_inner_smul_left, real_inner_smul_right, har, haz]
  · change inner ℝ (coordPartial 1 (coordPartial 1 (revolutionEnd q)) p) (revolutionEndNormal q p) = -deriv (deriv q) (p 1) / revolutionWeight (deriv q (p 1))
    rw [revolutionEnd_second_height hq]
    simp only [revolutionEndNormal, inner_add_right, real_inner_smul_left, real_inner_smul_right, hrr, hrz]
    simp <;> ring

end
end TightVer401
