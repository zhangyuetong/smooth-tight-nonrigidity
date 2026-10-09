import TightVer401.RuledStrain
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Elementary rules for the actual OpenAI coordinate differential. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem scalar_coord_div_differentiableAt {f g : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (hzero : g p ≠ 0) :
    DifferentiableAt ℝ (fun q => f q / g q) p := by
  change DifferentiableAt ℝ (fun q => f q * (g q)⁻¹) p
  exact hf.mul (hg.inv hzero)

theorem coordPartial_scalar_add {f g : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 2) :
    coordPartial i (fun q => f q + g q) p = coordPartial i f p + coordPartial i g p := by
  simp only [coordPartial, fderiv_fun_add hf hg, add_apply]

theorem coordPartial_scalar_sub {f g : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 2) :
    coordPartial i (fun q => f q - g q) p = coordPartial i f p - coordPartial i g p := by
  simp only [coordPartial, fderiv_fun_sub hf hg, sub_apply]

theorem coordPartial_scalar_mul {f g : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 2) :
    coordPartial i (fun q => f q * g q) p = f p * coordPartial i g p + g p * coordPartial i f p := by
  simp only [coordPartial, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem coordPartial_scalar_inv {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hzero : f p ≠ 0) (i : Fin 2) :
    coordPartial i (fun q => (f q)⁻¹) p = -coordPartial i f p / (f p)^2 := by
  have hd := (hasDerivAt_inv hzero).hasFDerivAt.comp p hf.hasFDerivAt
  change (fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ f) p) (Pi.single i 1) = _
  rw [hd.fderiv]
  simp only [coordPartial, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

theorem coordPartial_scalar_comp {F : ℝ → ℝ} {g : Coord → ℝ} {p : Coord} {F' : ℝ}
    (hF : HasDerivAt F F' (g p)) (hg : DifferentiableAt ℝ g p) (i : Fin 2) :
    coordPartial i (fun q => F (g q)) p = F' * coordPartial i g p := by
  have hd := hF.hasFDerivAt.comp p hg.hasFDerivAt
  change (fderiv ℝ (F ∘ g) p) (Pi.single i 1) = _
  rw [hd.fderiv]
  simp only [coordPartial, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

theorem coordPartial_scalar_div {f g : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (hzero : g p ≠ 0) (i : Fin 2) :
    coordPartial i (fun q => f q / g q) p =
      (coordPartial i f p * g p - f p * coordPartial i g p) / (g p)^2 := by
  change coordPartial i (fun q => f q * (g q)⁻¹) p = _
  have hgi : DifferentiableAt ℝ (fun q => (g q)⁻¹) p := hg.inv hzero
  rw [coordPartial_scalar_mul hf hgi i, coordPartial_scalar_inv hg hzero i]
  field_simp
  <;> ring

theorem coordPartial_scalar_const (c : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (fun _ : Coord => c) p = 0 := by
  simp [coordPartial]

theorem coordPartial_proj (p : Coord) (i j : Fin 2) :
    coordPartial i (fun q : Coord => q j) p = (Pi.single i (1 : ℝ) : Coord) j := by
  exact congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1))
    ((ContinuousLinearMap.proj (R := ℝ) j).hasFDerivAt (x := p)).fderiv

end
end TightVer401
