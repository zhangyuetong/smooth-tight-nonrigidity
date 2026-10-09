import TightVer401.RuledCurvature
import TightVer401.ScalarCoordinateCalculus

/-! The remaining actual ss second-form coefficient derives the characteristic
equation from the principal-normal ruled immersion. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem ruled_second_partial_ss
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord} {ks τs : ℝ}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0)) :
    coordPartial 0 (coordPartial 0 (ruledMap γ E)) p =
      (-p 1 * ks) • T (p 0) +
      (k (p 0) - p 1 * ((k (p 0))^2 + (τ (p 0))^2)) • E (p 0) +
      (p 1 * τs) • n (p 0) := by
  have hXs : coordPartial 0 (ruledMap γ E) = fun q =>
      (1 - k (q 0) * q 1) • T (q 0) + (τ (q 0) * q 1) • n (q 0) := by
    funext q
    exact ruled_partial_s (hγ (q 0)) (hE (q 0))
  have hkc : DifferentiableAt ℝ (fun q : Coord => k (q 0)) p :=
    (hk.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hτc : DifferentiableAt ℝ (fun q : Coord => τ (q 0)) p :=
    (hτ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hTc : DifferentiableAt ℝ (fun q : Coord => T (q 0)) p :=
    (hT.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hnc : DifferentiableAt ℝ (fun q : Coord => n (q 0)) p :=
    (hn.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have hku : DifferentiableAt ℝ (fun q : Coord => k (q 0) * q 1) p := hkc.mul hu
  have hA : DifferentiableAt ℝ (fun q : Coord => 1 - k (q 0) * q 1) p :=
    (differentiableAt_const (c := (1 : ℝ))).sub hku
  have hB : DifferentiableAt ℝ (fun q : Coord => τ (q 0) * q 1) p := hτc.mul hu
  have hAP : coordPartial 0 (fun q : Coord => 1 - k (q 0) * q 1) p = -ks * p 1 := by
    rw [coordPartial_scalar_sub (differentiableAt_const (c := (1 : ℝ))) hku 0,
      coordPartial_scalar_mul hkc hu 0, coordPartial_curve hk 0,
      coordPartial_scalar_const, coordPartial_proj]
    simp [mul_comm]
  have hBP : coordPartial 0 (fun q : Coord => τ (q 0) * q 1) p = τs * p 1 := by
    rw [coordPartial_scalar_mul hτc hu 0, coordPartial_curve hτ 0, coordPartial_proj]
    simp [mul_comm]
  rw [hXs]
  have hAT : DifferentiableAt ℝ (fun q : Coord => (1 - k (q 0) * q 1) • T (q 0)) p := hA.smul hTc
  have hBn : DifferentiableAt ℝ (fun q : Coord => (τ (q 0) * q 1) • n (q 0)) p := hB.smul hnc
  have hadd : coordPartial 0 (fun q : Coord =>
      (1 - k (q 0) * q 1) • T (q 0) + (τ (q 0) * q 1) • n (q 0)) p =
      coordPartial 0 (fun q : Coord => (1 - k (q 0) * q 1) • T (q 0)) p +
      coordPartial 0 (fun q : Coord => (τ (q 0) * q 1) • n (q 0)) p := by
    simp only [coordPartial, fderiv_fun_add hAT hBn, add_apply]
  rw [hadd, coordPartial_scalar_vector hA hTc, coordPartial_scalar_vector hB hnc,
    hAP, hBP, coordPartial_curve hT 0, coordPartial_curve hn 0]
  simp only [Pi.single_eq_same, one_smul]
  module

theorem ruled_second_form_ss
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord} {ks τs : ℝ}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0))
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) (hτ0 : τ (p 0) ≠ 0) :
    secondFundamental (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p 0 0 =
      p 1 * τ (p 0) * (τs / τ (p 0) + p 1 * (ks - k (p 0) * (τs / τ (p 0)))) /
        Real.sqrt (ruledEnergy (k (p 0)) (τ (p 0)) (p 1)) := by
  rw [secondFundamental, ruled_second_partial_ss hγ hE hT hn hk hτ]
  rcases hf with ⟨hTT, _, hnn, hTE, hTn, hEn⟩
  have hET : inner ℝ (E (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTE]
  have hnT : inner ℝ (n (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTn]
  simp only [ruledNormal, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hTT, hnn, hTn, hnT, hET, hEn,
    mul_zero, mul_one, add_zero, zero_add]
  have hroot : Real.sqrt (ruledEnergy (k (p 0)) (τ (p 0)) (p 1)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (ruledEnergy_pos hτ0))
  field_simp
  <;> ring

end
end TightVer401
