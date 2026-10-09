import TightVer401.ScalarCoordinateCalculus
import TightVer401.RuledPrimitives
import TightVer401.RuledReconstruction

/-! Actual coordinate differentiation of the supported-kernel profile. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def ruledFirstIntegral (ρ W : ℝ → ℝ) : Coord → ℝ :=
  fun p => 1 / (ρ (p 0) * p 1) - W (p 0)

def ruledProfileAlpha (τ ρ W F : ℝ → ℝ) : Coord → ℝ :=
  fun p => τ (p 0) * p 1 / (2 * ρ (p 0)) * deriv F (ruledFirstIntegral ρ W p)

def ruledProfileBeta (k ρ W F : ℝ → ℝ) : Coord → ℝ :=
  fun p => p 1 * F (ruledFirstIntegral ρ W p) -
    (1 - k (p 0) * p 1) / (2 * ρ (p 0)) * deriv F (ruledFirstIntegral ρ W p)

def ruledAlphaFactor (τ ρ : ℝ → ℝ) : Coord → ℝ :=
  fun p => τ (p 0) * p 1 / (2 * ρ (p 0))

def ruledBetaFactor (k ρ : ℝ → ℝ) : Coord → ℝ :=
  fun p => (1 - k (p 0) * p 1) / (2 * ρ (p 0))

theorem ruledFirstIntegral_differentiableAt {ρ W : ℝ → ℝ} {p : Coord} {lam D : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ (p 0) / 2) (p 0))
    (hW : HasDerivAt W (D / (2 * ρ (p 0))) (p 0))
    (hρ0 : ρ (p 0) ≠ 0) (hu0 : p 1 ≠ 0) :
    DifferentiableAt ℝ (ruledFirstIntegral ρ W) p := by
  have hρc : DifferentiableAt ℝ (fun q : Coord => ρ (q 0)) p :=
    (hρ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hWc : DifferentiableAt ℝ (fun q : Coord => W (q 0)) p :=
    (hW.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  change DifferentiableAt ℝ (fun q : Coord => 1 / (ρ (q 0) * q 1) - W (q 0)) p
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have hd : DifferentiableAt ℝ (fun q : Coord => ρ (q 0) * q 1) p := hρc.mul hu
  have hq : DifferentiableAt ℝ (fun q : Coord => 1 / (ρ (q 0) * q 1)) p :=
    scalar_coord_div_differentiableAt (differentiableAt_const 1) hd (mul_ne_zero hρ0 hu0)
  exact hq.sub hWc

theorem ruledFirstIntegral_partial {ρ W : ℝ → ℝ} {p : Coord} {lam D : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ (p 0) / 2) (p 0))
    (hW : HasDerivAt W (D / (2 * ρ (p 0))) (p 0))
    (hρ0 : ρ (p 0) ≠ 0) (hu0 : p 1 ≠ 0) (i : Fin 2) :
    coordPartial i (ruledFirstIntegral ρ W) p =
      -(Pi.single i (1 : ℝ) : Coord) 0 * (lam + p 1 * D) / (2 * ρ (p 0) * p 1) -
      (Pi.single i (1 : ℝ) : Coord) 1 / (ρ (p 0) * (p 1)^2) := by
  have hρc : DifferentiableAt ℝ (fun q : Coord => ρ (q 0)) p :=
    (hρ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hWc : DifferentiableAt ℝ (fun q : Coord => W (q 0)) p :=
    (hW.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have hd : DifferentiableAt ℝ (fun q : Coord => ρ (q 0) * q 1) p := hρc.mul hu
  have hq : DifferentiableAt ℝ (fun q : Coord => 1 / (ρ (q 0) * q 1)) p :=
    scalar_coord_div_differentiableAt (differentiableAt_const 1) hd (mul_ne_zero hρ0 hu0)
  change coordPartial i (fun q => 1 / (ρ (q 0) * q 1) - W (q 0)) p = _
  rw [coordPartial_scalar_sub hq hWc i,
    coordPartial_scalar_div (differentiableAt_const (c := (1 : ℝ)))
      hd (mul_ne_zero hρ0 hu0) i,
    coordPartial_scalar_mul hρc hu i, coordPartial_curve hρ i, coordPartial_curve hW i,
    coordPartial_proj, coordPartial_scalar_const]
  simp only [smul_eq_mul]
  field_simp
  <;> ring

theorem ruledProfile_factors {k τ ρ : ℝ → ℝ} {p : Coord} {ks lam : ℝ}
    (hk : HasDerivAt k ks (p 0))
    (hτ : HasDerivAt τ (lam * τ (p 0)) (p 0))
    (hρ : HasDerivAt ρ (lam * ρ (p 0) / 2) (p 0)) (hρ0 : ρ (p 0) ≠ 0) :
    DifferentiableAt ℝ (ruledAlphaFactor τ ρ) p ∧
    DifferentiableAt ℝ (ruledBetaFactor k ρ) p ∧
    ∀ i : Fin 2,
      coordPartial i (ruledAlphaFactor τ ρ) p =
        (Pi.single i (1 : ℝ) : Coord) 0 * lam * τ (p 0) * p 1 / (4 * ρ (p 0)) +
        (Pi.single i (1 : ℝ) : Coord) 1 * τ (p 0) / (2 * ρ (p 0)) ∧
      coordPartial i (ruledBetaFactor k ρ) p =
        (Pi.single i (1 : ℝ) : Coord) 0 *
          (-ks * p 1 / (2 * ρ (p 0)) - (1 - k (p 0) * p 1) * lam / (4 * ρ (p 0))) -
        (Pi.single i (1 : ℝ) : Coord) 1 * k (p 0) / (2 * ρ (p 0)) := by
  have hkc : DifferentiableAt ℝ (fun q : Coord => k (q 0)) p :=
    (hk.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hτc : DifferentiableAt ℝ (fun q : Coord => τ (q 0)) p :=
    (hτ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hρc : DifferentiableAt ℝ (fun q : Coord => ρ (q 0)) p :=
    (hρ.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have h1 : DifferentiableAt ℝ (fun _ : Coord => (1 : ℝ)) p := differentiableAt_const 1
  have h2 : DifferentiableAt ℝ (fun _ : Coord => (2 : ℝ)) p := differentiableAt_const 2
  have hd : DifferentiableAt ℝ (fun q : Coord => 2 * ρ (q 0)) p := h2.mul hρc
  have hd0 : 2 * ρ (p 0) ≠ 0 := mul_ne_zero (by norm_num) hρ0
  have hnumA : DifferentiableAt ℝ (fun q : Coord => τ (q 0) * q 1) p := hτc.mul hu
  have hku : DifferentiableAt ℝ (fun q : Coord => k (q 0) * q 1) p := hkc.mul hu
  have hnumB : DifferentiableAt ℝ (fun q : Coord => 1 - k (q 0) * q 1) p := h1.sub hku
  have hA : DifferentiableAt ℝ (ruledAlphaFactor τ ρ) p :=
    scalar_coord_div_differentiableAt hnumA hd hd0
  have hB : DifferentiableAt ℝ (ruledBetaFactor k ρ) p :=
    scalar_coord_div_differentiableAt hnumB hd hd0
  refine ⟨hA, hB, ?_⟩
  intro i
  constructor
  · change coordPartial i (fun q => τ (q 0) * q 1 / (2 * ρ (q 0))) p = _
    rw [coordPartial_scalar_div hnumA hd hd0 i,
      coordPartial_scalar_mul hτc hu i, coordPartial_scalar_mul h2 hρc i,
      coordPartial_curve hτ i, coordPartial_curve hρ i, coordPartial_proj, coordPartial_scalar_const]
    simp only [smul_eq_mul]
    field_simp
    <;> ring
  · change coordPartial i (fun q => (1 - k (q 0) * q 1) / (2 * ρ (q 0))) p = _
    rw [coordPartial_scalar_div hnumB hd hd0 i,
      coordPartial_scalar_sub h1 hku i,
      coordPartial_scalar_mul hkc hu i, coordPartial_scalar_mul h2 hρc i,
      coordPartial_curve hk i, coordPartial_curve hρ i, coordPartial_proj]
    simp only [coordPartial_scalar_const, smul_eq_mul]
    field_simp
    <;> ring

theorem ruledProfile_differential {k τ ρ W F : ℝ → ℝ} {p : Coord} {ks lam f₁ f₂ : ℝ}
    (hk : HasDerivAt k ks (p 0))
    (hτ : HasDerivAt τ (lam * τ (p 0)) (p 0))
    (hρ : HasDerivAt ρ (lam * ρ (p 0) / 2) (p 0))
    (hW : HasDerivAt W ((ks - k (p 0) * lam) / (2 * ρ (p 0))) (p 0))
    (hρ0 : ρ (p 0) ≠ 0) (hu0 : p 1 ≠ 0)
    (hF : HasDerivAt F f₁ (ruledFirstIntegral ρ W p))
    (hF' : HasDerivAt (deriv F) f₂ (ruledFirstIntegral ρ W p)) :
    DifferentiableAt ℝ (ruledProfileAlpha τ ρ W F) p ∧
    DifferentiableAt ℝ (ruledProfileBeta k ρ W F) p ∧
    ∀ i : Fin 2,
      coordPartial i (ruledProfileAlpha τ ρ W F) p =
        coordPartial i (ruledAlphaFactor τ ρ) p * f₁ +
        ruledAlphaFactor τ ρ p * f₂ * coordPartial i (ruledFirstIntegral ρ W) p ∧
      coordPartial i (ruledProfileBeta k ρ W F) p =
        (Pi.single i (1 : ℝ) : Coord) 1 * F (ruledFirstIntegral ρ W p) +
        p 1 * f₁ * coordPartial i (ruledFirstIntegral ρ W) p -
        (coordPartial i (ruledBetaFactor k ρ) p * f₁ +
          ruledBetaFactor k ρ p * f₂ * coordPartial i (ruledFirstIntegral ρ W) p) := by
  obtain ⟨hA, hB, _⟩ := ruledProfile_factors hk hτ hρ hρ0
  have hV := ruledFirstIntegral_differentiableAt hρ hW hρ0 hu0
  have hFc : DifferentiableAt ℝ (fun q => F (ruledFirstIntegral ρ W q)) p :=
    hF.differentiableAt.comp p hV
  have hF'c : DifferentiableAt ℝ (fun q => deriv F (ruledFirstIntegral ρ W q)) p :=
    hF'.differentiableAt.comp p hV
  have hu : DifferentiableAt ℝ (fun q : Coord => q 1) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)).differentiableAt
  have hval : deriv F (ruledFirstIntegral ρ W p) = f₁ := hF.deriv
  have huF : DifferentiableAt ℝ (fun q : Coord => q 1 * F (ruledFirstIntegral ρ W q)) p := hu.mul hFc
  have hBF : DifferentiableAt ℝ (fun q : Coord => ruledBetaFactor k ρ q * deriv F (ruledFirstIntegral ρ W q)) p := hB.mul hF'c
  refine ⟨hA.mul hF'c, huF.sub hBF, ?_⟩
  intro i
  constructor
  · change coordPartial i (fun q => ruledAlphaFactor τ ρ q * deriv F (ruledFirstIntegral ρ W q)) p = _
    rw [coordPartial_scalar_mul hA hF'c i, coordPartial_scalar_comp hF' hV i, hval]
    ring
  · change coordPartial i (fun q => q 1 * F (ruledFirstIntegral ρ W q) -
      ruledBetaFactor k ρ q * deriv F (ruledFirstIntegral ρ W q)) p = _
    rw [coordPartial_scalar_sub huF hBF i,
      coordPartial_scalar_mul hu hFc i, coordPartial_scalar_mul hB hF'c i,
      coordPartial_scalar_comp hF hV i, coordPartial_scalar_comp hF' hV i,
      coordPartial_proj, hval]
    ring

end
end TightVer401
