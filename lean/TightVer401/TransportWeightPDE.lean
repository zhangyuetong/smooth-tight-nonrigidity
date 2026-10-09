import TightVer401.RuledProfiles

/-! Actual two-variable differentiation of p/(τ u²). The inhomogeneous
potential equation becomes the homogeneous characteristic transport equation. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def ruledTransportWeight (τ : ℝ → ℝ) (P : Coord → ℝ) : Coord → ℝ :=
  fun q => P q / (τ (q 0) * q 1 * q 1)

theorem ruledTransportWeight_differentiableAt {τ : ℝ → ℝ} {P : Coord → ℝ} {q : Coord}
    (hτ : DifferentiableAt ℝ τ (q 0)) (hP : DifferentiableAt ℝ P q)
    (hτ0 : τ (q 0) ≠ 0) (hu0 : q 1 ≠ 0) :
    DifferentiableAt ℝ (ruledTransportWeight τ P) q := by
  have hs := ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
    (x := q)).differentiableAt
  have hu := ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
    (x := q)).differentiableAt
  have hc : DifferentiableAt ℝ (fun p : Coord => τ (p 0)) q := hτ.comp q hs
  exact scalar_coord_div_differentiableAt hP ((hc.mul hu).mul hu)
    (mul_ne_zero (mul_ne_zero hτ0 hu0) hu0)

theorem ruledTransportWeight_partial {τ : ℝ → ℝ} {P : Coord → ℝ} {q : Coord} {lam : ℝ}
    (hτ : HasDerivAt τ (lam * τ (q 0)) (q 0)) (hP : DifferentiableAt ℝ P q)
    (hτ0 : τ (q 0) ≠ 0) (hu0 : q 1 ≠ 0) (i : Fin 2) :
    coordPartial i (ruledTransportWeight τ P) q =
      (coordPartial i P q * (τ (q 0) * q 1 * q 1) - P q *
        ((Pi.single i (1 : ℝ) : Coord) 0 * lam * τ (q 0) * q 1 * q 1 +
          (Pi.single i (1 : ℝ) : Coord) 1 * (2 * τ (q 0) * q 1))) /
        (τ (q 0) * q 1 * q 1)^2 := by
  have hu : DifferentiableAt ℝ (fun p : Coord => p 1) q :=
    ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := q)).differentiableAt
  have hc : DifferentiableAt ℝ (fun p : Coord => τ (p 0)) q :=
    (hτ.hasFDerivAt.comp q (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt).differentiableAt
  have htu : DifferentiableAt ℝ (fun p : Coord => τ (p 0) * p 1) q := hc.mul hu
  have hden : DifferentiableAt ℝ (fun p : Coord => τ (p 0) * p 1 * p 1) q := htu.mul hu
  change coordPartial i (fun p => P p / (τ (p 0) * p 1 * p 1)) q = _
  rw [coordPartial_scalar_div hP hden
    (mul_ne_zero (mul_ne_zero hτ0 hu0) hu0),
    coordPartial_scalar_mul htu hu, coordPartial_scalar_mul hc hu,
    coordPartial_curve hτ, coordPartial_proj]
  simp only [smul_eq_mul]
  ring

theorem ruledTransportWeight_transport {τ : ℝ → ℝ} {P : Coord → ℝ} {q : Coord} {lam D : ℝ}
    (hτ : HasDerivAt τ (lam * τ (q 0)) (q 0)) (hP : DifferentiableAt ℝ P q)
    (hτ0 : τ (q 0) ≠ 0) (hu0 : q 1 ≠ 0)
    (hpde : coordPartial 0 P q - q 1 / 2 * (lam + q 1 * D) * coordPartial 1 P q =
      -q 1 * D * P q) :
    coordPartial 0 (ruledTransportWeight τ P) q - q 1 / 2 * (lam + q 1 * D) *
      coordPartial 1 (ruledTransportWeight τ P) q = 0 := by
  rw [ruledTransportWeight_partial hτ hP hτ0 hu0 0,
    ruledTransportWeight_partial hτ hP hτ0 hu0 1]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_mul, one_mul, zero_add, add_zero]
  have he : coordPartial 0 P q = q 1 / 2 * (lam + q 1 * D) * coordPartial 1 P q -
      q 1 * D * P q := by linarith
  rw [he]
  field_simp
  <;> ring

end
end TightVer401
