import TightVer401.ReciprocalExtension
import TightVer401.TwoCoordinateChain

/-! The reciprocal extension obeys global additive advection, derived from
the actual characteristic PDE in the original positive transverse variable. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem reciprocalExtension_transport {ρ lam D : ℝ → ℝ} {f : Coord → ℝ} {upper : ℝ}
    (hρ : ∀ s, HasDerivAt ρ (lam s * ρ s / 2) s)
    (hρpos : ∀ s, 0 < ρ s) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ f p)
    (hsupport : ∀ p : Coord, upper < p 1 → f p = 0)
    (hpde : ∀ p : Coord, 0 < p 1 → coordPartial 0 f p -
      p 1 / 2 * (lam (p 0) + p 1 * D (p 0)) * coordPartial 1 f p = 0)
    (p : Coord) :
    coordPartial 0 (reciprocalExtension ρ f) p +
      D (p 0) / (2 * ρ (p 0)) * coordPartial 1 (reciprocalExtension ρ f) p = 0 := by
  by_cases hr : 0 < p 1
  · have hρ0 := ne_of_gt (hρpos (p 0))
    have hr0 := ne_of_gt hr
    have hu : 0 < (reciprocalChart ρ p) 1 := one_div_pos.mpr (mul_pos (hρpos _) hr)
    have hs : DifferentiableAt ℝ (fun q : Coord => q 0) p :=
      ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
      (x := p)).differentiableAt
    have hz : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 / (2 * ρ (p 0))) (p 0) := by
      simpa using hasDerivAt_const (p 0) (0 : ℝ)
    have hv : DifferentiableAt ℝ (fun q : Coord => 1 / (ρ (q 0) * q 1)) p := by
      convert! ruledFirstIntegral_differentiableAt (hρ (p 0)) hz hρ0 hr0 using 1
      funext q
      simp [ruledFirstIntegral]
    have hvi (i : Fin 2) :
        coordPartial i (fun q : Coord => 1 / (ρ (q 0) * q 1)) p =
          -(Pi.single i (1 : ℝ) : Coord) 0 * lam (p 0) / (2 * ρ (p 0) * p 1) -
            (Pi.single i (1 : ℝ) : Coord) 1 / (ρ (p 0) * (p 1)^2) := by
      convert! ruledFirstIntegral_partial (hρ (p 0)) hz hρ0 hr0 i using 1
      · congr 1
        funext q
        simp [ruledFirstIntegral]
      · ring
    have hc (i : Fin 2) := coordPartial_scalar_comp_two hs hv (hf _ hu) i
    have he := (reciprocalExtension_eventually_eq_positive (ρ := ρ) (f := f) hr).fderiv_eq
      (𝕜 := ℝ)
    have hg (i : Fin 2) : coordPartial i (reciprocalExtension ρ f) p =
        coordPartial i (fun q => f (reciprocalChart ρ q)) p :=
      congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) he
    rw [hg 0, hg 1]
    change coordPartial 0 (fun q => f (![q 0, 1 / (ρ (q 0) * q 1)] : Coord)) p +
      D (p 0) / (2 * ρ (p 0)) *
        coordPartial 1 (fun q => f (![q 0, 1 / (ρ (q 0) * q 1)] : Coord)) p = 0
    rw [hc 0, hc 1, hvi 0, hvi 1, coordPartial_proj, coordPartial_proj]
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), one_mul, zero_mul, zero_div,
      neg_zero, neg_mul, sub_zero, zero_sub]
    have hp := hpde (reciprocalChart ρ p) hu
    dsimp only [reciprocalChart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hp
    convert! hp using 1
    field_simp
    <;> ring
  · have he := (reciprocalExtension_eventually_zero hupper (hρ (p 0)).continuousAt hρpos
      hsupport (le_of_not_gt hr)).fderiv_eq (𝕜 := ℝ)
    have hz : fderiv ℝ (fun _ : Coord => (0 : ℝ)) p = 0 :=
      (hasFDerivAt_const (c := (0 : ℝ)) p).fderiv
    simp [coordPartial, he, hz]

end
end TightVer401
