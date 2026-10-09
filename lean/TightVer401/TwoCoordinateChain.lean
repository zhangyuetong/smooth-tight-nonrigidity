import TightVer401.ScalarCoordinateCalculus
import TightVer401.AdvectionTransport

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem coordPartial_scalar_comp_two {f : Coord → ℝ} {g₀ g₁ : Coord → ℝ} {p : Coord}
    (h₀ : DifferentiableAt ℝ g₀ p) (h₁ : DifferentiableAt ℝ g₁ p)
    (hf : DifferentiableAt ℝ f (![g₀ p, g₁ p] : Coord)) (i : Fin 2) :
    coordPartial i (fun q => f (![g₀ q, g₁ q] : Coord)) p =
      coordPartial i g₀ p * coordPartial 0 f (![g₀ p, g₁ p] : Coord) +
      coordPartial i g₁ p * coordPartial 1 f (![g₀ p, g₁ p] : Coord) := by
  have hd : HasFDerivAt (fun q => (![g₀ q, g₁ q] : Coord))
      (ContinuousLinearMap.pi (![fderiv ℝ g₀ p, fderiv ℝ g₁ p] :
        Fin 2 → Coord →L[ℝ] ℝ)) p := by
    apply hasFDerivAt_pi.mpr
    intro j
    fin_cases j
    · convert! h₀.hasFDerivAt using 1
    · convert! h₁.hasFDerivAt using 1
  have hc := hf.hasFDerivAt.comp p hd
  change (fderiv ℝ (f ∘ (fun q => (![g₀ q, g₁ q] : Coord))) p) (Pi.single i 1) = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, fderiv_two_scalar_coordinates]
  rfl

end
end TightVer401
