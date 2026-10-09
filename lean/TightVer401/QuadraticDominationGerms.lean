import TightVer401.QuadraticDominationCalculus
import TightVer401.DualRadialQuadraticGerm
import TightVer401.ConcaveJetJoinBlend

/-! Exact cutoff plateaus, boundary first jet, and inner radial germ. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem quadraticDomination_plateau_derivatives {chi : ℝ → ℝ} {a r c : ℝ}
    (heq : ∀ x, a < x → chi x = c) (hr : a < r) :
    deriv chi r = 0 ∧ deriv (deriv chi) r = 0 := by
  have he : chi =ᶠ[𝓝 r] (fun _ => c) :=
    (eventually_gt_nhds hr).mono (fun x hx => heq x hx)
  constructor
  · simpa using he.deriv_eq
  · simpa using he.deriv.deriv_eq

theorem quadraticDomination_inner_derivatives {chi : ℝ → ℝ} {a r c : ℝ}
    (heq : ∀ x, x < a → chi x = c) (hr : r < a) :
    deriv chi r = 0 ∧ deriv (deriv chi) r = 0 := by
  have he : chi =ᶠ[𝓝 r] (fun _ => c) :=
    (eventually_lt_nhds hr).mono (fun x hx => heq x hx)
  constructor
  · simpa using he.deriv_eq
  · simpa using he.deriv.deriv_eq

theorem dualQuadraticFiller_boundary_first_jet {R : ℝ} (hR : 0 < R) (M : ℝ)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hchi1 : ∀ r, 3 * R / 4 ≤ r → chi r = 1) (t : ℝ) :
    dualQuadraticFiller R M chi h b ![R,t] = h t ∧
      coordPartial 0 (dualQuadraticFiller R M chi h b) ![R,t] = b t ∧
      coordPartial 1 (dualQuadraticFiller R M chi h b) ![R,t] = deriv h t := by
  have hc : chi R = 1 := hchi1 R (by linarith)
  have hd : deriv chi R = 0 := (quadraticDomination_plateau_derivatives
    (fun r hr => hchi1 r hr.le) (by linarith : 3 * R / 4 < R)).1
  simp [dualQuadraticFiller, dualQuadraticFiller_coordPartial R M hchi hh hb, hc, hd]

theorem dualQuadraticFiller_inner_germ (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi0 : ∀ r, r ≤ R / 2 → chi r = 0) {p : Coord} (hp : p 0 ≤ R / 2) :
    dualQuadraticFiller R M chi h b p =
      dualRadialQuadraticProfile R M (-M * R^2 / 2) (p 0) := by
  simp only [dualQuadraticFiller, hchi0 _ hp, zero_mul, add_zero, dualRadialQuadraticProfile]
  ring

/-- A concrete smooth cutoff, independent of angular data and the coefficient. -/
def quadraticDominationCutoff (R : ℝ) : ℝ → ℝ :=
  concaveJetJoinBlendTransition (5 * R / 8) (R / 8)

theorem quadraticDominationCutoff_properties {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (quadraticDominationCutoff R) ∧
      (∀ r, r ≤ R / 2 → quadraticDominationCutoff R r = 0) ∧
      (∀ r, 3 * R / 4 ≤ r → quadraticDominationCutoff R r = 1) ∧
      (∀ r, 0 ≤ quadraticDominationCutoff R r ∧ quadraticDominationCutoff R r ≤ 1) := by
  refine ⟨concaveJetJoinBlendTransition_contDiff _ _, ?_, ?_, concaveJetJoinBlendTransition_bound _ _⟩
  · intro r hr
    exact concaveJetJoinBlendTransition_left (by positivity) (by linarith)
  · intro r hr
    exact concaveJetJoinBlendTransition_right (by positivity) (by linarith)

end
end TightVer401
