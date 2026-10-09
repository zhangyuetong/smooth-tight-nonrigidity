import TightVer401.CharacteristicTransport
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The integrating factor is the actual positive function sqrt(|τ|).
Its differential equation is derived from τ, rather than imposed on ρ. -/
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ruledRho (τ : ℝ → ℝ) : ℝ → ℝ := fun s => Real.sqrt |τ s|

theorem ruledRho_pos {τ : ℝ → ℝ} {s : ℝ} (hτ : τ s ≠ 0) : 0 < ruledRho τ s :=
  Real.sqrt_pos.mpr (abs_pos.mpr hτ)

theorem ruledRho_sq (τ : ℝ → ℝ) (s : ℝ) : (ruledRho τ s)^2 = |τ s| :=
  Real.sq_sqrt (abs_nonneg _)

theorem ruledRho_periodic {τ : ℝ → ℝ} {L : ℝ} (hτ : Function.Periodic τ L) :
    Function.Periodic (ruledRho τ) L := by
  intro s
  simp only [ruledRho, hτ s]

theorem ruledRho_hasDerivAt {τ : ℝ → ℝ} {s dτ : ℝ}
    (hτ : HasDerivAt τ dτ s) (hne : τ s ≠ 0) :
    HasDerivAt (ruledRho τ) ((dτ / τ s) * ruledRho τ s / 2) s := by
  have hr0 : ruledRho τ s ≠ 0 := ne_of_gt (ruledRho_pos hne)
  have hrsq := ruledRho_sq τ s
  rcases hne.lt_or_gt with hneg | hpos
  · have ha : HasDerivAt (fun t => |τ t|) (-dτ) s := by
      convert! (hasDerivAt_abs_neg hneg).comp s hτ using 1 <;> ring
    convert! ha.sqrt (ne_of_gt (abs_pos.mpr hne)) using 1
    dsimp only [ruledRho] at *
    simp only [abs_of_neg hneg] at *
    field_simp
    nlinarith [congrArg (fun x : ℝ => dτ * x) hrsq]
  · have ha : HasDerivAt (fun t => |τ t|) dτ s := by
      convert! (hasDerivAt_abs_pos hpos).comp s hτ using 1 <;> ring
    convert! ha.sqrt (ne_of_gt (abs_pos.mpr hne)) using 1
    dsimp only [ruledRho] at *
    simp only [abs_of_pos hpos] at *
    field_simp
    nlinarith [congrArg (fun x : ℝ => dτ * x) hrsq]

end
end TightVer401
