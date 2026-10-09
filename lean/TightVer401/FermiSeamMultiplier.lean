import TightVer401.FermiCurvatureMass
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TightVer401
noncomputable section
open MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def fermiSeamSlopeCoefficient (a κ c : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(deriv a r + κ r * c r) / (2 * a r)

def fermiSeamLinearMultiplier (L : ℝ) (a κ c : ℝ → ℝ) : ℝ :=
  Real.exp (∫ r in 0..L, fermiSeamSlopeCoefficient a κ c r)

theorem periodic_positive_logarithmic_derivative_period_zero {a : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (haL : Function.Periodic a L) (hpos : ∀ r, 0 < a r) :
    (∫ r in 0..L, deriv a r / a r) = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp ha).2
  have hc : Continuous (fun r => deriv a r / a r) :=
    hd.continuous.div ha.continuous (fun r => (hpos r).ne')
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => (ha.differentiable (by simp) r).hasDerivAt.log (hpos r).ne')
    (hc.intervalIntegrable 0 L)
  rw [show a L = a 0 from by simpa using haL 0, sub_self] at he
  exact he

theorem fermiSeamSlopeCoefficient_contDiff {a κ c : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ r, 0 < a r) : ContDiff ℝ ∞ (fermiSeamSlopeCoefficient a κ c) :=
  ((contDiff_infty_iff_deriv.mp ha).2.add (hκ.mul hc)).neg.div
    (contDiff_const.mul ha) (fun r => mul_ne_zero (by norm_num) (hpos r).ne')

theorem fermiSeamSlopeCoefficient_period {a κ c : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (haL : Function.Periodic a L)
    (hκ : Continuous κ) (hc : Continuous c) (hpos : ∀ r, 0 < a r) :
    (∫ r in 0..L, fermiSeamSlopeCoefficient a κ c r) =
      -(1 / 2 : ℝ) * ∫ r in 0..L, κ r * c r / a r := by
  have hd := (contDiff_infty_iff_deriv.mp ha).2.continuous
  have hda : Continuous (fun r => deriv a r / a r) :=
    hd.div ha.continuous (fun r => (hpos r).ne')
  have hca : Continuous (fun r => κ r * c r / a r) :=
    (hκ.mul hc).div ha.continuous (fun r => (hpos r).ne')
  have he : fermiSeamSlopeCoefficient a κ c =
      (fun r => -(1 / 2 : ℝ) * (deriv a r / a r + κ r * c r / a r)) := by
    funext r
    simp only [fermiSeamSlopeCoefficient]
    field_simp
    <;> ring
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hda.intervalIntegrable 0 L) (hca.intervalIntegrable 0 L),
    periodic_positive_logarithmic_derivative_period_zero ha haL hpos, zero_add]

theorem fermiSeamSlopeCoefficient_perturbation {a κ c : ℝ → ℝ}
    (hpos : ∀ r, 0 < a r) (ε r : ℝ) :
    fermiSeamSlopeCoefficient a κ (fun s => c s + ε * a s * κ s) r =
      fermiSeamSlopeCoefficient a κ c r - ε / 2 * (κ r)^2 := by
  simp only [fermiSeamSlopeCoefficient]
  field_simp [(hpos r).ne']
  <;> ring

theorem fermiSeamSlopeCoefficient_perturbed_period {a κ c : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ r, 0 < a r) (L ε : ℝ) :
    (∫ r in 0..L, fermiSeamSlopeCoefficient a κ (fun s => c s + ε * a s * κ s) r) =
      (∫ r in 0..L, fermiSeamSlopeCoefficient a κ c r) -
        ε / 2 * ∫ r in 0..L, (κ r)^2 := by
  have he : fermiSeamSlopeCoefficient a κ (fun s => c s + ε * a s * κ s) =
      (fun r => fermiSeamSlopeCoefficient a κ c r - ε / 2 * (κ r)^2) :=
    funext (fermiSeamSlopeCoefficient_perturbation hpos ε)
  rw [he, intervalIntegral.integral_sub
    ((fermiSeamSlopeCoefficient_contDiff ha hκ hc hpos).continuous.intervalIntegrable 0 L)
    (((hκ.pow 2).continuous.const_mul (ε / 2)).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul]

theorem fermiSeamLinearMultiplier_perturbation {a κ c : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ r, 0 < a r) (L ε : ℝ) :
    fermiSeamLinearMultiplier L a κ (fun s => c s + ε * a s * κ s) =
      fermiSeamLinearMultiplier L a κ c *
        Real.exp (-(ε / 2 * ∫ r in 0..L, (κ r)^2)) := by
  unfold fermiSeamLinearMultiplier
  rw [fermiSeamSlopeCoefficient_perturbed_period ha hκ hc hpos L ε, sub_eq_add_neg, Real.exp_add]

end
end TightVer401
