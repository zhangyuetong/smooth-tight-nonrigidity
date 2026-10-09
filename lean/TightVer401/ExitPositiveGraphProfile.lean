import TightVer401.RuledPrimitives

namespace TightVer401
noncomputable section
open MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def exitGraphMean (P : ℝ) (b : ℝ → ℝ) : ℝ := (∫ r in 0..P, b r) / P

def exitPositiveGraphProfile (P : ℝ) (b : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.exp (rawPrimitive (fun s => b s - exitGraphMean P b) r)

theorem exitGraph_mean_zero {P : ℝ} {b : ℝ → ℝ}
    (hP : 0 < P) (hb : Continuous b) :
    (∫ r in 0..P, b r - exitGraphMean P b) = 0 := by
  rw [intervalIntegral.integral_sub (hb.intervalIntegrable 0 P) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, exitGraphMean]
  field_simp [ne_of_gt hP]
  ring

theorem exitPositiveGraphProfile_contDiff {P : ℝ} {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (exitPositiveGraphProfile P b) :=
  Real.contDiff_exp.comp (rawPrimitive_contDiff (hb.sub contDiff_const))

theorem exitPositiveGraphProfile_pos (P : ℝ) (b : ℝ → ℝ) (r : ℝ) :
    0 < exitPositiveGraphProfile P b r := Real.exp_pos _

theorem exitPositiveGraphProfile_hasDerivAt {P : ℝ} {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (r : ℝ) :
    HasDerivAt (exitPositiveGraphProfile P b)
      ((b r - exitGraphMean P b) * exitPositiveGraphProfile P b r) r := by
  convert! (rawPrimitive_hasDerivAt (hb.continuous.sub continuous_const) r).exp using 1
  change (b r - exitGraphMean P b) *
    Real.exp (rawPrimitive (fun s => b s - exitGraphMean P b) r) =
    Real.exp (rawPrimitive (fun s => b s - exitGraphMean P b) r) *
      (b r - exitGraphMean P b)
  exact mul_comm _ _

theorem exitPositiveGraphProfile_deriv {P : ℝ} {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (r : ℝ) :
    deriv (exitPositiveGraphProfile P b) r =
      (b r - exitGraphMean P b) * exitPositiveGraphProfile P b r :=
  (exitPositiveGraphProfile_hasDerivAt hb r).deriv

theorem exitPositiveGraphProfile_periodic {P : ℝ} {b : ℝ → ℝ}
    (hP : 0 < P) (hb : ContDiff ℝ ∞ b) (hp : Function.Periodic b P) :
    Function.Periodic (exitPositiveGraphProfile P b) P := by
  have hperiod : Function.Periodic (fun r => b r - exitGraphMean P b) P := by
    intro r
    simp only [hp r]
  have hraw : Function.Periodic (rawPrimitive (fun r => b r - exitGraphMean P b)) P := by
    intro r
    unfold rawPrimitive
    rw [hperiod.intervalIntegral_add_eq_add 0 r
      (fun a c => (hb.continuous.sub continuous_const).intervalIntegrable a c)]
    simp only [zero_add, exitGraph_mean_zero hP hb.continuous, add_zero]
  intro r
  exact congrArg Real.exp (hraw r)

theorem exists_exitPositiveGraphProfile {P : ℝ} {b : ℝ → ℝ}
    (hP : 0 < P) (hb : ContDiff ℝ ∞ b) (hp : Function.Periodic b P) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v P ∧
      (∀ r, 0 < v r) ∧
      ∀ r, HasDerivAt v ((b r - exitGraphMean P b) * v r) r :=
  ⟨exitPositiveGraphProfile P b, exitPositiveGraphProfile_contDiff hb,
    exitPositiveGraphProfile_periodic hP hb hp, exitPositiveGraphProfile_pos P b,
    exitPositiveGraphProfile_hasDerivAt hb⟩

end
end TightVer401
