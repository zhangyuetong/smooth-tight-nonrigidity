import TightVer401.RuledIntegratingFactor
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

/-! Periodic primitives of the actual characteristic coefficient, constructed
by the OpenAI integration operator. The period L is arbitrary. -/
namespace TightVer401
noncomputable section
open MeasureTheory
open scoped ContDiff
open OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false

theorem smooth_periodic_primitive_iff {f : ℝ → ℝ} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L) :
    (∫ s in 0..L, f s) = 0 ↔
      ∃ W : ℝ → ℝ, ContDiff ℝ ∞ W ∧ Function.Periodic W L ∧
        ∀ s, HasDerivAt W (f s) s := by
  constructor
  · intro hmean
    refine ⟨rawPrimitive f, rawPrimitive_contDiff hf, ?_, rawPrimitive_hasDerivAt hf.continuous⟩
    intro s
    unfold rawPrimitive
    rw [hp.intervalIntegral_add_eq_add 0 s (fun a b => hf.continuous.intervalIntegrable a b)]
    simp only [zero_add, hmean, add_zero]
  · rintro ⟨W, _, hWp, hW⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hW s)
      (hf.continuous.intervalIntegrable 0 L)]
    simpa only [zero_add, sub_self] using congrArg (fun v => v - W 0) (hWp 0)

theorem ruledRho_contDiff {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ)
    (hne : ∀ s, τ s ≠ 0) : ContDiff ℝ ∞ (ruledRho τ) :=
  (hτ.abs hne).sqrt (fun s => ne_of_gt (abs_pos.mpr (hne s)))

def ruledLambda (τ : ℝ → ℝ) : ℝ → ℝ := fun s => deriv τ s / τ s

def ruledD (k τ : ℝ → ℝ) : ℝ → ℝ := fun s => deriv k s - k s * ruledLambda τ s

def ruledPeriodCoefficient (k τ : ℝ → ℝ) : ℝ → ℝ :=
  fun s => ruledD k τ s / (2 * ruledRho τ s)

theorem ruledPeriodCoefficient_contDiff {k τ : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hne : ∀ s, τ s ≠ 0) :
    ContDiff ℝ ∞ (ruledPeriodCoefficient k τ) := by
  have hkd := (contDiff_infty_iff_deriv.mp hk).2
  have hτd := (contDiff_infty_iff_deriv.mp hτ).2
  exact (hkd.sub (hk.mul (hτd.div hτ hne))).div
    (contDiff_const.mul (ruledRho_contDiff hτ hne))
    (fun s => mul_ne_zero (by norm_num) (ne_of_gt (ruledRho_pos (hne s))))

theorem deriv_periodic {f : ℝ → ℝ} {L : ℝ} (hp : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hp
  have hd := congrArg (fun g : ℝ → ℝ => deriv g s) he
  simpa only [deriv_comp_add_const] using hd

theorem ruledPeriodCoefficient_periodic {k τ : ℝ → ℝ} {L : ℝ}
    (hk : Function.Periodic k L) (hτ : Function.Periodic τ L) :
    Function.Periodic (ruledPeriodCoefficient k τ) L := by
  intro s
  simp only [ruledPeriodCoefficient, ruledD, ruledLambda, deriv_periodic hk s,
    deriv_periodic hτ s, hk s, hτ s, ruledRho_periodic hτ s]

theorem ruled_period_zero_iff_periodic_primitive {k τ : ℝ → ℝ} {L : ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hne : ∀ s, τ s ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L) :
    (∫ s in 0..L, ruledPeriodCoefficient k τ s) = 0 ↔
      ∃ W : ℝ → ℝ, ContDiff ℝ ∞ W ∧ Function.Periodic W L ∧
        ∀ s, HasDerivAt W (ruledPeriodCoefficient k τ s) s :=
  smooth_periodic_primitive_iff (ruledPeriodCoefficient_contDiff hk hτ hne)
    (ruledPeriodCoefficient_periodic hkL hτL)

end
end TightVer401
