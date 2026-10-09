import TightVer401.MomentPrescriptionPeriodic
import TightVer401.PeriodicDerivativeSigns
import TightVer401.NormalLoopRuledFrame

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_balance_closing_speed {ζ : ℝ → Ambient} {b : ℝ → ℝ} {L η : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hb : ContDiff ℝ ∞ b)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hbpos : ∀ r, 0 < b r) (hζL : Function.Periodic ζ L) (hbL : Function.Periodic b L)
    (hL : 0 < L) (hmoment : normalLoopMoment b ζ (deriv ζ) L = 0) (hη : 0 < η) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 := by
  letI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨hP, hκ⟩ := normalLoop_actual_smooth hζ
  obtain ⟨hPL, hκL⟩ := normalLoop_actual_periodic hζ hζL
  obtain ⟨hgpos, hgneg⟩ := normalLoop_closed_curvature_derivative_signs
    hζ hb.continuous hunit hspeed hbpos hL hζL hmoment
  obtain ⟨a, ha, haL, hapos, hsmall, hM, hB⟩ := momentPrescription_periodic
    hP (contDiff_infty_iff_deriv.mp hκ).2 hb hPL (deriv_periodic hκL) hbL
    hbpos hgpos hgneg 0 hη
  refine ⟨a, ha, haL, hapos, hsmall, ?_, hB⟩
  have he : normalLoopMoment a ζ (deriv ζ) L = normalLoopMoment b ζ (deriv ζ) L := hM
  exact he.trans hmoment

theorem normalLoop_construct_balanced_frame {ζ : ℝ → Ambient} {b : ℝ → ℝ} {L η : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hb : ContDiff ℝ ∞ b)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hbpos : ∀ r, 0 < b r) (hζL : Function.Periodic ζ L) (hbL : Function.Periodic b L)
    (hL : 0 < L) (hmoment : normalLoopMoment b ζ (deriv ζ) L = 0) (hη : 0 < η) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
        ∃ d : PeriodicRuledFrame (rawPrimitive a L),
          d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
          d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
          d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
          d.τ = normalLoopPhysicalTau a e.symm ∧
          (∫ s in 0..rawPrimitive a L, ruledPeriodCoefficient d.k d.τ s) = 0 := by
  obtain ⟨a, ha, haL, hapos, hsmall, hM, hB⟩ :=
    normalLoop_balance_closing_speed hζ hb hunit hspeed hbpos hζL hbL hL hmoment hη
  obtain ⟨e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ, hperiod⟩ :=
    normalLoop_construct_periodic_ruled_frame hζ ha hunit hspeed hapos hζL haL hL hM
  refine ⟨a, ha, haL, hapos, hsmall, hM, e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ, ?_⟩
  rw [hperiod, hB, mul_zero]

end
end TightVer401
