import TightVer401.NormalLoopInterior
import TightVer401.NormalLoopPositiveClosure
import TightVer401.NormalLoopPrescription

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set MeasureTheory
open scoped ContDiff

/-- Manuscript condition (ii), using the actual normal-loop tangent moment. -/
def NormalLoopClosingSpeed (ζ : ℝ → Ambient) (L : ℝ) : Prop :=
  ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧
    (∀ r, 0 < b r) ∧ normalLoopMoment b ζ (deriv ζ) L = 0

/-- Manuscript condition (iii), with the actual derivative of geodesic curvature. -/
def NormalLoopBalancedSpeed (ζ : ℝ → Ambient) (L : ℝ) : Prop :=
  ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧
    (∀ r, 0 < a r) ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
    (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0

theorem normalLoop_existence_criterion {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) (hL : 0 < L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) :
    ((0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ))) ↔
      NormalLoopClosingSpeed ζ L) ∧
    (NormalLoopClosingSpeed ζ L ↔ NormalLoopBalancedSpeed ζ L) ∧
    ((0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ))) ↔
      NormalLoopBalancedSpeed ζ L) := by
  have h₁₂ : (0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ))) ↔
      NormalLoopClosingSpeed ζ L := by
    constructor
    · exact normalLoop_origin_interior_positive_closing_speed hζ hζL hL
    · rintro ⟨b, hb, _hbL, hbpos, hM⟩
      exact normalLoop_closure_convex_interior hζ hb.continuous hunit hspeed hbpos hL hζL hM
  have h₂₃ : NormalLoopClosingSpeed ζ L ↔ NormalLoopBalancedSpeed ζ L := by
    constructor
    · rintro ⟨b, hb, hbL, hbpos, hM⟩
      obtain ⟨a, ha, haL, hapos, _hsmall, hMa, hBa⟩ :=
        normalLoop_balance_closing_speed hζ hb hunit hspeed hbpos hζL hbL hL hM
          (show 0 < (1 : ℝ) by norm_num)
      exact ⟨a, ha, haL, hapos, hMa, hBa⟩
    · rintro ⟨a, ha, haL, hapos, hM, _hB⟩
      exact ⟨a, ha, haL, hapos, hM⟩
  exact ⟨h₁₂, h₂₃, h₁₂.trans h₂₃⟩

theorem normalLoop_existence_criterion_arbitrarily_close {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) (hL : 0 < L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hbL : Function.Periodic b L)
    (hbpos : ∀ r, 0 < b r) (hM : normalLoopMoment b ζ (deriv ζ) L = 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 ∧
      (∫ r in 0..L, ‖a r - b r‖) < η := by
  obtain ⟨a, ha, haL, hapos, hsmall, hMa, hBa⟩ :=
    normalLoop_balance_closing_speed hζ hb hunit hspeed hbpos hζL hbL hL hM hη
  exact ⟨a, ha, haL, hapos, hMa, hBa, hsmall⟩

end
end TightVer401
