import TightVer401.NormalLoopNonconstant

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem periodic_monotone_eq {f : ℝ → ℝ} {L : ℝ}
    (hperiod : Function.Periodic f L) (hL : 0 < L) (hmono : Monotone f)
    (x y : ℝ) : f x = f y := by
  have hle (x y : ℝ) : f y ≤ f x := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((y - x) / L)
    have hs : y ≤ x + (n : ℝ) * L := by
      have ht := (div_lt_iff₀ hL).mp hn
      linarith
    have hp := hperiod.nat_mul n x
    have hm := hmono hs
    rwa [hp] at hm
  exact le_antisymm (hle y x) (hle x y)

theorem periodic_nonconstant_derivative_signs {f : ℝ → ℝ} {L : ℝ}
    (hf : Differentiable ℝ f) (hperiod : Function.Periodic f L) (hL : 0 < L)
    (hnonconst : ∃ r, f r ≠ f 0) :
    (∃ r, 0 < deriv f r) ∧ (∃ r, deriv f r < 0) := by
  obtain ⟨r, hr⟩ := hnonconst
  constructor
  · by_contra h
    push Not at h
    have hanti := antitone_of_deriv_nonpos hf h
    have hp : Function.Periodic (fun x => -f x) L := fun x => congrArg Neg.neg (hperiod x)
    have he := periodic_monotone_eq hp hL hanti.neg r 0
    exact hr (neg_injective he)
  · by_contra h
    push Not at h
    have hmono := monotone_of_deriv_nonneg hf h
    exact hr (periodic_monotone_eq hperiod hL hmono r 0)

theorem normalLoop_closed_curvature_derivative_signs {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)
    (hζL : Function.Periodic ζ L) (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :
    (∃ r, 0 < deriv (normalLoopCurvature ζ) r) ∧
      (∃ r, deriv (normalLoopCurvature ζ) r < 0) := by
  exact periodic_nonconstant_derivative_signs
    ((normalLoop_actual_smooth hζ).2.differentiable (by simp))
    (normalLoop_actual_periodic hζ hζL).2 hL
    (normalLoop_closure_forces_nonconstant_curvature hζ ha hunit hspeed hpos hL hmoment)

end
end TightVer401
