import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The necessary second derivative condition at a real local maximum.

Only continuity at the maximum is needed: a hypothetically positive second
derivative itself forces a positive first derivative on a right interval.
-/

open Set Filter
open scoped Topology ContDiff

namespace TightVer401

/-- At a continuous local maximum the actual iterated derivative is nonpositive.
The derivative convention at nondifferentiable points is the Mathlib convention.
Continuity at the maximum prevents a discontinuous isolated upward jump. -/
theorem localMax_secondDeriv_nonpos {f : ℝ → ℝ} {a : ℝ}
    (hmax : IsLocalMax f a) (hc : ContinuousAt f a) :
    deriv (deriv f) a ≤ 0 := by
  by_contra hnot
  have hsecond : 0 < deriv (deriv f) a := lt_of_not_ge hnot
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hsecond hmax.deriv_eq_zero
  have hpos : ∀ᶠ x in 𝓝[>] a, 0 < deriv f x :=
    deriv_pos_right_of_sign_deriv (nhdsWithin_le_nhds hsign)
  have hmaxRight : ∀ᶠ x in 𝓝[>] a, f x ≤ f a :=
    nhdsWithin_le_nhds (show ∀ᶠ x in 𝓝 a, f x ≤ f a from hmax)
  obtain ⟨b, hab, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp (hpos.and hmaxRight)
  have hcontinuous : ContinuousOn f (Icc a b) := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      exact hc.continuousWithinAt
    · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      have hd : 0 < deriv f x := (hinterval ⟨hax, hx.2⟩).1
      exact (differentiableAt_of_deriv_ne_zero hd.ne').continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hcontinuous (by
      intro x hx
      rw [interior_Icc] at hx
      exact (hinterval ⟨hx.1, le_of_lt hx.2⟩).1)
  have hlt : f a < f b := hmono ⟨le_rfl, le_of_lt hab⟩ ⟨le_of_lt hab, le_rfl⟩ hab
  have hle : f b ≤ f a := (hinterval ⟨hab, le_rfl⟩).2
  exact (not_lt_of_ge hle) hlt

/-- Smooth functions satisfy the necessary second derivative condition at every
local maximum. -/
theorem smooth_localMax_secondDeriv_nonpos {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ ∞ f) (hmax : IsLocalMax f a) :
    deriv (deriv f) a ≤ 0 :=
  localMax_secondDeriv_nonpos hmax hf.continuous.continuousAt

end TightVer401
