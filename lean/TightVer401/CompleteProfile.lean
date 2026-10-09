import TightVer401.CompleteProfileAcceleration
import TightVer401.CompleteProfilePrimitive

namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's convex radial continuation, with full germ agreement. -/
theorem exists_completeProfile {H β : ℝ} {q₀ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : H ∈ U) (hq₀ : ContDiffOn ℝ ∞ q₀ U)
    (hvalue : 0 < q₀ H) (hslope : 0 < deriv q₀ H)
    (hconvex : ∀ z ∈ U, 0 < deriv (deriv q₀) z) (hβ : 0 < β) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧ q =ᶠ[𝓝 H] q₀ ∧
      (∀ z ∈ Ici H, 0 < q z ∧ 0 < deriv q z ∧ 0 < deriv (deriv q) z) ∧
      (∀ᶠ z in atTop, deriv (deriv q) z = β) ∧ Tendsto (deriv q) atTop atTop := by
  have hq₁ : ContDiffOn ℝ ∞ (deriv q₀) U := hq₀.deriv_of_isOpen hU (by simp)
  have hq₂ : ContDiffOn ℝ ∞ (deriv (deriv q₀)) U := hq₁.deriv_of_isOpen hU (by simp)
  obtain ⟨b, hb, hbpos, hbgerm, hbtail⟩ := exists_completeProfile_acceleration hU hH hq₂ hconvex hβ
  let v := completeProfilePrimitive H (deriv q₀ H) b
  have hv : ContDiff ℝ ∞ v := completeProfilePrimitive_contDiff H _ hb
  have hvder : deriv v = b := completeProfilePrimitive_deriv H _ hb.continuous
  have hvpos : ∀ z ∈ Ici H, 0 < v z :=
    completeProfilePrimitive_pos hb.continuous (fun z _ => hbpos z) hslope
  have hvgerm : v =ᶠ[𝓝 H] deriv q₀ := completeProfilePrimitive_germ hU hH hq₁ hb.continuous hbgerm
  let q := completeProfilePrimitive H (q₀ H) v
  have hq : ContDiff ℝ ∞ q := completeProfilePrimitive_contDiff H _ hv
  have hqder : deriv q = v := completeProfilePrimitive_deriv H _ hv.continuous
  have hqsecond : deriv (deriv q) = b := by rw [hqder, hvder]
  refine ⟨q, hq, completeProfilePrimitive_germ hU hH hq₀ hv.continuous hvgerm, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨completeProfilePrimitive_pos hv.continuous hvpos hvalue z hz, ?_, ?_⟩
    · rw [hqder]
      exact hvpos z hz
    · rw [hqsecond]
      exact hbpos z
  · simpa only [hqsecond] using hbtail
  · rw [hqder]
    exact completeProfilePrimitive_tendsto hb.continuous hβ hbtail

end
end TightVer401
