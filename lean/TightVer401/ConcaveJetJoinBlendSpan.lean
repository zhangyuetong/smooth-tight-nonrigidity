import TightVer401.ConcaveJetJoinBlend
import TightVer401.MomentControlCoefficients

namespace TightVer401
noncomputable section
open Set MeasureTheory

theorem concaveJetJoinBlendError_moment_mem_span {m : ℕ} {c r A B : ℝ} (hr : 0 < r)
    (hL hR : ℝ → ℝ) (f : ℝ → EuclideanSpace ℝ (Fin m))
    (hleft : A ≤ c - r) (hright : c + r ≤ B) :
    (∫ x in A..B, concaveJetJoinBlendError c r hL hR x • f x) ∈ momentSampleSpan f (Ioo A B) := by
  have hs : Function.support (concaveJetJoinBlendError c r hL hR) ⊆ Ioo A B := by
    intro x hx
    have hx' := concaveJetJoinBlendError_support hr hL hR hx
    exact ⟨hleft.trans_lt hx'.1, hx'.2.trans_le hright⟩
  have he : (∫ x in A..B, concaveJetJoinBlendError c r hL hR x • f x) =
      realControlMoment f (concaveJetJoinBlendError c r hL hR) := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have herr : concaveJetJoinBlendError c r hL hR x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact Ioo_subset_Ioc_self (hs herr)
  rw [he]
  exact realControlMoment_mem_span hs

end
end TightVer401
