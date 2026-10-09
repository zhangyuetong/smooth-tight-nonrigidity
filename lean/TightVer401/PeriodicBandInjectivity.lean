import TightVer401.PeriodicBandProfile
import TightVer401.RuledProfileBump

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

theorem periodic_bandProfile_nonzero {L b cb c : ℝ}
    {k τ ρ W : ℝ → ℝ} {T E n : ℝ → Ambient} {F : ℝ → ℝ}
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hρL : Function.Periodic ρ L) (hWL : Function.Periodic W L)
    (hTL : Function.Periodic T L) (hnL : Function.Periodic n L)
    (hf : IsOrthonormalFrame (T 0) (E 0) (n 0)) (hτ : τ 0 ≠ 0)
    (hρ : 0 < ρ 0) (hb : 0 < b) (hmax : 1 / (ρ 0 * b) - W 0 ≤ cb)
    (hc : cb < c) (hFc : F c ≠ 0) :
    ∃ p : AddCircle L × Ioo (0 : ℝ) b,
      bandProfile hkL.lift hτL.lift hρL.lift hWL.lift F hTL.lift hnL.lift p ≠ 0 := by
  let u := ruledLeaf ρ W c 0
  have hu : u ∈ Ioo 0 b := ruledLeaf_in_band hρ hb (hmax.trans_lt hc)
  refine ⟨(periodProjection L 0, ⟨u, hu⟩), ?_⟩
  rw [periodic_bandProfile_real_lift]
  have hcw : c + W 0 ≠ 0 := by
    have hi := one_div_pos.mpr (mul_pos hρ hb)
    have hh := hmax.trans_lt hc
    linarith
  have hv : ruledFirstIntegral ρ W (![0, u] : Coord) = c :=
    ruledLeaf_first_integral (ne_of_gt hρ) hcw
  apply ruled_profile_nonzero_of_value (by simpa using hf) (by simpa using hτ)
    (by simpa using ne_of_gt hu.1)
  simpa only [hv] using hFc

theorem periodic_bandProfile_injective {L b cb : ℝ}
    {k τ ρ W : ℝ → ℝ} {T E n : ℝ → Ambient} {F G : ℝ → ℝ}
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hρL : Function.Periodic ρ L) (hWL : Function.Periodic W L)
    (hTL : Function.Periodic T L) (hnL : Function.Periodic n L)
    (hf : IsOrthonormalFrame (T 0) (E 0) (n 0)) (hτ : τ 0 ≠ 0)
    (hρ : 0 < ρ 0) (hb : 0 < b) (hmax : 1 / (ρ 0 * b) - W 0 ≤ cb)
    (hF : tsupport F ⊆ Ioi cb) (hG : tsupport G ⊆ Ioi cb)
    (he : bandProfile hkL.lift hτL.lift hρL.lift hWL.lift F hTL.lift hnL.lift (b := b) =
      bandProfile hkL.lift hτL.lift hρL.lift hWL.lift G hTL.lift hnL.lift (b := b)) : F = G := by
  funext c
  by_cases hc : cb < c
  · apply ruled_profile_unique_at_leaf_level hf hτ hρ hb (hmax.trans_lt hc)
    intro u hu
    have h := congrFun he (periodProjection L 0, ⟨u, hu⟩)
    simpa only [periodic_bandProfile_real_lift] using h
  · have hFn : c ∉ tsupport F := fun h => hc (hF h)
    have hGn : c ∉ tsupport G := fun h => hc (hG h)
    rw [image_eq_zero_of_notMem_tsupport hFn, image_eq_zero_of_notMem_tsupport hGn]

end
end TightVer401
