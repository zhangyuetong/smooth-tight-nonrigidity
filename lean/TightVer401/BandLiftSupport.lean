import TightVer401.BandCoordinateLift
import TightVer401.BandSupportBounds

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

theorem bandCoordinateLift_periodic {L b : ℝ}
    (Y : AddCircle L × Ioo (0 : ℝ) b → Ambient) (u : ℝ) :
    Function.Periodic (fun s => bandCoordinateLift Y (![s, u] : Coord)) L := by
  intro s
  have he : periodProjection L (s + L) = periodProjection L s := AddCircle.coe_add_period L s
  simp [bandCoordinateLift, he]

theorem bandCoordinateLift_zero_outside_bounds {L b lower upper : ℝ}
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ upper)
    (p : Coord) (hp : p 1 < lower ∨ upper < p 1) : bandCoordinateLift Y p = 0 := by
  by_cases hb : p 1 ∈ Ioo 0 b
  · rw [bandCoordinateLift, dif_pos hb]
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hh := hsupport (periodProjection L (p 0), ⟨p 1, hb⟩) hs
    rcases hp with hlo | hhi
    · exact (not_le.mpr hlo) hh.1
    · exact (not_le.mpr hhi) hh.2
  · exact dif_neg hb

theorem bandCoordinateLift_support_bounds {L b lower upper : ℝ}
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ upper) :
    tsupport (bandCoordinateLift Y) ⊆ {p : Coord | p 1 ∈ Icc lower upper} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 1))
  intro p hp
  by_contra hn
  have hh : p 1 < lower ∨ upper < p 1 := by
    simpa only [mem_preimage, mem_Icc, not_and_or, not_le] using hn
  exact hp (bandCoordinateLift_zero_outside_bounds hsupport p hh)

end
end TightVer401
