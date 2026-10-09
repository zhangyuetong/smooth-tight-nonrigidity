import TightVer401.PeriodicRuledBending
import TightVer401.CoordinateBandExtension

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

def coordinateBandOpen (b : ℝ) : TopologicalSpace.Opens Coord :=
  ⟨{p : Coord | p 1 ∈ Ioo 0 b}, isOpen_Ioo.preimage (continuous_apply 1)⟩

def bandFromCoordinates (L b : ℝ) : coordinateBandOpen b → AddCircle L × Ioo (0 : ℝ) b :=
  fun p => (periodProjection L (p.val 0), ⟨p.val 1, p.property⟩)

theorem bandFromCoordinates_contMDiff (L b : ℝ) [Fact (0 < L)] :
    ContMDiff 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (bandFromCoordinates L b) := by
  have hv : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Coord) ∞
      (Subtype.val : coordinateBandOpen b → Coord) := contMDiff_subtype_val
  have hs := (contDiff_apply ℝ ℝ (0 : Fin 2)).contMDiff.comp hv
  have hu := (contDiff_apply ℝ ℝ (1 : Fin 2)).contMDiff.comp hv
  have hui : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞
      (fun p : coordinateBandOpen b => (⟨p.val 1, p.property⟩ : bandOpen b)) :=
    (ContMDiff.subtypeVal_comp_iff (bandOpen b) _).mp hu
  exact ((periodProjection_contMDiff L).comp hs).prodMk hui

def bandCoordinateLift {L b : ℝ} (Y : AddCircle L × Ioo (0 : ℝ) b → Ambient) : Coord → Ambient :=
  fun p => if h : p 1 ∈ Ioo 0 b then Y (periodProjection L (p 0), ⟨p 1, h⟩) else 0

theorem bandCoordinateLift_contDiffOn {L b : ℝ} [Fact (0 < L)]
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ Y) :
    ContDiffOn ℝ ∞ (bandCoordinateLift Y) {p : Coord | p 1 ∈ Ioo 0 b} := by
  have hg := hY.comp (bandFromCoordinates_contMDiff L b)
  have he : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞
      (fun p : coordinateBandOpen b => bandCoordinateLift Y p.val) := by
    apply hg.congr
    intro p
    exact dif_pos p.property
  intro p hp
  exact (contMDiffAt_subtype_iff.mp (he (⟨p, hp⟩ : coordinateBandOpen b))).contDiffAt.contDiffWithinAt

theorem bandCoordinateLift_contDiff {L b lower upper : ℝ} [Fact (0 < L)]
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ Y)
    (hlower : 0 < lower) (hupper : upper < b)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ upper) :
    ContDiff ℝ ∞ (bandCoordinateLift Y) := by
  have hz : ∀ p : Coord, p 1 ∈ Ioo 0 b → p 1 < lower ∨ upper < p 1 → bandCoordinateLift Y p = 0 := by
    intro p hp hout
    rw [bandCoordinateLift, dif_pos hp]
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hh := hsupport (periodProjection L (p 0), ⟨p 1, hp⟩) hs
    rcases hout with hlo | hhi
    · exact (not_le.mpr hlo) hh.1
    · exact (not_le.mpr hhi) hh.2
  have he : coordinateBandExtension b (bandCoordinateLift Y) = bandCoordinateLift Y := by
    funext p
    by_cases hp : p 1 ∈ Ioo 0 b <;> simp only [coordinateBandExtension, bandCoordinateLift, hp, if_true, if_false, dite_true, dite_false]
  rw [← he]
  exact coordinateBandExtension_contDiff hlower hupper (bandCoordinateLift_contDiffOn hY) hz

end
end TightVer401
