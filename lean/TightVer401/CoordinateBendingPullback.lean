import TightVer401.BandDifferential

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

theorem zero_strain_all_vectors {X Y : Coord → Ambient} {p : Coord}
    (hstrain : ∀ i j : Fin 2, strain X Y p i j = 0) (v w : Coord) :
    inner ℝ (fderiv ℝ X p v) (fderiv ℝ Y p w) +
      inner ℝ (fderiv ℝ Y p v) (fderiv ℝ X p w) = 0 := by
  have hv (z : Coord) : z = z 0 • Pi.single 0 (1 : ℝ) + z 1 • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  have hd (f : Coord → Ambient) (z : Coord) : fderiv ℝ f p z =
      z 0 • coordPartial 0 f p + z 1 • coordPartial 1 f p := by
    conv_lhs => rw [hv z]
    simp only [map_add, map_smul, coordPartial]
  have h00 := hstrain 0 0
  have h01 := hstrain 0 1
  have h10 := hstrain 1 0
  have h11 := hstrain 1 1
  simp only [strain] at h00 h01 h10 h11
  rw [hd X v, hd Y w, hd Y v, hd X w]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  calc
    _ = v 0 * w 0 * (inner ℝ (coordPartial 0 X p) (coordPartial 0 Y p) +
          inner ℝ (coordPartial 0 Y p) (coordPartial 0 X p)) +
        v 0 * w 1 * (inner ℝ (coordPartial 0 X p) (coordPartial 1 Y p) +
          inner ℝ (coordPartial 0 Y p) (coordPartial 1 X p)) +
        v 1 * w 0 * (inner ℝ (coordPartial 1 X p) (coordPartial 0 Y p) +
          inner ℝ (coordPartial 1 Y p) (coordPartial 0 X p)) +
        v 1 * w 1 * (inner ℝ (coordPartial 1 X p) (coordPartial 1 Y p) +
          inner ℝ (coordPartial 1 Y p) (coordPartial 1 X p)) := by ring
    _ = 0 := by rw [h00, h01, h10, h11]; ring

def realBandCoordinates (b : ℝ) : ℝ × Set.Ioo (0 : ℝ) b → Coord :=
  fun p => ![p.1, (p.2 : ℝ)]

theorem realBandCoordinates_contMDiff (b : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) ∞ (realBandCoordinates b) := by
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact contMDiff_fst
  · exact (contMDiff_subtype_val (U := bandOpen b)).comp contMDiff_snd

theorem realBand_zero_strain_pullback {b : ℝ} {X Y : Coord → Ambient}
    (p : ℝ × Set.Ioo (0 : ℝ) b)
    (hX : DifferentiableAt ℝ X (realBandCoordinates b p))
    (hY : DifferentiableAt ℝ Y (realBandCoordinates b p))
    (hstrain : ∀ i j : Fin 2, strain X Y (realBandCoordinates b p) i j = 0)
    (v w : ℝ × ℝ) :
    inner ℝ (bandDifferential (X ∘ realBandCoordinates b) p v)
      (bandDifferential (Y ∘ realBandCoordinates b) p w) +
    inner ℝ (bandDifferential (Y ∘ realBandCoordinates b) p v)
      (bandDifferential (X ∘ realBandCoordinates b) p w) = 0 := by
  have hc := (realBandCoordinates_contMDiff b p).mdifferentiableAt (by simp)
  have hx : bandDifferential (X ∘ realBandCoordinates b) p =
      (fderiv ℝ X (realBandCoordinates b p)).comp
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) (realBandCoordinates b) p) :=
    (hX.hasFDerivAt.hasMFDerivAt.comp p hc.hasMFDerivAt).mfderiv
  have hy : bandDifferential (Y ∘ realBandCoordinates b) p =
      (fderiv ℝ Y (realBandCoordinates b p)).comp
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) (realBandCoordinates b) p) :=
    (hY.hasFDerivAt.hasMFDerivAt.comp p hc.hasMFDerivAt).mfderiv
  rw [hx, hy]
  exact zero_strain_all_vectors hstrain _ _

end
end TightVer401
