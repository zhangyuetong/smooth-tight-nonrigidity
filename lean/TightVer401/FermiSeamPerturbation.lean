import TightVer401.FermiProductJets
import TightVer401.FermiSupportLocalSeam

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set Filter
open scoped ContDiff Matrix Topology
set_option backward.isDefEq.respectTransparency false

theorem fermiSupport_add {H J : Coord → ℝ} (hH : ContDiff ℝ ∞ H)
    (hJ : ContDiff ℝ ∞ J) (κ : ℝ → ℝ) (p : Coord) :
    fermiSupportL κ (fun q => H q + J q) p = fermiSupportL κ H p + fermiSupportL κ J p ∧
    fermiSupportM κ (fun q => H q + J q) p = fermiSupportM κ H p + fermiSupportM κ J p ∧
    fermiSupportN (fun q => H q + J q) p = fermiSupportN H p + fermiSupportN J p := by
  have h1 (i : Fin 2) : coordPartial i (fun q => H q + J q) =
      (fun q => coordPartial i H q + coordPartial i J q) := by
    funext q
    exact coordPartial_scalar_add (hH.differentiable (by simp) q) (hJ.differentiable (by simp) q) i
  have h2 (i j : Fin 2) : coordPartial i (coordPartial j (fun q => H q + J q)) p =
      coordPartial i (coordPartial j H) p + coordPartial i (coordPartial j J) p := by
    rw [h1 j]
    exact coordPartial_scalar_add
      ((fermiCoordinatePartial_contDiff hH j).differentiable (by simp) p)
      ((fermiCoordinatePartial_contDiff hJ j).differentiable (by simp) p) i
  simp only [fermiSupportL, fermiSupportM, fermiSupportN]
  rw [h2 0 0, h2 0 1, h2 1 1, h1 0, h1 1]
  constructor
  · ring
  · constructor <;> ring

theorem fermiSupport_local_add {H J : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) (hJ : ContDiff ℝ ∞ J)
    (κ : ℝ → ℝ) {p : Coord} (hp : p ∈ U) :
    fermiSupportL κ (fun q => H q + J q) p = fermiSupportL κ H p + fermiSupportL κ J p ∧
    fermiSupportM κ (fun q => H q + J q) p = fermiSupportM κ H p + fermiSupportM κ J p ∧
    fermiSupportN (fun q => H q + J q) p = fermiSupportN H p + fermiSupportN J p := by
  obtain ⟨G, hG, he⟩ := exists_smooth_coordinate_germ_extension hU hH hp
  have hsum : (fun q => G q + J q) =ᶠ[𝓝 p] (fun q => H q + J q) := by
    filter_upwards [he] with q hq
    rw [hq]
  have hc := fermiSupport_eventuallyEq he κ
  have hcs := fermiSupport_eventuallyEq hsum κ
  rw [← hc.1.eq_of_nhds, ← hc.2.1.eq_of_nhds, ← hc.2.2.eq_of_nhds,
    ← hcs.1.eq_of_nhds, ← hcs.2.1.eq_of_nhds, ← hcs.2.2.eq_of_nhds]
  exact fermiSupport_add hG hJ κ p

def fermiSeamPerturbation (ε : ℝ) (a κ χ : ℝ → ℝ) (p : Coord) : ℝ :=
  fermiProduct (fun r => ε / 2 * a r * κ r) (fermiQuadraticCutoff χ) p

theorem fermiSeamPerturbation_contDiff {a κ χ : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (ε : ℝ) :
    ContDiff ℝ ∞ (fermiSeamPerturbation ε a κ χ) :=
  fermiProduct_contDiff ((contDiff_const.mul ha).mul hκ) (fermiQuadraticCutoff_contDiff hχ)

theorem fermiSeamPerturbation_jets {a κ χ : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1) (ε r : ℝ) :
    fermiSeamPerturbation ε a κ χ ![r,0] = 0 ∧
    coordPartial 0 (fermiSeamPerturbation ε a κ χ) ![r,0] = 0 ∧
    coordPartial 1 (fermiSeamPerturbation ε a κ χ) ![r,0] = 0 ∧
    coordPartial 0 (coordPartial 0 (fermiSeamPerturbation ε a κ χ)) ![r,0] = 0 ∧
    coordPartial 0 (coordPartial 1 (fermiSeamPerturbation ε a κ χ)) ![r,0] = 0 ∧
    coordPartial 1 (coordPartial 1 (fermiSeamPerturbation ε a κ χ)) ![r,0] =
      ε * a r * κ r := by
  have hj := fermiProduct_quadraticCutoff_seam
    (A := fun r => ε / 2 * a r * κ r) ((contDiff_const.mul ha).mul hκ) hχ r
  simp only [hχ0, mul_one] at hj
  change fermiSeamPerturbation ε a κ χ ![r,0] = 0 ∧
    coordPartial 0 (fermiSeamPerturbation ε a κ χ) ![r,0] = 0 ∧
    coordPartial 1 (fermiSeamPerturbation ε a κ χ) ![r,0] = 0 ∧
    coordPartial 0 (coordPartial 0 (fermiSeamPerturbation ε a κ χ)) ![r,0] = 0 ∧
    coordPartial 0 (coordPartial 1 (fermiSeamPerturbation ε a κ χ)) ![r,0] = 0 ∧
    coordPartial 1 (coordPartial 1 (fermiSeamPerturbation ε a κ χ)) ![r,0] =
      2 * (ε / 2 * a r * κ r) at hj
  exact ⟨hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1,
    hj.2.2.2.2.2.trans (by ring)⟩

theorem fermiSeamPerturbation_support_jets {a κ χ : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1) (ε r : ℝ) :
    fermiSupportL κ (fermiSeamPerturbation ε a κ χ) ![r,0] = 0 ∧
    fermiSupportM κ (fermiSeamPerturbation ε a κ χ) ![r,0] = 0 ∧
    fermiSupportN (fermiSeamPerturbation ε a κ χ) ![r,0] = ε * a r * κ r := by
  have hj := fermiSeamPerturbation_jets ha hκ hχ hχ0 ε r
  rw [(fermiSupport_seam_values hκ _ r).1, (fermiSupport_seam_values hκ _ r).2]
  simp only [fermiSupportN, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1,
    hj.2.2.2.2.1, hj.2.2.2.2.2, mul_zero, add_zero, sub_zero]
  trivial

theorem fermiSeamPerturbation_preserves_support_seam {a κ χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord} (ha : ContDiff ℝ ∞ a)
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) (ε : ℝ) {r : ℝ}
    (hr : (![r,0] : Coord) ∈ U) :
    fermiSupportL κ (fun p => H p + fermiSeamPerturbation ε a κ χ p) ![r,0] =
      fermiSupportL κ H ![r,0] ∧
    fermiSupportM κ (fun p => H p + fermiSeamPerturbation ε a κ χ p) ![r,0] =
      fermiSupportM κ H ![r,0] ∧
    fermiSupportN (fun p => H p + fermiSeamPerturbation ε a κ χ p) ![r,0] =
      fermiSupportN H ![r,0] + ε * a r * κ r := by
  have hs := fermiSupport_local_add hU hH (fermiSeamPerturbation_contDiff ha hκ hχ ε) κ hr
  have hj := fermiSeamPerturbation_support_jets ha hκ hχ hχ0 ε r
  rw [hs.1, hs.2.1, hs.2.2, hj.1, hj.2.1, hj.2.2]
  simp

end
end TightVer401
