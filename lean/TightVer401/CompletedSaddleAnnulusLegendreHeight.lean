import TightVer401.PlanarLegendre
import TightVer401.CompletedSaddleAnnulusHeight

/-! Actual interior support graph height and its actual nonvanishing derivative.
Boundary resolution remains a distinct radial-germ construction. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def completedSaddleAnnulusGraphHeight (G : Coord → ℝ)
    (e : OpenPartialHomeomorph Coord Coord) (y : Coord) : ℝ :=
  -planarLegendre G e y

theorem completedSaddleAnnulusGraphHeight_contDiffOn {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (completedSaddleAnnulusGraphHeight G e) e.target :=
  (planarLegendre_contDiffOn e hG hi).neg

theorem completedSaddleAnnulusGraphHeight_support {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {y : Coord} (hy : y ∈ e.target) :
    completedSaddleAnnulusGraphHeight G e y = planarSupportMap G (e.symm y) 2 := by
  have hg : planarGradient G (e.symm y) = y :=
    (heG _ (e.map_target hy)).symm.trans (e.right_inv hy)
  have h0 : coordPartial 0 G (e.symm y) = y 0 := congrFun hg 0
  have h1 : coordPartial 1 G (e.symm y) = y 1 := congrFun hg 1
  change -(e.symm y ⬝ᵥ y - G (e.symm y)) =
    G (e.symm y) - e.symm y 0 * coordPartial 0 G (e.symm y) -
      e.symm y 1 * coordPartial 1 G (e.symm y)
  rw [h0,h1]
  simp only [dotProduct, Fin.sum_univ_two]
  ring

theorem completedSaddleAnnulusGraphHeight_gradient {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {y : Coord} (hy : y ∈ e.target) :
    planarGradient (completedSaddleAnnulusGraphHeight G e) y = -e.symm y := by
  have hd := ((planarLegendre_contDiffOn e hG hi y hy).contDiffAt
    (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  ext i
  change fderiv ℝ (-planarLegendre G e) y (Pi.single i 1) = -e.symm y i
  rw [(hd.hasFDerivAt.neg).fderiv]
  simp only [ContinuousLinearMap.neg_apply]
  change -coordPartial i (planarLegendre G e) y = -e.symm y i
  rw [planarLegendre_coordPartial e hG hi heG hy]

theorem completedSaddleAnnulusGraphHeight_fderiv_ne_zero {G : Coord → ℝ}
    (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hPuncture : ∀ p ∈ e.source, 0 < planarRadius p)
    {y : Coord} (hy : y ∈ e.target) :
    fderiv ℝ (completedSaddleAnnulusGraphHeight G e) y ≠ 0 := by
  intro hz
  have hg : planarGradient (completedSaddleAnnulusGraphHeight G e) y = 0 := by
    ext i
    change fderiv ℝ (completedSaddleAnnulusGraphHeight G e) y (Pi.single i 1) = 0
    rw [hz]
    rfl
  rw [completedSaddleAnnulusGraphHeight_gradient e hG hi heG hy] at hg
  have hp : e.symm y = 0 := neg_eq_zero.mp hg
  have hpos := hPuncture (e.symm y) (e.map_target hy)
  rw [hp] at hpos
  simpa [planarRadius] using hpos

end
end TightVer401
