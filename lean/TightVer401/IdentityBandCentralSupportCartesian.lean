import TightVer401.IdentityBandCentralSupportCompatibility
import TightVer401.GaussMapDifferential

/-! Actual Hessian correspondence for the global Cartesian support potential.
This transports raw ruled-frame pairings through actual Gauss coordinates. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Actual support/normal derivatives pair by the Cartesian Hessian with its
positive gnomonic weight. -/
theorem identityBand_cartesian_support_pairing {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (v w : Coord) :
    inner ℝ (fderiv ℝ (planarSupportMap G) p v) (fderiv ℝ planarUnitNormal p w) =
      dotProduct v ((planarHessian G p).mulVec w) / planarWeight p := by
  have hX := planarSupportMap_contDiffOn hG hU
  have hn : ∀ q ∈ U, IsUnitNormalAt (planarSupportMap G) (planarUnitNormal q) q :=
    fun q hq => planarSupportMap_isUnitNormal hG hU hq
  have hpair (i j : Fin 2) :
      inner ℝ (coordPartial i (planarSupportMap G) p) (coordPartial j planarUnitNormal p) =
        planarHessian G p i j / planarWeight p := by
    rw [real_inner_comm, gaussMap_partial_pairing hX gnomonicNormal_contDiff.contDiffOn hU hn hp,
      planarSupportMap_secondFundamental hG hU hp]
    simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, neg_neg]
    rw [planarHessian_symm hG hU hp j i]
    ring
  rw [fderiv_two_coordinates, fderiv_two_coordinates,
    inner_add_left, inner_add_right, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Actual reconstruction on an open raw-coordinate neighborhood gives the
full Hessian pullback, with both first derivative chain rules justified by
neighborhood equality. No tensor correspondence is assumed. -/
theorem identityBand_cartesian_pullback_pairing {G : Coord → ℝ} {U V : Set Coord}
    {X N : Coord → Ambient} {P : Coord → Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hPU : MapsTo P V U)
    (hrec : EqOn (planarSupportMap G ∘ P) X V)
    (hnorm : EqOn (planarUnitNormal ∘ P) N V)
    {p : Coord} (hp : p ∈ V) (v w : Coord) :
    inner ℝ (fderiv ℝ X p v) (fderiv ℝ N p w) =
      dotProduct (fderiv ℝ P p v)
        ((planarHessian G (P p)).mulVec (fderiv ℝ P p w)) / planarWeight (P p) := by
  have hdP := ((hP p hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hdX := (((planarSupportMap_contDiffOn hG hU) (P p) (hPU hp)).contDiffAt
    (hU.mem_nhds (hPU hp))).differentiableAt (by simp)
  have hdN := gnomonicNormal_contDiff.differentiable (by simp) (P p)
  have heX := (hrec.eventuallyEq_of_mem (hV.mem_nhds hp)).fderiv_eq (𝕜 := ℝ)
  have heN := (hnorm.eventuallyEq_of_mem (hV.mem_nhds hp)).fderiv_eq (𝕜 := ℝ)
  rw [← heX, ← heN, fderiv_comp p hdX hdP, fderiv_comp p hdN hdP]
  exact identityBand_cartesian_support_pairing hG hU (hPU hp)
    (fderiv ℝ P p v) (fderiv ℝ P p w)

end
end TightVer401