import TightVer401.PlanarGradientInverse
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! The Cartesian chart of the SAME final gradient constructed on an open
subtype. Mathlib's lift along the open inclusion preserves the target and
inverse literally; no new global inversion or degree argument is used. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Flatten the already chosen subtype chart along the actual open inclusion. -/
def positiveExitFinalGradientChart {U : Set Coord} (hU : IsOpen U)
    (h : OpenPartialHomeomorph U Coord) : OpenPartialHomeomorph Coord Coord :=
  h.lift_openEmbedding (f := (Subtype.val : U → Coord))
    hU.isOpenEmbedding_subtypeVal

@[simp] theorem positiveExitFinalGradientChart_source {U : Set Coord}
    (hU : IsOpen U) (h : OpenPartialHomeomorph U Coord)
    (hsource : h.source = univ) :
    (positiveExitFinalGradientChart hU h).source = U := by
  rw [positiveExitFinalGradientChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    hsource, image_univ, Subtype.range_val]

@[simp] theorem positiveExitFinalGradientChart_target {U : Set Coord}
    (hU : IsOpen U) (h : OpenPartialHomeomorph U Coord) :
    (positiveExitFinalGradientChart hU h).target = h.target := rfl

/-- Forward values on the actual source are those of the original chart. -/
theorem positiveExitFinalGradientChart_apply {U : Set Coord}
    (hU : IsOpen U) (h : OpenPartialHomeomorph U Coord)
    {p : Coord} (hp : p ∈ U) :
    positiveExitFinalGradientChart hU h p = h ⟨p, hp⟩ := by
  exact h.lift_openEmbedding_apply hU.isOpenEmbedding_subtypeVal
    (x := (⟨p, hp⟩ : U))

/-- The chosen inverse is unchanged, with only its subtype tag removed. -/
@[simp] theorem positiveExitFinalGradientChart_symm_apply {U : Set Coord}
    (hU : IsOpen U) (h : OpenPartialHomeomorph U Coord) (p : Coord) :
    (positiveExitFinalGradientChart hU h).symm p = (h.symm p).val := rfl

/-- A smooth ambient representative transfers to the flattened chart on its
full source; this does not choose another forward map or inverse. -/
theorem positiveExitFinalGradientChart_contDiffOn {U : Set Coord}
    (hU : IsOpen U) (h : OpenPartialHomeomorph U Coord)
    (hsource : h.source = univ) {F : Coord → Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hactual : ∀ p : U, h p = F p.val) :
    ContDiffOn ℝ ∞ (positiveExitFinalGradientChart hU h)
      (positiveExitFinalGradientChart hU h).source := by
  rw [positiveExitFinalGradientChart_source hU h hsource]
  apply hF.congr
  intro p hp
  exact (positiveExitFinalGradientChart_apply hU h hp).trans (hactual ⟨p, hp⟩)

/-- Inverse regularity is retained on exactly the original target. -/
theorem positiveExitFinalGradientChart_inverse_contDiffOn {U : Set Coord}
    (hU : IsOpen U) (h : OpenPartialHomeomorph U Coord)
    (hinverse : ContDiffOn ℝ ∞ (fun p => (h.symm p).val) h.target) :
    ContDiffOn ℝ ∞ (positiveExitFinalGradientChart hU h).symm
      (positiveExitFinalGradientChart hU h).target := hinverse

/-- The existing selected-patch subtype inverse supplies the exact Cartesian
inputs consumed by `exists_markedTorus_pair_of_negative_gradient_order`.
All equations retain the SAME final scalar Ge and chosen inverse h. -/
theorem positiveExit_final_gradient_cartesian_connection {Ge : Coord → ℝ}
    {U : Set Coord} (hU : IsOpen U) (hGe : ContDiffOn ℝ ∞ Ge U)
    (h : OpenPartialHomeomorph U Coord) (hsource : h.source = univ)
    (hactual : (h : U → Coord) = fun p => planarGradient Ge p.val)
    (hinverse : ContDiffOn ℝ ∞ (fun p => (h.symm p).val) h.target) :
    let e0 := positiveExitFinalGradientChart hU h
    e0.source = U ∧ e0.target = h.target ∧
      (∀ p ∈ e0.source, e0 p = planarGradient Ge p) ∧
      (∀ p, e0.symm p = (h.symm p).val) ∧
      ContDiffOn ℝ ∞ e0 e0.source ∧ ContDiffOn ℝ ∞ e0.symm e0.target := by
  dsimp only
  refine ⟨positiveExitFinalGradientChart_source hU h hsource,
    positiveExitFinalGradientChart_target hU h, ?_,
    positiveExitFinalGradientChart_symm_apply hU h,
    positiveExitFinalGradientChart_contDiffOn hU h hsource
      (planarGradient_contDiffOn hGe hU) (fun p => congrFun hactual p),
    positiveExitFinalGradientChart_inverse_contDiffOn hU h hinverse⟩
  intro p hp
  rw [positiveExitFinalGradientChart_source hU h hsource] at hp
  exact (positiveExitFinalGradientChart_apply hU h hp).trans (congrFun hactual ⟨p, hp⟩)

end
end TightVer401
