import TightVer401.RuledNormal

/-! A smooth map with injective actual differential induces the smooth positive
metric required by OpenAI's Gauss equation. No metric realizability is assumed. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix

theorem inducedMetric_bilinear (F : Coord → Ambient) (p v w : Coord) :
    inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) =
      v ⬝ᵥ (inducedMetric F p *ᵥ w) := by
  rw [fderiv_two_coordinates F p v, fderiv_two_coordinates F p w]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, inducedMetric,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem inducedMetric_posDef {F : Coord → Ambient} {p : Coord}
    (hF : Function.Injective (fderiv ℝ F p)) : (inducedMetric F p).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · show (inducedMetric F p).conjTranspose = inducedMetric F p
    ext i j
    simp [Matrix.conjTranspose_apply, inducedMetric, real_inner_comm]
  · intro v hv
    have hn : fderiv ℝ F p v ≠ 0 := by
      intro hz
      apply hv
      apply hF
      simpa using hz
    simpa only [star_trivial, ← inducedMetric_bilinear] using real_inner_self_pos.mpr hn

theorem inducedMetric_isometricOn {F : Coord → Ambient} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) : IsometricOn (inducedMetric F) F U :=
  ⟨hF, fun p _ v w => inducedMetric_bilinear F p v w⟩

theorem inducedMetric_smoothPositiveOn {F : Coord → Ambient} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hinj : ∀ p ∈ U, Function.Injective (fderiv ℝ F p)) :
    SmoothPositiveOn (inducedMetric F) U := by
  constructor
  · intro i j
    exact (partial_contDiffOn hF hU i).inner ℝ (partial_contDiffOn hF hU j)
  · intro p hp
    exact inducedMetric_posDef (hinj p hp)

end
end TightVer401
