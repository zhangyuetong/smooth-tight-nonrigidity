import TightVer401.AffineMarkedTorusLinear
import TightVer401.GeneralRuledCurvature
import TightVer401.GaussBridge

/-! Actual cross and normal transport for the literal triangular marker.
Its determinant is two. Cross covariance is a finite coordinate identity,
and the normal is the normalized actual inverse transpose, not B n.
Actual differential orthogonality and a function identity for the height
are derived from the already proved dual pairing.
-/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Matrix ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem affineMarkedTorusLinear_cross (v w : Ambient) :
    ambientCross (torusAffineMarker v) (torusAffineMarker w) =
      (2 : ℝ) • torusAffineMarkerContra (ambientCross v w) := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply, torusAffineMarker,
    torusAffineMarkerContra, torusAffineMarkerVec] <;> ring

/-- The actual normalized inverse-transpose normal. -/
def affineMarkedTorusLinearNormal (n : Ambient) : Ambient :=
  ‖torusAffineMarkerContra n‖⁻¹ • torusAffineMarkerContra n

theorem affineMarkedTorusLinearNormal_scale_pos {n : Ambient}
    (hn : inner ℝ n n = 1) : 0 < ‖torusAffineMarkerContra n‖ := by
  apply norm_pos_iff.mpr
  intro hc
  have hn0 := (torusAffineMarkerContra_eq_zero_iff n).mp hc
  simp [hn0] at hn

theorem affineMarkedTorusLinearNormal_unit {n : Ambient}
    (hn : inner ℝ n n = 1) :
    inner ℝ (affineMarkedTorusLinearNormal n) (affineMarkedTorusLinearNormal n) = 1 := by
  have hc : torusAffineMarkerContra n ≠ 0 :=
    (norm_pos_iff.mp (affineMarkedTorusLinearNormal_scale_pos hn))
  have hnorm : ‖affineMarkedTorusLinearNormal n‖ = 1 :=
    norm_smul_inv_norm (𝕜 := ℝ) hc
  rw [real_inner_self_eq_norm_sq, hnorm, one_pow]

/-- Actual Euclidean derivative chain of the literal marked map. -/
theorem affineMarkedTorusLinear_fderiv {X : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) :
    fderiv ℝ (fun q => torusAffineMarker (X q)) p =
      torusAffineMarkerLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ X p) := by
  have hd := torusAffineMarkerLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp p hX.hasFDerivAt
  exact hd.fderiv

theorem affineMarkedTorusLinear_coordPartial {X : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) (i : Fin 2) :
    coordPartial i (fun q => torusAffineMarker (X q)) p =
      torusAffineMarker (coordPartial i X p) := by
  simp only [coordPartial, affineMarkedTorusLinear_fderiv hX]
  rfl

/-- The transformed normal is an actual unit normal to the transformed
map's actual differential. Only the ordinary chain rule is needed. -/
theorem affineMarkedTorusLinear_isUnitNormalAt {X : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) {n : Ambient} (hn : IsUnitNormalAt X n p) :
    IsUnitNormalAt (fun q => torusAffineMarker (X q)) (affineMarkedTorusLinearNormal n) p := by
  refine ⟨affineMarkedTorusLinearNormal_unit hn.1, ?_⟩
  intro v
  rw [affineMarkedTorusLinear_fderiv hX]
  change inner ℝ (torusAffineMarker (fderiv ℝ X p v))
    (‖torusAffineMarkerContra n‖⁻¹ • torusAffineMarkerContra n) = 0
  rw [real_inner_smul_right, torusAffineMarker_dual_pairing, hn.2, mul_zero]

/-- A function identity, so both first and second height derivatives can
be transported using the retained scalar calculus. -/
theorem affineMarkedTorusLinear_height (X : Coord → Ambient) (n : Ambient) :
    height (fun q => torusAffineMarker (X q)) (affineMarkedTorusLinearNormal n) =
      (fun q => height X n q / ‖torusAffineMarkerContra n‖) := by
  funext q
  simp only [height, affineMarkedTorusLinearNormal, real_inner_smul_right,
    torusAffineMarker_dual_pairing, div_eq_mul_inv]
  ring

end
end TightVer401
