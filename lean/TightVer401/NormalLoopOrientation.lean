import TightVer401.NormalLoopFrame

/-! The cross-product choice fixes the positive orientation of the
constructed frame, independently of the sign of geodesic curvature. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Matrix

theorem normalLoopCross_swap (u v : Ambient) : ambientCross u v = -ambientCross v u := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply] <;> ring

theorem normalLoop_orientation {ζ E : ℝ → Ambient}
    (hζ : ∀ r, HasDerivAt ζ (E r) r) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (E r) (E r) = 1) (r : ℝ) :
    ambientCross (normalLoopP ζ E r) (E r) = ζ r ∧
      Matrix.det ![fun i => normalLoopP ζ E r i, fun i => E r i, fun i => ζ r i] = 1 := by
  have hζE := normalLoop_unit_tangent_orthogonal hζ hunit r
  have hcross : ambientCross (normalLoopP ζ E r) (E r) = ζ r := by
    calc
      ambientCross (normalLoopP ζ E r) (E r) =
          -ambientCross (E r) (normalLoopP ζ E r) := normalLoopCross_swap _ _
      _ = ambientCross (E r) (ambientCross (ζ r) (E r)) := by
        rw [normalLoopP, normalLoopCross_neg_right, neg_neg]
      _ = ζ r := by
        rw [normalLoopCross_double, hspeed r, hζE]
        simp
  refine ⟨hcross, ?_⟩
  rw [← ambientCross_triple_det, hcross]
  exact hunit r

end
end TightVer401
