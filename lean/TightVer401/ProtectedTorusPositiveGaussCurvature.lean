import TightVer401.ProtectedTorusPositiveGaussCurvatureSeams

/-! The actual positive Gaussian-curvature region of the literal protected torus.
The map uses one saddle and the very same constructed convex meridian. The
only pending producer is ordinary sphere-support potential/coordinate germ
data for the open saddle cylinder, owned by saddle/core-support smoothing.
Negative saddle curvature, zero seam curvature, and positive convex curvature
are all derived in the imported proof leaves; no sign or region conclusion
is a premise. The Gauss homeomorphism and its source matching are separate
application obligations, rather than conclusions of this region theorem.
-/
open scoped Manifold ContDiff Topology Matrix
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussRegionPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Exactly the genuine convex phase has positive actual preferred-chart
Gaussian curvature. The radius in every application is literally D.meridian. -/
theorem protectedTorusPositiveGauss_curvature_pos_iff {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (hS : ProtectedTorusSaddleSphereSupportGerms S.saddle) (p : NonrigidTorusSource) :
    0 < nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p ↔
      (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi) := by
  constructor
  · intro hpos
    let u := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
    have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      simpa [u] using (AddCircle.equivIco (2 * Real.pi) 0 p.2).property
    have hp : periodProjection (2 * Real.pi) u = p.2 := AddCircle.coe_equivIco
    by_cases hu0 : u = 0
    · have hp0 : p.2 = 0 := by rw [← hp, hu0]; rfl
      rw [protectedTorusPositiveGauss_south_curvature_zero S D p hp0] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    by_cases huπ : u = Real.pi
    · have hpπ : p.2 = periodProjection (2 * Real.pi) Real.pi := by rw [← hp, huπ]
      rw [protectedTorusPositiveGauss_north_curvature_zero S D p hpπ] at hpos
      exact False.elim (lt_irrefl 0 hpos)
    by_cases hup : u < Real.pi
    · have hneg := protectedTorusPositiveGauss_saddle_curvature_neg S.saddle D.meridian h hS p
        (show u ∈ Ioo (0 : ℝ) Real.pi from ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hup⟩)
      exact False.elim (not_lt_of_ge hneg.le hpos)
    · exact ⟨lt_of_le_of_ne (le_of_not_gt hup) (Ne.symm huπ), hu.2⟩
  · exact protectedTorusPositiveGauss_convex_curvature_pos S D p

/-- The actual positive region equals precisely the open convex phase. -/
theorem protectedTorusPositiveGauss_region_eq {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (hS : ProtectedTorusSaddleSphereSupportGerms S.saddle) :
    nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h) =
      {p | (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi)} := by
  ext p
  exact protectedTorusPositiveGauss_curvature_pos_iff S D hS p

end
end TightVer401
