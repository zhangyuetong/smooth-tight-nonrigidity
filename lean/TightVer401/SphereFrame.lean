import TightVer401.SphereGeometry

/-! Actual orthonormal tangent frames exist at every point of the two-sphere.
The frame is constructed from the orthogonal complement, rather than assumed. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

abbrev SpherePlane := EuclideanSpace ℝ (Fin 2)

def sphereCoordEquiv : Coord ≃L[ℝ] SpherePlane :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def sphereTangentFrame (w : Ambient) (hw : w ≠ 0) : SpherePlane →ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ w)ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 hw).repr.symm.toLinearIsometry

theorem sphereTangentFrame_orthogonal (w : Ambient) (hw : w ≠ 0) (v : SpherePlane) :
    inner ℝ w (sphereTangentFrame w hw v) = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 hw).repr.symm v).property

theorem sphereTangentFrame_onto (w : Ambient) (hw : w ≠ 0) (u : Ambient)
    (hu : inner ℝ w u = 0) : ∃ v, sphereTangentFrame w hw v = u := by
  let t : (ℝ ∙ w)ᗮ := ⟨u, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hu⟩
  refine ⟨(OrthonormalBasis.fromOrthogonalSpanSingleton 2 hw).repr t, ?_⟩
  change ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 hw).repr.symm
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 hw).repr t) : Ambient) = u
  simp [t]

end
end TightVer401
