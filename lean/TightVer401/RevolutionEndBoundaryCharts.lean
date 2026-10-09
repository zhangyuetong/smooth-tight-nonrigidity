import TightVer401.RevolutionEndCircleSmooth
import Mathlib.Geometry.Manifold.Instances.Real

namespace TightVer401
noncomputable section
open Set Bundle OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def revolutionEndBoundaryCoordinate (H : ℝ) : Ici H ≃ₜ EuclideanHalfSpace 1 where
  toFun z := ⟨WithLp.toLp 2 (fun _ : Fin 1 => (z : ℝ) - H), by
    change 0 ≤ (z : ℝ) - H
    exact sub_nonneg.mpr z.property⟩
  invFun u := ⟨u.val 0 + H, by
    have h := u.property
    change H ≤ u.val 0 + H
    change 0 ≤ u.val 0 at h
    linarith⟩
  left_inv z := by
    apply Subtype.ext
    change (z : ℝ) - H + H = (z : ℝ)
    ring
  right_inv u := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change u.val 0 + H - H = u.val 0
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp
      (continuous_pi (fun _ => continuous_subtype_val.sub continuous_const))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val).add_const H

instance revolutionEndBoundaryChartedSpace (H : ℝ) : ChartedSpace (EuclideanHalfSpace 1) (Ici H) :=
  (revolutionEndBoundaryCoordinate H).toOpenPartialHomeomorph.singletonChartedSpace (by simp)

instance revolutionEndBoundaryIsManifold (H : ℝ) : IsManifold (𝓡∂ 1) ∞ (Ici H) :=
  (revolutionEndBoundaryCoordinate H).toOpenPartialHomeomorph.isManifold_singleton (by simp)

end
end TightVer401
