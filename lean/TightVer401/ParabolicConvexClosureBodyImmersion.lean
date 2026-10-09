import TightVer401.ParabolicConvexClosureGeometryNative
import TightVer401.RevolutionEndImmersion
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-! Actual immersion of the native open lateral annulus.

For any open height set, the actual differential of its inclusion is injective.
An interior smooth profile has a genuine globally smooth germ at each height;
the retained full-cylinder immersion and the chain rule then prove injectivity
of the actual restricted manifold differential. No immersion hypothesis or
endpoint smoothness in the height parameter is supplied.
-/

open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance parabolicClosureBodyImmersionCirclePeriod : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The actual tangent differential of the open-height inclusion is the identity
in the native real tangent coordinates. -/
theorem parabolicConvexClosure_openHeightVal_mfderiv_apply
    (U : TopologicalSpace.Opens ℝ) (z : U) (v : TangentSpace 𝓘(ℝ, ℝ) z) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : U => (z : ℝ)) z v = v := by
  have hd := mfderiv_chartAt_eq_tangentCoordChange
    (I := 𝓘(ℝ, ℝ)) (x := z) (y := z) (mem_chart_source ℝ z)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : U => (z : ℝ)) z =
    tangentCoordChange 𝓘(ℝ, ℝ) z z z at hd
  rw [hd]
  change tangentCoordChange 𝓘(ℝ, ℝ) z z z (show ℝ from v) = (show ℝ from v)
  exact tangentCoordChange_self (mem_extChartAt_source z)

theorem parabolicConvexClosure_openHeightVal_mfderiv_injective
    (U : TopologicalSpace.Opens ℝ) (z : U) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun z : U => (z : ℝ)) z) := by
  intro v w hvw
  simpa only [parabolicConvexClosure_openHeightVal_mfderiv_apply] using hvw

/-- The actual differential of the native open-annulus inclusion is injective. -/
theorem parabolicConvexClosureHeightInclusion_mfderiv_injective
    (U : TopologicalSpace.Opens ℝ) (p : AddCircle (2 * Real.pi) × U) :
    Function.Injective (mfderiv nativeProductModel nativeProductModel
      (parabolicConvexClosureHeightInclusion U) p) := by
  change Function.Injective (mfderiv nativeProductModel nativeProductModel
    (Prod.map id (fun z : U => (z : ℝ))) p)
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((contMDiff_subtype_val (U := U) (n := ∞) p.2).mdifferentiableAt (by simp)),
    mfderiv_id]
  intro v w hvw
  apply Prod.ext
  · have h1 := congrArg (fun u : ℝ × ℝ => u.1) hvw
    exact h1
  · apply parabolicConvexClosure_openHeightVal_mfderiv_injective U p.2
    exact congrArg (fun u : ℝ × ℝ => u.2) hvw

/-- Interior smoothness and nonzero radius imply actual native manifold
immersion, including profiles with square-root endpoint germs. -/
theorem parabolicConvexClosure_nativeMap_mfderiv_injective
    (U : TopologicalSpace.Opens ℝ) {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r U) (p : AddCircle (2 * Real.pi) × U)
    (hp : r (p.2 : ℝ) ≠ 0) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureNativeMap r U) p) := by
  obtain ⟨q, hq, hg⟩ :=
    parabolicConvexClosure_profile_extension U.isOpen hr p.2.property
  have hmap := parabolicConvexClosure_nativeMap_germ (p := p) hg
  rw [← hmap.mfderiv_eq]
  have hi := (parabolicConvexClosureHeightInclusion_contMDiff U p).mdifferentiableAt
    (by simp)
  have hf := (revolutionEndCircleFull_contMDiff hq
    (parabolicConvexClosureHeightInclusion U p)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp p hf hi
  change mfderiv nativeProductModel 𝓘(ℝ, Ambient)
    (parabolicConvexClosureNativeMap q U) p = _ at hd
  rw [hd]
  have hqp : q (p.2 : ℝ) ≠ 0 := by
    rw [hg.self_of_nhds]
    exact hp
  intro v w hvw
  apply parabolicConvexClosureHeightInclusion_mfderiv_injective U p
  apply revolutionEndCircleFull_mfderiv_injective hq
    (parabolicConvexClosureHeightInclusion U p) hqp
  exact hvw

end
end TightVer401



