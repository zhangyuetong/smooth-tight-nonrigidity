import TightVer401.ParabolicConvexClosureGeometry
import TightVer401.RevolutionEndNativeNormal
import TightVer401.NativeProductPlaneAtlas

/-! Actual native open-annulus revolution geometry.

The source is the native circle times an arbitrary open height subset.
The actual surface and outward normal are restrictions of retained revolution
maps. Interior profile smoothness supplies actual smooth germs; no globally
smooth radius, Gauss injectivity, target image, inverse or closed boundary
geometry is assumed. All instances here are local.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance parabolicClosureGeometryCirclePeriod : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩
local instance parabolicClosureGeometryAmbientDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- The actual smooth inclusion of the native open annulus into the full cylinder. -/
def parabolicConvexClosureHeightInclusion (U : TopologicalSpace.Opens ℝ) :
    AddCircle (2 * Real.pi) × U → AddCircle (2 * Real.pi) × ℝ :=
  fun p => (p.1, (p.2 : ℝ))

theorem parabolicConvexClosureHeightInclusion_contMDiff (U : TopologicalSpace.Opens ℝ) :
    ContMDiff nativeProductModel nativeProductModel ∞
      (parabolicConvexClosureHeightInclusion U) :=
  contMDiff_fst.prodMk ((contMDiff_subtype_val (U := U)).comp contMDiff_snd)

/-- The actual native lateral surface, without an endpoint smoothness assertion. -/
def parabolicConvexClosureNativeMap (r : ℝ → ℝ) (U : TopologicalSpace.Opens ℝ)
    (p : AddCircle (2 * Real.pi) × U) : Ambient :=
  revolutionEndCircleFull r (parabolicConvexClosureHeightInclusion U p)

theorem parabolicConvexClosure_nativeMap_representative (r : ℝ → ℝ)
    (U : TopologicalSpace.Opens ℝ) (θ : ℝ) (z : U) :
    parabolicConvexClosureNativeMap r U (periodProjection (2 * Real.pi) θ, z) =
      revolutionEnd r (![θ, (z : ℝ)] : Coord) :=
  revolutionEndCircleFull_representative r θ z.val

theorem parabolicConvexClosure_nativeMap_germ {q r : ℝ → ℝ}
    {U : TopologicalSpace.Opens ℝ} {p : AddCircle (2 * Real.pi) × U}
    (h : q =ᶠ[𝓝 (p.2 : ℝ)] r) :
    parabolicConvexClosureNativeMap q U =ᶠ[𝓝 p] parabolicConvexClosureNativeMap r U := by
  filter_upwards [h.comp_tendsto
    (continuous_subtype_val.comp continuous_snd).continuousAt] with x hx
  change q (x.2 : ℝ) = r (x.2 : ℝ) at hx
  simp only [parabolicConvexClosureNativeMap, parabolicConvexClosureHeightInclusion,
    revolutionEndCircleFull, hx]

theorem parabolicConvexClosure_nativeMap_contMDiff {r : ℝ → ℝ}
    (U : TopologicalSpace.Opens ℝ) (hr : ContDiffOn ℝ ∞ r U) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (parabolicConvexClosureNativeMap r U) := by
  intro p
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension U.isOpen hr p.2.property
  have hs := (revolutionEndCircleFull_contMDiff hq).comp
    (parabolicConvexClosureHeightInclusion_contMDiff U)
  exact (hs p).congr_of_eventuallyEq (parabolicConvexClosure_nativeMap_germ hg).symm

/-- The correct outward normal on the actual native source. -/
def parabolicConvexClosureNativeOutwardNormal (r : ℝ → ℝ)
    (U : TopologicalSpace.Opens ℝ) (p : AddCircle (2 * Real.pi) × U) : Ambient :=
  -revolutionEndCircleNormal r (parabolicConvexClosureHeightInclusion U p)

theorem parabolicConvexClosureNativeOutwardNormal_norm (r : ℝ → ℝ)
    (U : TopologicalSpace.Opens ℝ) (p : AddCircle (2 * Real.pi) × U) :
    ‖parabolicConvexClosureNativeOutwardNormal r U p‖ = 1 := by
  simpa only [parabolicConvexClosureNativeOutwardNormal, norm_neg] using
    revolutionEndCircleNormal_norm r (parabolicConvexClosureHeightInclusion U p)

theorem parabolicConvexClosure_nativeOutwardNormal_germ {q r : ℝ → ℝ}
    {U : TopologicalSpace.Opens ℝ} {p : AddCircle (2 * Real.pi) × U}
    (h : q =ᶠ[𝓝 (p.2 : ℝ)] r) :
    parabolicConvexClosureNativeOutwardNormal q U =ᶠ[𝓝 p]
      parabolicConvexClosureNativeOutwardNormal r U := by
  filter_upwards [h.deriv.comp_tendsto
    (continuous_subtype_val.comp continuous_snd).continuousAt] with x hx
  change deriv q (x.2 : ℝ) = deriv r (x.2 : ℝ) at hx
  simp only [parabolicConvexClosureNativeOutwardNormal, parabolicConvexClosureHeightInclusion,
    revolutionEndCircleNormal, revolutionNormalHeight, hx]

theorem parabolicConvexClosure_nativeOutwardNormal_contMDiff {r : ℝ → ℝ}
    (U : TopologicalSpace.Opens ℝ) (hr : ContDiffOn ℝ ∞ r U) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (parabolicConvexClosureNativeOutwardNormal r U) := by
  intro p
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension U.isOpen hr p.2.property
  have hs := ((revolutionEndCircleNormal_contMDiff hq).comp
    (parabolicConvexClosureHeightInclusion_contMDiff U)).neg
  exact (hs p).congr_of_eventuallyEq
    (parabolicConvexClosure_nativeOutwardNormal_germ hg).symm

/-- The actual sphere-valued outward Gauss map, without injectivity or image grants. -/
def parabolicConvexClosureNativeOutwardGauss (r : ℝ → ℝ)
    (U : TopologicalSpace.Opens ℝ) (p : AddCircle (2 * Real.pi) × U) : RoundSphere :=
  ⟨parabolicConvexClosureNativeOutwardNormal r U p, by
    simpa using parabolicConvexClosureNativeOutwardNormal_norm r U p⟩

theorem parabolicConvexClosure_nativeOutwardGauss_contMDiff {r : ℝ → ℝ}
    (U : TopologicalSpace.Opens ℝ) (hr : ContDiffOn ℝ ∞ r U) :
    ContMDiff nativeProductModel (𝓡 2) ∞ (parabolicConvexClosureNativeOutwardGauss r U) :=
  (parabolicConvexClosure_nativeOutwardNormal_contMDiff U hr).codRestrict_sphere
    (fun p => by simpa using parabolicConvexClosureNativeOutwardNormal_norm r U p)

/-- Actual manifold differential orthogonality for the actual native lateral surface. -/
theorem parabolicConvexClosure_nativeOutwardNormal_orthogonal {r : ℝ → ℝ}
    (U : TopologicalSpace.Opens ℝ) (hr : ContDiffOn ℝ ∞ r U)
    (p : AddCircle (2 * Real.pi) × U) (v : TangentSpace nativeProductModel p) :
    @inner ℝ Ambient _
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (parabolicConvexClosureNativeMap r U) p v : Ambient)
      (parabolicConvexClosureNativeOutwardNormal r U p) = 0 := by
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension U.isOpen hr p.2.property
  have hmap := parabolicConvexClosure_nativeMap_germ (p := p) hg
  have hn := (parabolicConvexClosure_nativeOutwardNormal_germ (p := p) hg).self_of_nhds
  rw [← hmap.mfderiv_eq, ← hn]
  have hd := mfderiv_comp p
    ((revolutionEndCircleFull_contMDiff hq (parabolicConvexClosureHeightInclusion U p)).mdifferentiableAt
      (by simp))
    ((parabolicConvexClosureHeightInclusion_contMDiff U p).mdifferentiableAt (by simp))
  change mfderiv nativeProductModel 𝓘(ℝ, Ambient)
    (parabolicConvexClosureNativeMap q U) p = _ at hd
  rw [hd]
  change @inner ℝ Ambient _
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q)
      (parabolicConvexClosureHeightInclusion U p)
      (mfderiv nativeProductModel nativeProductModel
        (parabolicConvexClosureHeightInclusion U) p v) : Ambient)
    (-revolutionEndCircleNormal q (parabolicConvexClosureHeightInclusion U p)) = 0
  rw [inner_neg_right, revolutionEndCircleNormal_orthogonal hq, neg_zero]

end
end TightVer401
