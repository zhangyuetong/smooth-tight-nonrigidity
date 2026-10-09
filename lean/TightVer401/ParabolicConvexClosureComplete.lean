import TightVer401.ParabolicConvexClosureTorusInput
import TightVer401.ParabolicConvexClosureBodyImmersion
import TightVer401.ParabolicConvexClosureBodySupport
import TightVer401.ParabolicConvexClosureBoundaryCosine
import TightVer401.ParabolicConvexClosureBoundaryTorus
import TightVer401.ParabolicConvexClosureGaussSmoothNative

/-! Actual ver500 convex closure output, constructed from ordinary positive
parameters. Every geometric field concerns the same constructed radius and
literal surface/body maps. This proof never imports the pending scaffold. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- The actual convex closure, with the exact coordinator meridian input. -/
structure ParabolicConvexClosureData (RN mu h : ℝ)
    extends ProtectedParabolicMeridianInput RN mu h where
  radius_pos : 0 < RN
  coefficient_pos : 0 < mu
  height_pos : 0 < h
  second_negative : ∀ z ∈ Ioo (-h) h, deriv (deriv meridian) z < 0
  strictConcave : StrictConcaveOn ℝ (Icc (-h) h) meridian
  lower_endpoint : meridian (-h) = RN
  upper_endpoint : meridian h = RN
  collarWidth : ℝ
  collarWidth_mem : collarWidth ∈ Ioo 0 h
  lower_germ : EqOn meridian (fun z => RN + Real.sqrt (2 * mu * (h + z)))
    (Icc (-h) (-h + collarWidth))
  upper_germ : EqOn meridian (fun z => RN + Real.sqrt (2 * mu * (h - z)))
    (Icc (h - collarWidth) h)
  asymmetric : ∃ z ∈ Ioo 0 h, meridian (-z) ≠ meridian z
  native_smooth : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
    (parabolicConvexClosureNativeMap meridian (parabolicConvexClosureHeightDomain h))
  native_regular : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
    (parabolicConvexClosureNativeMap meridian (parabolicConvexClosureHeightDomain h)) p)
  native_embedding : Topology.IsEmbedding
    (parabolicConvexClosureNativeMap meridian (parabolicConvexClosureHeightDomain h))
  native_exterior : ∀ p, RN < ‖parabolicConvexClosureHorizontalCLM
      (parabolicConvexClosureNativeMap meridian (parabolicConvexClosureHeightDomain h) p)‖ ∧
    (parabolicConvexClosureNativeMap meridian (parabolicConvexClosureHeightDomain h) p) 2 ∈ Ioo (-h) h
  curvature_positive : ∀ p : Coord, p 1 ∈ Ioo (-h) h →
    0 < gaussianCurvature (inducedMetric (revolutionEnd meridian)) p
  gaussDiffeomorph : Diffeomorph nativeProductModel (𝓡 2)
    (AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h)
    parabolicConvexClosureSphereBelt ∞
  gaussDiffeomorph_eq : ∀ p, (gaussDiffeomorph p : RoundSphere) =
    parabolicConvexClosureNativeOutwardGauss meridian (parabolicConvexClosureHeightDomain h) p
  closed_embedding : Topology.IsClosedEmbedding (parabolicConvexClosureClosedMap meridian h)
  closed_boundary_smooth : ContMDiff parabolicConvexClosureBoundaryModel 𝓘(ℝ, Ambient) ∞
    (parabolicConvexClosureBoundaryCosineMap meridian h)
  closed_boundary_regular : ∀ p, Function.Injective
    (mfderiv parabolicConvexClosureBoundaryModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureBoundaryCosineMap meridian h) p)
  closed_boundary_embedding : Topology.IsEmbedding (parabolicConvexClosureBoundaryCosineMap meridian h)
  closed_boundary_image : range (parabolicConvexClosureBoundaryCosineMap meridian h) =
    range (parabolicConvexClosureClosedMap meridian h)
  upper_collar_smooth : ContDiff ℝ ∞ (parabolicConvexClosureCollar 1 RN mu h)
  lower_collar_smooth : ContDiff ℝ ∞ (parabolicConvexClosureCollar (-1) RN mu h)
  collar_regular : ∀ σ ∈ ({-1, 1} : Set ℝ), ∀ p : Coord, 0 ≤ p 1 →
    Function.Injective (fderiv ℝ (parabolicConvexClosureCollar σ RN mu h) p)
  upper_collar_agreement : ∀ θ t : ℝ, 0 ≤ t → mu * t^2 / 2 ≤ collarWidth →
    parabolicConvexClosureCollar 1 RN mu h (![θ, t] : Coord) =
      revolutionEnd meridian (![θ, h - mu * t^2 / 2] : Coord)
  lower_collar_agreement : ∀ θ t : ℝ, 0 ≤ t → mu * t^2 / 2 ≤ collarWidth →
    parabolicConvexClosureCollar (-1) RN mu h (![θ, t] : Coord) =
      revolutionEnd meridian (![θ, -h + mu * t^2 / 2] : Coord)
  body : ConvexBody Ambient
  body_carrier : (body : Set Ambient) = parabolicConvexClosureBodyCarrier meridian h
  body_interior : (interior (parabolicConvexClosureBodyCarrier meridian h)).Nonempty
  body_outward : ∀ p : AddCircle (2 * Real.pi) × parabolicConvexClosureHeightDomain h,
    ∀ q ∈ parabolicConvexClosureBodyCarrier meridian h,
      @inner ℝ Ambient _ (q - parabolicConvexClosureNativeMap meridian (parabolicConvexClosureHeightDomain h) p)
        (parabolicConvexClosureNativeOutwardNormal meridian (parabolicConvexClosureHeightDomain h) p) ≤ 0
  body_frontier : frontier (parabolicConvexClosureBodyCarrier meridian h) =
    parabolicConvexClosureDisk RN (-h) ∪ parabolicConvexClosureDisk RN h ∪
      range (parabolicConvexClosureBoundaryCosineMap meridian h)
  body_asymmetric : ∃ p ∈ parabolicConvexClosureBodyCarrier meridian h,
    -p ∉ parabolicConvexClosureBodyCarrier meridian h
  lateral_asymmetric : ∃ p ∈ range (parabolicConvexClosureBoundaryCosineMap meridian h),
    -p ∉ range (parabolicConvexClosureBoundaryCosineMap meridian h)

/-- Derive every geometry output for the very same actual meridian. The inputs
are only radius properties, with no surface, body, inverse or rank grants. -/
def parabolicConvexClosureDataOfMeridian (RN mu h : ℝ)
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) (r : ℝ → ℝ)
    (hc : ContinuousOn r (Icc (-h) h)) (hs : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hn : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0)
    (hconc : StrictConcaveOn ℝ (Icc (-h) h) r)
    (hl : r (-h) = RN) (hu : r h = RN) (hp : ∀ z ∈ Ioo (-h) h, RN < r z)
    (δ : ℝ) (hδ : δ ∈ Ioo 0 h)
    (hgl : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    (hgu : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h))
    (ha : ∃ z ∈ Ioo 0 h, r (-z) ≠ r z) : ParabolicConvexClosureData RN mu h := by
  have hclosed := parabolicConvexClosure_radius_pos_closed hRN hl hu hp
  have hgl' : EqOn r (fun z => parabolicClosureUpperRadius RN mu h (-z))
      (Icc (-h) (-h + δ)) := by
    simpa [parabolicClosureUpperRadius] using hgl
  have hgu' : EqOn r (parabolicClosureUpperRadius RN mu h) (Icc (h - δ) h) := hgu
  let E := parabolicConvexClosureNativeGaussDiffeomorph hmu hh hδ.1 hs hn hgl' hgu'
  have hrange := parabolicConvexClosureBoundaryCosineMap_range hh r
  refine {
    meridian := r
    meridian_continuous := hc
    meridian_smooth := hs
    meridian_exterior := hp
    meridian_north_germ := ⟨δ, hδ.1, fun _ hz => hgu hz⟩
    meridian_south_germ := ⟨δ, hδ.1, fun _ hz => hgl hz⟩
    radius_pos := hRN
    coefficient_pos := hmu
    height_pos := hh
    second_negative := hn
    strictConcave := hconc
    lower_endpoint := hl
    upper_endpoint := hu
    collarWidth := δ
    collarWidth_mem := hδ
    lower_germ := hgl
    upper_germ := hgu
    asymmetric := ha
    native_smooth := parabolicConvexClosure_nativeMap_contMDiff (parabolicConvexClosureHeightDomain h) hs
    native_regular := fun p => parabolicConvexClosure_nativeMap_mfderiv_injective
      (parabolicConvexClosureHeightDomain h) hs p
        (hclosed p.2 (Ioo_subset_Icc_self p.2.property)).ne'
    native_embedding := parabolicConvexClosure_nativeMap_isEmbedding hc hclosed
    native_exterior := ?_
    curvature_positive := fun p hz => parabolicConvexClosure_revolution_gaussianCurvature_pos
      isOpen_Ioo hs hz (hRN.trans (hp _ hz)) (hn _ hz)
    gaussDiffeomorph := E
    gaussDiffeomorph_eq := fun _ => rfl
    closed_embedding := parabolicConvexClosureClosedMap_isClosedEmbedding hc hclosed
    closed_boundary_smooth := ?_
    closed_boundary_regular := ?_
    closed_boundary_embedding := parabolicConvexClosureBoundaryCosineMap_isEmbedding hh hc hclosed
    closed_boundary_image := hrange
    upper_collar_smooth := parabolicConvexClosureCollar_contDiff 1 RN mu h
    lower_collar_smooth := parabolicConvexClosureCollar_contDiff (-1) RN mu h
    collar_regular := fun σ _ p ht => parabolicConvexClosureCollar_differential_injective
      hmu.ne' (ne_of_gt (hRN.trans_le (le_add_of_nonneg_right (mul_nonneg hmu.le ht))))
    upper_collar_agreement := fun _ _ ht hd => parabolicConvexClosureCollar_upper_eq hmu hgu ht hd
    lower_collar_agreement := fun _ _ ht hd => parabolicConvexClosureCollar_lower_eq hmu hgl ht hd
    body := parabolicConvexClosureConvexBody hh hRN hc hconc.concaveOn hp
    body_carrier := rfl
    body_interior := parabolicConvexClosureBody_interior_nonempty hh hRN hc hp
    body_outward := fun p q hq => parabolicConvexClosure_nativeOutwardNormal_supports hconc.concaveOn hs p q hq
    body_frontier := ?_
    body_asymmetric := parabolicConvexClosureBody_exists_not_neg_mem hRN hp ha
    lateral_asymmetric := ?_
  }
  · intro p
    let q : ParabolicConvexClosureClosedAnnulus h :=
      (p.1, ⟨(p.2 : ℝ), Ioo_subset_Icc_self p.2.property⟩)
    change RN < ‖parabolicConvexClosureHorizontalCLM (parabolicConvexClosureClosedMap r h q)‖ ∧
      (parabolicConvexClosureClosedMap r h q) 2 ∈ Ioo (-h) h
    rw [parabolicConvexClosureClosedMap_horizontal_norm hclosed,
      parabolicConvexClosureClosedMap_height]
    exact ⟨hp _ p.2.property, p.2.property⟩
  · exact parabolicConvexClosureBoundaryCosineMap_contMDiff hRN hmu hh hδ.1 hs hp hgl hgu
  · exact parabolicConvexClosureBoundaryCosineMap_mfderiv_injective hRN hmu hh hδ.1 hs hp hgl hgu
  · rw [hrange]
    exact parabolicConvexClosureBody_frontier_eq_disks_union_closedMap hh hRN hc hp hl hu
  · rw [hrange]
    exact parabolicConvexClosureClosedMap_exists_not_neg_mem hclosed ha

/-- Construct all actual closure geometry from RN, mu, h > 0. The radius is
constructed here; no meridian or geometric conclusion is assumed. -/
theorem exists_parabolic_convex_closure (RN mu h : ℝ)
    (hRN : 0 < RN) (hmu : 0 < mu) (hh : 0 < h) :
    Nonempty (ParabolicConvexClosureData RN mu h) := by
  obtain ⟨r, hc, hs, hn, hconc, hl, hu, hp, ⟨δ, hδ, hgl, hgu⟩, ha⟩ :=
    exists_parabolic_convex_meridian RN mu h hRN hmu hh
  exact ⟨parabolicConvexClosureDataOfMeridian RN mu h hRN hmu hh r hc hs hn
    hconc hl hu hp δ hδ hgl hgu ha⟩

end
end TightVer401
