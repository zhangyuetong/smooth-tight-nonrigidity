import TightVer401.NativeProductPlaneAtlas
import TightVer401.PeriodProjectionDifferential
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Actual smooth global native tangent-frame evaluation on the quotient torus.

Preferred circle transitions are locally translations, so their actual
 derivatives are the identity. The product transitions therefore preserve
constant real tangent vectors. Smoothness of the actual differential applied
to this frame follows from Mathlib's derivative-in-tangent-coordinates API.
-/

open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold Bundle OAI.RawQuotientLie OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance protectedPositiveGaussFramePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance protectedPositiveGaussFrameNativeManifold :
    IsManifold nativeProductModel ∞ NonrigidTorusSource := nonrigidTorusSource_isManifold

/-- Actual transition germ in the registered additive quotient atlas. -/
theorem protectedTorusPositiveGauss_circle_transition_germ (L : ℝ) [Fact (0 < L)]
    (p q : AddCircle L) (hq : q ∈ (chartAt ℝ p).source) :
    (extChartAt 𝓘(ℝ, ℝ) q ∘ (extChartAt 𝓘(ℝ, ℝ) p).symm)
      =ᶠ[𝓝 (extChartAt 𝓘(ℝ, ℝ) p q)]
        (fun t => t - extChartAt 𝓘(ℝ, ℝ) p q) := by
  let b : ℝ := extChartAt 𝓘(ℝ, ℝ) p q
  have hqb : p + periodProjection L b = q := by
    have he := (chartAt ℝ p).left_inv hq
    change (addLeftChart (periodChart L) p).symm b = q at he
    rw [addLeftChart_symm_apply] at he
    exact he
  have ht : ∀ᶠ t : ℝ in 𝓝 b, t - b ∈ (periodChart L).source := by
    have hz := (periodChart L).open_source.mem_nhds (periodChart_zero_source L)
    have hc : Tendsto (fun t : ℝ => t - b) (𝓝 b) (𝓝 0) := by
      have hc' : ContinuousAt (fun t : ℝ => t - b) b :=
        continuousAt_id.sub continuousAt_const
      change Tendsto (fun t : ℝ => t - b) (𝓝 b) (𝓝 (b - b)) at hc'
      simpa only [sub_self] using hc'
    exact hc.eventually hz
  filter_upwards [ht] with t htt
  change (addLeftChart (periodChart L) q) ((addLeftChart (periodChart L) p).symm t) = t - b
  rw [addLeftChart_symm_apply, addLeftChart_apply]
  change (periodChart L).symm (-q + (p + periodProjection L t)) = t - b
  have he : -q + (p + periodProjection L t) = periodProjection L (t - b) := by
    rw [← hqb, map_sub]
    abel
  rw [he]
  exact (periodChart L).left_inv htt

/-- The actual product preferred-chart transition is a translation germ. -/
theorem protectedTorusPositiveGauss_product_transition_germ
    (p q : NonrigidTorusSource) (hq : q ∈ (chartAt (ModelProd ℝ ℝ) p).source) :
    (extChartAt nativeProductModel q ∘ (extChartAt nativeProductModel p).symm)
      =ᶠ[𝓝 (extChartAt nativeProductModel p q)]
        (fun t => t - extChartAt nativeProductModel p q) := by
  have hq' : q.1 ∈ (chartAt ℝ p.1).source ∧ q.2 ∈ (chartAt ℝ p.2).source := hq
  have h1 := protectedTorusPositiveGauss_circle_transition_germ (2 * Real.pi) p.1 q.1 hq'.1
  have h2 := protectedTorusPositiveGauss_circle_transition_germ (2 * Real.pi) p.2 q.2 hq'.2
  have h1' := h1.comp_tendsto (continuous_fst.continuousAt :
    Tendsto (fun t : ℝ × ℝ => t.1) (𝓝 (extChartAt nativeProductModel p q))
      (𝓝 (extChartAt 𝓘(ℝ, ℝ) p.1 q.1)))
  have h2' := h2.comp_tendsto (continuous_snd.continuousAt :
    Tendsto (fun t : ℝ × ℝ => t.2) (𝓝 (extChartAt nativeProductModel p q))
      (𝓝 (extChartAt 𝓘(ℝ, ℝ) p.2 q.2)))
  filter_upwards [h1', h2'] with t ht1 ht2
  exact Prod.ext ht1 ht2

/-- The registered quotient torus's actual tangent coordinate change is the identity. -/
theorem protectedTorusPositiveGauss_tangentCoordChange
    (p q : NonrigidTorusSource) (hq : q ∈ (chartAt (ModelProd ℝ ℝ) p).source) :
    tangentCoordChange nativeProductModel p q q = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ nativeProductModel,
    fderivWithin_univ]
  rw [(protectedTorusPositiveGauss_product_transition_germ p q hq).fderiv_eq]
  exact ((hasFDerivAt_id (extChartAt nativeProductModel p q)).sub_const
    (extChartAt nativeProductModel p q)).fderiv

/-- Actual differential evaluation in every constant native tangent direction is smooth.
No smooth-frame field or metric compatibility is supplied. -/
theorem protectedTorusPositiveGauss_nativeFrame_contMDiff
    {F : NonrigidTorusSource → Ambient}
    (hF : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F) (v : ℝ × ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (fun p => (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p v : Ambient)) := by
  intro p
  have hd := (hF p).mfderiv_const (m := ∞) (by simp)
  have hs := hd.clm_apply (contMDiffAt_const (c := v))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt (ModelProd ℝ ℝ) p).open_source.mem_nhds
    (mem_chart_source (ModelProd ℝ ℝ) p)] with q hq
  rw [inTangentCoordinates_eq id F
    (fun q => mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q) hq (by simp)]
  symm
  change ((tangentBundleCore 𝓘(ℝ, Ambient) Ambient).coordChange
      (achart Ambient (F q)) (achart Ambient (F p)) (F q) ∘L
        mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q ∘L
          tangentCoordChange nativeProductModel p q q) v =
    (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F q v : Ambient)
  rw [tangentBundleCore_coordChange_model_space,
    protectedTorusPositiveGauss_tangentCoordChange p q hq]
  rfl

end
end TightVer401



