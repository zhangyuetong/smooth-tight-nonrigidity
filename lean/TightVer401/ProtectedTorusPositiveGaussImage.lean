import TightVer401.ProtectedTorusPositiveGaussPhaseHeight
import TightVer401.ParabolicConvexClosureComplete

/-! Exact producer image bridge for the literal open convex phase.
The same actual radius appears in the assembled map, native lateral map and
ambient lateral carrier. The cosine-height inverse proves surjectivity;
no image, placement, curvature or smoothness conclusion is an input. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussImagePeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The literal convex phase has exactly the actual native meridian-map range. -/
theorem protectedTorusPositiveGauss_phase_image_eq_nativeRange
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) {h : ℝ} (hh : 0 < h) :
    protectedTorusMap S r h '' (protectedTorusPositiveGaussRegion : Set NonrigidTorusSource) =
      range (parabolicConvexClosureNativeMap r (parabolicConvexClosureHeightDomain h)) := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    let φ := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
    have hφ : φ ∈ Ioo Real.pi (2 * Real.pi) := (protectedTorusPositiveGaussRegion_iff p).mp hp
    let z : parabolicConvexClosureHeightDomain h :=
      ⟨protectedTorusPositiveGaussHeight h φ, protectedTorusPositiveGaussHeight_mem hh hφ⟩
    refine ⟨(p.1,z),?_⟩
    simp only [protectedTorusMap, if_neg (not_le.mpr hφ.1),
      protectedTorusConvexCylinder, parabolicConvexClosureNativeMap,
      parabolicConvexClosureHeightInclusion, protectedTorusPositiveGaussHeight, φ, z]
  · rintro ⟨q,rfl⟩
    let φ := protectedTorusPositiveGaussHeightInverse h q.2.val
    have hφ : φ ∈ Ioo Real.pi (2 * Real.pi) :=
      protectedTorusPositiveGaussHeightInverse_mem hh q.2.property
    have hrep : (AddCircle.equivIco (2 * Real.pi) 0
        (periodProjection (2 * Real.pi) φ)).val = φ :=
      congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show φ ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) from
          ⟨by linarith [hφ.1,Real.pi_pos], by simpa using hφ.2⟩))
    refine ⟨(q.1,periodProjection (2 * Real.pi) φ),?_,?_⟩
    · exact (protectedTorusPositiveGaussRegion_iff
        (q.1,periodProjection (2 * Real.pi) φ)).mpr (by simpa only [hrep] using hφ)
    · simp only [protectedTorusMap,hrep,if_neg (not_le.mpr hφ.1),protectedTorusConvexCylinder,
        parabolicConvexClosureNativeMap,parabolicConvexClosureHeightInclusion]
      have hz := protectedTorusPositiveGaussHeight_right hh q.2.property
      change -h * Real.cos φ = q.2.val at hz
      rw [hz]

/-- Actual native meridian-map range equals the full open lateral carrier. -/
theorem protectedTorusPositiveGauss_nativeMap_range {r : ℝ → ℝ} {h : ℝ}
    (hpos : ∀ z ∈ Icc (-h) h, 0 < r z) :
    range (parabolicConvexClosureNativeMap r (parabolicConvexClosureHeightDomain h)) =
      parabolicConvexClosureLateralCarrier r h := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    let q : ParabolicConvexClosureClosedAnnulus h :=
      (p.1,⟨p.2.val,Ioo_subset_Icc_self p.2.property⟩)
    have hn := parabolicConvexClosureClosedMap_horizontal_norm hpos q
    have hz := parabolicConvexClosureClosedMap_height r h q
    change ‖parabolicConvexClosureHorizontalCLM
      (parabolicConvexClosureNativeMap r (parabolicConvexClosureHeightDomain h) p)‖ = r p.2.val at hn
    change (parabolicConvexClosureNativeMap r (parabolicConvexClosureHeightDomain h) p) 2 = p.2.val at hz
    exact ⟨by rw [hz]; exact p.2.property, by simpa only [hz] using hn⟩
  · intro hy
    have hc : y ∈ parabolicConvexClosureClosedLateralCarrier r h :=
      ⟨Ioo_subset_Icc_self hy.1,hy.2⟩
    rw [← parabolicConvexClosureClosedMap_range hpos] at hc
    obtain ⟨q,hq⟩ := hc
    have hz : q.2.val ∈ Ioo (-h) h := by
      rw [← parabolicConvexClosureClosedMap_height r h q,hq]
      exact hy.1
    refine ⟨(q.1,⟨q.2.val,hz⟩),?_⟩
    exact hq

/-- SAME constructed meridian gives the full literal convex-phase image. -/
theorem protectedTorusPositiveGauss_phase_image {RN μ h : ℝ}
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (D : ParabolicConvexClosureData RN μ h) :
    protectedTorusMap S D.meridian h '' (protectedTorusPositiveGaussRegion : Set NonrigidTorusSource) =
      parabolicConvexClosureLateralCarrier D.meridian h := by
  rw [protectedTorusPositiveGauss_phase_image_eq_nativeRange S D.meridian D.height_pos]
  exact protectedTorusPositiveGauss_nativeMap_range
    (parabolicConvexClosure_radius_pos_closed D.radius_pos D.lower_endpoint D.upper_endpoint
      D.meridian_exterior)

end
end TightVer401
