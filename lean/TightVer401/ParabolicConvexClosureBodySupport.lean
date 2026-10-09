import TightVer401.ParabolicConvexClosureBodyAnnulus
import Mathlib.Analysis.Convex.Deriv

/-! Actual supporting orientation, lateral asymmetry and boundary image.

Concavity gives the actual tangent supporting line even when the profile has
square-root endpoint germs. Its combination with horizontal Cauchy--Schwarz
proves the whole-body supporting inequality for the existing native outward
normal. The closed lateral image and its asymmetry are literal Ambient sets.
-/

open scoped Manifold ContDiff Topology Pointwise RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance parabolicClosureBodySupportCirclePeriod : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The actual tangent line supports a concave profile on its entire closed interval. -/
theorem parabolicConvexClosure_radius_supporting_line {r : ℝ → ℝ} {h z y : ℝ}
    (hc : ConcaveOn ℝ (Icc (-h) h) r) (hz : z ∈ Ioo (-h) h)
    (hd : DifferentiableAt ℝ r z) (hy : y ∈ Icc (-h) h) :
    r y ≤ r z + deriv r z * (y - z) := by
  rcases lt_trichotomy z y with hzy | rfl | hyz
  · have hs := hc.slope_le_deriv (Ioo_subset_Icc_self hz) hy hzy hd
    rw [slope_def_field] at hs
    have hb := (div_le_iff₀ (sub_pos.mpr hzy)).mp hs
    linarith
  · simp
  · have hs := hc.deriv_le_slope hy (Ioo_subset_Icc_self hz) hyz hd
    rw [slope_def_field] at hs
    have hb := (le_div_iff₀ (sub_pos.mpr hyz)).mp hs
    nlinarith

private theorem parabolicConvexClosure_angle_trig (θ : AddCircle (2 * Real.pi)) :
    (Real.Angle.cos θ)^2 + (Real.Angle.sin θ)^2 = 1 := by
  induction θ using Real.Angle.induction_on with
  | h t => simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using Real.cos_sq_add_sin_sq t

/-- Horizontal Cauchy--Schwarz in the actual Ambient coordinates. -/
theorem parabolicConvexClosure_horizontal_support (q : Ambient)
    (θ : AddCircle (2 * Real.pi)) :
    q 0 * Real.Angle.cos θ + q 1 * Real.Angle.sin θ ≤
      ‖parabolicConvexClosureHorizontalCLM q‖ := by
  have ht := parabolicConvexClosure_angle_trig θ
  have hn := parabolicConvexClosureHorizontal_norm_sq q
  have he : (q 0 * Real.Angle.cos θ + q 1 * Real.Angle.sin θ)^2 +
      (q 0 * Real.Angle.sin θ - q 1 * Real.Angle.cos θ)^2 =
      ((q 0)^2 + (q 1)^2) * ((Real.Angle.cos θ)^2 + (Real.Angle.sin θ)^2) := by ring
  rw [ht, mul_one, ← hn] at he
  nlinarith [sq_nonneg (q 0 * Real.Angle.sin θ - q 1 * Real.Angle.cos θ),
    norm_nonneg (parabolicConvexClosureHorizontalCLM q)]

/-- Exact pairing with the actual outward normal, in physical coordinates. -/
theorem parabolicConvexClosure_nativeOutwardNormal_pairing
    (r : ℝ → ℝ) (U : TopologicalSpace.Opens ℝ)
    (p : AddCircle (2 * Real.pi) × U) (q : Ambient) :
    inner ℝ (q - parabolicConvexClosureNativeMap r U p)
      (parabolicConvexClosureNativeOutwardNormal r U p) =
    (q 0 * Real.Angle.cos p.1 + q 1 * Real.Angle.sin p.1 - r (p.2 : ℝ) -
      deriv r (p.2 : ℝ) * (q 2 - (p.2 : ℝ))) / revolutionWeight (deriv r (p.2 : ℝ)) := by
  have ht := congrArg (fun t : ℝ => r (p.2 : ℝ) * t)
    (parabolicConvexClosure_angle_trig p.1)
  simp only [mul_one] at ht
  simp [PiLp.inner_apply, Fin.sum_univ_three, parabolicConvexClosureNativeMap,
    parabolicConvexClosureNativeOutwardNormal, parabolicConvexClosureHeightInclusion,
    revolutionEndCircleFull, revolutionEndCircleNormal, revolutionCircleRadial,
    revolutionAxis, revolutionNormalHeight]
  field_simp [(revolutionWeight_pos (deriv r (p.2 : ℝ))).ne']
  nlinarith [ht]

/-- The existing native outward normal supports every point of the actual body.
Positivity is not needed for this inequality; the positive-radius meridian
specialization additionally places the surface point on the lateral frontier. -/
theorem parabolicConvexClosure_nativeOutwardNormal_supports {r : ℝ → ℝ} {h : ℝ}
    (hc : ConcaveOn ℝ (Icc (-h) h) r)
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (p : AddCircle (2 * Real.pi) ×
      (⟨Ioo (-h) h, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ))
    (q : Ambient) (hq : q ∈ parabolicConvexClosureBodyCarrier r h) :
    inner ℝ (q - parabolicConvexClosureNativeMap r
      (⟨Ioo (-h) h, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) p)
      (parabolicConvexClosureNativeOutwardNormal r
        (⟨Ioo (-h) h, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) p) ≤ 0 := by
  have hd : DifferentiableAt ℝ r (p.2 : ℝ) :=
    (hr.differentiableOn (by simp) _ p.2.property).differentiableAt
      (isOpen_Ioo.mem_nhds p.2.property)
  have hs := parabolicConvexClosure_radius_supporting_line hc p.2.property hd hq.1
  have hhoriz := parabolicConvexClosure_horizontal_support q p.1
  rw [parabolicConvexClosure_nativeOutwardNormal_pairing]
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [hq.2]
  · exact (revolutionWeight_pos _).le

/-- Genuine central-asymmetry witness on the actual closed lateral image. -/
theorem parabolicConvexClosureClosedMap_exists_not_neg_mem {r : ℝ → ℝ} {h : ℝ}
    (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hasym : ∃ z ∈ Ioo 0 h, r (-z) ≠ r z) :
    ∃ p ∈ range (parabolicConvexClosureClosedMap r h),
      -p ∉ range (parabolicConvexClosureClosedMap r h) := by
  obtain ⟨z, hz, he⟩ := hasym
  have hzI : z ∈ Icc (-h) h := ⟨by linarith [hz.1, hz.2], hz.2.le⟩
  have hpos := hrpos z hzI
  have hnorm : ‖(r z : ℂ)‖ = r z := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  refine ⟨parabolicConvexClosureRadialPoint (r z) z, ?_, ?_⟩
  · rw [parabolicConvexClosureClosedMap_range hrpos]
    change z ∈ Icc (-h) h ∧ _
    refine ⟨hzI, ?_⟩
    rw [parabolicConvexClosureRadialPoint_horizontal]
    exact hnorm
  · intro hp
    rw [parabolicConvexClosureClosedMap_range hrpos] at hp
    have hb := hp.2
    have hh : (-parabolicConvexClosureRadialPoint (r z) z) 2 = -z := rfl
    rw [map_neg, norm_neg, parabolicConvexClosureRadialPoint_horizontal, hnorm, hh] at hb
    exact he hb.symm

 theorem parabolicConvexClosureClosedMap_not_neg_invariant {r : ℝ → ℝ} {h : ℝ}
    (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hasym : ∃ z ∈ Ioo 0 h, r (-z) ≠ r z) :
    Neg.neg '' range (parabolicConvexClosureClosedMap r h) ≠
      range (parabolicConvexClosureClosedMap r h) := by
  obtain ⟨p, hp, hn⟩ := parabolicConvexClosureClosedMap_exists_not_neg_mem hrpos hasym
  intro he
  apply hn
  rw [← he]
  exact mem_image_of_mem Neg.neg hp

/-- Exact actual frontier: endpoint disks and the actual closed annulus image.
Its endpoint circles are already contained in the two disks. -/
theorem parabolicConvexClosureBody_frontier_eq_disks_union_closedMap
    {r : ℝ → ℝ} {h RN : ℝ} (hh : 0 < h) (hRN : 0 < RN)
    (hr : ContinuousOn r (Icc (-h) h))
    (hrpos : ∀ z ∈ Ioo (-h) h, RN < r z)
    (hl : r (-h) = RN) (hu : r h = RN) :
    frontier (parabolicConvexClosureBodyCarrier r h) =
      parabolicConvexClosureDisk RN (-h) ∪ parabolicConvexClosureDisk RN h ∪
        range (parabolicConvexClosureClosedMap r h) := by
  rw [parabolicConvexClosureBody_frontier hh hRN hr hrpos hl hu,
    parabolicConvexClosureClosedMap_range_decomposition hh
      (parabolicConvexClosure_radius_pos_closed hRN hl hu hrpos) hl hu]
  ext p
  simp only [mem_union]
  constructor
  · rintro (hd | hp)
    · exact Or.inl hd
    · exact Or.inr (Or.inr hp)
  · rintro (hd | (hc | hp))
    · exact Or.inl hd
    · rcases hc with hlc | huc
      · exact Or.inl (Or.inl ⟨hlc.1, hlc.2.le⟩)
      · exact Or.inl (Or.inr ⟨huc.1, huc.2.le⟩)
    · exact Or.inr hp

end
end TightVer401
