import TightVer401.TorusAffineMarkerEllipsePair
import TightVer401.ParabolicConvexClosureComplete

/-! Rigidity of the actual marked open lateral carrier. Closure and boundary
permutation are derived from ordinary continuous positive meridian data.
The generic statement allows distinct endpoint radii; the constructed ver500
same-radius meridian specializes through its actual interior asymmetry witness. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Matrix Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
local instance torusAffineMarkerAnnulusPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual closure of the open lateral carrier, from ordinary radius continuity. -/
theorem torusAffineMarker_lateral_closure {r : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hr : ContinuousOn r (Icc (-h) h)) (hpos : ∀ z ∈ Icc (-h) h, 0 < r z) :
    closure (parabolicConvexClosureLateralCarrier r h) =
      parabolicConvexClosureClosedLateralCarrier r h := by
  have hclosed : IsClosed (parabolicConvexClosureClosedLateralCarrier r h) := by
    rw [← parabolicConvexClosureClosedMap_range hpos]
    exact (parabolicConvexClosureClosedMap_isClosedEmbedding hr hpos).isClosed_range
  apply le_antisymm
  · apply closure_minimal _ hclosed
    exact fun p hp => ⟨Ioo_subset_Icc_self hp.1, hp.2⟩
  · intro p hp
    rw [← parabolicConvexClosureClosedMap_range hpos] at hp
    obtain ⟨q, rfl⟩ := hp
    let f : ℝ → Ambient := fun z => r z • revolutionCircleRadial q.1 + z • revolutionAxis
    have hc : ContinuousOn f (Icc (-h) h) :=
      (hr.smul continuousOn_const).add (continuousOn_id.smul continuousOn_const)
    have hz : q.2.val ∈ closure (Ioo (-h) h) := by
      rw [closure_Ioo (by linarith : -h ≠ h)]
      exact q.2.property
    have hf : ContinuousWithinAt f (Ioo (-h) h) q.2.val :=
      (hc _ q.2.property).mono Ioo_subset_Icc_self
    change f q.2.val ∈ closure (parabolicConvexClosureLateralCarrier r h)
    apply hf.mem_closure hz
    intro z hzi
    let qz : ParabolicConvexClosureClosedAnnulus h := (q.1, ⟨z, Ioo_subset_Icc_self hzi⟩)
    have hn := parabolicConvexClosureClosedMap_horizontal_norm hpos qz
    change ‖parabolicConvexClosureHorizontalCLM (f z)‖ = r z at hn
    have hheight : f z 2 = z := by
      simp [f, revolutionCircleRadial, revolutionAxis]
    exact ⟨by rwa [hheight], by simpa only [hheight] using hn⟩

/-- The actual endpoint circle has precisely its stated marked ellipse image. -/
theorem torusAffineMarker_endpoint_circle_image {R : ℝ} (hR : 0 < R) (z : ℝ) :
    torusAffineMarker '' parabolicConvexClosureEndpointCircle R z =
      torusAffineMarkerEllipse (torusAffineMarkerCenter z) R (2 * R) := by
  have hc : parabolicConvexClosureEndpointCircle R z =
      {p : Ambient | p 2 = z ∧ (p 0)^2 + (p 1)^2 = R^2} := by
    ext p
    constructor
    · rintro ⟨hz,hn⟩
      refine ⟨hz,?_⟩
      rw [← parabolicConvexClosureHorizontal_norm_sq, hn]
    · rintro ⟨hz,hs⟩
      refine ⟨hz,?_⟩
      have hn := parabolicConvexClosureHorizontal_norm_sq p
      nlinarith [norm_nonneg (parabolicConvexClosureHorizontalCLM p)]
  rw [hc]
  exact torusAffineMarker_circle_image R z hR.ne'

/-- Actual closure difference is the two circles, with potentially distinct radii. -/
theorem torusAffineMarker_lateral_boundary {r : ℝ → ℝ} {h RN RS : ℝ}
    (hh : 0 < h) (hr : ContinuousOn r (Icc (-h) h))
    (hpos : ∀ z ∈ Icc (-h) h, 0 < r z) (hN : r h = RN) (hS : r (-h) = RS) :
    closure (parabolicConvexClosureLateralCarrier r h) \ parabolicConvexClosureLateralCarrier r h =
      parabolicConvexClosureEndpointCircle RN h ∪ parabolicConvexClosureEndpointCircle RS (-h) := by
  rw [torusAffineMarker_lateral_closure hh hr hpos]
  ext p
  constructor
  · rintro ⟨hp,hn⟩
    by_cases hU : p 2 = h
    · exact Or.inl ⟨hU,by simpa only [hU,hN] using hp.2⟩
    have hL : p 2 = -h := by
      by_contra hL
      exact hn ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hL),lt_of_le_of_ne hp.1.2 hU⟩,hp.2⟩
    exact Or.inr ⟨hL,by simpa only [hL,hS] using hp.2⟩
  · rintro (⟨hz,hn⟩ | ⟨hz,hn⟩)
    · refine ⟨⟨?_,?_⟩,?_⟩
      · rw [hz]; exact ⟨by linarith,le_rfl⟩
      · simpa only [hz,hN] using hn
      · intro hp; have ht := hp.1.2; rw [hz] at ht; exact lt_irrefl _ ht
    · refine ⟨⟨?_,?_⟩,?_⟩
      · rw [hz]; exact ⟨le_rfl,by linarith⟩
      · simpa only [hz,hS] using hn
      · intro hp; have ht := hp.1.1; rw [hz] at ht; exact lt_irrefl _ ht

/-- The marked open carrier has exactly two actual ellipse boundary components. -/
theorem torusAffineMarker_marked_boundary {r : ℝ → ℝ} {h RN RS : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hRS : 0 < RS)
    (hr : ContinuousOn r (Icc (-h) h)) (hpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hN : r h = RN) (hS : r (-h) = RS) :
    closure (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) \
      (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) =
      torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS) := by
  have he : torusAffineMarker '' closure (parabolicConvexClosureLateralCarrier r h) =
      closure (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) :=
    torusAffineMarkerHomeomorph.image_closure _
  rw [← he, ← image_sdiff torusAffineMarker_injective,
    torusAffineMarker_lateral_boundary hh hr hpos hN hS, image_union,
    torusAffineMarker_endpoint_circle_image hRN, torusAffineMarker_endpoint_circle_image hRS]

/-- Every isometry preserving the actual marked annulus preserves its derived boundary pair. -/
theorem torusAffineMarker_boundary_preserved {r : ℝ → ℝ} {h RN RS : ℝ}
    (hh : 0 < h) (hRN : 0 < RN) (hRS : 0 < RS)
    (hr : ContinuousOn r (Icc (-h) h)) (hpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hN : r h = RN) (hS : r (-h) = RS) (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) =
      torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) :
    torusAffineMarkerIsometry L b ''
        (torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
          torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS)) =
      torusAffineMarkerEllipse (torusAffineMarkerCenter h) RN (2 * RN) ∪
        torusAffineMarkerEllipse (torusAffineMarkerCenter (-h)) RS (2 * RS) := by
  have hi : Function.Injective (torusAffineMarkerIsometry L b) :=
    (torusAffineMarkerIsometryHomeomorph L b).injective
  rw [← torusAffineMarker_marked_boundary hh hRN hRS hr hpos hN hS, image_sdiff hi]
  have he := (torusAffineMarkerIsometryHomeomorph L b).image_closure
    (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h)
  change torusAffineMarkerIsometry L b ''
    closure (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) =
    closure (torusAffineMarkerIsometry L b ''
      (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h)) at he
  rw [he,hp]

/-- An actual interior non-evenness witness excludes central symmetry of the open carrier. -/
theorem torusAffineMarker_lateral_not_centrally_symmetric {r : ℝ → ℝ} {h : ℝ}
    (hpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hasym : ∃ z ∈ Ioo 0 h, r (-z) ≠ r z) :
    ¬ (∀ p ∈ parabolicConvexClosureLateralCarrier r h,
      -p ∈ parabolicConvexClosureLateralCarrier r h) := by
  obtain ⟨z,hz,hne⟩ := hasym
  have hzI : z ∈ Ioo (-h) h := ⟨by linarith [hz.1,hz.2],hz.2⟩
  have hp := hpos z (Ioo_subset_Icc_self hzI)
  have hn : ‖(r z : ℂ)‖ = r z := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  let p := parabolicConvexClosureRadialPoint (r z) z
  have hmem : p ∈ parabolicConvexClosureLateralCarrier r h := by
    exact ⟨hzI, by simpa only [p,parabolicConvexClosureRadialPoint_horizontal,
      parabolicConvexClosureRadialPoint_height] using hn⟩
  intro hall
  have he := (hall p hmem).2
  change ‖parabolicConvexClosureHorizontalCLM (-p)‖ = r ((-p) 2) at he
  rw [map_neg,norm_neg] at he
  change ‖parabolicConvexClosureHorizontalCLM (parabolicConvexClosureRadialPoint (r z) z)‖ = r (-z) at he
  rw [parabolicConvexClosureRadialPoint_horizontal] at he
  rw [hn] at he
  exact hne he.symm

/-- Actual generic open-annulus rigidity, with no boundary or stabilizer grant. -/
theorem torusAffineMarker_open_annulus_rigid (axes : MarkerEllipseAxesRecognition)
    {r : ℝ → ℝ} {h RN RS : ℝ} (hh : 0 < h) (hRN : 0 < RN) (hRS : 0 < RS)
    (hr : ContinuousOn r (Icc (-h) h)) (hpos : ∀ z ∈ Icc (-h) h, 0 < r z)
    (hN : r h = RN) (hS : r (-h) = RS)
    (hbreak : RN ≠ RS ∨ ∃ z ∈ Ioo 0 h, r (-z) ≠ r z)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) =
      torusAffineMarker '' parabolicConvexClosureLateralCarrier r h) :
    ∀ p, torusAffineMarkerIsometry L b p = p := by
  rcases torusAffineMarkerEllipse_pair_stabilizer axes hRN hRS hh L b
    (torusAffineMarker_boundary_preserved hh hRN hRS hr hpos hN hS L b hp) with hi | ⟨he,hi⟩
  · exact hi
  · exfalso
    rcases hbreak with hn | hasym
    · exact hn he
    · apply torusAffineMarker_lateral_not_centrally_symmetric hpos hasym
      intro p hpm
      have hm : -torusAffineMarker p ∈
          torusAffineMarker '' parabolicConvexClosureLateralCarrier r h := by
        rw [← hp]
        exact ⟨torusAffineMarker p,mem_image_of_mem _ hpm,hi _⟩
      obtain ⟨q,hq,hqp⟩ := hm
      have heq : q = -p := torusAffineMarker_injective (hqp.trans (torusAffineMarker_neg p).symm)
      rwa [heq] at hq

/-- The actual compiled SAME-radius ver500 closure specializes the generic marker theorem. -/
theorem torusAffineMarker_actual_meridian_rigid (axes : MarkerEllipseAxesRecognition)
    {RN μ h : ℝ} (d : ParabolicConvexClosureData RN μ h)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (torusAffineMarker '' parabolicConvexClosureLateralCarrier d.meridian h) =
      torusAffineMarker '' parabolicConvexClosureLateralCarrier d.meridian h) :
    ∀ p, torusAffineMarkerIsometry L b p = p :=
  torusAffineMarker_open_annulus_rigid axes d.height_pos d.radius_pos d.radius_pos
    d.meridian_continuous
    (parabolicConvexClosure_radius_pos_closed d.radius_pos d.lower_endpoint d.upper_endpoint
      d.meridian_exterior) d.upper_endpoint d.lower_endpoint (Or.inr d.asymmetric) L b hp

end
end TightVer401

