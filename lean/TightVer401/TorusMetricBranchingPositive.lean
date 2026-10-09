import TightVer401.TorusMetricBranching
import TightVer401.ClassicalExternal

/-! The entire actual positive-curvature region is unchanged by protected
branching when the actual stability estimates are negative on the support image.
ClassicalExternal is imported for the actual curvature/region definitions only;
none of its externally granted claims is used here. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Actual native preferred-chart curvature depends only on the actual map germ. -/
theorem nativeTorusChartCurvature_eq_of_eventuallyEq
    {F G : NonrigidTorusSource → Ambient} {p : NonrigidTorusSource}
    (h : F =ᶠ[𝓝 p] G) :
    nativeTorusChartCurvature F p = nativeTorusChartCurvature G p := by
  let e := chartAt (ModelProd ℝ ℝ) p
  let L := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let c := L.symm (e p)
  have hsource : p ∈ e.source := mem_chart_source (ModelProd ℝ ℝ) p
  have htarget : e p ∈ e.target := e.map_source hsource
  have hLc : L c = e p := L.apply_symm_apply (e p)
  have hc0 : ContinuousAt e.symm (L c) := by
    rw [hLc]
    exact e.continuousAt_symm htarget
  have hc : ContinuousAt (fun q : Coord => e.symm (L q)) c :=
    hc0.comp L.continuous.continuousAt
  have ht : Tendsto (fun q : Coord => e.symm (L q)) (𝓝 c) (𝓝 p) := by
    simpa only [hLc, e.left_inv hsource] using hc.tendsto
  have hchart : nativeProductCoordinateMap F p =ᶠ[𝓝 c]
      nativeProductCoordinateMap G p := by
    change (fun q : Coord => F (e.symm (L q))) =ᶠ[𝓝 c]
      (fun q : Coord => G (e.symm (L q)))
    exact h.comp_tendsto ht
  exact gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hchart)

/-- Off the actual compact support image, both literal branch germs equal F. -/
theorem protectedTorus_bending_branch_germs_off_support {T w : ℝ} [Fact (0 < T)]
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (ε : ℝ)
    {p : NonrigidTorusSource} (hp : p ∉ e '' tsupport Y) :
    (F + ε • protectedTorusBendingField e A Y =ᶠ[𝓝 p] F) ∧
      (F - ε • protectedTorusBendingField e A Y =ᶠ[𝓝 p] F) := by
  have hz := protectedTorusBendingField_eventually_zero e A hcompact hsupport hp
  constructor
  · filter_upwards [hz] with q hq
    simp only [Pi.add_apply, Pi.smul_apply, hq, smul_zero, add_zero]
  · filter_upwards [hz] with q hq
    simp only [Pi.sub_apply, Pi.smul_apply, hq, smul_zero, sub_zero]

/-- Off the support image, actual intrinsic chart curvatures of both branches
equal the baseline curvature, including all metric derivatives it uses. -/
theorem protectedTorus_bending_curvature_off_support {T w : ℝ} [Fact (0 < T)]
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (ε : ℝ)
    {p : NonrigidTorusSource} (hp : p ∉ e '' tsupport Y) :
    nativeTorusChartCurvature (F + ε • protectedTorusBendingField e A Y) p =
        nativeTorusChartCurvature F p ∧
      nativeTorusChartCurvature (F - ε • protectedTorusBendingField e A Y) p =
        nativeTorusChartCurvature F p := by
  obtain ⟨hplus, hminus⟩ :=
    protectedTorus_bending_branch_germs_off_support e A hcompact hsupport F ε hp
  exact ⟨nativeTorusChartCurvature_eq_of_eventuallyEq hplus,
    nativeTorusChartCurvature_eq_of_eventuallyEq hminus⟩

/-- Actual negative-curvature stability on K gives equality of both ENTIRE
positive regions and their actual images. No positive-region/image conclusion
is an input. These are the same literal Z and ε as the metric branching theorem. -/
theorem protectedTorus_bending_positive_regions {T w : ℝ} [Fact (0 < T)]
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (ε : ℝ)
    (hFneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature F p < 0)
    (hplusneg : ∀ p ∈ e '' tsupport Y,
      nativeTorusChartCurvature (F + ε • protectedTorusBendingField e A Y) p < 0)
    (hminusneg : ∀ p ∈ e '' tsupport Y,
      nativeTorusChartCurvature (F - ε • protectedTorusBendingField e A Y) p < 0) :
    let Z := protectedTorusBendingField e A Y
    nativeTorusPositiveRegion (F + ε • Z) = nativeTorusPositiveRegion F ∧
      nativeTorusPositiveRegion (F - ε • Z) = nativeTorusPositiveRegion F ∧
      EqOn (F + ε • Z) F (nativeTorusPositiveRegion F) ∧
      EqOn (F - ε • Z) F (nativeTorusPositiveRegion F) ∧
      (F + ε • Z) '' nativeTorusPositiveRegion (F + ε • Z) =
        F '' nativeTorusPositiveRegion F ∧
      (F - ε • Z) '' nativeTorusPositiveRegion (F - ε • Z) =
        F '' nativeTorusPositiveRegion F ∧
      (F + ε • Z) '' nativeTorusPositiveRegion (F + ε • Z) =
        (F - ε • Z) '' nativeTorusPositiveRegion (F - ε • Z) := by
  let Z := protectedTorusBendingField e A Y
  have hregions : nativeTorusPositiveRegion (F + ε • Z) = nativeTorusPositiveRegion F ∧
      nativeTorusPositiveRegion (F - ε • Z) = nativeTorusPositiveRegion F := by
    constructor
    · ext p
      change (0 < nativeTorusChartCurvature (F + ε • Z) p) ↔
        (0 < nativeTorusChartCurvature F p)
      by_cases hp : p ∈ e '' tsupport Y
      · exact ⟨fun h => False.elim (lt_asymm h (hplusneg p hp)),
          fun h => False.elim (lt_asymm h (hFneg p hp))⟩
      · rw [(protectedTorus_bending_curvature_off_support e A hcompact hsupport F ε hp).1]
    · ext p
      change (0 < nativeTorusChartCurvature (F - ε • Z) p) ↔
        (0 < nativeTorusChartCurvature F p)
      by_cases hp : p ∈ e '' tsupport Y
      · exact ⟨fun h => False.elim (lt_asymm h (hminusneg p hp)),
          fun h => False.elim (lt_asymm h (hFneg p hp))⟩
      · rw [(protectedTorus_bending_curvature_off_support e A hcompact hsupport F ε hp).2]
  have hagree : EqOn (F + ε • Z) F (nativeTorusPositiveRegion F) ∧
      EqOn (F - ε • Z) F (nativeTorusPositiveRegion F) := by
    have hnot : ∀ p ∈ nativeTorusPositiveRegion F, p ∉ e '' tsupport Y := by
      intro p hp hK
      exact lt_asymm hp (hFneg p hK)
    constructor
    · intro p hp
      exact (protectedTorus_bending_branch_germs_off_support e A hcompact hsupport F ε
        (hnot p hp)).1.self_of_nhds
    · intro p hp
      exact (protectedTorus_bending_branch_germs_off_support e A hcompact hsupport F ε
        (hnot p hp)).2.self_of_nhds
  have hplusImage : (F + ε • Z) '' nativeTorusPositiveRegion (F + ε • Z) =
      F '' nativeTorusPositiveRegion F := by
    rw [hregions.1]
    exact hagree.1.image_eq
  have hminusImage : (F - ε • Z) '' nativeTorusPositiveRegion (F - ε • Z) =
      F '' nativeTorusPositiveRegion F := by
    rw [hregions.2]
    exact hagree.2.image_eq
  exact ⟨hregions.1, hregions.2, hagree.1, hagree.2,
    hplusImage, hminusImage, hplusImage.trans hminusImage.symm⟩

end
end TightVer401
