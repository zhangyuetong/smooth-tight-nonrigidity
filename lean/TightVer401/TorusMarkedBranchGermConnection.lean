import TightVer401.TorusMetricBranchingPositive
import TightVer401.ProtectedTorusLinearFieldConnection

/-! Actual locality and positive-image preservation for the literal marked
branches B(F) ± a C(Z). The original field Z, placement and support image remain
the same; no identification with B(F ± a Z) is made. These are consumers of
actual support negativity, not a marker or torus construction grant. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable {T w : ℝ} [Fact (0 < T)]

/-- Off the SAME compact support image, the full marked branch map germs
are those of the marked baseline. No smoothness or invertibility is needed. -/
theorem protectedTorus_marked_branch_germs_off_support
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (B C : Ambient →L[ℝ] Ambient) (a : ℝ)
    {p : NonrigidTorusSource} (hp : p ∉ e '' tsupport Y) :
    ((fun q => B (F q) + a • C (protectedTorusBendingField e A Y q))
      =ᶠ[𝓝 p] (fun q => B (F q))) ∧
    ((fun q => B (F q) - a • C (protectedTorusBendingField e A Y q))
      =ᶠ[𝓝 p] (fun q => B (F q))) := by
  have hz := protectedTorusBendingField_eventually_zero e A hcompact hsupport hp
  constructor
  · filter_upwards [hz] with q hq
    rw [hq, map_zero, smul_zero, add_zero]
  · filter_upwards [hz] with q hq
    rw [hq, map_zero, smul_zero, sub_zero]

/-- All actual preferred-chart metric and curvature derivatives agree off
that SAME support image, by the already proved native map-germ locality. -/
theorem protectedTorus_marked_curvature_off_support
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (B C : Ambient →L[ℝ] Ambient) (a : ℝ)
    {p : NonrigidTorusSource} (hp : p ∉ e '' tsupport Y) :
    nativeTorusChartCurvature
      (fun q => B (F q) + a • C (protectedTorusBendingField e A Y q)) p =
        nativeTorusChartCurvature (fun q => B (F q)) p ∧
    nativeTorusChartCurvature
      (fun q => B (F q) - a • C (protectedTorusBendingField e A Y q)) p =
        nativeTorusChartCurvature (fun q => B (F q)) p := by
  obtain ⟨hplus, hminus⟩ :=
    protectedTorus_marked_branch_germs_off_support e A hcompact hsupport F B C a hp
  exact ⟨nativeTorusChartCurvature_eq_of_eventuallyEq hplus,
    nativeTorusChartCurvature_eq_of_eventuallyEq hminus⟩

/-- Derived preservation of BOTH entire actual positive regions and images
for the same literal marked family, given actual baseline/branch negativity
on the same original support image. No positive-region conclusion is an input. -/
theorem protectedTorus_marked_positive_regions
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (F : NonrigidTorusSource → Ambient) (B C : Ambient →L[ℝ] Ambient) (a : ℝ)
    (hFneg : ∀ p ∈ e '' tsupport Y,
      nativeTorusChartCurvature (fun q => B (F q)) p < 0)
    (hplusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (fun q => B (F q) + a • C (protectedTorusBendingField e A Y q)) p < 0)
    (hminusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (fun q => B (F q) - a • C (protectedTorusBendingField e A Y q)) p < 0) :
    let G := fun q => B (F q)
    let Z := fun q => C (protectedTorusBendingField e A Y q)
    nativeTorusPositiveRegion (G + a • Z) = nativeTorusPositiveRegion G ∧
      nativeTorusPositiveRegion (G - a • Z) = nativeTorusPositiveRegion G ∧
      EqOn (G + a • Z) G (nativeTorusPositiveRegion G) ∧
      EqOn (G - a • Z) G (nativeTorusPositiveRegion G) ∧
      (G + a • Z) '' nativeTorusPositiveRegion (G + a • Z) =
        G '' nativeTorusPositiveRegion G ∧
      (G - a • Z) '' nativeTorusPositiveRegion (G - a • Z) =
        G '' nativeTorusPositiveRegion G ∧
      (G + a • Z) '' nativeTorusPositiveRegion (G + a • Z) =
        (G - a • Z) '' nativeTorusPositiveRegion (G - a • Z) := by
  let G := fun q => B (F q)
  let Z := fun q => C (protectedTorusBendingField e A Y q)
  have hregions : nativeTorusPositiveRegion (G + a • Z) = nativeTorusPositiveRegion G ∧
      nativeTorusPositiveRegion (G - a • Z) = nativeTorusPositiveRegion G := by
    constructor
    · ext p
      change (0 < nativeTorusChartCurvature (G + a • Z) p) ↔
        (0 < nativeTorusChartCurvature G p)
      by_cases hp : p ∈ e '' tsupport Y
      · exact ⟨fun h => False.elim (lt_asymm h (hplusneg p hp)),
          fun h => False.elim (lt_asymm h (hFneg p hp))⟩
      · have hk : nativeTorusChartCurvature (G + a • Z) p =
            nativeTorusChartCurvature G p :=
          (protectedTorus_marked_curvature_off_support e A hcompact hsupport F B C a hp).1
        rw [hk]
    · ext p
      change (0 < nativeTorusChartCurvature (G - a • Z) p) ↔
        (0 < nativeTorusChartCurvature G p)
      by_cases hp : p ∈ e '' tsupport Y
      · exact ⟨fun h => False.elim (lt_asymm h (hminusneg p hp)),
          fun h => False.elim (lt_asymm h (hFneg p hp))⟩
      · have hk : nativeTorusChartCurvature (G - a • Z) p =
            nativeTorusChartCurvature G p :=
          (protectedTorus_marked_curvature_off_support e A hcompact hsupport F B C a hp).2
        rw [hk]
  have hagree : EqOn (G + a • Z) G (nativeTorusPositiveRegion G) ∧
      EqOn (G - a • Z) G (nativeTorusPositiveRegion G) := by
    have hnot : ∀ p ∈ nativeTorusPositiveRegion G, p ∉ e '' tsupport Y := by
      intro p hp hK
      exact lt_asymm hp (hFneg p hK)
    constructor
    · intro p hp
      exact (protectedTorus_marked_branch_germs_off_support
        e A hcompact hsupport F B C a (hnot p hp)).1.self_of_nhds
    · intro p hp
      exact (protectedTorus_marked_branch_germs_off_support
        e A hcompact hsupport F B C a (hnot p hp)).2.self_of_nhds
  have hplusImage : (G + a • Z) '' nativeTorusPositiveRegion (G + a • Z) =
      G '' nativeTorusPositiveRegion G := by
    rw [hregions.1]
    exact hagree.1.image_eq
  have hminusImage : (G - a • Z) '' nativeTorusPositiveRegion (G - a • Z) =
      G '' nativeTorusPositiveRegion G := by
    rw [hregions.2]
    exact hagree.2.image_eq
  exact ⟨hregions.1, hregions.2, hagree.1, hagree.2,
    hplusImage, hminusImage, hplusImage.trans hminusImage.symm⟩

/-- An actual invertible linear marking preserves absence of open planar
patches by pulling back the actual nonzero affine-plane functional. -/
theorem torusMarked_hasNoOpenPlanarPatch_linear_equiv
    {M : Type*} [TopologicalSpace M] {F : M → Ambient}
    (hF : HasNoOpenPlanarPatch F) (B : Ambient ≃L[ℝ] Ambient) :
    HasNoOpenPlanarPatch (fun p => B (F p)) := by
  intro U hU hne ell hell c hplane
  have hcomp : ell.comp B.toContinuousLinearMap ≠ 0 := by
    intro hz
    apply hell
    ext v
    change ell v = 0
    have hv := congrArg (fun L : Ambient →L[ℝ] ℝ => L (B.symm v)) hz
    change ell (B (B.symm v)) = 0 at hv
    simpa only [B.apply_symm_apply] using hv
  exact hF U hU hne (ell.comp B.toContinuousLinearMap) hcomp c hplane

end
end TightVer401
