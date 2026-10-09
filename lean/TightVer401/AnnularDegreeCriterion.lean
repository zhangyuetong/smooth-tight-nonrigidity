import TightVer401.AnnularDegreeDefinitions
import TightVer401.AnnularDegreeGlobal
import TightVer401.AnnularDegreeBoundaryHomeomorphs
import TightVer401.AnnularDegreeJordanWinding

/-! The ordinary manuscript interface: two actual boundary homeomorphisms
and one ordinary winding value for each image curve. The full winding
profile and union boundary homeomorphism are derived, rather than assumed.
Source disk contours are positive. Subtracting the inner source contour
implements the opposite induced annular boundary orientation. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff

/-- A homeomorphism of the actual boundary identifies the entire image
loop with the target Jordan frontier, including all real parameter values. -/
theorem annular_image_jordan_loop_range_of_boundary_homeomorph
    {f : ℂ → ℂ} {Hs Ht : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization Hs γ)
    (B : frontier (jordanInterior Hs) ≃ₜ frontier (jordanInterior Ht))
    (hB : ∀ x, (B x : ℂ) = f x) :
    range (f ∘ γ) = frontier (jordanInterior Ht) := by
  apply Subset.antisymm
  · rintro y ⟨t, rfl⟩
    change f (γ t) ∈ frontier (jordanInterior Ht)
    have hb : (B ⟨γ t, hγ.mem_frontier t⟩ : ℂ) = f (γ t) :=
      hB ⟨γ t, hγ.mem_frontier t⟩
    rw [← hb]
    exact (B ⟨γ t, hγ.mem_frontier t⟩).property
  · intro y hy
    let x : frontier (jordanInterior Hs) := B.symm ⟨y, hy⟩
    have hx : (x : ℂ) ∈ γ '' Icc 0 1 := by
      rw [hγ.boundary]
      exact x.property
    obtain ⟨t, _, htx⟩ := hx
    refine ⟨t, ?_⟩
    change f (γ t) = y
    rw [htx]
    exact (hB x).symm.trans (congrArg Subtype.val (B.apply_symm_apply ⟨y, hy⟩))

/-- All source boundary points lie in the actual closed annulus. -/
theorem annular_jordan_boundary_subset_closure {Ho Hi : ℂ ≃ₜ ℂ}
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi) ⊆
      annularJordanClosure Ho Hi := by
  intro z hz
  have hzfront : z ∈ frontier (annularJordanInterior Ho Hi) :=
    (frontier_annularJordanInterior Ho Hi hn).symm ▸ hz
  exact closure_annularJordanInterior Ho Hi hn ▸ frontier_subset_closure hzfront

/-- The manuscript annular criterion from ordinary individual boundary
homeomorphisms and one winding test per boundary component. Both assignments
are supported and no image-boundary differential rank is required. -/
theorem annular_degree_ordinary_boundary_criterion_core : AnnularDegreeOrdinaryBoundaryClaim := by
  classical
  intro Ho Hi To Ti γo γi hγo hγi hnS hnT F O hO hF hKO s hs hJ swap Bo Bi hBo hBi w hw hWo hWi
  let Oc : Set ℂ := seamComplexCoord ⁻¹' O
  have hOc : IsOpen Oc := hO.preimage seamComplexCoord.continuous
  have hFc : ContDiffOn ℝ ∞ (annularComplexConjugate F) Oc :=
    (hF.comp_continuousLinearMap (seamComplexCoord : ℂ →L[ℝ] Coord)).continuousLinearMap_comp
      (seamComplexCoord.symm : Coord →L[ℝ] ℂ)
  have hBoundaryK := annular_jordan_boundary_subset_closure hnS
  have hBoundaryO : frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi) ⊆ Oc := by
    intro z hz
    exact hKO ⟨z, hBoundaryK hz, rfl⟩
  have hγoO : ∀ t, γo t ∈ Oc :=
    fun t => hBoundaryO (Or.inl (hγo.toRegular.mem_frontier t))
  have hγiO : ∀ t, γi t ∈ Oc :=
    fun t => hBoundaryO (Or.inr (hγi.toRegular.mem_frontier t))
  have hClosedO : γo 1 = γo 0 := by simpa using hγo.periodic 0
  have hClosedI : γi 1 = γi 0 := by simpa using hγi.periodic 0
  have hBoundaryCont : ContinuousOn (annularComplexConjugate F)
      (frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi)) :=
    hFc.continuousOn.mono hBoundaryO
  cases swap
  · have hImageO := annular_image_jordan_loop_range_of_boundary_homeomorph hγo.toRegular Bo hBo
    have hImageI := annular_image_jordan_loop_range_of_boundary_homeomorph hγi.toRegular Bi hBi
    obtain ⟨hZero, hOne⟩ := annular_boundary_winding_profile_of_one_point
      hOc hFc hγo.smooth hγi.smooth hγoO hγiO hClosedO hClosedI To Ti hnT
      hImageO hImageI w hw hWo hWi
    obtain ⟨B, hB⟩ := annular_jordan_boundary_homeomorph_of_components
      hnT hBoundaryCont Bo Bi hBo hBi
    exact annular_degree_global_diffeomorphism_core Ho Hi To Ti γo γi hγo hγi
      hnS hnT F O hO hF hKO s hs hJ B hB hZero hOne
  · have hImageO := annular_image_jordan_loop_range_of_boundary_homeomorph hγo.toRegular Bo hBo
    have hImageI := annular_image_jordan_loop_range_of_boundary_homeomorph hγi.toRegular Bi hBi
    obtain ⟨hZeroReverse, hOneReverse⟩ := annular_boundary_winding_profile_of_one_point
      hOc hFc hγi.smooth hγo.smooth hγiO hγoO hClosedI hClosedO To Ti hnT
      hImageI hImageO w hw hWi hWo
    have hZero : ∀ y ∈ annularJordanForbidden To Ti,
        annularBoundaryIntegral F γo γi y = 0 := by
      intro y hy
      have hh := hZeroReverse y hy
      unfold annularBoundaryIntegral
      linarith
    have hOne : ∀ y ∈ annularJordanInterior To Ti,
        |annularBoundaryIntegral F γo γi y| = 1 := by
      intro y hy
      unfold annularBoundaryIntegral
      rw [abs_sub_comm]
      exact hOneReverse y hy
    obtain ⟨Bswap, hBswap⟩ := annular_boundary_union_homeomorph_of_components
      ((annular_jordan_frontier_isCompact Ho).union (annular_jordan_frontier_isCompact Hi))
      hBoundaryCont (annular_nested_jordan_frontiers_disjoint hnT).symm Bo Bi hBo hBi
    let B := Bswap.trans (Homeomorph.setCongr
      (union_comm (frontier (jordanInterior Ti)) (frontier (jordanInterior To))))
    have hB : ∀ x, (B x : ℂ) = annularComplexConjugate F x := fun x => hBswap x
    exact annular_degree_global_diffeomorphism_core Ho Hi To Ti γo γi hγo hγi
      hnS hnT F O hO hF hKO s hs hJ B hB hZero hOne

end
end TightVer401
