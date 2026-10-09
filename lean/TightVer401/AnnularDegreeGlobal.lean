import TightVer401.AnnularDegreeDefinitions
import TightVer401.AnnularDegreeExclusion
import TightVer401.AnnularDegreeLocalInverse
import TightVer401.AnnularDegreeLocalJacobian
import TightVer401.AnnularDegreeJordan
import TightVer401.AnnularDegreeAngularForm
import TightVer401.AnnularDegreeFormula
import Mathlib.Topology.Homeomorph.Lemmas

/-! Global assembly after the actual signed-preimage formula has been proved.
The signed-count hypotheses below are explicitly intermediate: the public
annular degree criterion must discharge them from actual boundary winding.
Boundary differential rank is never a hypothesis of this assembly. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff

/-- A continuous compact-source bijection gives the actual closure
homeomorphism, with its forward map identified pointwise. -/
theorem annular_compact_closure_homeomorph
    {F : Coord → Coord} {K L : Set Coord}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hMaps : MapsTo F K L)
    (hInj : InjOn F K) (hSurj : SurjOn F K L) :
    ∃ H : K ≃ₜ L, ∀ x : K, (H x : Coord) = F x := by
  classical
  let f : K → L := fun x => ⟨F x, hMaps x.property⟩
  have hf : Bijective f := by
    constructor
    · intro x z hxz
      apply Subtype.ext
      exact hInj x.property z.property (congrArg Subtype.val hxz)
    · intro y
      obtain ⟨x, hx, hxy⟩ := hSurj y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : K ≃ L := Equiv.ofBijective f hf
  have he : Continuous e := hF.domRestrict.subtype_mk _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact ⟨he.homeoOfEquivCompactToT2, fun _ => rfl⟩

/-- Intermediate global assembly. Zero actual signed counts outside the
target closure exclude boundary hits by actual local openness; unit absolute
counts in the target interior give unique actual interior preimages. The
closure homeomorphism and smooth inverse are then constructed. -/
theorem annular_global_inverse_of_signed_counts
    {F : Coord → Coord} {K L V : Set Coord} {s : ℤ}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hFs : ContDiffOn ℝ ∞ F (interior K))
    (hs : s = 1 ∨ s = -1)
    (hJ : ∀ x ∈ interior K, 0 < (s : ℝ) * annularJacobian F x)
    (hV : IsOpen V) (hInterior : interior L = V) (hClosure : closure V = L)
    (hBoundaryImage : F '' frontier K = frontier V)
    (hBoundaryInj : InjOn F (frontier K))
    (hZero : ∀ y ∉ L, annularSignedPreimageCount F K y = 0)
    (hOne : ∀ y ∈ V, (annularSignedPreimageCount F K y).natAbs = 1) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      e.source = interior K ∧ e.target = V ∧ (e : Coord → Coord) = F ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∃ H : K ≃ₜ L, ∀ x : K, (H x : Coord) = F x := by
  classical
  have hj : ∀ x ∈ interior K, annularJacobian F x ≠ 0 :=
    fun x hx => annularJacobian_ne_zero_of_sign (hJ x hx)
  have hOffExterior : ∀ y ∈ Lᶜ, y ∉ F '' frontier K := by
    intro y hy hboundary
    have hyfront : y ∈ frontier V := hBoundaryImage ▸ hboundary
    exact hy (hClosure ▸ frontier_subset_closure hyfront)
  have hAvoid := annular_interior_avoids_closure_zero_count_region
    hK hF hFs hs hJ hOffExterior (fun y hy => hZero y hy)
  have hForbiddenClosure : closure Lᶜ = Vᶜ := by
    rw [closure_compl, hInterior]
  have hMapsInterior : MapsTo F (interior K) V := by
    intro x hx
    have h := hAvoid x hx
    rw [hForbiddenClosure] at h
    exact not_not.mp h
  have hOffInterior : ∀ y ∈ V, y ∉ F '' frontier K := by
    intro y hy hboundary
    have hyfront : y ∈ frontier V := hBoundaryImage ▸ hboundary
    exact hyfront.2 (hV.interior_eq.symm ▸ hy)
  have hUnique : ∀ y ∈ V, ∃! x, x ∈ interior K ∧ F x = y := by
    intro y hy
    have hfin := annularFiber_finite hK hF hFs hj (hOffInterior y hy)
    obtain ⟨x, hx, hunique⟩ := annularFiber_unique_of_signedCount_natAbs_one
      hfin hs (fun p hp => hJ p (annularFiber_subset_interior (hOffInterior y hy) hp))
      (hOne y hy)
    refine ⟨x, ⟨annularFiber_subset_interior (hOffInterior y hy) hx, hx.2⟩, ?_⟩
    intro z hz
    exact hunique z ⟨interior_subset hz.1, hz.2⟩
  have hImage : F '' interior K = V := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hMapsInterior hx
    · intro y hy
      obtain ⟨x, hx, _⟩ := hUnique y hy
      exact ⟨x, hx.1, hx.2⟩
  have hUniqueImage : ∀ y ∈ F '' interior K, ∃! x, x ∈ interior K ∧ F x = y :=
    fun y hy => hUnique y (hImage ▸ hy)
  have hInjInterior := annular_injOn_of_unique_preimages hUniqueImage
  have hMapsClosure : MapsTo F K L := by
    intro x hx
    by_cases hxi : x ∈ interior K
    · exact hClosure ▸ subset_closure (hMapsInterior hxi)
    · have hxf : x ∈ frontier K := ⟨subset_closure hx, hxi⟩
      have hyf : F x ∈ frontier V := hBoundaryImage ▸ mem_image_of_mem F hxf
      exact hClosure ▸ frontier_subset_closure hyf
  have hInjClosure : InjOn F K := by
    intro x hx z hz hxz
    by_cases hxi : x ∈ interior K
    · by_cases hzi : z ∈ interior K
      · exact hInjInterior hxi hzi hxz
      · have hzf : z ∈ frontier K := ⟨subset_closure hz, hzi⟩
        have hyf : F z ∈ frontier V := hBoundaryImage ▸ mem_image_of_mem F hzf
        have hyv : F z ∈ V := hxz ▸ hMapsInterior hxi
        exact (hyf.2 (hV.interior_eq.symm ▸ hyv)).elim
    · by_cases hzi : z ∈ interior K
      · have hxf : x ∈ frontier K := ⟨subset_closure hx, hxi⟩
        have hyf : F x ∈ frontier V := hBoundaryImage ▸ mem_image_of_mem F hxf
        have hyv : F x ∈ V := hxz.symm ▸ hMapsInterior hzi
        exact (hyf.2 (hV.interior_eq.symm ▸ hyv)).elim
      · exact hBoundaryInj ⟨subset_closure hx, hxi⟩ ⟨subset_closure hz, hzi⟩ hxz
  have hSurjClosure : SurjOn F K L := by
    intro y hy
    by_cases hyV : y ∈ V
    · obtain ⟨x, hx, _⟩ := hUnique y hyV
      exact ⟨x, interior_subset hx.1, hx.2⟩
    · have hyf : y ∈ frontier V :=
        ⟨hClosure.symm ▸ hy, hV.interior_eq.symm ▸ hyV⟩
      obtain ⟨x, hxf, hxy⟩ := hBoundaryImage.symm ▸ hyf
      exact ⟨x, hK.isClosed.closure_eq ▸ hxf.1, hxy⟩
  obtain ⟨e, heSource, heTarget, heF, heSmooth⟩ :=
    annular_exists_smooth_image_inverse isOpen_interior hFs hj hUniqueImage
  refine ⟨e, heSource, heTarget.trans hImage, heF, heSmooth, ?_⟩
  exact annular_compact_closure_homeomorph hK hF hMapsClosure hInjClosure hSurjClosure

/-- Exact transport of actual fibers, including their source membership. -/
def annularComplexFiberCoordEquiv (F : Coord → Coord) (K : Set ℂ) (y : ℂ) :
    {z // z ∈ K ∧ annularComplexConjugate F z = y} ≃
      annularFiber F (seamComplexCoord '' K) (seamComplexCoord y) where
  toFun z := ⟨seamComplexCoord z,
    ⟨⟨z, z.property.1, rfl⟩, by
      simpa only [annularComplexConjugate, comp_apply,
        ContinuousLinearEquiv.apply_symm_apply] using congrArg seamComplexCoord z.property.2⟩⟩
  invFun x := ⟨seamComplexCoord.symm x, by
    constructor
    · obtain ⟨z, hz, he⟩ := x.property.1
      simpa only [← he, ContinuousLinearEquiv.symm_apply_apply] using hz
    · change seamComplexCoord.symm (F (seamComplexCoord (seamComplexCoord.symm x))) = y
      rw [ContinuousLinearEquiv.apply_symm_apply, x.property.2,
        ContinuousLinearEquiv.symm_apply_apply]⟩
  left_inv z := Subtype.ext (seamComplexCoord.symm_apply_apply z)
  right_inv x := Subtype.ext (seamComplexCoord.apply_symm_apply x)

theorem annular_complex_fiber_ncard_coord (F : Coord → Coord) (K : Set ℂ) (y : ℂ) :
    ({z | z ∈ K ∧ annularComplexConjugate F z = y}).ncard =
      (annularFiber F (seamComplexCoord '' K) (seamComplexCoord y)).ncard :=
  Set.ncard_congr' (annularComplexFiberCoordEquiv F K y)

/-- A homeomorphism of the actual complex boundary transports to the
coordinate boundary image and injectivity hypotheses of global assembly. -/
theorem annular_transport_boundary_homeomorph
    {F : Coord → Coord} {S T : Set ℂ} (B : S ≃ₜ T)
    (hB : ∀ x : S, (B x : ℂ) = annularComplexConjugate F x) :
    F '' (seamComplexCoord '' S) = seamComplexCoord '' T ∧
      InjOn F (seamComplexCoord '' S) := by
  constructor
  · apply Subset.antisymm
    · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨B ⟨z, hz⟩, (B ⟨z, hz⟩).property, ?_⟩
      simpa only [annularComplexConjugate, comp_apply,
        ContinuousLinearEquiv.apply_symm_apply] using congrArg seamComplexCoord (hB ⟨z, hz⟩)
    · rintro y ⟨z, hz, rfl⟩
      let x : S := B.symm ⟨z, hz⟩
      refine ⟨seamComplexCoord x, ⟨x, x.property, rfl⟩, ?_⟩
      have hx : (B x : ℂ) = z := congrArg Subtype.val (B.apply_symm_apply ⟨z, hz⟩)
      have hf : annularComplexConjugate F x = z := (hB x).symm.trans hx
      simpa only [annularComplexConjugate, comp_apply,
        ContinuousLinearEquiv.apply_symm_apply] using congrArg seamComplexCoord hf
  · rintro x ⟨z, hz, rfl⟩ w ⟨v, hv, rfl⟩ hFzv
    have hfv : annularComplexConjugate F z = annularComplexConjugate F v :=
      congrArg seamComplexCoord.symm hFzv
    have hbv : B ⟨z, hz⟩ = B ⟨v, hv⟩ :=
      Subtype.ext ((hB ⟨z, hz⟩).trans (hfv.trans (hB ⟨v, hv⟩).symm))
    exact congrArg seamComplexCoord (congrArg Subtype.val (B.injective hbv))

theorem annularCoordJordanClosure_isCompact (Ho Hi : ℂ ≃ₜ ℂ) :
    IsCompact (annularCoordJordanClosure Ho Hi) :=
  (annularJordanClosure_isCompact Ho Hi).image seamComplexCoord.continuous

theorem annularCoordJordanInterior_isOpen (Ho Hi : ℂ ≃ₜ ℂ) :
    IsOpen (annularCoordJordanInterior Ho Hi) :=
  seamComplexCoord.toHomeomorph.isOpenMap _ (annularJordanInterior_isOpen Ho Hi)

theorem interior_annularCoordJordanClosure (Ho Hi : ℂ ≃ₜ ℂ) :
    interior (annularCoordJordanClosure Ho Hi) = annularCoordJordanInterior Ho Hi := by
  change interior (seamComplexCoord.toHomeomorph '' annularJordanClosure Ho Hi) =
    seamComplexCoord.toHomeomorph '' annularJordanInterior Ho Hi
  rw [← seamComplexCoord.toHomeomorph.image_interior,
    interior_annularJordanClosure]

theorem closure_annularCoordJordanInterior (Ho Hi : ℂ ≃ₜ ℂ)
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    closure (annularCoordJordanInterior Ho Hi) = annularCoordJordanClosure Ho Hi := by
  change closure (seamComplexCoord.toHomeomorph '' annularJordanInterior Ho Hi) =
    seamComplexCoord.toHomeomorph '' annularJordanClosure Ho Hi
  rw [← seamComplexCoord.toHomeomorph.image_closure,
    closure_annularJordanInterior Ho Hi hn]

theorem frontier_annularCoordJordanInterior (Ho Hi : ℂ ≃ₜ ℂ)
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    frontier (annularCoordJordanInterior Ho Hi) = seamComplexCoord '' annularJordanBoundary Ho Hi := by
  change frontier (seamComplexCoord.toHomeomorph '' annularJordanInterior Ho Hi) =
    seamComplexCoord.toHomeomorph ''
      (frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi))
  rw [← seamComplexCoord.toHomeomorph.image_frontier,
    frontier_annularJordanInterior Ho Hi hn]

theorem frontier_annularCoordJordanClosure (Ho Hi : ℂ ≃ₜ ℂ)
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    frontier (annularCoordJordanClosure Ho Hi) = seamComplexCoord '' annularJordanBoundary Ho Hi := by
  rw [frontier, (annularCoordJordanClosure_isCompact Ho Hi).isClosed.closure_eq,
    interior_annularCoordJordanClosure]
  rw [← closure_annularCoordJordanInterior Ho Hi hn,
    ← (annularCoordJordanInterior_isOpen Ho Hi).frontier_eq]
  exact frontier_annularCoordJordanInterior Ho Hi hn

theorem annularJordanForbidden_eq_compl_closure (Ho Hi : ℂ ≃ₜ ℂ) :
    annularJordanForbidden Ho Hi = (annularJordanClosure Ho Hi)ᶜ := by
  ext z
  simp only [annularJordanForbidden, annularJordanClosure, mem_union,
    mem_compl_iff, Set.mem_sdiff, not_and_or, not_not, or_comm]

/-- The lift specified by positive source orientation agrees in endpoint
increment with the actual smooth lift used to define the angular integral. -/
theorem annular_positive_source_argument_integral
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ) :
    circleFormIntegral (fun _ => 1) (centeredArgument (H 0)) γ = 1 := by
  have hcenter : H 0 ∈ jordanInterior H := ⟨0, Metric.mem_ball_self zero_lt_one, rfl⟩
  obtain ⟨u, hu, hturn⟩ := hγ.positive (H 0) hcenter
  have hO : IsOpen {z : ℂ | z ≠ H 0} := isOpen_ne_fun continuous_id continuous_const
  have havoid : ∀ t, γ t ∈ {z : ℂ | z ≠ H 0} := by
    intro t heq
    have ht := hγ.toRegular.mem_frontier t
    rw [(jordanInterior_isOpen H).frontier_eq] at ht
    exact ht.2 (heq ▸ hcenter)
  obtain ⟨v, hv, hproj⟩ := annular_exists_smooth_real_circuit_lift hO
    (smoothCircleOn_centeredArgument (H 0)) hγ.smooth havoid
  let vI : C(unitInterval, ℝ) :=
    ⟨fun t => v t, hv.continuous.comp continuous_subtype_val⟩
  have hinc : v 1 - v 0 = 1 := by
    have hh := real_lift_path_increment_eq vI u (fun t => (hproj t).trans (hu t).symm)
    change v 1 - v 0 = u 1 - u 0 at hh
    rw [hh, hturn]
    ring
  simpa only [one_mul, hinc] using circleFormIntegral_constant_weight hO
    (smoothCircleOn_centeredArgument (H 0)) (fun _ => 1) γ hγ.smooth havoid
    v hv.continuous hproj 1 (fun _ _ => rfl)

/-- Intermediate interface with a full winding profile, subsequently derived
from the ordinary one-point component tests in `AnnularDegreeCriterion`.
Its winding premises concern only actual
boundary integrals, never a degree/count
identity or a prescribed global image. The boundary homeomorphism covers the
two disjoint nested Jordan curves and permits either component assignment. -/
def AnnularDegreeGlobalDiffeomorphismClaim : Prop :=
  ∀ (Houter Hinner Touter Tinner : ℂ ≃ₜ ℂ) (γouter γinner : ℝ → ℂ),
    PositiveJordanParametrization Houter γouter →
    PositiveJordanParametrization Hinner γinner →
    closure (jordanInterior Hinner) ⊆ jordanInterior Houter →
    closure (jordanInterior Tinner) ⊆ jordanInterior Touter →
    ∀ (F : Coord → Coord) (O : Set Coord), IsOpen O → ContDiffOn ℝ ∞ F O →
      annularCoordJordanClosure Houter Hinner ⊆ O →
      ∀ (s : ℤ), (s = 1 ∨ s = -1) →
        (∀ x ∈ annularCoordJordanInterior Houter Hinner,
          0 < (s : ℝ) * annularJacobian F x) →
        ∀ B : annularJordanBoundary Houter Hinner ≃ₜ annularJordanBoundary Touter Tinner,
          (∀ x, (B x : ℂ) = annularComplexConjugate F x) →
          (∀ y ∈ annularJordanForbidden Touter Tinner,
            annularBoundaryIntegral F γouter γinner y = 0) →
          (∀ y ∈ annularJordanInterior Touter Tinner,
            |annularBoundaryIntegral F γouter γinner y| = 1) →
          ∃ e : OpenPartialHomeomorph Coord Coord,
            e.source = annularCoordJordanInterior Houter Hinner ∧
            e.target = annularCoordJordanInterior Touter Tinner ∧
            (e : Coord → Coord) = F ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
            ∃ H : annularCoordJordanClosure Houter Hinner ≃ₜ
                annularCoordJordanClosure Touter Tinner,
              ∀ x, (H x : Coord) = F x

/-- The annular degree criterion for the actual map. The degree identity is
proved in `AnnularDegreeFormula`, and the inverse is assembled from the actual
nonzero derivative. Interior points avoid both target Jordan boundaries;
boundary derivatives are allowed to degenerate. -/
theorem annular_degree_global_diffeomorphism_core : AnnularDegreeGlobalDiffeomorphismClaim := by
  classical
  intro Ho Hi To Ti γo γi hγo hγi hnS hnT F O hO hF hKO s hs hJ B hB hZeroW hOneW
  let K := annularCoordJordanClosure Ho Hi
  let L := annularCoordJordanClosure To Ti
  let V := annularCoordJordanInterior To Ti
  have hK : IsCompact K := annularCoordJordanClosure_isCompact Ho Hi
  have hKi : interior K = annularCoordJordanInterior Ho Hi :=
    interior_annularCoordJordanClosure Ho Hi
  have hLi : interior L = V := interior_annularCoordJordanClosure To Ti
  have hVc : closure V = L := closure_annularCoordJordanInterior To Ti hnT
  have hV : IsOpen V := annularCoordJordanInterior_isOpen To Ti
  have hFc : ContinuousOn F K := hF.continuousOn.mono hKO
  have hFs : ContDiffOn ℝ ∞ F (interior K) := hF.mono (fun _ hx => hKO (interior_subset hx))
  have hJs : ∀ x ∈ interior K, 0 < (s : ℝ) * annularJacobian F x :=
    fun x hx => hJ x (hKi ▸ hx)
  have hKf : frontier K = seamComplexCoord '' annularJordanBoundary Ho Hi :=
    frontier_annularCoordJordanClosure Ho Hi hnS
  have hVf : frontier V = seamComplexCoord '' annularJordanBoundary To Ti :=
    frontier_annularCoordJordanInterior To Ti hnT
  obtain ⟨hBoundary, hBoundaryInj⟩ := annular_transport_boundary_homeomorph B hB
  have hBoundaryImage : F '' frontier K = frontier V := by
    rw [hKf, hVf]
    exact hBoundary
  have hBoundaryInj' : InjOn F (frontier K) := hKf.symm ▸ hBoundaryInj
  let Oc : Set ℂ := seamComplexCoord ⁻¹' O
  have hOc : IsOpen Oc := hO.preimage seamComplexCoord.continuous
  have hComplex : ContDiffOn ℝ ∞ (annularComplexConjugate F) Oc :=
    (hF.comp_continuousLinearMap (seamComplexCoord : ℂ →L[ℝ] Coord)).continuousLinearMap_comp
      (seamComplexCoord.symm : Coord →L[ℝ] ℂ)
  have hKOc : annularJordanClosure Ho Hi ⊆ Oc := by
    intro z hz
    exact hKO ⟨z, hz, rfl⟩
  have hComplexJ : ∀ z ∈ annularJordanInterior Ho Hi,
      0 < (s : ℝ) * (fderiv ℝ (annularComplexConjugate F) z).det := by
    intro z hz
    have hzO : seamComplexCoord z ∈ O :=
      hKO ⟨z, annularJordanInterior_subset_closure Ho Hi hz, rfl⟩
    have hdiff := (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hzO)
    have heq := annular_complex_conjugate_jacobian hdiff
    change annularJacobian F (seamComplexCoord z) =
      (fderiv ℝ (annularComplexConjugate F) z).det at heq
    rw [← heq]
    exact hJ _ ⟨z, hz, rfl⟩
  have hsR : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hPositiveO := annular_positive_source_argument_integral hγo
  have hPositiveI := annular_positive_source_argument_integral hγi
  have hFormula : ∀ y, y ∉ F '' frontier K →
      (annularSignedPreimageCount F K y : ℝ) =
        annularBoundaryIntegral F γo γi (seamComplexCoord.symm y) := by
    intro y hy
    have hyc : seamComplexCoord.symm y ∉ annularComplexConjugate F ''
        (frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi)) := by
      rintro ⟨z, hz, heq⟩
      apply hy
      refine ⟨seamComplexCoord z, hKf.symm ▸ ⟨z, hz, rfl⟩, ?_⟩
      simpa only [annularComplexConjugate, comp_apply,
        ContinuousLinearEquiv.apply_symm_apply] using congrArg seamComplexCoord heq
    have hform := annular_complex_positive_boundary_preimage_formula
      hγo.toRegular hγi.toRegular hnS hPositiveO hPositiveI
      (annularComplexConjugate F) Oc hOc hComplex hKOc (s : ℝ) hsR hComplexJ
      (seamComplexCoord.symm y) hyc
    have hcard := annular_complex_fiber_ncard_coord F
      (annularJordanClosure Ho Hi) (seamComplexCoord.symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hcard
    change ({z | z ∈ annularJordanClosure Ho Hi ∧
      annularComplexConjugate F z = seamComplexCoord.symm y}).ncard =
      (annularFiber F K y).ncard at hcard
    have hcount := annularSignedPreimageCount_off_boundary hK hFc hFs hs hJs hy
    rw [hcount]
    push_cast
    change (s : ℝ) * ((annularFiber F K y).ncard : ℝ) =
      annularBoundaryIntegral F γo γi (seamComplexCoord.symm y)
    rw [← hcard]
    exact hform.symm
  have hZero : ∀ y ∉ L, annularSignedPreimageCount F K y = 0 := by
    intro y hyL
    have hyoff : y ∉ F '' frontier K := by
      intro hyF
      have hyfront : y ∈ frontier V := hBoundaryImage ▸ hyF
      exact hyL (hVc ▸ frontier_subset_closure hyfront)
    have hyc : seamComplexCoord.symm y ∈ annularJordanForbidden To Ti := by
      rw [annularJordanForbidden_eq_compl_closure]
      intro hyc
      exact hyL ⟨seamComplexCoord.symm y, hyc, seamComplexCoord.apply_symm_apply y⟩
    have hz : (annularSignedPreimageCount F K y : ℝ) = 0 :=
      (hFormula y hyoff).trans (hZeroW _ hyc)
    exact_mod_cast hz
  have hOne : ∀ y ∈ V, (annularSignedPreimageCount F K y).natAbs = 1 := by
    intro y hyV
    have hyoff : y ∉ F '' frontier K := by
      intro hyF
      have hyfront : y ∈ frontier V := hBoundaryImage ▸ hyF
      exact hyfront.2 (hV.interior_eq.symm ▸ hyV)
    have hyc : seamComplexCoord.symm y ∈ annularJordanInterior To Ti := by
      obtain ⟨z, hz, heq⟩ := hyV
      simpa only [← heq, ContinuousLinearEquiv.symm_apply_apply] using hz
    have hc : |(annularSignedPreimageCount F K y : ℝ)| = 1 := by
      rw [hFormula y hyoff]
      exact hOneW _ hyc
    have hn : ((annularSignedPreimageCount F K y).natAbs : ℝ) = 1 := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hc
    exact_mod_cast hn
  obtain ⟨e, heS, heT, heF, heSmooth, H, hHF⟩ :=
    annular_global_inverse_of_signed_counts hK hFc hFs hs hJs hV hLi hVc
      hBoundaryImage hBoundaryInj' hZero hOne
  exact ⟨e, heS.trans hKi, heT, heF, heSmooth, H, hHF⟩

end
end TightVer401
