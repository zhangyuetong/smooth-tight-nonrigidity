import TightVer401.IdentityBandPlanarSupportImage
import TightVer401.IdentityBandBendingPullback

/-! Exact transport of the retained field and its topological support to the
actual open planar image. The field is defined on that image's subtype. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Manifold

variable {M : Type*} [TopologicalSpace M]

/-- A source chart defined on all of M gives a genuine homeomorphism onto its
actual target, without making any choice outside that target. -/
def identityBandPlanarRegionHomeomorph (e : OpenPartialHomeomorph M Coord)
    (he : e.source = univ) : M ≃ₜ e.target :=
  ((Homeomorph.Set.univ M).symm.trans (Homeomorph.setCongr he.symm)).trans
    e.toHomeomorphSourceTarget

@[simp] theorem identityBandPlanarRegionHomeomorph_apply_val
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ) (p : M) :
    (identityBandPlanarRegionHomeomorph e he p).val = e p := rfl

@[simp] theorem identityBandPlanarRegionHomeomorph_symm_apply
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ) (q : e.target) :
    (identityBandPlanarRegionHomeomorph e he).symm q = e.symm q.val := rfl

/-- Reparametrize the actual retained vector field only on the planar domain. -/
def identityBandPlanarRegionField (e : OpenPartialHomeomorph M Coord)
    (he : e.source = univ) (Y : M → Ambient) : e.target → Ambient :=
  Y ∘ (identityBandPlanarRegionHomeomorph e he).symm

@[simp] theorem identityBandPlanarRegionField_apply
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ)
    (Y : M → Ambient) (q : e.target) :
    identityBandPlanarRegionField e he Y q = Y (e.symm q.val) := rfl

/-- Equality of the full topological supports, including their closure points. -/
theorem identityBandPlanarRegionField_tsupport
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ) (Y : M → Ambient) :
    (Subtype.val : e.target → Coord) '' tsupport (identityBandPlanarRegionField e he Y) =
      e '' tsupport Y := by
  let H := identityBandPlanarRegionHomeomorph e he
  change (Subtype.val : e.target → Coord) '' tsupport (Y ∘ H.symm) = e '' tsupport Y
  rw [tsupport_comp_eq_preimage]
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨H.symm z, hz, ?_⟩
    change (H (H.symm z)).val = z.val
    exact congrArg Subtype.val (H.apply_symm_apply z)
  · rintro ⟨p, hp, rfl⟩
    refine ⟨H p, ?_, ?_⟩
    · change H.symm (H p) ∈ tsupport Y
      simpa only [H.symm_apply_apply] using hp
    · rfl

theorem identityBandPlanarRegionField_hasCompactSupport
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ)
    {Y : M → Ambient} (hY : HasCompactSupport Y) :
    HasCompactSupport (identityBandPlanarRegionField e he Y) :=
  hY.comp_homeomorph (identityBandPlanarRegionHomeomorph e he).symm

theorem identityBandPlanarRegionField_nonzero
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ)
    {Y : M → Ambient} (hY : ∃ p, Y p ≠ 0) :
    ∃ q, identityBandPlanarRegionField e he Y q ≠ 0 := by
  obtain ⟨p, hp⟩ := hY
  let H := identityBandPlanarRegionHomeomorph e he
  refine ⟨H p, ?_⟩
  change Y (H.symm (H p)) ≠ 0
  simpa only [H.symm_apply_apply] using hp

/-- An existing protected source region transports through the same chart. -/
theorem identityBandPlanarRegionField_protected
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ)
    {Y : M → Ambient} {K : Set M} (hK : tsupport Y ⊆ K) :
    (Subtype.val : e.target → Coord) '' tsupport (identityBandPlanarRegionField e he Y) ⊆
      e '' K := by
  rw [identityBandPlanarRegionField_tsupport]
  exact image_mono hK

/-- The transported field is compact, nonzero, and has exactly the original
support image inside the prescribed actual protected region. -/
theorem identityBandPlanarRegionField_transport
    (e : OpenPartialHomeomorph M Coord) (he : e.source = univ)
    {Y : M → Ambient} (hcompact : HasCompactSupport Y) (hnonzero : ∃ p, Y p ≠ 0)
    {K : Set M} (hK : tsupport Y ⊆ K) :
    let Z := identityBandPlanarRegionField e he Y
    HasCompactSupport Z ∧ (∃ q, Z q ≠ 0) ∧
      (Subtype.val : e.target → Coord) '' tsupport Z = e '' tsupport Y ∧
      (Subtype.val : e.target → Coord) '' tsupport Z ⊆ e '' K := by
  exact ⟨identityBandPlanarRegionField_hasCompactSupport e he hcompact,
    identityBandPlanarRegionField_nonzero e he hnonzero,
    identityBandPlanarRegionField_tsupport e he Y,
    identityBandPlanarRegionField_protected e he hK⟩

/-- The full protected bending support lies in the image of the same physical
identity-flow annulus after planar reparametrization. No source atlas is needed
for this topological support statement. -/
theorem identityBandPlanarRegionField_flow_support {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (he : e.source = univ) {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hsupport : (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.1, (p.2 : ℝ))) '' tsupport Y ⊆
      range (identityFlowCoordinates (δ := δ) d hbalance 0)) :
    (Subtype.val : e.target → Coord) '' tsupport (identityBandPlanarRegionField e he Y) ⊆
      range (e ∘ identityFlowBandInclusion d hbalance 0 hinside) := by
  have hs := identityFlowBandInclusion_support_in_range d hbalance 0 hinside
    (fun p hp => hsupport ⟨p, hp, rfl⟩)
  rw [range_comp]
  exact identityBandPlanarRegionField_protected e he hs

end
end TightVer401

