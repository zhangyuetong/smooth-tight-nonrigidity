import TightVer401.AnnularDegreeJordan
import Mathlib.Topology.Homeomorph.Lemmas

/-! Assemble the manuscript's two actual boundary homeomorphisms into a
homeomorphism of their union. No differential condition, global injectivity,
or global image condition is assumed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.CircleDomainRigidity
open scoped Topology

theorem annular_jordan_frontier_isCompact (H : ℂ ≃ₜ ℂ) :
    IsCompact (frontier (jordanInterior H)) :=
  (isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
    frontier_subset_closure

/-- Strict nesting separates the two actual boundary curves. -/
theorem annular_nested_jordan_frontiers_disjoint {Ho Hi : ℂ ≃ₜ ℂ}
    (hnested : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    Disjoint (frontier (jordanInterior Ho)) (frontier (jordanInterior Hi)) := by
  apply Set.disjoint_left.mpr
  intro z hzo hzi
  have hzinside : z ∈ jordanInterior Ho := hnested (frontier_subset_closure hzi)
  exact hzo.2 ((jordanInterior_isOpen Ho).interior_eq.symm ▸ hzinside)

/-- Component boundary homeomorphisms derive all three set-map properties
on their union. Distinct target components exclude the cross-component case. -/
theorem annular_boundary_union_map_properties
    {f : ℂ → ℂ} {So Si To Ti : Set ℂ}
    (hTarget : Disjoint To Ti) (Bo : So ≃ₜ To) (Bi : Si ≃ₜ Ti)
    (hBo : ∀ x : So, (Bo x : ℂ) = f x)
    (hBi : ∀ x : Si, (Bi x : ℂ) = f x) :
    MapsTo f (So ∪ Si) (To ∪ Ti) ∧
      InjOn f (So ∪ Si) ∧ SurjOn f (So ∪ Si) (To ∪ Ti) := by
  have hMo : MapsTo f So To := by
    intro x hx
    rw [← hBo ⟨x, hx⟩]
    exact (Bo ⟨x, hx⟩).property
  have hMi : MapsTo f Si Ti := by
    intro x hx
    rw [← hBi ⟨x, hx⟩]
    exact (Bi ⟨x, hx⟩).property
  have hIo : InjOn f So := by
    intro x hx z hz heq
    have hb : Bo ⟨x, hx⟩ = Bo ⟨z, hz⟩ :=
      Subtype.ext ((hBo ⟨x, hx⟩).trans (heq.trans (hBo ⟨z, hz⟩).symm))
    exact congrArg Subtype.val (Bo.injective hb)
  have hIi : InjOn f Si := by
    intro x hx z hz heq
    have hb : Bi ⟨x, hx⟩ = Bi ⟨z, hz⟩ :=
      Subtype.ext ((hBi ⟨x, hx⟩).trans (heq.trans (hBi ⟨z, hz⟩).symm))
    exact congrArg Subtype.val (Bi.injective hb)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hMo hx)
    · exact Or.inr (hMi hx)
  · intro x hx z hz heq
    rcases hx with hx | hx <;> rcases hz with hz | hz
    · exact hIo hx hz heq
    · exact (Set.disjoint_left.mp hTarget (hMo hx) (heq.symm ▸ hMi hz)).elim
    · exact (Set.disjoint_left.mp hTarget (heq.symm ▸ hMo hz) (hMi hx)).elim
    · exact hIi hx hz heq
  · intro y hy
    rcases hy with hy | hy
    · let x : So := Bo.symm ⟨y, hy⟩
      refine ⟨x, Or.inl x.property, ?_⟩
      exact (hBo x).symm.trans (congrArg Subtype.val (Bo.apply_symm_apply ⟨y, hy⟩))
    · let x : Si := Bi.symm ⟨y, hy⟩
      refine ⟨x, Or.inr x.property, ?_⟩
      exact (hBi x).symm.trans (congrArg Subtype.val (Bi.apply_symm_apply ⟨y, hy⟩))

/-- The actual continuous map on a compact two-component boundary is the
forward map of the assembled homeomorphism. -/
theorem annular_boundary_union_homeomorph_of_components
    {f : ℂ → ℂ} {So Si To Ti : Set ℂ}
    (hSource : IsCompact (So ∪ Si)) (hf : ContinuousOn f (So ∪ Si))
    (hTarget : Disjoint To Ti) (Bo : So ≃ₜ To) (Bi : Si ≃ₜ Ti)
    (hBo : ∀ x : So, (Bo x : ℂ) = f x)
    (hBi : ∀ x : Si, (Bi x : ℂ) = f x) :
    ∃ B : ↥(So ∪ Si) ≃ₜ ↥(To ∪ Ti), ∀ x, (B x : ℂ) = f x := by
  classical
  obtain ⟨hMaps, hInj, hSurj⟩ := annular_boundary_union_map_properties hTarget Bo Bi hBo hBi
  let g : ↥(So ∪ Si) → ↥(To ∪ Ti) := fun x => ⟨f x, hMaps x.property⟩
  have hg : Bijective g := by
    constructor
    · intro x z hxz
      exact Subtype.ext (hInj x.property z.property (congrArg Subtype.val hxz))
    · intro y
      obtain ⟨x, hx, hxy⟩ := hSurj y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : ↥(So ∪ Si) ≃ ↥(To ∪ Ti) := Equiv.ofBijective g hg
  have he : Continuous e := hf.domRestrict.subtype_mk _
  let : CompactSpace ↥(So ∪ Si) := isCompact_iff_compactSpace.mp hSource
  exact ⟨he.homeoOfEquivCompactToT2, fun _ => rfl⟩

/-- The manuscript's ordinary individual Jordan boundary homeomorphisms
produce the exact union homeomorphism required by the annular degree proof.
The actual map may have vanishing differential rank on either boundary. -/
theorem annular_jordan_boundary_homeomorph_of_components
    {f : ℂ → ℂ} {Ho Hi To Ti : ℂ ≃ₜ ℂ}
    (hTargetNested : closure (jordanInterior Ti) ⊆ jordanInterior To)
    (hf : ContinuousOn f
      (frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi)))
    (Bo : frontier (jordanInterior Ho) ≃ₜ frontier (jordanInterior To))
    (Bi : frontier (jordanInterior Hi) ≃ₜ frontier (jordanInterior Ti))
    (hBo : ∀ x, (Bo x : ℂ) = f x) (hBi : ∀ x, (Bi x : ℂ) = f x) :
    ∃ B : ↥(frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi)) ≃ₜ
        ↥(frontier (jordanInterior To) ∪ frontier (jordanInterior Ti)),
      ∀ x, (B x : ℂ) = f x :=
  annular_boundary_union_homeomorph_of_components
    ((annular_jordan_frontier_isCompact Ho).union (annular_jordan_frontier_isCompact Hi))
    hf (annular_nested_jordan_frontiers_disjoint hTargetNested) Bo Bi hBo hBi

end
end TightVer401
