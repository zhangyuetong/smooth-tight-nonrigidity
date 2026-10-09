import OAI.Analysis.CircleDomains.Selection.OuterContours
import TightVer401.SeamNormalCoordinates

/-! Ordinary Jordan containment for the completion consumer. Closed-disk versus
new-boundary disjointness supplies the direction; no nesting, filling or global
inverse conclusion is assumed. -/
namespace TightVer401
noncomputable section
open Set OAI.CircleDomainRigidity
open scoped Topology

/-- A common enclosed origin rules out disjoint fills but does not choose the
nesting direction from disjoint frontier curves alone. -/
theorem dualRadialCompletionContainment_nested_or (HOld HNew : ℂ ≃ₜ ℂ)
    (hOld0 : (0 : ℂ) ∈ jordanInterior HOld)
    (hNew0 : (0 : ℂ) ∈ jordanInterior HNew)
    (hDisjoint : Disjoint (frontier (jordanInterior HOld))
      (frontier (jordanInterior HNew))) :
    closure (jordanInterior HOld) ⊆ jordanInterior HNew ∨
      closure (jordanInterior HNew) ⊆ jordanInterior HOld := by
  rcases disjoint_or_nested_jordanInteriors HOld HNew hDisjoint with h | h | h
  · exact False.elim (Set.disjoint_left.mp h (subset_closure hOld0) (subset_closure hNew0))
  · exact Or.inl h
  · exact Or.inr h

/-- The old connected closed disk cannot cross a new Jordan frontier it
misses. Their common enclosed origin selects the new interior side. -/
theorem dualRadialCompletionContainment_closed_subset (HOld HNew : ℂ ≃ₜ ℂ)
    (hOld0 : (0 : ℂ) ∈ jordanInterior HOld)
    (hNew0 : (0 : ℂ) ∈ jordanInterior HNew)
    (hDisjoint : Disjoint (closure (jordanInterior HOld))
      (frontier (jordanInterior HNew))) :
    closure (jordanInterior HOld) ⊆ jordanInterior HNew := by
  have hNewOpen := jordanInterior_isOpen HNew
  have hCover : closure (jordanInterior HOld) ⊆
      jordanInterior HNew ∪ (closure (jordanInterior HNew))ᶜ := by
    intro z hzOld
    by_cases hzNew : z ∈ jordanInterior HNew
    · exact Or.inl hzNew
    · right
      intro hzClosure
      apply Set.disjoint_left.mp hDisjoint hzOld
      rw [frontier, hNewOpen.interior_eq]
      exact ⟨hzClosure, hzNew⟩
  have hSides := (isConnected_jordanInterior HOld).closure.isPreconnected.subset_or_subset
    hNewOpen isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ hx hy => hy (subset_closure hx))) hCover
  rcases hSides with hInside | hOutside
  · exact hInside
  · exact False.elim (hOutside (subset_closure hOld0) (subset_closure hNew0))

/-- Transport the actual retained closed source disk through the existing
complex-to-Cartesian coordinate equivalence. -/
theorem dualRadialCompletionContainment_coordinate_closed_subset (HOld HNew : ℂ ≃ₜ ℂ)
    (hOld0 : (0 : ℂ) ∈ jordanInterior HOld)
    (hNew0 : (0 : ℂ) ∈ jordanInterior HNew)
    (hDisjoint : Disjoint (closure (jordanInterior HOld))
      (frontier (jordanInterior HNew))) :
    seamComplexCoord '' closure (jordanInterior HOld) ⊆
      seamComplexCoord '' jordanInterior HNew :=
  image_mono (dualRadialCompletionContainment_closed_subset HOld HNew hOld0 hNew0 hDisjoint)

end
end TightVer401
