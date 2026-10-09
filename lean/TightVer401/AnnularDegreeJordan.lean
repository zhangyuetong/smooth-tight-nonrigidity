import OAI.Analysis.CircleDomains.Selection.OuterContours
import Mathlib.Topology.Neighborhoods

/-!
Actual nested Jordan-annulus geometry, using the pinned OpenAI Jordan disks.
The planar homeomorphisms identify Jordan disks; no degree or injectivity of
an annular map is assumed here.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.CircleDomainRigidity
open scoped Topology

/-- The open region between the two actual Jordan boundary curves. -/
def annularJordanInterior (Houter Hinner : ℂ ≃ₜ ℂ) : Set ℂ :=
  jordanInterior Houter \ closure (jordanInterior Hinner)

/-- The closed region between the two actual Jordan boundary curves. -/
def annularJordanClosure (Houter Hinner : ℂ ≃ₜ ℂ) : Set ℂ :=
  closure (jordanInterior Houter) \ jordanInterior Hinner

/-- The open inner disk and the open exterior of the outer closed disk. -/
def annularJordanForbidden (Houter Hinner : ℂ ≃ₜ ℂ) : Set ℂ :=
  jordanInterior Hinner ∪ (closure (jordanInterior Houter))ᶜ

theorem annularJordanInterior_isOpen (Houter Hinner : ℂ ≃ₜ ℂ) :
    IsOpen (annularJordanInterior Houter Hinner) :=
  (jordanInterior_isOpen Houter).sdiff isClosed_closure

theorem annularJordanClosure_isClosed (Houter Hinner : ℂ ≃ₜ ℂ) :
    IsClosed (annularJordanClosure Houter Hinner) :=
  isClosed_closure.sdiff (jordanInterior_isOpen Hinner)

theorem annularJordanClosure_isCompact (Houter Hinner : ℂ ≃ₜ ℂ) :
    IsCompact (annularJordanClosure Houter Hinner) :=
  (isCompact_closure_jordanInterior Houter).of_isClosed_subset
    (annularJordanClosure_isClosed Houter Hinner) (fun _ hx => hx.1)

theorem annularJordanInterior_subset_closure (Houter Hinner : ℂ ≃ₜ ℂ) :
    annularJordanInterior Houter Hinner ⊆ annularJordanClosure Houter Hinner := by
  intro x hx
  exact ⟨subset_closure hx.1, fun hi => hx.2 (subset_closure hi)⟩

theorem interior_annularJordanClosure (Houter Hinner : ℂ ≃ₜ ℂ) :
    interior (annularJordanClosure Houter Hinner) = annularJordanInterior Houter Hinner := by
  simp only [annularJordanClosure, annularJordanInterior, sdiff_eq,
    interior_inter, interior_compl, interior_closure_jordanInterior]

/-- Each boundary point is approached from the open intervening region.
Strict nesting makes the other removed disk irrelevant near that boundary. -/
theorem closure_annularJordanInterior (Houter Hinner : ℂ ≃ₜ ℂ)
    (hNested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter) :
    closure (annularJordanInterior Houter Hinner) = annularJordanClosure Houter Hinner := by
  apply subset_antisymm
  · exact closure_minimal (annularJordanInterior_subset_closure Houter Hinner)
      (annularJordanClosure_isClosed Houter Hinner)
  · intro x hx
    by_cases hxo : x ∈ jordanInterior Houter
    · have hxe : x ∈ closure ((closure (jordanInterior Hinner))ᶜ) := by
        rw [closure_compl, interior_closure_jordanInterior]
        exact hx.2
      exact (jordanInterior_isOpen Houter).inter_closure ⟨hxo, hxe⟩
    · have hxe : x ∈ (closure (jordanInterior Hinner))ᶜ :=
        fun hi => hxo (hNested hi)
      exact isClosed_closure.isOpen_compl.closure_inter ⟨hx.1, hxe⟩

/-- The annulus frontier is exactly the two original Jordan boundaries. -/
theorem frontier_annularJordanInterior (Houter Hinner : ℂ ≃ₜ ℂ)
    (hNested : closure (jordanInterior Hinner) ⊆ jordanInterior Houter) :
    frontier (annularJordanInterior Houter Hinner) =
      frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner) := by
  rw [(annularJordanInterior_isOpen Houter Hinner).frontier_eq,
    closure_annularJordanInterior Houter Hinner hNested,
    (jordanInterior_isOpen Houter).frontier_eq,
    (jordanInterior_isOpen Hinner).frontier_eq]
  ext x
  change ((x ∈ closure (jordanInterior Houter) ∧ x ∉ jordanInterior Hinner) ∧
      ¬(x ∈ jordanInterior Houter ∧ x ∉ closure (jordanInterior Hinner))) ↔
    ((x ∈ closure (jordanInterior Houter) ∧ x ∉ jordanInterior Houter) ∨
      (x ∈ closure (jordanInterior Hinner) ∧ x ∉ jordanInterior Hinner))
  constructor
  · intro hx
    by_cases hxo : x ∈ jordanInterior Houter
    · right
      exact ⟨by by_contra hxi; exact hx.2 ⟨hxo, hxi⟩, hx.1.2⟩
    · exact Or.inl ⟨hx.1.1, hxo⟩
  · intro hx
    rcases hx with hx | hx
    · exact ⟨⟨hx.1, fun hi => hx.2 (hNested (subset_closure hi))⟩,
        fun hi => hx.2 hi.1⟩
    · exact ⟨⟨subset_closure (hNested hx.1), hx.2⟩, fun hi => hi.2 hx.1⟩

theorem annularJordanForbidden_isOpen (Houter Hinner : ℂ ≃ₜ ℂ) :
    IsOpen (annularJordanForbidden Houter Hinner) :=
  (jordanInterior_isOpen Hinner).union isClosed_closure.isOpen_compl

/-- No forbidden target lies in the closed intervening annulus. -/
theorem annularJordanForbidden_disjoint_closure (Houter Hinner : ℂ ≃ₜ ℂ) :
    Disjoint (annularJordanForbidden Houter Hinner) (annularJordanClosure Houter Hinner) := by
  apply Set.disjoint_left.mpr
  intro x hx hk
  rcases hx with hx | hx
  · exact hk.2 hx
  · exact hx hk.1

/-- The inner Jordan boundary is approached through the forbidden inner disk. -/
theorem annularJordan_inner_boundary_subset_closure_forbidden (Houter Hinner : ℂ ≃ₜ ℂ) :
    frontier (jordanInterior Hinner) ⊆ closure (annularJordanForbidden Houter Hinner) := by
  intro x hx
  exact closure_mono (subset_union_left : jordanInterior Hinner ⊆
    annularJordanForbidden Houter Hinner) (frontier_subset_closure hx)

/-- Regular openness of a Jordan disk gives forbidden exterior targets
arbitrarily near every point of the outer Jordan boundary. -/
theorem annularJordan_outer_boundary_subset_closure_forbidden (Houter Hinner : ℂ ≃ₜ ℂ) :
    frontier (jordanInterior Houter) ⊆ closure (annularJordanForbidden Houter Hinner) := by
  intro x hx
  have hxe : x ∈ closure ((closure (jordanInterior Houter))ᶜ) := by
    rw [closure_compl, interior_closure_jordanInterior]
    rw [(jordanInterior_isOpen Houter).frontier_eq] at hx
    exact hx.2
  exact closure_mono (subset_union_right : (closure (jordanInterior Houter))ᶜ ⊆
    annularJordanForbidden Houter Hinner) hxe

theorem annularJordan_boundaries_subset_closure_forbidden (Houter Hinner : ℂ ≃ₜ ℂ) :
    frontier (jordanInterior Houter) ∪ frontier (jordanInterior Hinner) ⊆
      closure (annularJordanForbidden Houter Hinner) :=
  union_subset (annularJordan_outer_boundary_subset_closure_forbidden Houter Hinner)
    (annularJordan_inner_boundary_subset_closure_forbidden Houter Hinner)

end
end TightVer401
