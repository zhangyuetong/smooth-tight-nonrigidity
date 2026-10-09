import OAI.Analysis.CircleDomains.Topology.TerminalDisks
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Small disjoint interior disks for the finite actual preimage set. The
local charts in this helper are supplied by the actual inverse function theorem;
their injectivity is used only on the selected disks, never globally.
-/
namespace TightVer401
noncomputable section
open Set Function Metric
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology

/-- Each finite set of locally regular points has pairwise disjoint positive
round disks, contained in prescribed open interior and inverse-chart sources.
No fiber enumeration or global injectivity is assumed. -/
theorem annular_exists_disjoint_local_inverse_disks
    {F : ℂ → ℂ} {S U : Set ℂ} (hS : S.Finite) (hU : IsOpen U) (hSU : S ⊆ U)
    (hlocal : ∀ x ∈ S, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      x ∈ e.source ∧ (e : ℂ → ℂ) = F) :
    ∃ (e : S → OpenPartialHomeomorph ℂ ℂ) (r : S → ℝ),
      (∀ x, (e x : ℂ → ℂ) = F) ∧ (∀ x, 0 < r x) ∧
      Pairwise (Disjoint on fun x : S => closedBall (x : ℂ) (r x)) ∧
      (∀ x : S, closedBall (x : ℂ) (r x) ⊆ U ∧
        closedBall (x : ℂ) (r x) ⊆ (e x).source ∧
        InjOn F (closedBall (x : ℂ) (r x))) ∧
      S ⊆ ⋃ x : S, ball (x : ℂ) (r x) := by
  classical
  let := hS.fintype
  choose e he heF using fun x : S => hlocal x x.property
  let O : S → Set ℂ := fun x => U ∩ (e x).source
  have hO (x : S) : O x ∈ nhds (x : ℂ) :=
    Filter.inter_mem (hU.mem_nhds (hSU x.property)) ((e x).open_source.mem_nhds (he x))
  obtain ⟨r, hr, hsub, hd⟩ := exists_disjoint_closedBalls_in_neighborhoods
    (fun x : S => (x : ℂ)) Subtype.val_injective O hO (fun _ => 1) (fun _ => zero_lt_one)
  refine ⟨e, r, heF, fun x => (hr x).1, hd, ?_, ?_⟩
  · intro x
    refine ⟨(hsub x).trans inter_subset_left, (hsub x).trans inter_subset_right, ?_⟩
    rw [← heF x]
    exact (e x).injOn.mono ((hsub x).trans inter_subset_right)
  · intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩).1⟩

end
end TightVer401
