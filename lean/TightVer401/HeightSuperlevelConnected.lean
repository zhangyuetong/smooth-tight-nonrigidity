import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Compact

/-! Strict superlevels of a continuous function on a compact locally connected
space are connected if all local maxima coincide. Components are open; maximizing
on a component closure produces an interior local maximum. -/
namespace TightVer401
noncomputable section
open Set
open scoped Topology

/-- A relative component contains all points of its closure still in the set. -/
private theorem height_component_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {U : Set X} {x : X} (hx : x ∈ U) :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  intro y hy
  rw [connectedComponentIn_eq_image hx] at hy ⊢
  have hcl : (⟨y, hy.2⟩ : U) ∈ closure (connectedComponent (⟨x, hx⟩ : U)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hy.1
  rw [isClosed_connectedComponent.closure_eq] at hcl
  exact ⟨⟨y, hy.2⟩, hcl, rfl⟩

/-- Every nonempty component of a strict superlevel has a local maximum in it. -/
theorem height_superlevel_component_exists_localMax
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {h : X → ℝ} (hh : Continuous h) {a : ℝ} {x : X} (hx : a < h x) :
    ∃ p ∈ connectedComponentIn {y : X | a < h y} x, IsLocalMax h p := by
  let U : Set X := {y | a < h y}
  let C : Set X := connectedComponentIn U x
  have hxU : x ∈ U := hx
  have hxC : x ∈ C := mem_connectedComponentIn hxU
  have hU : IsOpen U := isOpen_lt continuous_const hh
  have hC : IsOpen C := hU.connectedComponentIn
  apply isClosed_closure.isCompact.exists_isLocalMax_mem_open
    subset_closure hh.continuousOn (subset_closure hxC) ?_ hC
  intro y hy
  have hyU : y ∉ U := by
    intro hyU
    exact hy.2 (height_component_closure_inter_subset hxU ⟨hy.1, hyU⟩)
  have hya : h y ≤ a := le_of_not_gt hyU
  exact hya.trans_lt hx

/-- If every pair of local maxima coincide, every strict superlevel is
preconnected, including empty superlevels. No maximum or connectedness data is
assumed for the superlevel itself. -/
theorem height_superlevel_isPreconnected_of_unique_localMax
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {h : X → ℝ} (hh : Continuous h)
    (hunique : ∀ p q : X, IsLocalMax h p → IsLocalMax h q → p = q)
    (a : ℝ) : IsPreconnected {x : X | a < h x} := by
  let U : Set X := {x | a < h x}
  rcases eq_empty_or_nonempty U with hEmpty | ⟨x, hx⟩
  · change IsPreconnected U
    rw [hEmpty]
    exact isPreconnected_empty
  · obtain ⟨p, hp, hpmax⟩ := height_superlevel_component_exists_localMax hh hx
    have hsubset : U ⊆ connectedComponentIn U x := by
      intro y hy
      obtain ⟨q, hq, hqmax⟩ := height_superlevel_component_exists_localMax hh hy
      have hpq : p = q := hunique p q hpmax hqmax
      have hpy : p ∈ connectedComponentIn U y := by
        rw [hpq]
        exact hq
      have hcomp : connectedComponentIn U x = connectedComponentIn U y :=
        (connectedComponentIn_eq hp).trans (connectedComponentIn_eq hpy).symm
      rw [hcomp]
      exact mem_connectedComponentIn hy
    have hEq : U = connectedComponentIn U x :=
      hsubset.antisymm (connectedComponentIn_subset U x)
    change IsPreconnected U
    rw [hEq]
    exact isPreconnected_connectedComponentIn

end
end TightVer401
