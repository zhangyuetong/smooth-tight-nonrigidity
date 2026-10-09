import TightVer401.PeriodicJordanSeparation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace TightVer401
noncomputable section
open Set Metric
open scoped Topology

theorem homeomorphic_filling_mem_inside {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ} {z : ℂ}
    (hb : range f = H '' sphere (0 : ℂ) 1)
    (hz : z ∈ H '' ball (0 : ℂ) 1) :
    jordanComplexCoordinates.symm z ∈ Schoenflies.inside
      (range (jordanComplexCoordinates.symm ∘ f)) := by
  let e := jordanComplexCoordinates.symm.toHomeomorph
  let U : Set Schoenflies.Plane := e '' (H '' ball (0 : ℂ) 1)
  let C : Set Schoenflies.Plane := range (jordanComplexCoordinates.symm ∘ f)
  let p := jordanComplexCoordinates.symm z
  have hU : IsOpen U := e.isOpenMap _ (H.isOpenMap _ isOpen_ball)
  have hpU : p ∈ U := ⟨z, hz, rfl⟩
  have hC : C = frontier U := by
    change range (e ∘ f) = frontier (e '' (H '' ball (0 : ℂ) 1))
    rw [← e.image_frontier, ← H.image_frontier, frontier_ball _ one_ne_zero,
      ← hb, range_comp]
  have hK : IsCompact (closure U) := by
    change IsCompact (closure (e '' (H '' ball (0 : ℂ) 1)))
    rw [← e.image_closure, ← H.image_closure, closure_ball _ one_ne_zero]
    exact ((isCompact_closedBall (0 : ℂ) 1).image H.continuous).image e.continuous
  have hpC : p ∉ C := by
    rw [hC]
    intro hp
    exact hp.2 (by rwa [hU.interior_eq])
  let Q := connectedComponentIn Cᶜ p
  have hQC : Q ⊆ Cᶜ := connectedComponentIn_subset Cᶜ p
  have hcover : Q ⊆ U ∪ (closure U)ᶜ := by
    intro q hq
    by_cases hqu : q ∈ U
    · exact Or.inl hqu
    · apply Or.inr
      intro hqcl
      apply hQC hq
      rw [hC]
      exact ⟨hqcl, by rwa [hU.interior_eq]⟩
  have hd : Disjoint U (closure U)ᶜ :=
    disjoint_left.mpr (fun q hqu hqc => hqc (subset_closure hqu))
  have hQU : Q ⊆ U := by
    rcases IsPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl hd hcover
      isPreconnected_connectedComponentIn with h | h
    · exact h
    · exact False.elim ((h (mem_connectedComponentIn hpC)) (subset_closure hpU))
  exact ⟨hpC, hK.isBounded.subset (hQU.trans subset_closure)⟩
end
end TightVer401
