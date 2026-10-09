import TightVer401.DualRadialCompletionExitTrace

/-! Identify actual bounded components with the same supplied homeomorphic
filling, using only boundary range and native Jordan geometry. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

theorem dualRadialCompletionTraceInside_eq_of_range {H : ℂ ≃ₜ ℂ} {P : ℝ → Coord}
    (hRange : range (positiveExitComplexTrace P) = H '' sphere (0 : ℂ) 1)
    (hJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange P)) :
    positiveExitInside P = seamComplexCoord '' (H '' ball (0 : ℂ) 1) := by
  let E := jordanComplexCoordinates.symm.toHomeomorph
  let U := E '' (H '' ball (0 : ℂ) 1)
  let C := positiveExitJordanRange P
  have hU : IsOpen U := E.isOpenMap _ (H.isOpenMap _ isOpen_ball)
  have hFront : C = frontier U := by
    change range (E ∘ positiveExitComplexTrace P) = frontier (E '' (H '' ball (0 : ℂ) 1))
    rw [← E.image_frontier, ← H.image_frontier, frontier_ball _ one_ne_zero,
      ← hRange, range_comp]
  have hInside : U ⊆ Schoenflies.inside C := by
    rintro p ⟨z, hz, rfl⟩
    exact homeomorphic_filling_mem_inside hRange hz
  have hCover : Schoenflies.inside C ⊆ U ∪ (closure U)ᶜ := by
    intro p hp
    by_cases hpU : p ∈ U
    · exact Or.inl hpU
    · right
      intro hpCl
      apply Schoenflies.inside_subset_compl hp
      rw [hFront, frontier, hU.interior_eq]
      exact ⟨hpCl, hpU⟩
  have hSides := (Schoenflies.jordan_curve_theorem hJordan).isConnected_inside.isPreconnected.subset_or_subset
    hU isClosed_closure.isOpen_compl
    (disjoint_left.mpr (fun _ hp hc => hc (subset_closure hp))) hCover
  have hNonempty : U.Nonempty := by
    refine ⟨E (H 0), H 0, ?_, rfl⟩
    exact ⟨0, by simp, rfl⟩
  have hEq : Schoenflies.inside C = U := by
    apply Subset.antisymm _ hInside
    rcases hSides with h | h
    · exact h
    · obtain ⟨p, hp⟩ := hNonempty
      exact False.elim (h (hInside hp) (subset_closure hp))
  have hPoint (z : ℂ) : positiveExitComplexPoint (seamComplexCoord z) = z := by
    apply Complex.ext <;> simp [positiveExitComplexPoint, seamComplexCoord_apply]
  ext p
  constructor
  · intro hp
    change jordanComplexCoordinates.symm (positiveExitComplexPoint p) ∈ Schoenflies.inside C at hp
    rw [hEq] at hp
    obtain ⟨z, hz, he⟩ := hp
    have hzEq : z = positiveExitComplexPoint p := E.injective he
    refine ⟨z, hz, ?_⟩
    rw [hzEq]
    ext i
    fin_cases i <;> simp [positiveExitComplexPoint, seamComplexCoord_apply]
  · rintro ⟨z, hz, rfl⟩
    change jordanComplexCoordinates.symm (positiveExitComplexPoint (seamComplexCoord z)) ∈ Schoenflies.inside C
    rw [hPoint, hEq]
    exact ⟨z, hz, rfl⟩

theorem dualRadialCompletionTraceInside_eq {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ}
    (hf : DualRadialCompletionPositiveTrace H f) :
    positiveExitInside (seamComplexCoord ∘ f) = seamComplexCoord '' (H '' ball (0 : ℂ) 1) := by
  have hComplex : positiveExitComplexTrace (seamComplexCoord ∘ f) = f := by
    funext t
    apply Complex.ext <;> rfl
  apply dualRadialCompletionTraceInside_eq_of_range
  · rw [hComplex]
    exact dualRadialCompletion_positiveTrace_range hf
  · unfold positiveExitJordanRange
    rw [hComplex]
    exact periodicComplexCurve_isJordanCurve hf.1 hf.2.1 hf.2.2.1

end
end TightVer401
