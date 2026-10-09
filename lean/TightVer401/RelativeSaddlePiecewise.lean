import TightVer401.SmoothingClosedSeamJets

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual two-sided potential, with the positive side specified by a set.
Its boundary condition is topological data, not a smoothing conclusion. -/
def relativeSaddlePiecewise (P : Set Coord) (f g : Coord → ℝ) (x : Coord) : ℝ :=
  @ite ℝ (x ∈ P) (Classical.propDecidable _) (f x) (g x)

theorem relativeSaddlePiecewise_germ {P : Set Coord} {f g : Coord → ℝ}
    {x : Coord} (hx : x ∉ frontier P) :
    relativeSaddlePiecewise P f g =ᶠ[𝓝 x] f ∨
      relativeSaddlePiecewise P f g =ᶠ[𝓝 x] g := by
  classical
  have hi : x ∈ (frontier P)ᶜ := hx
  rw [compl_frontier_eq_union_interior] at hi
  rcases hi with hi | hi
  · left
    filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
    simp [relativeSaddlePiecewise, hy]
  · right
    filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
    have hyn : y ∉ P := hy
    simp [relativeSaddlePiecewise, hyn]

/-- Smoothness and saddle sign of the exterior are derived from the actual
branch functions and the absence of any additional boundary in the domain. -/
theorem relativeSaddlePiecewise_exterior {P V S : Set Coord}
    (hV : IsOpen V) (hBoundary : V ∩ frontier P ⊆ S)
    {f g : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    (hnegf : ∀ x ∈ V, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ V, (planarHessian g x).det < 0) :
    ContDiffOn ℝ ∞ (relativeSaddlePiecewise P f g) (V \ S) ∧
      ∀ x ∈ V \ S, (planarHessian (relativeSaddlePiecewise P f g) x).det < 0 := by
  have hGerm (x : Coord) (hx : x ∈ V \ S) :=
    relativeSaddlePiecewise_germ (f := f) (g := g)
      (show x ∉ frontier P from fun hb => hx.2 (hBoundary ⟨hx.1,hb⟩))
  constructor
  · intro x hx
    rcases hGerm x hx with he | he
    · exact ((hf.contDiffAt (hV.mem_nhds hx.1)).congr_of_eventuallyEq he).contDiffWithinAt
    · exact ((hg.contDiffAt (hV.mem_nhds hx.1)).congr_of_eventuallyEq he).contDiffWithinAt
  · intro x hx
    rcases hGerm x hx with he | he
    · rw [smoothing_planarHessian_germ he]
      exact hnegf x hx.1
    · rw [smoothing_planarHessian_germ he]
      exact hnegg x hx.1

end
end TightVer401
