import TightVer401.RelativeSaddlePiecewise

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- On the interior of the positive side, the actual piecewise potential has
the first branch's germ. No regularity of either branch is needed here. -/
theorem relativeSaddlePiecewise_germ_interior {P : Set Coord}
    {f g : Coord → ℝ} {x : Coord} (hx : x ∈ interior P) :
    relativeSaddlePiecewise P f g =ᶠ[𝓝 x] f := by
  classical
  filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
  simp [relativeSaddlePiecewise, hy]

/-- On the interior of the complementary side, the actual piecewise potential
has the second branch's germ. -/
theorem relativeSaddlePiecewise_germ_interior_compl {P : Set Coord}
    {f g : Coord → ℝ} {x : Coord} (hx : x ∈ interior Pᶜ) :
    relativeSaddlePiecewise P f g =ᶠ[𝓝 x] g := by
  classical
  filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
  have hyn : y ∉ P := hy
  simp [relativeSaddlePiecewise, hyn]

/-- Construct the exterior regularity and saddle sign from branch potentials
smooth on their own open domains. The inclusions describe where each branch is
used, and the frontier condition excludes additional gluing boundaries in the
exterior. Neither branch needs a smooth extension to all of `V`. -/
theorem relativeSaddlePiecewise_exterior_domains {P V S Uf Ug : Set Coord}
    (_hV : IsOpen V) (hBoundary : V ∩ frontier P ⊆ S)
    (hUf : IsOpen Uf) (hUg : IsOpen Ug)
    (hPositiveDomain : V ∩ interior P ⊆ Uf)
    (hNegativeDomain : V ∩ interior Pᶜ ⊆ Ug)
    {f g : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f Uf)
    (hg : ContDiffOn ℝ ∞ g Ug)
    (hnegf : ∀ x ∈ Uf, (planarHessian f x).det < 0)
    (hnegg : ∀ x ∈ Ug, (planarHessian g x).det < 0) :
    ContDiffOn ℝ ∞ (relativeSaddlePiecewise P f g) (V \ S) ∧
      ∀ x ∈ V \ S,
        (planarHessian (relativeSaddlePiecewise P f g) x).det < 0 := by
  have hBranchGerm (x : Coord) (hx : x ∈ V \ S) :
      (x ∈ Uf ∧ relativeSaddlePiecewise P f g =ᶠ[𝓝 x] f) ∨
        (x ∈ Ug ∧ relativeSaddlePiecewise P f g =ᶠ[𝓝 x] g) := by
    have hi : x ∈ (frontier P)ᶜ :=
      fun hb => hx.2 (hBoundary ⟨hx.1, hb⟩)
    rw [compl_frontier_eq_union_interior] at hi
    rcases hi with hi | hi
    · exact Or.inl ⟨hPositiveDomain ⟨hx.1, hi⟩,
        relativeSaddlePiecewise_germ_interior hi⟩
    · exact Or.inr ⟨hNegativeDomain ⟨hx.1, hi⟩,
        relativeSaddlePiecewise_germ_interior_compl hi⟩
  constructor
  · intro x hx
    rcases hBranchGerm x hx with ⟨hxUf, he⟩ | ⟨hxUg, he⟩
    · exact ((hf.contDiffAt (hUf.mem_nhds hxUf)).congr_of_eventuallyEq he).contDiffWithinAt
    · exact ((hg.contDiffAt (hUg.mem_nhds hxUg)).congr_of_eventuallyEq he).contDiffWithinAt
  · intro x hx
    rcases hBranchGerm x hx with ⟨hxUf, he⟩ | ⟨hxUg, he⟩
    · rw [smoothing_planarHessian_germ he]
      exact hnegf x hxUf
    · rw [smoothing_planarHessian_germ he]
      exact hnegg x hxUg

end
end TightVer401
