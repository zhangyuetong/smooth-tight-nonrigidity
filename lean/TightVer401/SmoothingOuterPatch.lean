import TightVer401.SmoothingLocalChartExistence

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

noncomputable def smoothingOpenPatch (T : Set Coord) (P O : Coord → ℝ) (x : Coord) : ℝ := by
  classical
  exact if x ∈ T then P x else O x

theorem smoothingOpenPatch_germ_inside {T : Set Coord} (hT : IsOpen T) (P O : Coord → ℝ)
    {x : Coord} (hx : x ∈ T) : smoothingOpenPatch T P O =ᶠ[𝓝 x] P := by
  classical
  filter_upwards [hT.mem_nhds hx] with y hy
  simp only [smoothingOpenPatch,if_pos hy]

theorem smoothingOpenPatch_germ_outside {T : Set Coord} (hT : IsOpen T) (P O : Coord → ℝ)
    {x : Coord} (hx : x ∉ T)
    (hBoundary : x ∈ frontier T → P =ᶠ[𝓝 x] O) :
    smoothingOpenPatch T P O =ᶠ[𝓝 x] O := by
  classical
  by_cases hc : x ∈ closure T
  · have hf : x ∈ frontier T := by rw [hT.frontier_eq]; exact ⟨hc,hx⟩
    filter_upwards [hBoundary hf] with y hy
    simp only [smoothingOpenPatch]
    split_ifs <;> first | exact hy | rfl
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    have hn : y ∉ T := fun ht => hy (subset_closure ht)
    simp only [smoothingOpenPatch,if_neg hn]

/-- Gluing along actual equal germs preserves smoothness, saddle Hessians and
uniform C¹ control; the seam is contained in the actual replacement domain. -/
theorem smoothingOpenPatch_properties {V T A : Set Coord} (hV : IsOpen V) (hT : IsOpen T)
    (hA : IsClosed A) (hAT : A ⊆ T) {P O : Coord → ℝ}
    (hP : ContDiffOn ℝ ∞ P T) (hO : ContDiffOn ℝ ∞ O (V \ A))
    (hBoundary : ∀ x ∈ V ∩ frontier T, P =ᶠ[𝓝 x] O)
    (hnegP : ∀ x ∈ V ∩ T, (planarHessian P x).det < 0)
    (hnegO : ∀ x ∈ V \ A, (planarHessian O x).det < 0)
    {η : ℝ} (hη : 0 < η)
    (hClose : ∀ x ∈ V ∩ T, |P x-O x| < η ∧ ‖planarGradient P x-planarGradient O x‖ < η) :
    ContDiffOn ℝ ∞ (smoothingOpenPatch T P O) V ∧
      (∀ x ∈ V, (planarHessian (smoothingOpenPatch T P O) x).det < 0) ∧
      (∀ x ∈ V \ T, smoothingOpenPatch T P O =ᶠ[𝓝 x] O) ∧
      ∀ x ∈ V, |smoothingOpenPatch T P O x-O x| < η ∧
        ‖planarGradient (smoothingOpenPatch T P O) x-planarGradient O x‖ < η := by
  have hOutside (x : Coord) (hx : x ∈ V) (ht : x ∉ T) : smoothingOpenPatch T P O =ᶠ[𝓝 x] O :=
    smoothingOpenPatch_germ_outside hT P O ht (fun hf => hBoundary x ⟨hx,hf⟩)
  have hOff (x : Coord) (hx : x ∈ V) (ht : x ∉ T) : x ∈ V \ A :=
    ⟨hx,fun ha => ht (hAT ha)⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    by_cases ht : x ∈ T
    · exact (((hP x ht).contDiffAt (hT.mem_nhds ht)).congr_of_eventuallyEq
        (smoothingOpenPatch_germ_inside hT P O ht)).contDiffWithinAt
    · exact (((hO x (hOff x hx ht)).contDiffAt ((hV.inter hA.isOpen_compl).mem_nhds (hOff x hx ht))).congr_of_eventuallyEq
        (hOutside x hx ht)).contDiffWithinAt
  · intro x hx
    by_cases ht : x ∈ T
    · rw [smoothing_planarHessian_germ (smoothingOpenPatch_germ_inside hT P O ht)]
      exact hnegP x ⟨hx,ht⟩
    · rw [smoothing_planarHessian_germ (hOutside x hx ht)]
      exact hnegO x (hOff x hx ht)
  · intro x hx
    exact hOutside x hx.1 hx.2
  · intro x hx
    by_cases ht : x ∈ T
    · have hg := smoothingOpenPatch_germ_inside hT P O ht
      rw [hg.eq_of_nhds,smoothing_planarGradient_germ hg]
      exact hClose x ⟨hx,ht⟩
    · have hg := hOutside x hx ht
      rw [hg.eq_of_nhds,smoothing_planarGradient_germ hg]
      simpa only [sub_self,abs_zero,norm_zero,and_self] using hη

end
end TightVer401
