import TightVer401.QuadraticRadialFillingBoundary
import TightVer401.QuadraticRadialFillingGlue

/-! Derived actual incoming outer-gradient bounds and source band placement. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual incoming gradient has a finite physical-radius bound on a
compact outer circle. The bound is derived, not an input to the filling. -/
theorem quadraticRadialFilling_incoming_gradient_boundary_bound
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {S : ℝ}
    (hCircleU : quadraticRadialFillingRadiusLevel S ⊆ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ quadraticRadialFillingRadiusLevel S,
      planarRadius (planarGradient F x) < B := by
  have hc : ContinuousOn (fun x => planarRadius (planarGradient F x))
      (quadraticRadialFillingRadiusLevel S) :=
    quadraticRadialFilling_radius_continuous.comp_continuousOn
      ((planarGradient_contDiffOn hF hU).continuousOn.mono hCircleU)
  have hK : IsCompact ((fun x => planarRadius (planarGradient F x)) ''
      quadraticRadialFillingRadiusLevel S) :=
    (quadraticRadialFilling_radiusLevel_isCompact S).image_of_continuousOn hc
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove
  refine ⟨max B₀ 0 + 1, ?_, ?_⟩
  · linarith [le_max_right B₀ 0]
  · intro x hx
    have hb : planarRadius (planarGradient F x) ≤ B₀ := hB₀ ⟨x, hx, rfl⟩
    linarith [le_max_left B₀ 0]

/-- Exact retained incoming germs transfer that derived boundary bound to
the actual smoothed potential. No new regularity assumption on `H` is needed
for the germ derivative identity. -/
theorem quadraticRadialFilling_retained_gradient_boundary_bound
    {F H : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {S : ℝ}
    (hCircleU : quadraticRadialFillingRadiusLevel S ⊆ U)
    (hRetained : ∀ x ∈ quadraticRadialFillingRadiusLevel S, H =ᶠ[𝓝 x] F) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ quadraticRadialFillingRadiusLevel S,
      planarRadius (planarGradient H x) < B := by
  obtain ⟨B, hB, hbound⟩ :=
    quadraticRadialFilling_incoming_gradient_boundary_bound hF hU hCircleU
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hgrad : planarGradient H x = planarGradient F x := by
    ext i
    unfold planarGradient coordPartial
    rw [(hRetained x hx).fderiv_eq]
  rw [hgrad]
  exact hbound x hx

/-- An actual incoming exterior shell completes the positive radial disk to
a domain containing the entire compact degree source band. -/
theorem quadraticRadialFilling_closedAnnulus_subset_domain
    {ε R S : ℝ} (hε : 0 < ε) {U : Set Coord}
    (hShell : quadraticRadialFillingClosedAnnulus R S ⊆ U) :
    quadraticRadialFillingClosedAnnulus ε S ⊆ quadraticRadialFillingDomain R U := by
  intro x hx
  refine ⟨hε.trans_le hx.1, ?_⟩
  by_cases hin : planarRadius x < R
  · exact Or.inl hin
  · exact Or.inr (hShell ⟨le_of_not_gt hin, hx.2⟩)

theorem quadraticRadialFilling_openAnnulus_closure_subset_domain
    {ε R S : ℝ} (hε : 0 < ε) {U : Set Coord}
    (hShell : quadraticRadialFillingClosedAnnulus R S ⊆ U) :
    closure (quadraticRadialFillingOpenAnnulus ε S) ⊆ quadraticRadialFillingDomain R U :=
  (quadraticRadialFilling_openAnnulus_closure_subset ε S).trans
    (quadraticRadialFilling_closedAnnulus_subset_domain hε hShell)

end
end TightVer401
