import TightVer401.PositiveExitConstructionSelectedHomotopy

/-! Actual protected-point winding transport. Literal closed-loop homotopies
and their avoidance preserve Jordan interior and exterior membership; no
annulus image or nesting conclusion is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem protectedWinding_boundary_range {J : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : PositiveJordanParametrization J γ) :
    range γ = frontier (jordanInterior J) := by
  apply subset_antisymm
  · rintro _ ⟨s, rfl⟩
    exact hγ.toRegular.mem_frontier s
  · rw [← hγ.boundary]
    exact image_subset_range _ _

private theorem protectedWinding_integral_one {J : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : PositiveJordanParametrization J γ) {y : ℂ}
    (hy : y ∈ jordanInterior J) :
    planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
      (annularAngularFormQ (id : ℂ → ℂ) y) γ = 1 := by
  have havoid : ∀ t, γ t ≠ y := by
    intro t he
    have ht := hγ.toRegular.mem_frontier t
    rw [(jordanInterior_isOpen J).frontier_eq] at ht
    exact ht.2 (he.symm ▸ hy)
  obtain ⟨u, hu, hturn⟩ := hγ.positive y hy
  rw [annularAngularForm_integral_eq_pathIncrement isOpen_univ
    contDiff_id.contDiffOn hγ.smooth (fun _ => mem_univ _) y havoid]
  unfold pathArgumentIncrement
  rw [circlePathIncrement_eq_lift _ u (fun t => by
    change (u t : UnitAddCircle) = normalizedArgument (γ t - y)
    exact hu t), hturn]
  ring

private theorem protectedWinding_endpoint_not_frontier
    {J : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : PositiveJordanParametrization J γ)
    (H : C(unitInterval, C(unitInterval, ℂ))) (y : ℂ)
    (havoid : ∀ a t, H a t ≠ y) (a : unitInterval)
    (he : H a = annularLoopPath γ hγ.smooth.continuous) :
    y ∉ frontier (jordanInterior J) := by
  intro hy
  rw [← hγ.boundary] at hy
  obtain ⟨s, hs, hsy⟩ := hy
  have ht := congrArg (fun f : C(unitInterval, ℂ) => f ⟨s, hs⟩) he
  change H a ⟨s, hs⟩ = γ s at ht
  exact havoid a ⟨s, hs⟩ (ht.trans hsy)

/-- The actual two angular integrals agree along the SAME literal avoiding
closed-loop homotopy. -/
theorem positiveExit_protected_homotopy_integral_eq
    {J₀ J₁ : ℂ ≃ₜ ℂ} {γ₀ γ₁ : ℝ → ℂ}
    (h₀ : PositiveJordanParametrization J₀ γ₀)
    (h₁ : PositiveJordanParametrization J₁ γ₁)
    (H : C(unitInterval, C(unitInterval, ℂ))) (y : ℂ)
    (hH0 : H 0 = annularLoopPath γ₀ h₀.smooth.continuous)
    (hH1 : H 1 = annularLoopPath γ₁ h₁.smooth.continuous)
    (hclosed : ∀ a, H a 1 = H a 0) (havoid : ∀ a t, H a t ≠ y) :
    planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
      (annularAngularFormQ (id : ℂ → ℂ) y) γ₀ =
    planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
      (annularAngularFormQ (id : ℂ → ℂ) y) γ₁ := by
  have hn₀ := protectedWinding_endpoint_not_frontier h₀ H y havoid 0 hH0
  have hn₁ := protectedWinding_endpoint_not_frontier h₁ H y havoid 1 hH1
  have ha₀ : ∀ t, γ₀ t ≠ y := fun t he => hn₀ (he ▸ h₀.toRegular.mem_frontier t)
  have ha₁ : ∀ t, γ₁ t ≠ y := fun t he => hn₁ (he ▸ h₁.toRegular.mem_frontier t)
  rw [annularAngularForm_integral_eq_pathIncrement isOpen_univ
    contDiff_id.contDiffOn h₀.smooth (fun _ => mem_univ _) y ha₀,
    annularAngularForm_integral_eq_pathIncrement isOpen_univ
    contDiff_id.contDiffOn h₁.smooth (fun _ => mem_univ _) y ha₁]
  have hh := positiveExit_actual_loop_homotopy_increment_eq H y havoid hclosed 0 1
  simp only [hH0, hH1] at hh
  simpa only [id_comp] using hh

/-- Actual protected-point side transport for two positively oriented Jordan
loops. Both equivalences follow from actual winding, not prescribed nesting. -/
theorem positiveExit_protected_homotopy_sides_iff
    {J₀ J₁ : ℂ ≃ₜ ℂ} {γ₀ γ₁ : ℝ → ℂ}
    (h₀ : PositiveJordanParametrization J₀ γ₀)
    (h₁ : PositiveJordanParametrization J₁ γ₁)
    (H : C(unitInterval, C(unitInterval, ℂ))) (y : ℂ)
    (hH0 : H 0 = annularLoopPath γ₀ h₀.smooth.continuous)
    (hH1 : H 1 = annularLoopPath γ₁ h₁.smooth.continuous)
    (hclosed : ∀ a, H a 1 = H a 0) (havoid : ∀ a t, H a t ≠ y) :
    (y ∈ jordanInterior J₀ ↔ y ∈ jordanInterior J₁) ∧
    (y ∉ closure (jordanInterior J₀) ↔ y ∉ closure (jordanInterior J₁)) := by
  have hn₀ := protectedWinding_endpoint_not_frontier h₀ H y havoid 0 hH0
  have hn₁ := protectedWinding_endpoint_not_frontier h₁ H y havoid 1 hH1
  have hex₀ : y ∉ jordanInterior J₀ ↔ y ∉ closure (jordanInterior J₀) := by
    constructor
    · intro hni hc
      exact hn₀ (by rw [(jordanInterior_isOpen J₀).frontier_eq]; exact ⟨hc, hni⟩)
    · exact fun hc hi => hc (subset_closure hi)
  have hex₁ : y ∉ jordanInterior J₁ ↔ y ∉ closure (jordanInterior J₁) := by
    constructor
    · intro hni hc
      exact hn₁ (by rw [(jordanInterior_isOpen J₁).frontier_eq]; exact ⟨hc, hni⟩)
    · exact fun hc hi => hc (subset_closure hi)
  have heq := positiveExit_protected_homotopy_integral_eq h₀ h₁ H y hH0 hH1 hclosed havoid
  have hz₀ (hy : y ∉ closure (jordanInterior J₀)) :
      planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
        (annularAngularFormQ (id : ℂ → ℂ) y) γ₀ = 0 := by
    exact annularAngularForm_integral_zero_exterior isOpen_univ contDiff_id.contDiffOn
      h₀.smooth (fun _ => mem_univ _) (by simpa only [zero_add] using h₀.periodic 0)
      J₀ (by simpa only [id_comp] using (protectedWinding_boundary_range h₀).subset) y hy
  have hz₁ (hy : y ∉ closure (jordanInterior J₁)) :
      planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
        (annularAngularFormQ (id : ℂ → ℂ) y) γ₁ = 0 := by
    exact annularAngularForm_integral_zero_exterior isOpen_univ contDiff_id.contDiffOn
      h₁.smooth (fun _ => mem_univ _) (by simpa only [zero_add] using h₁.periodic 0)
      J₁ (by simpa only [id_comp] using (protectedWinding_boundary_range h₁).subset) y hy
  have hi : y ∈ jordanInterior J₀ ↔ y ∈ jordanInterior J₁ := by
    constructor
    · intro hy
      by_contra hni
      have hh := heq
      rw [protectedWinding_integral_one h₀ hy, hz₁ (hex₁.mp hni)] at hh
      norm_num at hh
    · intro hy
      by_contra hni
      have hh := heq
      rw [hz₀ (hex₀.mp hni), protectedWinding_integral_one h₁ hy] at hh
      norm_num at hh
  exact ⟨hi, hex₀.symm.trans (hi.not.trans hex₁)⟩

section PointTransport
variable {J₀ J₁ : ℂ ≃ₜ ℂ} {γ₀ γ₁ : ℝ → ℂ}
  (h₀ : PositiveJordanParametrization J₀ γ₀)
  (h₁ : PositiveJordanParametrization J₁ γ₁)
  (H : C(unitInterval, C(unitInterval, ℂ))) (y : ℂ)
  (hH0 : H 0 = annularLoopPath γ₀ h₀.smooth.continuous)
  (hH1 : H 1 = annularLoopPath γ₁ h₁.smooth.continuous)
  (hclosed : ∀ a, H a 1 = H a 0) (havoid : ∀ a t, H a t ≠ y)

include h₀ h₁ H hH0 hH1 hclosed havoid

/-- A protected point inside the first actual loop remains inside the second. -/
theorem positiveExit_protected_homotopy_inside
    (hy : y ∈ jordanInterior J₀) : y ∈ jordanInterior J₁ :=
  (positiveExit_protected_homotopy_sides_iff h₀ h₁ H y hH0 hH1 hclosed havoid).1.mp hy

/-- A protected point outside the first closed disk remains outside the second. -/
theorem positiveExit_protected_homotopy_exterior
    (hy : y ∉ closure (jordanInterior J₀)) : y ∉ closure (jordanInterior J₁) :=
  (positiveExit_protected_homotopy_sides_iff h₀ h₁ H y hH0 hH1 hclosed havoid).2.mp hy
end PointTransport

end
end TightVer401
