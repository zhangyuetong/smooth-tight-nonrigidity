import TightVer401.VisibleConnectorGradientOrder
import TightVer401.VisibleConnectorGradientInverseApplicationBoundary

/-! The actual signed-map order consumer. Positive Jacobian preserves the
order of ordinary positive Jordan image fills; negative Jacobian uses the
already proved reverse-order theorem. Boundary winding and signed counts are
proved by the existing producers, never supplied as conclusions. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem sourceOrder_range_boundary {H : ℂ ≃ₜ ℂ} {gamma : ℝ → ℂ}
    (h : PositiveJordanParametrization H gamma) :
    range gamma = frontier (jordanInterior H) := by
  apply Subset.antisymm
  · rintro z ⟨t,rfl⟩
    exact h.toRegular.mem_frontier t
  · intro z hz
    rw [← h.boundary] at hz
    exact image_subset_range _ _ hz

private theorem sourceOrder_boundary_subset_source {Ho Hi : ℂ ≃ₜ ℂ}
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi) ⊆
      annularJordanClosure Ho Hi := by
  intro z hz
  rcases hz with hz | hz
  · rw [(jordanInterior_isOpen Ho).frontier_eq] at hz
    exact ⟨hz.1,fun hi => hz.2 (hn (subset_closure hi))⟩
  · rw [(jordanInterior_isOpen Hi).frontier_eq] at hz
    exact ⟨subset_closure (hn hz.1),hz.2⟩

private theorem sourceOrder_annulus_nonempty (Ho Hi : ℂ ≃ₜ ℂ)
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    ∃ y : ℂ, y ∈ jordanInterior Ho ∧ y ∉ closure (jordanInterior Hi) := by
  have hx : Ho 1 ∈ frontier (jordanInterior Ho) := by
    rw [frontier_jordanInterior]
    exact ⟨1,by simp,rfl⟩
  rw [(jordanInterior_isOpen Ho).frontier_eq] at hx
  have hxout : Ho 1 ∉ closure (jordanInterior Hi) := fun hi => hx.2 (hn hi)
  obtain ⟨y,hyout,hyin⟩ := mem_closure_iff_nhds.mp hx.1
    (closure (jordanInterior Hi))ᶜ (isClosed_closure.isOpen_compl.mem_nhds hxout)
  exact ⟨y,hyin,hyout⟩

/-- Positive actual Jacobian forces the actual inner image fill strictly
inside the actual outer image fill. The loops are literal images under F;
positive arguments give the numerical boundary winds through the existing
boundary-winding proof. No target order or global inverse is an input. -/
theorem visibleConnector_actual_positive_map_preserves_positive_jordan_order
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {gammaOuter gammaInner : ℝ → ℂ}
    (hsourceOuter : PositiveJordanParametrization Ho gammaOuter)
    (hsourceInner : PositiveJordanParametrization Hi gammaInner)
    (hsourceNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hsourceO : annularJordanClosure Ho Hi ⊆ O)
    (hpositive : ∀ z ∈ annularJordanInterior Ho Hi, 0 < (fderiv ℝ F z).det)
    (himageOuter : PositiveJordanParametrization To (F ∘ gammaOuter))
    (himageInner : PositiveJordanParametrization Ti (F ∘ gammaInner))
    (hdisjoint : Disjoint (frontier (jordanInterior To)) (frontier (jordanInterior Ti)))
    {c : ℂ} (hcOuter : c ∈ jordanInterior To) (hcInner : c ∈ jordanInterior Ti) :
    closure (jordanInterior Ti) ⊆ jordanInterior To := by
  rcases disjoint_or_nested_jordanInteriors To Ti hdisjoint with hd | hwrong | hright
  · exact False.elim (Set.disjoint_left.mp hd (subset_closure hcOuter) (subset_closure hcInner))
  · exfalso
    obtain ⟨y,hyInner,hyOuter⟩ := sourceOrder_annulus_nonempty Ti To hwrong
    have hb := sourceOrder_boundary_subset_source hsourceNested
    have hBoundaryOuter : frontier (jordanInterior Ho) ⊆ O :=
      fun _ hz => hsourceO (hb (Or.inl hz))
    have hBoundaryInner : frontier (jordanInterior Hi) ⊆ O :=
      fun _ hz => hsourceO (hb (Or.inr hz))
    have hgammaOuterO : ∀ t, gammaOuter t ∈ O :=
      fun t => hBoundaryOuter (hsourceOuter.toRegular.mem_frontier t)
    have hgammaInnerO : ∀ t, gammaInner t ∈ O :=
      fun t => hBoundaryInner (hsourceInner.toRegular.mem_frontier t)
    have hClosedOuter : gammaOuter 1 = gammaOuter 0 := by
      simpa only [zero_add] using hsourceOuter.periodic 0
    have hClosedInner : gammaInner 1 = gammaInner 0 := by
      simpa only [zero_add] using hsourceInner.periodic 0
    have hRangeOuter := sourceOrder_range_boundary himageOuter
    have hRangeInner := sourceOrder_range_boundary himageInner
    have hyoff : y ∉ F '' (frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi)) := by
      rintro ⟨z,hz,hzy⟩
      rcases hz with hz | hz
      · rw [← hsourceOuter.boundary] at hz
        obtain ⟨t,_,rfl⟩ := hz
        have ht : F (gammaOuter t) ∈ closure (jordanInterior To) :=
          frontier_subset_closure (himageOuter.toRegular.mem_frontier t)
        exact hyOuter (hzy ▸ ht)
      · rw [← hsourceInner.boundary] at hz
        obtain ⟨t,_,rfl⟩ := hz
        have ht := himageInner.toRegular.mem_frontier t
        rw [(jordanInterior_isOpen Ti).frontier_eq] at ht
        apply ht.2
        change F (gammaInner t) ∈ jordanInterior Ti
        rw [hzy]
        exact hyInner
    have hInnerWind := visibleConnectorGradientInverseApplication_boundary_winding
      hO hF hsourceInner himageInner hBoundaryInner (fun _ => rfl)
    have hInnerProfile := annularAngularForm_integral_profile hO hF
      hsourceInner.smooth hgammaInnerO hClosedInner Ti hRangeInner (Ti 0)
      (show Ti 0 ∈ jordanInterior Ti from ⟨0,Metric.mem_ball_self zero_lt_one,rfl⟩)
      1 hInnerWind
    have hOuterZero := annularAngularForm_integral_zero_exterior hO hF
      hsourceOuter.smooth hgammaOuterO hClosedOuter To hRangeOuter.subset y hyOuter
    have hDegreeNeg : annularBoundaryDegree F gammaOuter gammaInner y = -1 := by
      unfold annularBoundaryDegree
      rw [hOuterZero,hInnerProfile.1 y hyInner]
      norm_num
    have hCount := annularBoundaryDegree_eq_actual_sign_mul_ncard
      hsourceOuter.toRegular hsourceInner.toRegular hsourceNested
      (annular_positive_source_argument_integral hsourceOuter)
      (annular_positive_source_argument_integral hsourceInner)
      F O hO hF hsourceO 1 (Or.inl rfl)
      (fun z hz => by simpa only [Int.cast_one,one_mul] using hpositive z hz) y hyoff
    rw [hDegreeNeg] at hCount
    have hn : (0 : ℤ) ≤
        ({x | x ∈ annularJordanClosure Ho Hi ∧ F x = y}.ncard : ℤ) := Int.natCast_nonneg _
    omega
  · exact hright

/-- Orientation-parametric consumer of the same actual positive source and
image boundaries. The negative case reuses the frozen negative-map proof;
only the positive case above adds a new signed-count contradiction. -/
theorem visibleConnector_actual_signed_map_orders_positive_jordan_fills
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {gammaOuter gammaInner : ℝ → ℂ}
    (hsourceOuter : PositiveJordanParametrization Ho gammaOuter)
    (hsourceInner : PositiveJordanParametrization Hi gammaInner)
    (hsourceNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hsourceO : annularJordanClosure Ho Hi ⊆ O)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hJ : ∀ z ∈ annularJordanInterior Ho Hi, 0 < (s : ℝ) * (fderiv ℝ F z).det)
    (himageOuter : PositiveJordanParametrization To (F ∘ gammaOuter))
    (himageInner : PositiveJordanParametrization Ti (F ∘ gammaInner))
    (hdisjoint : Disjoint (frontier (jordanInterior To)) (frontier (jordanInterior Ti)))
    {c : ℂ} (hcOuter : c ∈ jordanInterior To) (hcInner : c ∈ jordanInterior Ti) :
    if s = 1 then closure (jordanInterior Ti) ⊆ jordanInterior To
      else closure (jordanInterior To) ⊆ jordanInterior Ti := by
  rcases hs with rfl | rfl
  · have hp : ∀ z ∈ annularJordanInterior Ho Hi, 0 < (fderiv ℝ F z).det :=
      fun z hz => by simpa only [Int.cast_one,one_mul] using hJ z hz
    simpa using
      visibleConnector_actual_positive_map_preserves_positive_jordan_order
        hsourceOuter hsourceInner hsourceNested F O hO hF hsourceO hp
        himageOuter himageInner hdisjoint hcOuter hcInner
  · have hn : ∀ z ∈ annularJordanInterior Ho Hi, (fderiv ℝ F z).det < 0 := by
      intro z hz
      have h := hJ z hz
      norm_num at h
      linarith
    have hOrder := visibleConnector_actual_negative_map_reverses_positive_jordan_order
      hsourceOuter.toRegular hsourceInner.toRegular hsourceNested
      (annular_positive_source_argument_integral hsourceOuter)
      (annular_positive_source_argument_integral hsourceInner)
      F O hO hF hsourceO hn himageOuter himageInner hdisjoint hcOuter hcInner
    simpa using hOrder

end
end TightVer401
