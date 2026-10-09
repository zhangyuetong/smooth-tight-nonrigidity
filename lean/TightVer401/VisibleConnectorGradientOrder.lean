import TightVer401.AnnularDegreeBoundaryWinding
import TightVer401.AnnularDegreeJordanWinding

/-! Negative actual Jacobian reverses the order of the two actual Jordan
image boundaries. Target nesting and an inverse are conclusions, not inputs
to the signed-count contradiction. The map F remains literal throughout. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem gradientOrder_range_boundary {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    range γ = frontier (jordanInterior H) := by
  apply Subset.antisymm
  · rintro z ⟨t, rfl⟩
    exact hγ.mem_frontier t
  · intro z hz
    rw [← hγ.boundary] at hz
    exact image_subset_range _ _ hz

private theorem gradientOrder_boundary_subset_source {Ho Hi : ℂ ≃ₜ ℂ}
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi) ⊆
      annularJordanClosure Ho Hi := by
  intro z hz
  rcases hz with hz | hz
  · rw [(jordanInterior_isOpen Ho).frontier_eq] at hz
    exact ⟨hz.1, fun hi => hz.2 (hn (subset_closure hi))⟩
  · rw [(jordanInterior_isOpen Hi).frontier_eq] at hz
    exact ⟨subset_closure (hn hz.1), hz.2⟩

private theorem gradientOrder_annulus_nonempty (Ho Hi : ℂ ≃ₜ ℂ)
    (hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    ∃ y : ℂ, y ∈ jordanInterior Ho ∧ y ∉ closure (jordanInterior Hi) := by
  have hx : Ho 1 ∈ frontier (jordanInterior Ho) := by
    rw [frontier_jordanInterior]
    exact ⟨1, by simp, rfl⟩
  rw [(jordanInterior_isOpen Ho).frontier_eq] at hx
  have hxout : Ho 1 ∉ closure (jordanInterior Hi) := fun hi => hx.2 (hn hi)
  obtain ⟨y, hyout, hyin⟩ := mem_closure_iff_nhds.mp hx.1
    (closure (jordanInterior Hi))ᶜ (isClosed_closure.isOpen_compl.mem_nhds hxout)
  exact ⟨y, hyin, hyout⟩

/-- Ordinary source positivity, actual image winding and actual negative
Jacobian force strict reversed image-fill order. The target parametrizations
are the literal image loops F composed with the source parametrizations. -/
theorem visibleConnector_actual_negative_map_reverses_jordan_order
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {γo γi : ℝ → ℂ}
    (hsourceOuter : RegularJordanParametrization Ho γo)
    (hsourceInner : RegularJordanParametrization Hi γi)
    (hsourceNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (hpositiveOuter : circleFormIntegral (fun _ => 1) (centeredArgument (Ho 0)) γo = 1)
    (hpositiveInner : circleFormIntegral (fun _ => 1) (centeredArgument (Hi 0)) γi = 1)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hsourceO : annularJordanClosure Ho Hi ⊆ O)
    (hnegative : ∀ z ∈ annularJordanInterior Ho Hi, (fderiv ℝ F z).det < 0)
    (himageOuter : RegularJordanParametrization To (F ∘ γo))
    (himageInner : RegularJordanParametrization Ti (F ∘ γi))
    (himagePositiveOuter : planarFormIntegral (annularAngularFormP F (To 0))
      (annularAngularFormQ F (To 0)) γo = 1)
    (hdisjoint : Disjoint (frontier (jordanInterior To)) (frontier (jordanInterior Ti)))
    {c : ℂ} (hcOuter : c ∈ jordanInterior To) (hcInner : c ∈ jordanInterior Ti) :
    closure (jordanInterior To) ⊆ jordanInterior Ti := by
  rcases disjoint_or_nested_jordanInteriors To Ti hdisjoint with hd | hright | hwrong
  · exact False.elim (Set.disjoint_left.mp hd (subset_closure hcOuter) (subset_closure hcInner))
  · exact hright
  · exfalso
    obtain ⟨y, hyOuter, hyInner⟩ := gradientOrder_annulus_nonempty To Ti hwrong
    have hboundaryO := gradientOrder_boundary_subset_source hsourceNested
    have hγoO : ∀ t, γo t ∈ O := fun t => hsourceO
      (hboundaryO (Or.inl (hsourceOuter.mem_frontier t)))
    have hγiO : ∀ t, γi t ∈ O := fun t => hsourceO
      (hboundaryO (Or.inr (hsourceInner.mem_frontier t)))
    have hClosedO : γo 1 = γo 0 := by simpa only [zero_add] using hsourceOuter.periodic 0
    have hClosedI : γi 1 = γi 0 := by simpa only [zero_add] using hsourceInner.periodic 0
    have hrangeO := gradientOrder_range_boundary himageOuter
    have hrangeI := gradientOrder_range_boundary himageInner
    have hyoff : y ∉ F '' (frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi)) := by
      rintro ⟨z, hz, hzy⟩
      rcases hz with hz | hz
      · rw [← hsourceOuter.boundary] at hz
        obtain ⟨t, _, rfl⟩ := hz
        have ht := himageOuter.mem_frontier t
        rw [(jordanInterior_isOpen To).frontier_eq] at ht
        apply ht.2
        change F (γo t) ∈ jordanInterior To
        rw [hzy]
        exact hyOuter
      · rw [← hsourceInner.boundary] at hz
        obtain ⟨t, _, rfl⟩ := hz
        have ht := frontier_subset_closure (himageInner.mem_frontier t)
        exact hyInner (hzy ▸ ht)
    have houterProfile := annularAngularForm_integral_profile hO hF
      hsourceOuter.smooth hγoO hClosedO To hrangeO (To 0)
      (show To 0 ∈ jordanInterior To from ⟨0, Metric.mem_ball_self zero_lt_one, rfl⟩)
      1 himagePositiveOuter
    have hinnerZero := annularAngularForm_integral_zero_exterior hO hF
      hsourceInner.smooth hγiO hClosedI Ti hrangeI.subset y hyInner
    have hdegreeOne : annularBoundaryDegree F γo γi y = 1 := by
      unfold annularBoundaryDegree
      rw [houterProfile.1 y hyOuter, hinnerZero]
      norm_num
    have hcount := annularBoundaryDegree_eq_actual_sign_mul_ncard
      hsourceOuter hsourceInner hsourceNested hpositiveOuter hpositiveInner F O hO hF
      hsourceO (-1) (Or.inr rfl)
      (fun z hz => by have hn := hnegative z hz; norm_num; linarith) y hyoff
    rw [hdegreeOne] at hcount
    have hn : (0 : ℤ) ≤
        ({x | x ∈ annularJordanClosure Ho Hi ∧ F x = y}.ncard : ℤ) := Int.natCast_nonneg _
    omega

private theorem gradientOrder_positive_image_integral
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    {H : ℂ ≃ₜ ℂ} (himage : PositiveJordanParametrization H (F ∘ γ)) :
    planarFormIntegral (annularAngularFormP F (H 0)) (annularAngularFormQ F (H 0)) γ = 1 := by
  have hcenter : H 0 ∈ jordanInterior H := ⟨0, Metric.mem_ball_self zero_lt_one, rfl⟩
  have hAvoid : ∀ t, F (γ t) ≠ H 0 := by
    intro t he
    have ht := himage.toRegular.mem_frontier t
    rw [(jordanInterior_isOpen H).frontier_eq] at ht
    apply ht.2
    change F (γ t) ∈ jordanInterior H
    rw [he]
    exact hcenter
  obtain ⟨u, huproj, hinc⟩ := himage.positive (H 0) hcenter
  rw [annularAngularForm_integral_eq_pathIncrement hO hF hγ hγO (H 0) hAvoid]
  unfold pathArgumentIncrement
  rw [circlePathIncrement_eq_lift _ u (fun t => by
    change (u t : UnitAddCircle) = normalizedArgument (F (γ t) - H 0)
    exact huproj t)]
  linarith

/-- Convenience consumer of ordinary actual positive image parametrizations.
Their positive argument lifts supply the numerical winding input above. -/
theorem visibleConnector_actual_negative_map_reverses_positive_jordan_order
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {γo γi : ℝ → ℂ}
    (hsourceOuter : RegularJordanParametrization Ho γo)
    (hsourceInner : RegularJordanParametrization Hi γi)
    (hsourceNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (hpositiveOuter : circleFormIntegral (fun _ => 1) (centeredArgument (Ho 0)) γo = 1)
    (hpositiveInner : circleFormIntegral (fun _ => 1) (centeredArgument (Hi 0)) γi = 1)
    (F : ℂ → ℂ) (O : Set ℂ) (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hsourceO : annularJordanClosure Ho Hi ⊆ O)
    (hnegative : ∀ z ∈ annularJordanInterior Ho Hi, (fderiv ℝ F z).det < 0)
    (himageOuter : PositiveJordanParametrization To (F ∘ γo))
    (himageInner : PositiveJordanParametrization Ti (F ∘ γi))
    (hdisjoint : Disjoint (frontier (jordanInterior To)) (frontier (jordanInterior Ti)))
    {c : ℂ} (hcOuter : c ∈ jordanInterior To) (hcInner : c ∈ jordanInterior Ti) :
    closure (jordanInterior To) ⊆ jordanInterior Ti := by
  have hb := gradientOrder_boundary_subset_source hsourceNested
  exact visibleConnector_actual_negative_map_reverses_jordan_order
    hsourceOuter hsourceInner hsourceNested hpositiveOuter hpositiveInner F O hO hF hsourceO hnegative
    himageOuter.toRegular himageInner.toRegular
    (gradientOrder_positive_image_integral hO hF hsourceOuter.smooth
      (fun t => hsourceO (hb (Or.inl (hsourceOuter.mem_frontier t)))) himageOuter)
    hdisjoint hcOuter hcInner

end
end TightVer401
