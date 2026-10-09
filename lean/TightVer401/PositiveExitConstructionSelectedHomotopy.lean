import TightVer401.AnnularDegreeJordanWinding

/-! Actual varying-loop argument increments and the whole closed source
annulus domain gate. A homotopy is an ordinary map with literal image and
endpoint equations. Its actual selected-flow producer is a separate step;
this file never assumes the resulting annular domain or chart. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual argument increment is constant along any continuous family
of closed loops avoiding the given point. Continuity is from the pinned
actual circle-path lift, and the closed-loop values are actual integers. -/
theorem positiveExit_actual_loop_homotopy_increment_eq
    (H : C(unitInterval, C(unitInterval, ℂ))) (y : ℂ)
    (havoid : ∀ a t, H a t ≠ y) (hclosed : ∀ a, H a 1 = H a 0)
    (a b : unitInterval) :
    pathArgumentIncrement ⟨(H a, y), by rintro ⟨t, ht⟩; exact havoid a t ht⟩ =
      pathArgumentIncrement ⟨(H b, y), by rintro ⟨t, ht⟩; exact havoid b t ht⟩ := by
  let p : unitInterval → AvoidingPathPoint := fun a =>
    ⟨(H a, y), by rintro ⟨t, ht⟩; exact havoid a t ht⟩
  have hp : Continuous p := (H.continuous.prodMk continuous_const).subtype_mk _
  have hi : Continuous (fun a => pathArgumentIncrement (p a)) :=
    continuous_pathArgumentIncrement.comp hp
  have hMaps : MapsTo (fun a => pathArgumentIncrement (p a)) univ
      (range ((↑) : ℤ → ℝ)) := by
    intro a _
    obtain ⟨n, hn⟩ := pathArgumentIncrement_integer_of_closed (p a) (hclosed a)
    exact ⟨n, hn.symm⟩
  letI : PreconnectedSpace unitInterval :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact isPreconnected_univ.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
    hi.continuousOn hMaps (mem_univ a) (mem_univ b)

private theorem selectedHomotopy_boundary_range {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    range γ = frontier (jordanInterior H) := by
  apply subset_antisymm
  · rintro _ ⟨s, rfl⟩
    exact hγ.mem_frontier s
  · rw [← hγ.boundary]
    exact image_subset_range _ _

/-- A literal homotopy of the two source loops INSIDE U places their entire
closed intervening Jordan region inside U. Ordinary positive winding at an
interior point enters; target order, degree,
annular inverse and an annular-domain witness are not inputs. -/
theorem positiveExit_actual_source_homotopy_closed_annulus_in_domain
    {Ho Hi : ℂ ≃ₜ ℂ} {γo γi : ℝ → ℂ}
    (ho : RegularJordanParametrization Ho γo)
    (hi : RegularJordanParametrization Hi γi)
    {U : Set ℂ} (houterU : ∀ s, γo s ∈ U) (hinnerU : ∀ s, γi s ∈ U)
    (c : ℂ) (hc : c ∈ jordanInterior Ho)
    (hwind : planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) c)
      (annularAngularFormQ (id : ℂ → ℂ) c) γo = 1)
    (H : C(unitInterval, C(unitInterval, ℂ)))
    (hH0 : H 0 = annularLoopPath γo ho.smooth.continuous)
    (hH1 : H 1 = annularLoopPath γi hi.smooth.continuous)
    (hclosed : ∀ a, H a 1 = H a 0) (hHU : ∀ a t, H a t ∈ U) :
    annularJordanClosure Ho Hi ⊆ U := by
  intro y hy
  by_contra hyU
  have hoy : y ∉ frontier (jordanInterior Ho) := by
    rw [← selectedHomotopy_boundary_range ho]
    rintro ⟨s, rfl⟩
    exact hyU (houterU s)
  have hiy : y ∉ frontier (jordanInterior Hi) := by
    rw [← selectedHomotopy_boundary_range hi]
    rintro ⟨s, rfl⟩
    exact hyU (hinnerU s)
  have hyo : y ∈ jordanInterior Ho := by
    by_contra hnot
    apply hoy
    rw [(jordanInterior_isOpen Ho).frontier_eq]
    exact ⟨hy.1, hnot⟩
  have hyi : y ∉ closure (jordanInterior Hi) := by
    intro hycl
    apply hiy
    rw [(jordanInterior_isOpen Hi).frontier_eq]
    exact ⟨hycl, hy.2⟩
  have hclosedo : γo 1 = γo 0 := by simpa only [zero_add] using ho.periodic 0
  have hclosedi : γi 1 = γi 0 := by simpa only [zero_add] using hi.periodic 0
  have hid : ContDiffOn ℝ ∞ (id : ℂ → ℂ) univ := contDiff_id.contDiffOn
  have hbo : range ((id : ℂ → ℂ) ∘ γo) = frontier (jordanInterior Ho) := by
    simpa only [id_comp] using selectedHomotopy_boundary_range ho
  have hbi : range ((id : ℂ → ℂ) ∘ γi) ⊆ frontier (jordanInterior Hi) := by
    simpa only [id_comp] using (selectedHomotopy_boundary_range hi).subset
  have hout : planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
      (annularAngularFormQ (id : ℂ → ℂ) y) γo = 1 :=
    (annularAngularForm_integral_profile isOpen_univ hid ho.smooth
      (fun s => mem_univ _) hclosedo Ho hbo c hc 1 hwind).1 y hyo
  have hin : planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
      (annularAngularFormQ (id : ℂ → ℂ) y) γi = 0 :=
    annularAngularForm_integral_zero_exterior isOpen_univ hid hi.smooth
      (fun s => mem_univ _) hclosedi Hi hbi y hyi
  have havoido (s) : γo s ≠ y := fun he => hyU (he ▸ houterU s)
  have havoidi (s) : γi s ≠ y := fun he => hyU (he ▸ hinnerU s)
  have hintO := annularAngularForm_integral_eq_pathIncrement isOpen_univ hid
    ho.smooth (fun s => mem_univ _) y havoido
  have hintI := annularAngularForm_integral_eq_pathIncrement isOpen_univ hid
    hi.smooth (fun s => mem_univ _) y havoidi
  have hhom := positiveExit_actual_loop_homotopy_increment_eq H y
    (fun a t he => hyU (he ▸ hHU a t)) hclosed 0 1
  simp only [hH0, hH1] at hhom
  have heq : planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
      (annularAngularFormQ (id : ℂ → ℂ) y) γo =
      planarFormIntegral (annularAngularFormP (id : ℂ → ℂ) y)
        (annularAngularFormQ (id : ℂ → ℂ) y) γi := by
    rw [hintO, hintI]
    simpa only [id_comp] using hhom
  rw [hout, hin] at heq
  norm_num at heq

end
end TightVer401
