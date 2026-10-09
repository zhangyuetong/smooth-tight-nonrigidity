import TightVer401.QuadraticRadialFillingGradientJordan

/-! A genuine ambient model constructed from an image-set Jordan hypothesis.
No injectivity of the supplied traversal is assumed here. -/
namespace TightVer401
noncomputable section
open Set Function
open scoped Topology

theorem quadraticRadialFillingJordanImage_exists_filling {γ : ℝ → ℂ}
    (hJ : Schoenflies.IsJordanCurve
      (range (jordanComplexCoordinates.symm ∘ γ))) :
    ∃ Γ : ℂ ≃ₜ ℂ, range γ = Γ '' Metric.sphere (0 : ℂ) 1 := by
  let e : ℂ ≃ₜ Schoenflies.Plane := jordanComplexCoordinates.toHomeomorph.symm
  let c : Circle → Schoenflies.Plane := fun z => e (z : ℂ)
  have hc : Continuous c := e.continuous.comp continuous_subtype_val
  have hi : Injective c := e.injective.comp Subtype.val_injective
  have hC := circle_embedding_range_isJordanCurve c hc hi
  obtain ⟨b⟩ := hC.homeomorph hJ
  obtain ⟨G, hG⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hC hJ b
  let Γ : ℂ ≃ₜ ℂ := e.trans (G.trans e.symm)
  refine ⟨Γ, ?_⟩
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    let y : range (jordanComplexCoordinates.symm ∘ γ) :=
      ⟨e (γ t), ⟨t, rfl⟩⟩
    obtain ⟨a, ha⟩ := b.surjective y
    obtain ⟨w, hw⟩ := a.property
    refine ⟨(w : ℂ), ?_, ?_⟩
    · simpa only [Metric.mem_sphere, dist_zero_right] using Circle.norm_coe w
    · apply e.injective
      simp only [Γ, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
      have hGa := hG a
      rw [← hw] at hGa
      exact hGa.trans (congrArg Subtype.val ha)
  · rintro ⟨w, hw, rfl⟩
    let q : Circle := ⟨w, hw⟩
    let a : range c := ⟨c q, mem_range_self q⟩
    obtain ⟨t, ht⟩ := (b a).property
    refine ⟨t, ?_⟩
    apply e.injective
    simp only [Γ, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    exact ht.trans (hG a).symm

end
end TightVer401
