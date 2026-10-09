import TightVer401.ThinBandRuledGauss

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem periodicRuledFrame_exists_northern_strip {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hn : ∀ r, 0 < d.n r 2) :
    ∃ δ > 0, ∀ p ∈ (univ ×ˢ Icc (-δ) δ : Set (AddCircle L × ℝ)), 0 < d.fullGaussMap p 2 := by
  let K : Set (AddCircle L × ℝ) := (fun q : AddCircle L => (q, (0 : ℝ))) '' univ
  let U : Set (AddCircle L × ℝ) := {p | 0 < d.fullGaussMap p 2}
  have hK : IsCompact K := isCompact_univ.image (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun p : AddCircle L × ℝ => d.fullGaussMap p 2) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp
      (periodicRuledFrame_fullGaussMap_continuous d)
  have hU : IsOpen U := isOpen_lt continuous_const hc
  have hKU : K ⊆ U := by
    rintro _ ⟨q, _, rfl⟩
    change 0 < d.fullGaussMap (q, (0 : ℝ)) 2
    have hzero : d.fullGaussMap (q, (0 : ℝ)) = d.period_n.lift q := by
      simp [PeriodicRuledFrame.fullGaussMap, ruledNormal, ruledEnergy]
    rw [hzero]
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    simpa only [Function.Periodic.lift_coe] using hn r
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro p hp
  apply hthick
  apply Metric.thickening_subset_cthickening δ K
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(p.1, 0), ⟨p.1, mem_univ _, rfl⟩, ?_⟩
  rw [dist_prod_same_left, Real.dist_eq, sub_zero]
  exact (abs_le.mpr hp.2).trans_lt (half_lt_self hδ)

end
end TightVer401
