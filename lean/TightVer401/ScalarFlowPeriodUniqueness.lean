import TightVer401.ScalarFlowVariation
import OAI.Geometry.WeakMTW.Analysis.SmoothFlow

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem scalarFlowPeriod_unique_Icc_local {F : Coord → Coord} {W : Set Coord}
    {u v : ℝ → Coord} {a b t₀ : ℝ}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (ht : t₀ ∈ Ioo a b)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (F (u t)) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (F (v t)) t)
    (huW : ∀ t ∈ Icc a b, u t ∈ W) (hvW : ∀ t ∈ Icc a b, v t ∈ W)
    (h0 : u t₀ = v t₀) : EqOn u v (Icc a b) := by
  let S := u '' Icc a b ∪ v '' Icc a b
  have hS : IsCompact S := (isCompact_Icc.image_of_continuousOn hu).union
    (isCompact_Icc.image_of_continuousOn hv)
  have hSW : S ⊆ W := by
    rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact huW t ht
    · exact hvW t ht
  have hlocal : LocallyLipschitzOn S F := by
    intro p hp
    have hc : ContDiffAt ℝ 1 F p :=
      ((hF p (hSW hp)).contDiffAt (hW.mem_nhds (hSW hp))).of_le (by simp)
    obtain ⟨K, T, hT, hLip⟩ := hc.exists_lipschitzOnWith
    exact ⟨K, T, mem_nhdsWithin_of_mem_nhds hT, hLip⟩
  obtain ⟨K, hK⟩ := hlocal.exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc (fun _ _ => hK) ht hu hdu
    (fun t ht => Or.inl (mem_image_of_mem _ (Ioo_subset_Icc_self ht))) hv hdv
    (fun t ht => Or.inr (mem_image_of_mem _ (Ioo_subset_Icc_self ht))) h0

end
end TightVer401
