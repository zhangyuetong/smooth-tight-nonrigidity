import TightVer401.ThinBandRuledHorizontal
import TightVer401.ThinBandRuledProtected

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem periodicRuledFrame_exists_embedded_projected_Gauss_band
    {L : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    (hγ : Function.Injective d.period_γ.lift) (hn : Function.Injective d.period_n.lift)
    (hvertical : ∀ r, d.n r 2 ≠ 0)
    (hπγ : Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift)) :
    ∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ)) ∧
      Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := δ)) ∧
      Function.Injective (fun p : AddCircle L × Ioo (0 : ℝ) δ =>
        d.fullGaussMap (p.1, (p.2 : ℝ))) := by
  obtain ⟨w, hw, hs, hg⟩ := periodicRuledFrame_exists_embedded_Gauss_injective_band d hγ hn
  obtain ⟨v, hv, hp⟩ := periodicRuledFrame_exists_thin_horizontal_embedding d hvertical hπγ
  let δ := min w v
  have hδ : 0 < δ := lt_min hw hv
  have hsw : Ioo (0 : ℝ) δ ⊆ Ioo 0 w := fun x hx =>
    ⟨hx.1, hx.2.trans_le (min_le_left w v)⟩
  have hsv : Ioo (0 : ℝ) δ ⊆ Ioo 0 v := fun x hx =>
    ⟨hx.1, hx.2.trans_le (min_le_right w v)⟩
  let jw : AddCircle L × Ioo (0 : ℝ) δ → AddCircle L × Ioo (0 : ℝ) w :=
    fun p => (p.1, Set.inclusion hsw p.2)
  let jv : AddCircle L × Ioo (0 : ℝ) δ → AddCircle L × Ioo (0 : ℝ) v :=
    fun p => (p.1, Set.inclusion hsv p.2)
  have hiw : Topology.IsEmbedding jw :=
    Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion hsw)
  have hiv : Topology.IsEmbedding jv :=
    Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion hsv)
  have hsδ : Topology.IsEmbedding (d.bandMap (b := w) ∘ jw) := hs.comp hiw
  have hpδ : Topology.IsEmbedding ((corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := v)) ∘ jv) :=
    hp.comp hiv
  refine ⟨δ, hδ, hsδ, hpδ, ?_⟩
  intro p q he
  have he' : d.fullGaussMap ((jw p).1, ((jw p).2 : ℝ)) =
      d.fullGaussMap ((jw q).1, ((jw q).2 : ℝ)) := he
  exact hiw.injective (hg he')

end
end TightVer401
