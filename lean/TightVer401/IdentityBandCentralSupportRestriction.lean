import TightVer401.CorrugatedSpikeActualBand

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Restrict both actual embeddings to a narrower positive band. -/
theorem identityBandCentralSupport_restrict_band_embeddings {T w oldw : ℝ}
    (d : PeriodicRuledFrame T) (hwold : w ≤ oldw)
    (hX : Topology.IsEmbedding (d.bandMap (b := oldw)))
    (hH : Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := oldw))) :
    Topology.IsEmbedding (d.bandMap (b := w)) ∧
      Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)) := by
  have hsub : Ioo (0 : ℝ) w ⊆ Ioo 0 oldw := fun x hx => ⟨hx.1, hx.2.trans_le hwold⟩
  let j : AddCircle T × Ioo (0 : ℝ) w → AddCircle T × Ioo (0 : ℝ) oldw :=
    fun p => (p.1, Set.inclusion hsub p.2)
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion hsub)
  have heq : d.bandMap (b := oldw) ∘ j = d.bandMap (b := w) := rfl
  have hheq : (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := oldw)) ∘ j =
      corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w) := rfl
  constructor
  · rw [← heq]
    exact hX.comp hj
  · rw [← hheq]
    exact hH.comp hj

end
end TightVer401
