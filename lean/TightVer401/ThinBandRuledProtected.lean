import TightVer401.ThinBandRuledEmbedding
import TightVer401.ThinBandRuledGauss

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- One actual width simultaneously embeds the band and makes its actual
Gauss map injective. The two widths are constructed and then intersected. -/
theorem periodicRuledFrame_exists_embedded_Gauss_injective_band
    {L : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    (hγ : Function.Injective d.period_γ.lift) (hn : Function.Injective d.period_n.lift) :
    ∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ)) ∧
      Function.Injective (fun p : AddCircle L × Ioo (0 : ℝ) δ =>
        d.fullGaussMap (p.1, (p.2 : ℝ))) := by
  obtain ⟨w, hw, hemb⟩ := periodicRuledFrame_exists_thin_band_embedding d hγ
  obtain ⟨v, hv, hi⟩ := periodicRuledFrame_exists_thin_Gauss_injective d hn
  let δ := min w v
  have hδ : 0 < δ := lt_min hw hv
  have hδw : δ ≤ w := min_le_left _ _
  have hδv : δ ≤ v := min_le_right _ _
  have hs : Ioo (0 : ℝ) δ ⊆ Ioo 0 w := fun x hx => ⟨hx.1, hx.2.trans_le hδw⟩
  let j : AddCircle L × Ioo (0 : ℝ) δ → AddCircle L × Ioo (0 : ℝ) w :=
    fun p => (p.1, Set.inclusion hs p.2)
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion hs)
  refine ⟨δ, hδ, hemb.comp hj, ?_⟩
  intro p q he
  have hp : (p.1, (p.2 : ℝ)) ∈ (univ ×ˢ Icc (-v) v : Set (AddCircle L × ℝ)) :=
    ⟨mem_univ _, ⟨by linarith [p.2.property.1], p.2.property.2.le.trans hδv⟩⟩
  have hq : (q.1, (q.2 : ℝ)) ∈ (univ ×ˢ Icc (-v) v : Set (AddCircle L × ℝ)) :=
    ⟨mem_univ _, ⟨by linarith [q.2.property.1], q.2.property.2.le.trans hδv⟩⟩
  have hsame := hi hp hq he
  have hfirst : p.1 = q.1 := congrArg (fun x : AddCircle L × ℝ => x.1) hsame
  have hsecond : (p.2 : ℝ) = (q.2 : ℝ) := congrArg (fun x : AddCircle L × ℝ => x.2) hsame
  exact Prod.ext hfirst (Subtype.ext hsecond)

end
end TightVer401
