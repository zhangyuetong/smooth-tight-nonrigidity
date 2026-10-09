import TightVer401.BandBendingRuledCurvature
import TightVer401.CorrugatedIdentityBendingBand

/-! The existing identity-holonomy construction now produces an actual nonzero
compact bending and a proved uniform curvature threshold for its opposite branches. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Construct the bending using the retained protected identity-band theorem,
then derive the small-amplitude curvature threshold rather than assume it. -/
theorem periodicRuledFrame_exists_identity_bending_curvature_pair
    {L b : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    (hidentity : PrincipalNormalIdentityBand d) (hb : 0 < b)
    (hemb : Topology.IsEmbedding (d.bandMap (b := b))) :
    ∃ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient,
      IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ (∃ p, Y p ≠ 0) ∧
      ∃ δ > 0, (∀ a : ℝ, |a| < δ →
        bandInducedForm (d.bandMap + a • Y) = bandInducedForm (d.bandMap - a • Y) ∧
        ∀ p : Coord,
          gaussianCurvature (inducedMetric
            (fun q => ruledMap d.γ d.E q + a • bandCoordinateLift Y q)) p < 0 ∧
          gaussianCurvature (inducedMetric
            (fun q => ruledMap d.γ d.E q - a • bandCoordinateLift Y q)) p < 0) ∧
        (∀ a : ℝ, a ≠ 0 → d.bandMap + a • Y ≠ d.bandMap - a • Y) := by
  obtain ⟨hbalance, r, hr, hrb, hs, hi, he, hinside, Y, hY, hc, hn,
    hcoords, himage, hflow, hleaves⟩ :=
    periodicRuledFrame_protectedIdentityBendingSubband d hidentity hb hemb
  obtain ⟨δ, hδ, hbound⟩ := periodicRuledFrame_compact_bending_curvature_threshold d hb hY hc
  refine ⟨Y, hY, hc, hn, δ, hδ, ?_, ?_⟩
  · intro a ha
    refine ⟨bandBending_opposite_branches_metric d.bandMap_contMDiff hY a, fun p => ?_⟩
    constructor
    · exact hbound a ha p
    · have hneg := hbound (-a) (by simpa only [abs_neg] using ha) p
      simpa only [neg_smul, sub_eq_add_neg] using hneg
  · intro a ha
    exact bandBending_opposite_branches_ne ha hn

end
end TightVer401
