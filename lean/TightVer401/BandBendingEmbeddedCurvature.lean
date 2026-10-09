import TightVer401.NativeSupportedEmbeddingStability
import TightVer401.BandBendingIdentityCurvature
import TightVer401.BandBendingNativeCurvature
import TightVer401.NativeProductPlaneMetricBundleApplications

/-! One actual constructed identity-holonomy band admits distinct opposite
smooth embedded bendings with equal actual induced forms and negative curvature. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- The protected band construction and proved compact-support stability give
an actual opposite-branch embedded band pair. Image noncongruence and torus
completion remain separate mathematical conclusions. -/
theorem periodicRuledFrame_exists_identity_embedded_curvature_pair
    {L b : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    (hidentity : PrincipalNormalIdentityBand d) (hb : 0 < b)
    (hemb : Topology.IsEmbedding (d.bandMap (b := b))) :
    ∃ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient,
      IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ (∃ p, Y p ≠ 0) ∧
      ∃ δ > 0, (∀ a : ℝ, |a| < δ →
        Topology.IsEmbedding (d.bandMap + a • Y) ∧
        Topology.IsEmbedding (d.bandMap - a • Y) ∧
        bandInducedForm (d.bandMap + a • Y) = bandInducedForm (d.bandMap - a • Y) ∧
        ∀ p : AddCircle L × Ioo (0 : ℝ) b,
          gaussianCurvature (inducedMetric
            (nativeProductPlaneCoordinateMap (d.bandMap + a • Y) p))
            (![0, (p.2 : ℝ)] : Coord) < 0 ∧
          gaussianCurvature (inducedMetric
            (nativeProductPlaneCoordinateMap (d.bandMap - a • Y) p))
            (![0, (p.2 : ℝ)] : Coord) < 0) ∧
        (∀ a : ℝ, a ≠ 0 → d.bandMap + a • Y ≠ d.bandMap - a • Y) := by
  letI : LocallyCompactSpace (ModelProd ℝ ℝ) :=
    inferInstanceAs (LocallyCompactSpace (ℝ × ℝ))
  letI : LocallyCompactSpace (AddCircle L × Ioo (0 : ℝ) b) :=
    ChartedSpace.locallyCompactSpace (ModelProd ℝ ℝ) _
  obtain ⟨hbalance, r, hr, hrb, hs, hi, he, hinside, Y, hY, hc, hn,
    hcoords, himage, hflow, hleaves⟩ :=
    periodicRuledFrame_protectedIdentityBendingSubband d hidentity hb hemb
  have himm : ∀ p : AddCircle L × Ioo (0 : ℝ) b,
      Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) d.bandMap p) :=
    fun p => periodicRuledFrame_bandMap_immersion d p
  obtain ⟨δe, hδe, hembed⟩ := nativeSupportedEmbedding_exists_amplitude_threshold
    d.bandMap_contMDiff hY.1 hemb himm hc
  obtain ⟨δk, hδk, hcurv⟩ :=
    periodicRuledFrame_native_compact_bending_curvature_threshold d hb hY hc
  refine ⟨Y, hY, hc, hn, min δe δk, lt_min hδe hδk, ?_, ?_⟩
  · intro a ha
    have hae : |a| < δe := lt_of_lt_of_le ha (min_le_left _ _)
    have hak : |a| < δk := lt_of_lt_of_le ha (min_le_right _ _)
    have hemp : Topology.IsEmbedding (d.bandMap + a • Y) := hembed a hae
    have hemm : Topology.IsEmbedding (d.bandMap - a • Y) := by
      have ht : Topology.IsEmbedding (d.bandMap + (-a) • Y) :=
        hembed (-a) (by simpa only [abs_neg] using hae)
      have heq : d.bandMap + (-a) • Y = d.bandMap - a • Y := by
        simp only [neg_smul, sub_eq_add_neg]
      rw [heq] at ht
      exact ht
    refine ⟨hemp, hemm, bandBending_opposite_branches_metric d.bandMap_contMDiff hY a,
      fun p => ⟨hcurv a hak p, ?_⟩⟩
    simpa only [neg_smul, sub_eq_add_neg] using hcurv (-a) (by simpa using hak) p
  · intro a ha
    exact bandBending_opposite_branches_ne ha hn

end
end TightVer401
