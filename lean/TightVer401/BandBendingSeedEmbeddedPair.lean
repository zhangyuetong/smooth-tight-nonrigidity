import TightVer401.BandBendingEmbeddedCurvature
import TightVer401.CorrugatedIdentityBendingBand

/-! Actual embedded opposite band branches from the corrected corrugated seed.
The physical frame and original embedded identity band are extracted from the
same seed construction; the proved perturbation thresholds are then applied.
-/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Seed parameters alone construct an identity-holonomy embedded band with a
nonzero compact bending whose sufficiently small opposite branches are embedded,
have equal actual induced forms and have negative actual native-chart curvature.
Their maps are distinct at every nonzero amplitude. Image noncongruence and torus
completion are separate conclusions. -/
theorem corrugatedSeed_exists_identity_embedded_curvature_pair {N : ℕ}
    (hN : 10000 ≤ N) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      letI : Fact (0 < T) := ⟨hT⟩
      ∃ d : PeriodicRuledFrame T, ∃ w > 0,
        PrincipalNormalIdentityBand d ∧ Topology.IsEmbedding (d.bandMap (b := w)) ∧
        ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
          IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧ (∃ p, Y p ≠ 0) ∧
          ∃ δ > 0, (∀ a : ℝ, |a| < δ →
            Topology.IsEmbedding (d.bandMap + a • Y) ∧
            Topology.IsEmbedding (d.bandMap - a • Y) ∧
            bandInducedForm (d.bandMap + a • Y) = bandInducedForm (d.bandMap - a • Y) ∧
            ∀ p : AddCircle T × Ioo (0 : ℝ) w,
              gaussianCurvature (inducedMetric
                (nativeProductPlaneCoordinateMap (d.bandMap + a • Y) p))
                (![0, (p.2 : ℝ)] : Coord) < 0 ∧
              gaussianCurvature (inducedMetric
                (nativeProductPlaneCoordinateMap (d.bandMap - a • Y) p))
                (![0, (p.2 : ℝ)] : Coord) < 0) ∧
            (∀ a : ℝ, a ≠ 0 → d.bandMap + a • Y ≠ d.bandMap - a • Y) := by
  obtain ⟨e, _he, _hψ, a, _ha, _haT, _hapos, _hsmall, _hMfull, _hBfull, _hout, _href,
    S, _hS, _hSsmooth, d, _hγ, _hT, _hE, _hn, _hk, _hτ, hidentity, hTpos, w, hw,
    _hsmooth, _himm, hemb, _hproj, _hprojs, _hproji, _hgauss, _hnorth, _hGs, _hGinj,
    _hGdiff, _horth, _hreturn, _hcomplete, _hsaturated, _hprotected⟩ :=
      corrugatedSeed_exists_protected_identity_band_bending hN hη
  letI : Fact (0 < rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := ⟨hTpos⟩
  refine ⟨rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ)), hTpos,
    d, w, hw, hidentity, hemb, ?_⟩
  exact periodicRuledFrame_exists_identity_embedded_curvature_pair d hidentity hw hemb

end
end TightVer401
