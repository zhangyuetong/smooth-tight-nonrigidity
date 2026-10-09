import TightVer401.CorrugatedSeedVisibilityAngleDerivative
import TightVer401.CorrugatedSeedVisibilityAngleExp
import TightVer401.PositiveAngularLift
import TightVer401.PeriodicJordanSeparation

/-! The partner's Jordan property is derived from its actual visibility angle,
whose derivative is positive and whose lift advances by exactly one turn. -/
namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Manifold Topology
local instance seedPartnerJordanPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance seedPartnerJordanChart : ChartedSpace ℝ (AddCircle (2 * Real.pi)) :=
  periodCircleChartedSpace (2 * Real.pi)

theorem corrugatedSeedPartner_injOn {N : ℕ} (hN : 10000 ≤ N) :
    InjOn (corrugatedSeedPartner (N : ℝ)) (Ico 0 (2 * Real.pi)) := by
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  exact curve_injOn_of_positiveAngularLift
    (fun t => (corrugatedSeedVisibleAngle_exp hNr t).symm)
    (corrugatedSeedVisibleAngle_deriv_pos hNr)
    (corrugatedSeedVisibleAngle_shift (by omega : 2 ≤ N))

theorem corrugatedSeedPartner_native_embedding {N : ℕ} (hN : 10000 ≤ N) :
    let hp := corrugatedSeedPartner_periodic (by omega : 2 ≤ N)
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ hp.lift ∧ Topology.IsEmbedding hp.lift := by
  exact periodicComplexCurve_native_embedding (corrugatedSeedPartner_contDiff (N : ℝ))
    (corrugatedSeedPartner_periodic (by omega : 2 ≤ N))
    (corrugatedSeedPartner_injOn hN)

theorem corrugatedSeedPartner_isJordanCurve {N : ℕ} (hN : 10000 ≤ N) :
    Schoenflies.IsJordanCurve
      (range (jordanComplexCoordinates.symm ∘ corrugatedSeedPartner (N : ℝ))) :=
  periodicComplexCurve_isJordanCurve (corrugatedSeedPartner_contDiff (N : ℝ))
    (corrugatedSeedPartner_periodic (by omega : 2 ≤ N))
    (corrugatedSeedPartner_injOn hN)

theorem corrugatedSeedPartner_separates {N : ℕ} (hN : 10000 ≤ N) :
    Schoenflies.IsSeparating
      (range (jordanComplexCoordinates.symm ∘ corrugatedSeedPartner (N : ℝ))) :=
  Schoenflies.jordan_curve_theorem (corrugatedSeedPartner_isJordanCurve hN)

end
end TightVer401
