import TightVer401.PeriodicComplexJordan
import TightVer401.CorrugatedSeedClosure

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Manifold Topology
local instance seedBetaJordanPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance seedBetaJordanChart : ChartedSpace ℝ (AddCircle (2 * Real.pi)) :=
  periodCircleChartedSpace (2 * Real.pi)

theorem corrugatedSeedBeta_isJordanCurve {N : ℕ} (hN : 2 ≤ N) :
    Schoenflies.IsJordanCurve
      (range (jordanComplexCoordinates.symm ∘ corrugatedSeedBeta (N : ℝ))) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact periodicComplexCurve_isJordanCurve (corrugatedSeedBeta_contDiff (N : ℝ))
    (corrugatedSeedBeta_periodic hN) (corrugatedSeedBeta_injOn hNr)

theorem corrugatedSeedBeta_native_embedding {N : ℕ} (hN : 2 ≤ N) :
    let hp := corrugatedSeedBeta_periodic hN
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ hp.lift ∧ Topology.IsEmbedding hp.lift := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact periodicComplexCurve_native_embedding (corrugatedSeedBeta_contDiff (N : ℝ))
    (corrugatedSeedBeta_periodic hN) (corrugatedSeedBeta_injOn hNr)

end
end TightVer401
