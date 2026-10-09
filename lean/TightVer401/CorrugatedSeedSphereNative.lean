import TightVer401.CorrugatedSeedSphere
import TightVer401.PeriodicComplexJordan

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local instance : ChartedSpace ℝ (AddCircle (2 * Real.pi)) := periodCircleChartedSpace _
local instance : IsManifold 𝓘(ℝ, ℝ) ∞ (AddCircle (2 * Real.pi)) := periodCircle_isManifold _
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem corrugatedSeedSpherePoint_injOn {N : ℝ} (hN : 1 < N) :
    InjOn (corrugatedSeedSpherePoint N) (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  exact corrugatedSeedSphere_injOn hN hs ht (congrArg Subtype.val h)

theorem corrugatedSeedSphere_native_embedding {N : ℕ} (hN : 2 ≤ N) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (corrugatedSeedSpherePoint_periodic hN).lift ∧
      Topology.IsEmbedding (corrugatedSeedSpherePoint_periodic hN).lift := by
  let hp := corrugatedSeedSpherePoint_periodic hN
  let ha := corrugatedSeedSphere_periodic hN
  have he : (fun q => (hp.lift q).val) = ha.lift := by
    funext q
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [hp.lift_coe, ha.lift_coe]
    rfl
  have hambient : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ (fun q => (hp.lift q).val) := by
    rw [he]
    exact periodicLift_contMDiff (corrugatedSeedSphere_contDiff _) ha
  have hC : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ hp.lift :=
    hambient.codRestrict_sphere (fun q => (hp.lift q).property)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hinj := periodicComplexCurve_lift_injective hp (corrugatedSeedSpherePoint_injOn hNr)
  exact ⟨hC, (hC.continuous.isClosedEmbedding hinj).isEmbedding⟩

end
end TightVer401
