import TightVer401.NativeCircleJordan
import TightVer401.PeriodicCircleFunctions

namespace TightVer401
noncomputable section
open Set Function
open scoped ContDiff Manifold Topology
local instance (L : ℝ) [Fact (0 < L)] : ChartedSpace ℝ (AddCircle L) :=
  periodCircleChartedSpace L

theorem periodicComplexCurve_lift_injective {L : ℝ} [Fact (0 < L)]
    {V : Type*} {f : ℝ → V} (hp : Function.Periodic f L)
    (hi : InjOn f (Ico 0 L)) : Injective hp.lift := by
  intro q r he
  let x := AddCircle.equivIco L 0 q
  let y := AddCircle.equivIco L 0 r
  have hx : (x : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using x.property
  have hy : (y : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using y.property
  have hxq : periodProjection L (x : ℝ) = q := AddCircle.coe_equivIco
  have hyr : periodProjection L (y : ℝ) = r := AddCircle.coe_equivIco
  have hqx : hp.lift q = f (x : ℝ) := by rw [← hxq]; exact hp.lift_coe _
  have hry : hp.lift r = f (y : ℝ) := by rw [← hyr]; exact hp.lift_coe _
  have hxy := hi hx hy (hqx.symm.trans (he.trans hry))
  rw [← hxq, ← hyr, hxy]

theorem periodicComplexCurve_isJordanCurve {L : ℝ} [hL : Fact (0 < L)]
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (hi : InjOn f (Ico 0 L)) :
    Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘ f)) := by
  have hcont : Continuous hp.lift := (periodicLift_contMDiff hf hp).continuous
  have hj := addCircle_complex_embedding_range_isJordanCurve L (ne_of_gt hL.out)
    hp.lift hcont (periodicComplexCurve_lift_injective hp hi)
  have hr : range (jordanComplexCoordinates.symm ∘ hp.lift) =
      range (jordanComplexCoordinates.symm ∘ f) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact ⟨s, by simp only [comp_apply, hp.lift_coe]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨periodProjection L s, by simp only [comp_apply, periodicLift_coe]⟩
  rwa [hr] at hj

theorem periodicComplexCurve_native_embedding {L : ℝ} [Fact (0 < L)]
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (hi : InjOn f (Ico 0 L)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ hp.lift ∧ Topology.IsEmbedding hp.lift := by
  have hC := periodicLift_contMDiff hf hp
  exact ⟨hC, (hC.continuous.isClosedEmbedding (periodicComplexCurve_lift_injective hp hi)).isEmbedding⟩

end
end TightVer401
