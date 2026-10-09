import TightVer401.CurveL1StabilityRepresentative
import TightVer401.PeriodicCircleFunctions

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem speedCurve_periodic {L : ℝ} {a : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hP : Continuous P) (haL : Function.Periodic a L)
    (hPL : Function.Periodic P L) (hclose : (∫ x in 0..L, a x • P x) = 0) :
    Function.Periodic (speedCurve a P) L := by
  have hp : Function.Periodic (fun x => a x • P x) L := fun x => by
    change a (x + L) • P (x + L) = a x • P x
    rw [haL x, hPL x]
  intro x
  dsimp [speedCurve, rawPrimitive]
  rw [hp.intervalIntegral_add_eq_add 0 x (fun c d => (ha.smul hP).intervalIntegrable c d)]
  simpa only [zero_add, hclose, add_zero]

theorem speedCurve_periodicLift_injective {L : ℝ} [Fact (0 < L)]
    {a : ℝ → ℝ} {P : ℝ → E} (hp : Function.Periodic (speedCurve a P) L)
    (hi : Set.InjOn (speedCurve a P) (Ico 0 L)) : Function.Injective hp.lift := by
  intro q r he
  let x := AddCircle.equivIco L 0 q
  let y := AddCircle.equivIco L 0 r
  have hx : (x : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using x.property
  have hy : (y : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using y.property
  have hxq : periodProjection L (x : ℝ) = q := AddCircle.coe_equivIco
  have hyr : periodProjection L (y : ℝ) = r := AddCircle.coe_equivIco
  have hqx : hp.lift q = speedCurve a P (x : ℝ) := by rw [← hxq]; exact hp.lift_coe _
  have hry : hp.lift r = speedCurve a P (y : ℝ) := by rw [← hyr]; exact hp.lift_coe _
  have hxy := hi hx hy (hqx.symm.trans (he.trans hry))
  rw [← hxq, ← hyr, hxy]

/-- The actual L1 threshold preserves a native smooth embedded quotient curve.
Only positive speed is required for local separation; C1 speed closeness is absent. -/
theorem exists_speedCurve_L1_embedding_threshold (L : ℝ) [hL : Fact (0 < L)]
    (P : ℝ → E) (hP : ContDiff ℝ ∞ P) (hPL : Function.Periodic P L)
    (hne : ∀ x, P x ≠ 0) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbL : Function.Periodic b L) (_hbpos : ∀ x, 0 < b x)
    (hbclose : (∫ x in 0..L, b x • P x) = 0)
    (hbinj : Set.InjOn (speedCurve b P) (Ico 0 L)) :
    letI := periodCircleChartedSpace L
    ∃ η > 0, ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a L →
      (∀ x, 0 < a x) → (∫ x in 0..L, a x • P x) = 0 →
      (∫ x in 0..L, |a x - b x|) < η →
      ∃ C : AddCircle L → E, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ C ∧
        Topology.IsEmbedding C ∧ (∀ x, C (periodProjection L x) = speedCurve a P x) ∧
        Set.InjOn (speedCurve a P) (Ico 0 L) := by
  letI := periodCircleChartedSpace L
  obtain ⟨η, hη, hthreshold⟩ := exists_speedCurve_L1_representative_threshold hL.out P hP.continuous hne
    b hb.continuous (speedCurve_periodic hb.continuous hP.continuous hbL hPL hbclose) hbinj
  refine ⟨η, hη, fun a ha haL hapos haclose hsmall => ?_⟩
  have hp := speedCurve_periodic ha.continuous hP.continuous haL hPL haclose
  have hi := hthreshold a ha.continuous hapos hp hsmall
  have hC : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift :=
    periodicLift_contMDiff (rawPrimitive_contDiff (ha.smul hP)) hp
  have hinj := speedCurve_periodicLift_injective hp hi
  exact ⟨hp.lift, hC, (hC.continuous.isClosedEmbedding hinj).isEmbedding,
    fun x => hp.lift_coe x, hi⟩

end
end TightVer401
