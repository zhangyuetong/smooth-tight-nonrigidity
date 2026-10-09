import TightVer401.CurveL1Stability
import TightVer401.NormalLoopPrescription
import TightVer401.NormalLoopStability

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_balance_embedded_speed {ζ : ℝ → Ambient} {b : ℝ → ℝ} {L η : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hb : ContDiff ℝ ∞ b)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hbpos : ∀ r, 0 < b r) (hζL : Function.Periodic ζ L) (hbL : Function.Periodic b L)
    (hL : 0 < L) (hmoment : normalLoopMoment b ζ (deriv ζ) L = 0)
    (hbinj : Set.InjOn (normalLoopCurve b ζ (deriv ζ)) (Ico 0 L)) (hη : 0 < η) :
    letI : Fact (0 < L) := ⟨hL⟩
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 ∧
      Set.InjOn (normalLoopCurve a ζ (deriv ζ)) (Ico 0 L) ∧
      ∃ C : AddCircle L → Ambient, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ C ∧
        Topology.IsEmbedding C ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) C q)) ∧
        (∀ r, C (periodProjection L r) = normalLoopCurve a ζ (deriv ζ) r) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hP := (normalLoop_actual_smooth hζ).1
  have hPL := (normalLoop_actual_periodic hζ hζL).1
  have hne (r) : normalLoopTangent ζ r ≠ 0 := by
    intro hz
    have hn := normalLoopTangent_norm hζ hunit hspeed r
    rw [hz, norm_zero] at hn
    norm_num at hn
  obtain ⟨θ, hθ, hthreshold⟩ := exists_speedCurve_L1_smooth_embedding_threshold
    L (normalLoopTangent ζ) hP hPL hne b hb hbL hbpos hmoment hbinj
  obtain ⟨a, ha, haL, hapos, hsmall, hM, hB⟩ := normalLoop_balance_closing_speed
    hζ hb hunit hspeed hbpos hζL hbL hL hmoment (lt_min hη hθ)
  have hsmallabs : (∫ r in 0..L, |a r - b r|) < θ := by
    simpa only [Real.norm_eq_abs] using hsmall.trans_le (min_le_right η θ)
  obtain ⟨C, hC, hemb, himm, hrep, hi⟩ := hthreshold a ha haL hapos hM hsmallabs
  exact ⟨a, ha, haL, hapos, hsmall.trans_le (min_le_left η θ), hM, hB, hi,
    C, hC, hemb, himm, hrep⟩

end
end TightVer401
