import TightVer401.NormalLoopEmbeddingSpeed
import TightVer401.CurveL1StabilityIsotopy
import TightVer401.CurveL1StabilityProjection

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem normalLoop_relative_embedded_balanced_path
    {ζ : ℝ → Ambient} {b : ℝ → ℝ} {L η : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hb : ContDiff ℝ ∞ b)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hbpos : ∀ r, 0 < b r) (hζL : Function.Periodic ζ L) (hbL : Function.Periodic b L)
    (hL : 0 < L) (hmoment : normalLoopMoment b ζ (deriv ζ) L = 0)
    (hbinj : Set.InjOn (normalLoopCurve b ζ (deriv ζ)) (Ico 0 L))
    (π : Ambient →L[ℝ] F) (hπregular : ∀ r, π (normalLoopTangent ζ r) ≠ 0)
    (hπinj : Set.InjOn (π ∘ normalLoopCurve b ζ (deriv ζ)) (Ico 0 L)) (hη : 0 < η) :
    letI : Fact (0 < L) := ⟨hL⟩
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 ∧
      ∃ H : ℝ × AddCircle L → Ambient,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ H ∧
        (∀ t r, H (t, periodProjection L r) =
          normalLoopCurve (speedLinearInterpolation b a t) ζ (deriv ζ) r) ∧
        (∀ r, H (0, periodProjection L r) = normalLoopCurve b ζ (deriv ζ) r) ∧
        (∀ r, H (1, periodProjection L r) = normalLoopCurve a ζ (deriv ζ) r) ∧
        (∀ t ∈ Icc 0 1, Topology.IsEmbedding (fun q => H (t, q)) ∧
          Topology.IsEmbedding (π ∘ (fun q => H (t, q))) ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (fun q => H (t, q)) q)) ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (π ∘ (fun q => H (t, q))) q))) ∧
        (∀ t ∈ Icc 0 1, ∀ q, ‖H (t, q) - H (0, q)‖ < η) ∧
        (∀ t ∈ Icc 0 1, ∀ r,
          0 < speedLinearInterpolation b a t r ∧
          HasDerivAt (normalLoopCurve (speedLinearInterpolation b a t) ζ (deriv ζ))
            (speedLinearInterpolation b a t r • normalLoopTangent ζ r) r ∧
          inner ℝ (normalLoopTangent ζ r) (ζ r) = 0) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hP := (normalLoop_actual_smooth hζ).1
  have hPL := (normalLoop_actual_periodic hζ hζL).1
  have hne (r) : normalLoopTangent ζ r ≠ 0 := by
    intro hz
    have hn := normalLoopTangent_norm hζ hunit hspeed r
    rw [hz, norm_zero] at hn
    norm_num at hn
  obtain ⟨θ, hθ, hiso⟩ := exists_speedCurve_L1_embedded_interpolation_threshold
    L (normalLoopTangent ζ) hP hPL hne b hb hbL hbpos hmoment hbinj
  obtain ⟨θπ, hθπ, hproj⟩ := exists_speedCurve_L1_regular_projection_threshold
    L π (normalLoopTangent ζ) hP hPL hπregular b hb hbL hbpos hmoment hπinj
  obtain ⟨a, ha, haL, hapos, hsmall, hM, hB⟩ := normalLoop_balance_closing_speed
    hζ hb hunit hspeed hbpos hζL hbL hL hmoment (lt_min hη (lt_min hθ hθπ))
  have hsη := hsmall.trans_le (min_le_left η (min θ θπ))
  have hsmallabs : (∫ r in 0..L, |a r - b r|) < min θ θπ := by
    simpa only [Real.norm_eq_abs] using hsmall.trans_le (min_le_right η (min θ θπ))
  obtain ⟨H, hH, hrep, hemb, hzero, hone⟩ := hiso a ha haL hapos hM
    (hsmallabs.trans_le (min_le_left θ θπ))
  refine ⟨a, ha, haL, hapos, hsη, hM, hB, H, hH, hrep, hzero, hone, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hsp, himm⟩ := hemb t ht
    have hpr := hproj (speedLinearInterpolation b a t)
      (speedLinearInterpolation_contDiff hb ha t) (speedLinearInterpolation_periodic hbL haL t)
      (speedLinearInterpolation_positive hbpos hapos ht)
      (speedLinearInterpolation_closing hb.continuous ha.continuous hP.continuous hmoment hM t)
      ((speedLinearInterpolation_L1_le hb.continuous ha.continuous hL.le ht).trans_lt
        (hsmallabs.trans_le (min_le_right θ θπ))) (fun q => H (t, q)) (hrep t)
    exact ⟨hsp, hpr.1, himm, hpr.2⟩
  · intro t ht q
    let x := AddCircle.equivIco L 0 q
    have hx : (x : ℝ) ∈ Icc 0 L := ⟨x.property.1, by simpa only [zero_add] using x.property.2.le⟩
    have hxq : periodProjection L (x : ℝ) = q := AddCircle.coe_equivIco
    rw [← hxq, hrep, hzero]
    apply (normalLoopCurve_uniform_norm_sub_le
      (speedLinearInterpolation_contDiff hb ha t).continuous hb.continuous hζ hunit hspeed hx).trans_lt
    have hl := speedLinearInterpolation_L1_le hb.continuous ha.continuous hL.le ht
    exact hl.trans_lt (by simpa only [Real.norm_eq_abs] using hsη)
  · intro t ht r
    have hat := speedLinearInterpolation_contDiff hb ha t
    have hframe := normalLoop_actual_frame hζ hunit hspeed r
    exact ⟨speedLinearInterpolation_positive hbpos hapos ht r,
      rawPrimitive_hasDerivAt (hat.continuous.smul hP.continuous) r, hframe.1.2.2.2.2.1⟩

end
end TightVer401
