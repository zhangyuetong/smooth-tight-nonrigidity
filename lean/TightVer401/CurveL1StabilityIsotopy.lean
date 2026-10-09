import TightVer401.CurveL1StabilityPath

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_speedCurve_L1_embedded_interpolation_threshold (L : ℝ) [hL : Fact (0 < L)]
    (P : ℝ → E) (hP : ContDiff ℝ ∞ P) (hPL : Function.Periodic P L)
    (hne : ∀ r, P r ≠ 0) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbL : Function.Periodic b L) (hbpos : ∀ r, 0 < b r)
    (hbclose : (∫ r in 0..L, b r • P r) = 0)
    (hbinj : Set.InjOn (speedCurve b P) (Ico 0 L)) :
    ∃ η > 0, ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a L →
      (∀ r, 0 < a r) → (∫ r in 0..L, a r • P r) = 0 →
      (∫ r in 0..L, |a r - b r|) < η →
      ∃ H : ℝ × AddCircle L → E,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ H ∧
        (∀ t r, H (t, periodProjection L r) = speedCurve (speedLinearInterpolation b a t) P r) ∧
        (∀ t ∈ Icc 0 1, Topology.IsEmbedding (fun q => H (t, q)) ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q => H (t, q)) q))) ∧
        (∀ r, H (0, periodProjection L r) = speedCurve b P r) ∧
        (∀ r, H (1, periodProjection L r) = speedCurve a P r) := by
  obtain ⟨η, hη, hthreshold⟩ := exists_speedCurve_L1_smooth_embedding_threshold
    L P hP hPL hne b hb hbL hbpos hbclose hbinj
  refine ⟨η, hη, fun a ha haL hapos haclose hsmall => ?_⟩
  obtain ⟨Ca, hCa, _, _, hCarep, _⟩ := hthreshold a ha haL hapos haclose hsmall
  have hpb := speedCurve_periodic hb.continuous hP.continuous hbL hPL hbclose
  let Cb := hpb.lift
  have hCb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Cb :=
    periodicLift_contMDiff (rawPrimitive_contDiff (hb.smul hP)) hpb
  let H : ℝ × AddCircle L → E := fun p => (1 - p.1) • Cb p.2 + p.1 • Ca p.2
  have ht : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle L => p.1) := contMDiff_fst
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ H :=
    ((contMDiff_const.sub ht).smul (hCb.comp contMDiff_snd)).add
      (ht.smul (hCa.comp contMDiff_snd))
  have hrep (t r : ℝ) : H (t, periodProjection L r) =
      speedCurve (speedLinearInterpolation b a t) P r := by
    dsimp [H, Cb]
    rw [periodicLift_coe, hCarep, speedCurve_linearInterpolation hb.continuous ha.continuous hP.continuous]
  refine ⟨H, hH, hrep, ?_, ?_, ?_⟩
  · intro t ht01
    have hat := speedLinearInterpolation_contDiff hb ha t
    have hatL := speedLinearInterpolation_periodic hbL haL t
    have hatpos := speedLinearInterpolation_positive hbpos hapos ht01
    have hatclose := speedLinearInterpolation_closing hb.continuous ha.continuous hP.continuous hbclose haclose t
    have hatsmall := (speedLinearInterpolation_L1_le hb.continuous ha.continuous hL.out.le ht01).trans_lt hsmall
    obtain ⟨Ct, _, hemb, himm, htrep, _⟩ := hthreshold
      (speedLinearInterpolation b a t) hat hatL hatpos hatclose hatsmall
    have heq : (fun q => H (t, q)) = Ct := by
      funext q
      obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact (hrep t r).trans (htrep r).symm
    rw [heq]
    exact ⟨hemb, himm⟩
  · intro r
    dsimp [H, Cb]
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using periodicLift_coe hpb r
  · intro r
    dsimp [H]
    simpa only [sub_self, zero_smul, one_smul, zero_add] using hCarep r

end
end TightVer401
