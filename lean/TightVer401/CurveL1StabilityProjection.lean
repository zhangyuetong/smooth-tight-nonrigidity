import TightVer401.CurveL1Stability

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem speedCurve_linear_projection (π : E →L[ℝ] F) {a : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hP : Continuous P) (r : ℝ) :
    speedCurve a (π ∘ P) r = π (speedCurve a P r) := by
  simpa only [speedCurve, rawPrimitive, Function.comp_apply, Pi.smul_apply', map_smul] using
    π.intervalIntegral_comp_comm ((ha.smul hP).intervalIntegrable (μ := volume) 0 r)

theorem speedCurve_projected_closing (π : E →L[ℝ] F) {a : ℝ → ℝ} {P : ℝ → E} {L : ℝ}
    (ha : Continuous a) (hP : Continuous P) (hclose : (∫ r in 0..L, a r • P r) = 0) :
    (∫ r in 0..L, a r • (π ∘ P) r) = 0 := by
  have he := speedCurve_linear_projection π ha hP L
  simpa only [speedCurve, rawPrimitive, hclose, map_zero] using he

theorem exists_speedCurve_L1_regular_projection_threshold (L : ℝ) [Fact (0 < L)]
    (π : E →L[ℝ] F) (P : ℝ → E) (hP : ContDiff ℝ ∞ P)
    (hPL : Function.Periodic P L) (hne : ∀ r, π (P r) ≠ 0)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hbL : Function.Periodic b L)
    (hbpos : ∀ r, 0 < b r) (hbclose : (∫ r in 0..L, b r • P r) = 0)
    (hbinj : Set.InjOn (π ∘ speedCurve b P) (Ico 0 L)) :
    ∃ η > 0, ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a L →
      (∀ r, 0 < a r) → (∫ r in 0..L, a r • P r) = 0 →
      (∫ r in 0..L, |a r - b r|) < η →
      ∀ C : AddCircle L → E, (∀ r, C (periodProjection L r) = speedCurve a P r) →
        Topology.IsEmbedding (π ∘ C) ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (π ∘ C) q)) := by
  have hproj : ContDiff ℝ ∞ (π ∘ P) := π.contDiff.comp hP
  have hperiod : Function.Periodic (π ∘ P) L := by
    intro r
    change π (P (r + L)) = π (P r)
    rw [hPL r]
  have hib : Set.InjOn (speedCurve b (π ∘ P)) (Ico 0 L) := by
    have he : speedCurve b (π ∘ P) = π ∘ speedCurve b P :=
      funext (speedCurve_linear_projection π hb.continuous hP.continuous)
    rw [he]
    exact hbinj
  obtain ⟨η, hη, hthreshold⟩ := exists_speedCurve_L1_smooth_embedding_threshold
    L (π ∘ P) hproj hperiod hne b hb hbL hbpos
    (speedCurve_projected_closing π hb.continuous hP.continuous hbclose) hib
  refine ⟨η, hη, fun a ha haL hapos haclose hsmall C hC => ?_⟩
  obtain ⟨D, _, hemb, himm, hD, _⟩ := hthreshold a ha haL hapos
    (speedCurve_projected_closing π ha.continuous hP.continuous haclose) hsmall
  have he : π ∘ C = D := by
    funext q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    change π (C (periodProjection L r)) = D (periodProjection L r)
    rw [hC, hD, speedCurve_linear_projection π ha.continuous hP.continuous]
  rw [he]
  exact ⟨hemb, himm⟩

end
end TightVer401
