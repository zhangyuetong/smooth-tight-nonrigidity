import TightVer401.CovariantSpeedPrimitive
import TightVer401.NormalLoopEmbeddingPeriod

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem covariantSpeedCurve_raw_periodic {T L : ℝ} {ξ : ℂ} {a : ℝ → ℝ} {P : ℝ → ℂ}
    (hp : Function.Periodic (covariantSpeedCurve T ξ a P) L) :
    Function.Periodic (speedCurve a P) L := by
  intro t
  have he := hp t
  simpa only [covariantSpeedCurve, add_left_cancel_iff] using he

theorem covariantSpeedCurve_injOn_iff {T : ℝ} {ξ : ℂ} {a : ℝ → ℝ} {P : ℝ → ℂ}
    (S : Set ℝ) :
    Set.InjOn (covariantSpeedCurve T ξ a P) S ↔ Set.InjOn (speedCurve a P) S := by
  constructor
  · intro hi x hx y hy he
    apply hi hx hy
    exact congrArg (fun z => speedCurve a P T / (ξ - 1) + z) he
  · intro hi x hx y hy he
    exact hi hx hy (add_left_cancel he)

/-- Actual rotational cell covariance supplies full-period closure, while
the positive-speed L1 theorem preserves the horizontal embedding. -/
theorem exists_covariantSpeedCurve_L1_smooth_embedding_threshold
    (L : ℝ) [hL : Fact (0 < L)] {T : ℝ} {ξ : ℂ} (N : ℕ)
    (hNT : (N : ℝ) * T = L) (hξ : ξ ≠ 1) (hN : ξ ^ N = 1)
    (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hPcell : ∀ t, P (t + T) = ξ * P t) (hne : ∀ t, P t ≠ 0)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hbT : Function.Periodic b T)
    (hbinj : Set.InjOn (covariantSpeedCurve T ξ b P) (Ico 0 L)) :
    ∃ η > 0, ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → Function.Periodic a T →
      (∀ t, 0 < a t) → (∫ t in 0..L, |a t - b t|) < η →
      Function.Periodic (covariantSpeedCurve T ξ a P) L ∧
      Set.InjOn (covariantSpeedCurve T ξ a P) (Ico 0 L) ∧
      ∃ C : AddCircle L → ℂ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ C ∧
        Topology.IsEmbedding C ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) C q)) ∧
        (∀ t, C (periodProjection L t) = covariantSpeedCurve T ξ a P t) := by
  have hbcov : Function.Periodic (covariantSpeedCurve T ξ b P) L := by
    rw [← hNT]
    exact covariantSpeedCurve_periodic hb.continuous hP.continuous hbT hPcell hξ N hN
  have hbraw := covariantSpeedCurve_raw_periodic hbcov
  have hib := (covariantSpeedCurve_injOn_iff (Ico 0 L)).mp hbinj
  obtain ⟨η, hη, hthreshold⟩ := exists_speedCurve_L1_representative_threshold
    hL.out P hP.continuous hne b hb.continuous hbraw hib
  refine ⟨η, hη, fun a ha haT hapos hsmall => ?_⟩
  have hp : Function.Periodic (covariantSpeedCurve T ξ a P) L := by
    rw [← hNT]
    exact covariantSpeedCurve_periodic ha.continuous hP.continuous haT hPcell hξ N hN
  have hiraw := hthreshold a ha.continuous hapos (covariantSpeedCurve_raw_periodic hp) hsmall
  have hi := (covariantSpeedCurve_injOn_iff (T := T) (ξ := ξ) (Ico 0 L)).mpr hiraw
  have hf := covariantSpeedCurve_contDiff T ξ ha hP
  obtain ⟨hC, hemb⟩ := periodicCurve_lift_embedding hf hp hi
  have hderiv (t : ℝ) : deriv (covariantSpeedCurve T ξ a P) t ≠ 0 := by
    rw [(covariantSpeedCurve_hasDerivAt T ξ ha.continuous hP.continuous t).deriv]
    exact smul_ne_zero (hapos t).ne' (hne t)
  exact ⟨hp, hi, hp.lift, hC, hemb,
    periodicCurve_lift_mfderiv_injective hf hp hderiv, hp.lift_coe⟩

end
end TightVer401
