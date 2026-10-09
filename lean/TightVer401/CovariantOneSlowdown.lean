import TightVer401.CovariantSpeedClosure
import TightVer401.CovariantSpeedVisibility
import TightVer401.OneSlowdown

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A scalar cell slowdown retains the actual covariant horizontal embedding
and visibility, and supplies complete spatial closure by coordinate algebra. -/
theorem covariant_one_slowdown_embedded_visible
    (L T : ℝ) [hL : Fact (0 < L)] [hT : Fact (0 < T)] (N : ℕ) (hNz : N ≠ 0)
    (hNT : (N : ℝ) * T = L) (ξ : ℂ) (hξ : ξ ≠ 1) (hN : ξ ^ N = 1)
    (π : E →L[ℝ] ℂ) (σ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun v : E => (π v, σ v)))
    (P : ℝ → E) (hP : ContDiff ℝ ∞ P)
    (hPcell : ∀ r, π (P (r + T)) = ξ * π (P r))
    (hσT : Function.Periodic (σ ∘ P) T) (hπne : ∀ r, π (P r) ≠ 0)
    (κ b : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hb : ContDiff ℝ ∞ b)
    (hκT : Function.Periodic κ T) (hbT : Function.Periodic b T) (hbpos : ∀ r, 0 < b r)
    (hσnonzero : ∃ r, σ (P r) ≠ 0) (hκnonconstant : ∃ r, κ r ≠ κ 0)
    (hscalar : (∫ r in 0..T, b r * σ (P r)) = 0)
    (hbinj : Set.InjOn (covariantSpeedCurve T ξ b (π ∘ P)) (Ico 0 L))
    (R : ℝ) (hR : 0 ≤ R) (U V : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hUL : Function.Periodic U L) (hVL : Function.Periodic V L)
    (hvisible : ∀ r, R < ‖covariantSpeedCurve T ξ b (π ∘ P) r‖ ∧
      0 < inner ℝ (U r) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ b (π ∘ P) r)) ∧
      0 < inner ℝ (V r) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ b (π ∘ P) r)))
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a T ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..T, ‖a r - b r‖) < η ∧
      (∫ r in 0..T, a r * σ (P r)) = 0 ∧ (∫ r in 0..L, a r • P r) = 0 ∧
      (∫ r in 0..T, deriv κ r / Real.sqrt (a r)) = 0 ∧
      (∫ r in 0..L, deriv κ r / Real.sqrt (a r)) = 0 ∧
      (∀ r, R < ‖covariantSpeedCurve T ξ a (π ∘ P) r‖ ∧
        0 < inner ℝ (U r) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ a (π ∘ P) r)) ∧
        0 < inner ℝ (V r) (corrugatedVisibilityDirection R (covariantSpeedCurve T ξ a (π ∘ P) r))) ∧
      (∃ Cs : AddCircle L → E, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ Cs ∧
        Topology.IsEmbedding Cs ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) Cs q)) ∧
        ∀ r, Cs (periodProjection L r) = speedCurve a P r) ∧
      (∃ Ch : AddCircle L → ℂ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ Ch ∧
        Topology.IsEmbedding Ch ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) Ch q)) ∧
        ∀ r, Ch (periodProjection L r) = covariantSpeedCurve T ξ a (π ∘ P) r) ∧
      ∃ A : AddCircle T → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧
        (∀ r, A (periodProjection T r) = a r) ∧
        ∃ n : ℕ, n ≤ 2 ∧ ∃ centers radii : Fin n → ℝ,
          (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
          Function.support (fun q => A q - hbT.lift q) ⊆
            ⋃ j, periodProjection T '' Icc (centers j - radii j) (centers j + radii j) := by
  have hPh : ContDiff ℝ ∞ (π ∘ P) := π.contDiff.comp hP
  have hσP : ContDiff ℝ ∞ (σ ∘ P) := σ.contDiff.comp hP
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNz)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNz
  have hcell : T ∈ Icc 0 L := ⟨hT.out.le, by rw [← hNT]; nlinarith [hT.out]⟩
  obtain ⟨θ, hθ, hembed⟩ := exists_covariantSpeedCurve_L1_smooth_embedding_threshold
    L N hNT hξ hN (π ∘ P) hPh hPcell hπne b hb hbT hbinj
  obtain ⟨θv, hθv, hvis⟩ := exists_covariantSpeedCurve_L1_visibility_threshold
    L N hNT hcell hξ hN hR (π ∘ P) hPh hPcell b hb hbT U V hU hV hUL hVL hvisible
  let ηcell := min η (min θ θv / N)
  have hηcell : 0 < ηcell := lt_min hη (div_pos (lt_min hθ hθv) hNr)
  obtain ⟨a, ha, haT, hapos, hsmall, hMcell, hBcell, hAdata⟩ := one_slowdown_holonomy_correction
    hσP hκ hb hσT hκT hbT hbpos hσnonzero hκnonconstant hscalar hηcell hε
  have hfullsmall : (∫ r in 0..L, |a r - b r|) < min θ θv := by
    rw [← hNT, periodic_speed_L1_nat_mul ha.continuous hb.continuous haT hbT N]
    have hc : (∫ r in 0..T, |a r - b r|) < min θ θv / N := by
      simpa only [Real.norm_eq_abs] using hsmall.trans_le (min_le_right η (min θ θv / N))
    simpa only [mul_comm] using (lt_div_iff₀ hNr).mp hc
  obtain ⟨_, hiCov, Ch, hCh, hembCh, himmCh, hrepCh⟩ := hembed a ha haT hapos
    (hfullsmall.trans_le (min_le_left θ θv))
  have hvisiblea := hvis a ha haT (hfullsmall.trans_le (min_le_right θ θv))
  have hMfull : (∫ r in 0..L, a r • P r) = 0 := by
    rw [← hNT]
    exact covariantSpeed_full_moment_zero π σ hjoint ha.continuous hP.continuous haT hPcell hσT hξ N hN hMcell
  have hPL : Function.Periodic P L := by
    rw [← hNT]
    exact covariantSpeed_full_tangent_periodic π σ hjoint hPcell hσT N hN
  have haL : Function.Periodic a L := by rw [← hNT]; exact haT.nat_mul N
  have hrawπ := (covariantSpeedCurve_injOn_iff (T := T) (ξ := ξ) (Ico 0 L)).mp hiCov
  have hiraw : Set.InjOn (speedCurve a P) (Ico 0 L) := by
    intro x hx y hy he
    apply hrawπ hx hy
    rw [speedCurve_linear_projection π ha.continuous hP.continuous,
      speedCurve_linear_projection π ha.continuous hP.continuous, he]
  have hp := speedCurve_periodic ha.continuous hP.continuous haL hPL hMfull
  have hsmooth : ContDiff ℝ ∞ (speedCurve a P) := rawPrimitive_contDiff (ha.smul hP)
  obtain ⟨hCs, hembCs⟩ := periodicCurve_lift_embedding hsmooth hp hiraw
  have hPne (r) : P r ≠ 0 := by intro hz; exact hπne r (by rw [hz, map_zero])
  have hderiv (r) : deriv (speedCurve a P) r ≠ 0 := by
    have hv : HasDerivAt (speedCurve a P) (a r • P r) r :=
      rawPrimitive_hasDerivAt (ha.continuous.smul hP.continuous) r
    rw [hv.deriv]
    exact smul_ne_zero (hapos r).ne' (hPne r)
  have hBfull : (∫ r in 0..L, deriv κ r / Real.sqrt (a r)) = 0 := by
    have hd := (contDiff_infty_iff_deriv.mp hκ).2
    have hg : Continuous (fun r => deriv κ r / Real.sqrt (a r)) :=
      (hd.div (ha.sqrt (fun r => (hapos r).ne'))
        (fun r => (Real.sqrt_pos.mpr (hapos r)).ne')).continuous
    have hgp : Function.Periodic (fun r => deriv κ r / Real.sqrt (a r)) T := by
      intro r
      change deriv κ (r + T) / Real.sqrt (a (r + T)) = deriv κ r / Real.sqrt (a r)
      rw [deriv_periodic hκT r, haT r]
    rw [← hNT, periodic_cellIntegral_nat_mul hg hgp N, hBcell, smul_zero]
  exact ⟨a, ha, haT, hapos, hsmall.trans_le (min_le_left η (min θ θv / N)), hMcell,
    hMfull, hBcell, hBfull, hvisiblea,
    ⟨hp.lift, hCs, hembCs, periodicCurve_lift_mfderiv_injective hsmooth hp hderiv, hp.lift_coe⟩,
    ⟨Ch, hCh, hembCh, himmCh, hrepCh⟩, hAdata⟩

end
end TightVer401
