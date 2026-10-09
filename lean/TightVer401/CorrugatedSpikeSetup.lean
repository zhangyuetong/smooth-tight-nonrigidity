import TightVer401.CovariantOneSlowdown
import TightVer401.CorrugatedSeedFrameEmbedding
import TightVer401.CorrugatedSeedFrameVisibility
import TightVer401.CorrugatedSeedFrameSetup
import TightVer401.NormalLoopRelativeFrame

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

theorem corrugatedAmbientCoordinates_injective :
    Function.Injective (fun u : Ambient =>
      (corrugatedAmbientHorizontalCLM u, (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2) u)) := by
  intro u v he
  have hh : corrugatedAmbientHorizontal u = corrugatedAmbientHorizontal v := by
    simpa only [corrugatedAmbientHorizontalCLM_apply] using congrArg Prod.fst he
  have hv : u 2 = v 2 := congrArg Prod.snd he
  ext i
  fin_cases i
  · exact congrArg Complex.re hh
  · exact congrArg Complex.im hh
  · exact hv

/-- Actual seed data discharge every hypothesis of the scalar cell correction
and of the L1 embedding and visibility estimates. -/
theorem corrugatedSeed_spike_speed {N : ℕ} (hN : 10000 ≤ N)
    [Fact (0 < corrugatedSeedArcCell (N : ℝ))]
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hψ : ContDiff ℝ ∞ e.symm)
    (hi : ∀ r, HasDerivAt e.symm (corrugatedSeedSphericalSpeed (N : ℝ) (e.symm r))⁻¹ r)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
    let Ph := corrugatedSeedFrameHorizontal (N : ℝ) e.symm
    let b := corrugatedSeedInitialSpeed (N : ℝ) e.symm
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a ell ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..ell, ‖a r - b r‖) < η ∧
      (∫ r in 0..ell, a r * normalLoopTangent ζ r 2) = 0 ∧
      (∫ r in 0..L, a r • normalLoopTangent ζ r) = 0 ∧
      (∫ r in 0..ell, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 ∧
      (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 ∧
      Set.InjOn (speedCurve a (normalLoopTangent ζ)) (Ico 0 L) ∧
      Set.InjOn (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a Ph) (Ico 0 L) ∧
      (∀ r, (1 / 4 : ℝ) < ‖covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a Ph r‖ ∧
        0 < inner ℝ (Ph r) (corrugatedVisibilityDirection (1 / 4)
          (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a Ph r))) ∧
      ∃ A B : AddCircle ell → ℝ,
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ B ∧
        (∀ r, A (periodProjection ell r) = a r) ∧
        (∀ r, B (periodProjection ell r) = b r) ∧
        ∃ n : ℕ, n ≤ 2 ∧ ∃ centers radii : Fin n → ℝ,
          (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
          Function.support (fun q => A q - B q) ⊆
            ⋃ j, periodProjection ell '' Icc (centers j - radii j) (centers j + radii j) := by
  dsimp only
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNlarge : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNz : N ≠ 0 := by omega
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
  let P := normalLoopTangent ζ
  let Ph := corrugatedSeedFrameHorizontal (N : ℝ) e.symm
  let b := corrugatedSeedInitialSpeed (N : ℝ) e.symm
  let σ : Ambient →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2
  have hell : 0 < ell := corrugatedSeedArcCell_pos hNr
  letI : Fact (0 < ell) := ⟨hell⟩
  have hL : 0 < L := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNz)) hell
  letI : Fact (0 < L) := ⟨hL⟩
  have hc := corrugatedSeedArcInverse_cell hNr e he
  have hζ : ContDiff ℝ ∞ ζ := (corrugatedSeedSphere_contDiff (N : ℝ)).comp hψ
  have hPk := normalLoop_actual_smooth hζ
  have hPhEq : corrugatedAmbientHorizontalCLM ∘ P = Ph := by
    funext r
    exact corrugatedAmbientHorizontalCLM_apply (P r)
  have hPcell : ∀ r, corrugatedAmbientHorizontalCLM (P (r + ell)) =
      corrugatedSeedRotation (N : ℝ) * corrugatedAmbientHorizontalCLM (P r) := by
    intro r
    simpa only [corrugatedAmbientHorizontalCLM_apply, P, ζ, ell, corrugatedSeedFrameHorizontal] using
      corrugatedSeedFrameHorizontal_cell hNr hψ hi hc r
  have hσT : Function.Periodic (σ ∘ P) ell :=
    corrugatedSeedFrame_vertical_periodic hNr hψ hi hc
  have hπne : ∀ r, corrugatedAmbientHorizontalCLM (P r) ≠ 0 := by
    intro r
    simpa only [corrugatedAmbientHorizontalCLM_apply, P, ζ, corrugatedSeedFrameHorizontal] using
      corrugatedSeedFrameHorizontal_ne_zero hNr hψ hi r
  have hb := corrugatedSeedInitialSpeed_contDiff (N : ℝ) hψ
  have hbT := corrugatedSeedInitialSpeed_periodic (ne_of_gt (by linarith : (0 : ℝ) < N)) hc
  have hκT := corrugatedSeedFrame_curvature_periodic hNr hψ hi hc
  have hz : e 0 = 0 := by rw [he]; simp [corrugatedSeedArcMap, rawPrimitive]
  have hsz : e.symm 0 = 0 := (congrArg e.symm hz.symm).trans (e.symm_apply_apply 0)
  have hσnonzero : ∃ r, σ (P r) ≠ 0 := by
    refine ⟨0, ne_of_lt (corrugatedSeedFrame_vertical_nonzero hNr
      (hψ.differentiable (by simp)) hsz ?_)⟩
    rw [(hi 0).deriv]
    exact inv_pos.mpr (corrugatedSeedSphericalSpeed_pos hNr _)
  have hκnonconstant : ∃ r, normalLoopCurvature ζ r ≠ normalLoopCurvature ζ 0 := by
    by_contra hn
    push Not at hn
    exact corrugatedSeedFrame_curvature_nonconstant hNr hψ hi e.symm.surjective
      ⟨normalLoopCurvature ζ 0, hn⟩
  have hPhL : Function.Periodic Ph L := by
    intro r
    simpa only [corrugatedSeedRotation_pow hNz, one_mul] using
      corrugated_covariant_iterate (corrugatedSeedFrameHorizontal_cell hNr hψ hi hc) N r
  have hbinj : Set.InjOn (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) b
      (corrugatedAmbientHorizontalCLM ∘ P)) (Ico 0 L) := by
    rw [hPhEq]
    exact corrugatedSeed_covariant_baseline_injOn hN e he hψ
  have hvis : ∀ r, (1 / 4 : ℝ) < ‖covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) b
      (corrugatedAmbientHorizontalCLM ∘ P) r‖ ∧
      0 < inner ℝ (Ph r) (corrugatedVisibilityDirection (1 / 4)
        (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) b (corrugatedAmbientHorizontalCLM ∘ P) r)) ∧
      0 < inner ℝ (Ph r) (corrugatedVisibilityDirection (1 / 4)
        (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) b (corrugatedAmbientHorizontalCLM ∘ P) r)) := by
    intro r
    rw [hPhEq]
    have hv := corrugatedSeed_covariant_baseline_visibility hNlarge hψ hi hc r
    exact ⟨hv.1, hv.2, hv.2⟩
  obtain ⟨a, ha, haT, hapos, hsmall, hMcell, hMfull, hBcell, hBfull, hvisa,
    ⟨Cs, _, hiCs, _, hrepCs⟩, ⟨Ch, _, hiCh, _, hrepCh⟩,
    A, hA, hArep, n, hn, centers, radii, hrad, hlen, hsupp⟩ :=
    covariant_one_slowdown_embedded_visible L ell N hNz rfl
      (corrugatedSeedRotation (N : ℝ)) (corrugatedSeedRotation_ne_one hNr)
      (corrugatedSeedRotation_pow hNz) corrugatedAmbientHorizontalCLM σ
      corrugatedAmbientCoordinates_injective P hPk.1 hPcell hσT hπne
      (normalLoopCurvature ζ) b hPk.2 hb hκT hbT
      (corrugatedSeedInitialSpeed_pos (N : ℝ) e.symm) hσnonzero hκnonconstant
      (corrugatedSeed_initial_scalar_moment hNr hψ hc) hbinj (1 / 4) (by norm_num)
      Ph Ph (corrugatedSeedFrameHorizontal_contDiff (N : ℝ) hψ)
      (corrugatedSeedFrameHorizontal_contDiff (N : ℝ) hψ) hPhL hPhL hvis hη hε
  have hiRaw := periodicPullback_representative_injective hiCs.injective hrepCs
  have hiCov := periodicPullback_representative_injective hiCh.injective hrepCh
  rw [hPhEq] at hiCov hvisa
  exact ⟨a, ha, haT, hapos, hsmall, hMcell, hMfull, hBcell, hBfull, hiRaw, hiCov,
    (fun r => ⟨(hvisa r).1, (hvisa r).2.1⟩),
    A, hbT.lift, hA, periodicLift_contMDiff hb hbT, hArep, hbT.lift_coe,
    n, hn, centers, radii, hrad, hlen, hsupp⟩

end
end TightVer401
