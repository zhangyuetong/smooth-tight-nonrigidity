import TightVer401.CorrugatedSeedClosure
import TightVer401.CurveL1StabilityBounds

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The actual starting point forced by rotational cell covariance. -/
def covariantSpeedCurve (T : ℝ) (ξ : ℂ) (a : ℝ → ℝ) (P : ℝ → ℂ) (t : ℝ) : ℂ :=
  speedCurve a P T / (ξ - 1) + speedCurve a P t

theorem covariantSpeedCurve_contDiff (T : ℝ) (ξ : ℂ) {a : ℝ → ℝ} {P : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (covariantSpeedCurve T ξ a P) :=
  contDiff_const.add (rawPrimitive_contDiff (ha.smul hP))

theorem covariantSpeedCurve_hasDerivAt (T : ℝ) (ξ : ℂ) {a : ℝ → ℝ} {P : ℝ → ℂ}
    (ha : Continuous a) (hP : Continuous P) (t : ℝ) :
    HasDerivAt (covariantSpeedCurve T ξ a P) (a t • P t) t :=
  (rawPrimitive_hasDerivAt (ha.smul hP) t).const_add _

theorem covariantSpeedCurve_cell {T : ℝ} {ξ : ℂ} {a : ℝ → ℝ} {P : ℝ → ℂ}
    (ha : Continuous a) (hP : Continuous P) (haT : Function.Periodic a T)
    (hPcell : ∀ t, P (t + T) = ξ * P t) (hξ : ξ ≠ 1) (t : ℝ) :
    covariantSpeedCurve T ξ a P (t + T) = ξ * covariantSpeedCurve T ξ a P t := by
  have hvel : ∀ t, a (t + T) • P (t + T) = ξ * (a t • P t) := by
    intro s
    rw [haT s, hPcell s]
    change (a s : ℂ) * (ξ * P s) = ξ * ((a s : ℂ) * P s)
    ring
  have he := corrugated_covariant_rawPrimitive (ha.smul hP) hvel t
  change speedCurve a P (t + T) = speedCurve a P T + ξ * speedCurve a P t at he
  unfold covariantSpeedCurve
  rw [he]
  have hz := sub_ne_zero.mpr hξ
  field_simp
  ring

theorem covariantSpeedCurve_periodic {T : ℝ} {ξ : ℂ} {a : ℝ → ℝ} {P : ℝ → ℂ}
    (ha : Continuous a) (hP : Continuous P) (haT : Function.Periodic a T)
    (hPcell : ∀ t, P (t + T) = ξ * P t) (hξ : ξ ≠ 1)
    (N : ℕ) (hN : ξ ^ N = 1) :
    Function.Periodic (covariantSpeedCurve T ξ a P) ((N : ℝ) * T) := by
  intro t
  simpa only [hN, one_mul] using
    corrugated_covariant_iterate (covariantSpeedCurve_cell ha hP haT hPcell hξ) N t

/-- Both the moving covariance point and the actual primitive are controlled
by the same speed L1 error, on any containing period interval. -/
theorem covariantSpeedCurve_uniform_norm_sub_le {a b : ℝ → ℝ} {P : ℝ → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hP : Continuous P) {L T M : ℝ} {ξ : ℂ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc 0 L, ‖P x‖ ≤ M)
    (hT : T ∈ Icc 0 L) {t : ℝ} (ht : t ∈ Icc 0 L) :
    ‖covariantSpeedCurve T ξ a P t - covariantSpeedCurve T ξ b P t‖ ≤
      (‖ξ - 1‖⁻¹ + 1) * M * ∫ r in 0..L, |a r - b r| := by
  have hcell := speedCurve_uniform_norm_sub_le ha hb hP hM hbound hT
  have hraw := speedCurve_uniform_norm_sub_le ha hb hP hM hbound ht
  have he : covariantSpeedCurve T ξ a P t - covariantSpeedCurve T ξ b P t =
      (speedCurve a P T - speedCurve b P T) / (ξ - 1) +
        (speedCurve a P t - speedCurve b P t) := by
    unfold covariantSpeedCurve
    rw [sub_div]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_div, div_eq_mul_inv]
  have hcell' := mul_le_mul_of_nonneg_right hcell (inv_nonneg.mpr (norm_nonneg (ξ - 1)))
  calc
    ‖speedCurve a P T - speedCurve b P T‖ * ‖ξ - 1‖⁻¹ +
        ‖speedCurve a P t - speedCurve b P t‖ ≤
        (M * ∫ r in 0..L, |a r - b r|) * ‖ξ - 1‖⁻¹ +
          M * ∫ r in 0..L, |a r - b r| := add_le_add hcell' hraw
    _ = _ := by ring

theorem exists_covariantSpeedCurve_L1_uniform_threshold {T L : ℝ} {ξ : ℂ}
    {b : ℝ → ℝ} {P : ℝ → ℂ} (hb : Continuous b) (hP : Continuous P)
    (hT : T ∈ Icc 0 L) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ a : ℝ → ℝ, Continuous a →
      (∫ r in 0..L, |a r - b r|) < η →
      ∀ t ∈ Icc 0 L,
        ‖covariantSpeedCurve T ξ a P t - covariantSpeedCurve T ξ b P t‖ < ε := by
  obtain ⟨M, hM, hbound⟩ := exists_speedCurve_uniform_bound P hP L
  let C := (‖ξ - 1‖⁻¹ + 1) * M
  have hC : 0 < C := mul_pos (by positivity) hM
  refine ⟨ε / C, div_pos hε hC, fun a ha hsmall t ht => ?_⟩
  apply (covariantSpeedCurve_uniform_norm_sub_le ha hb hP hM.le hbound hT ht).trans_lt
  have he := (lt_div_iff₀ hC).mp hsmall
  simpa only [C, mul_comm] using he

end
end TightVer401
