import TightVer401.CorrugatedSeedPrimitive

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff

theorem corrugated_covariant_iterate {f : ℝ → ℂ} {T : ℝ} {ξ : ℂ}
    (hcov : ∀ t, f (t + T) = ξ * f t) (n : ℕ) (t : ℝ) :
    f (t + (n : ℝ) * T) = ξ ^ n * f t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, hcov, ih,
      pow_succ]
    ring

theorem corrugatedSeedRotation_pow {N : ℕ} (hN : N ≠ 0) :
    corrugatedSeedRotation (N : ℝ) ^ N = 1 := by
  unfold corrugatedSeedRotation
  rw [← Complex.exp_nat_mul]
  have he : (N : ℂ) * ((corrugatedSeedCell (N : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I := by
    simp only [corrugatedSeedCell, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast]
    field_simp
  rw [he, Complex.exp_two_pi_mul_I]

theorem corrugatedSeedBeta_periodic {N : ℕ} (hN : 2 ≤ N) :
    Function.Periodic (corrugatedSeedBeta (N : ℝ)) (2 * Real.pi) := by
  have hNz : N ≠ 0 := by omega
  have hz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNz
  have he : (N : ℝ) * corrugatedSeedCell (N : ℝ) = 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  intro t
  simpa only [he, corrugatedSeedRotation_pow hNz, one_mul] using
    corrugated_covariant_iterate (corrugatedSeedBeta_cell hz) N t

theorem corrugatedSeedDelta_periodic {N : ℕ} (hN : 2 ≤ N) (k : ℝ) :
    Function.Periodic (corrugatedSeedDelta k (N : ℝ)) (2 * Real.pi) := by
  have hNz : N ≠ 0 := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNz
  have he : (N : ℝ) * corrugatedSeedCell (N : ℝ) = 2 * Real.pi := by
    unfold corrugatedSeedCell
    field_simp
  intro t
  simpa only [he, corrugatedSeedRotation_pow hNz, one_mul] using
    corrugated_covariant_iterate (corrugatedSeedDelta_cell hNr k) N t

theorem corrugatedSeedBeta_injOn {N : ℝ} (hN : 1 < N) :
    InjOn (corrugatedSeedBeta N) (Ico 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hr : corrugatedSeedRadius N x = corrugatedSeedRadius N y := by
    simpa only [corrugatedSeedBeta_norm hN] using congrArg norm hxy
  have he : Complex.exp ((corrugatedSeedPhase N x : ℂ) * Complex.I) =
      Complex.exp ((corrugatedSeedPhase N y : ℂ) * Complex.I) := by
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt
      (corrugatedSeedRadius_pos hN x)))
    simpa only [corrugatedSeedBeta, ← hr] using hxy
  have hs : (1 / N) * Real.sin (N * x) = (1 / N) * Real.sin (N * y) := by
    dsimp [corrugatedSeedRadius] at hr
    linarith
  have hf (t : ℝ) : Complex.exp ((corrugatedSeedPhase N t : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) *
        Complex.exp (((2 * ((1 / N) * Real.sin (N * t)) : ℝ) : ℂ) * Complex.I) := by
    simp only [corrugatedSeedPhase, Complex.ofReal_add, add_mul, Complex.exp_add]
    congr 2
    ring
  rw [hf x, hf y, hs] at he
  have he' := mul_right_cancel₀ (Complex.exp_ne_zero _) he
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp) hx hy
  exact Subtype.ext he'

def corrugatedSeedRoot (N : ℝ) : ℝ := corrugatedRootValue (1 / N)

def corrugatedSeedPartner (N : ℝ) : ℝ → ℂ :=
  corrugatedSeedDelta (corrugatedSeedRoot N) N

theorem corrugatedSeedRoot_spec {N : ℝ} (hN : 1 < N) :
    corrugatedRootIntegral (1 / N) (corrugatedSeedRoot N) = 0 := by
  apply corrugatedRootValue_spec
  rw [abs_of_pos (by positivity)]
  exact (div_lt_one (by linarith)).mpr hN

theorem corrugatedSeedPartner_contDiff (N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedPartner N) := corrugatedSeedDelta_contDiff _ _

theorem corrugatedSeedPartner_periodic {N : ℕ} (hN : 2 ≤ N) :
    Function.Periodic (corrugatedSeedPartner (N : ℝ)) (2 * Real.pi) :=
  corrugatedSeedDelta_periodic hN _

theorem corrugatedSeedPartner_cell {N : ℝ} (hN : 1 < N) (t : ℝ) :
    corrugatedSeedPartner N (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * corrugatedSeedPartner N t :=
  corrugatedSeedDelta_cell hN _ t

theorem corrugatedSeedPartner_deriv {N : ℝ} (hN : 1 < N) (t : ℝ) :
    deriv (corrugatedSeedPartner N) t =
      corrugatedSeedMultiplier (corrugatedSeedRoot N) N t • deriv (corrugatedSeedBeta N) t :=
  corrugatedSeedDelta_deriv_eq (ne_of_gt (by linarith)) _ t

end
end TightVer401
