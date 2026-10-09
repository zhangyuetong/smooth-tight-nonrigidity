import TightVer401.QuadraticDominationCalculus
import TightVer401.MomentSlowdownBounds
import TightVer401.CurveL1StabilityBounds
import TightVer401.RuledPrimitives

/-! Uniform bounds are derived from actual smooth periodic data. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def dualQuadraticRadialError (R : ℝ) (chi h b : ℝ → ℝ) (r t : ℝ) : ℝ :=
  deriv (deriv chi) r * (h t + (r - R) * b t) + 2 * deriv chi r * b t

def dualQuadraticAngularError (R : ℝ) (chi h b : ℝ → ℝ) (r t : ℝ) : ℝ :=
  chi r * (deriv (deriv h) t + (r - R) * deriv (deriv b) t) +
    r * (deriv chi r * (h t + (r - R) * b t) + chi r * b t)

theorem quadraticDomination_affine_bound {R B r x y : ℝ}
    (hR : 0 ≤ R) (_hB : 0 ≤ B) (hr : r ∈ Icc 0 R) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |x + (r - R) * y| ≤ B + R * B := by
  have hdist : |r - R| ≤ R := by rw [abs_of_nonpos (by linarith [hr.2])]; linarith [hr.1]
  calc
    _ ≤ |x| + |r - R| * |y| := by simpa [abs_mul] using abs_add_le x ((r - R) * y)
    _ ≤ B + R * B := add_le_add hx (mul_le_mul hdist hy (abs_nonneg _) hR)

theorem quadraticDomination_uniform_estimates {R : ℝ} (hR : 0 < R)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) :
    ∃ A D C : ℝ, 0 < A ∧ 0 < D ∧ 0 < C ∧
      (∀ r ∈ Icc 0 R, ∀ t, |dualQuadraticRadialError R chi h b r t| ≤ A) ∧
      (∀ r ∈ Icc 0 R, ∀ t, |dualQuadraticAngularError R chi h b r t| ≤ D) ∧
      (∀ t, |b t + deriv (deriv b) t| ≤ C) := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hh2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hh).2).2
  have hb2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hb).2).2
  obtain ⟨B, hB, hbound⟩ := momentSlowdown_control_bound (2 * Real.pi)
    (ψ := ![h, b, deriv (deriv h), deriv (deriv b)])
    (by intro j; fin_cases j <;> simpa using (show ContDiff ℝ ∞ _ from by assumption))
    (by intro j; fin_cases j
        · exact hhper
        · exact hbper
        · exact deriv_periodic (deriv_periodic hhper)
        · exact deriv_periodic (deriv_periodic hbper))
  have hbh (t) : |h t| ≤ B := hbound 0 t
  have hbb (t) : |b t| ≤ B := hbound 1 t
  have hbh2 (t) : |deriv (deriv h) t| ≤ B := hbound 2 t
  have hbb2 (t) : |deriv (deriv b) t| ≤ B := hbound 3 t
  have hc1 := (contDiff_infty_iff_deriv.mp hchi).2
  have hc2 := (contDiff_infty_iff_deriv.mp hc1).2
  obtain ⟨K, hK, hk⟩ := exists_speedCurve_uniform_bound
    (fun r => (![chi r, deriv chi r, deriv (deriv chi) r] : Fin 3 → ℝ))
    (by apply continuous_pi; intro j; fin_cases j
        · exact hchi.continuous
        · exact hc1.continuous
        · exact hc2.continuous) R
  have hkc (r) (hr : r ∈ Icc 0 R) : |chi r| ≤ K :=
    (show |chi r| ≤ ‖![chi r, deriv chi r, deriv (deriv chi) r]‖ from
      by simpa [Real.norm_eq_abs] using norm_le_pi_norm (![chi r, deriv chi r, deriv (deriv chi) r] : Fin 3 → ℝ) 0).trans (hk r hr)
  have hkc1 (r) (hr : r ∈ Icc 0 R) : |deriv chi r| ≤ K :=
    (show |deriv chi r| ≤ ‖![chi r, deriv chi r, deriv (deriv chi) r]‖ from
      by simpa [Real.norm_eq_abs] using norm_le_pi_norm (![chi r, deriv chi r, deriv (deriv chi) r] : Fin 3 → ℝ) 1).trans (hk r hr)
  have hkc2 (r) (hr : r ∈ Icc 0 R) : |deriv (deriv chi) r| ≤ K :=
    (show |deriv (deriv chi) r| ≤ ‖![chi r, deriv chi r, deriv (deriv chi) r]‖ from
      by simpa [Real.norm_eq_abs] using norm_le_pi_norm (![chi r, deriv chi r, deriv (deriv chi) r] : Fin 3 → ℝ) 2).trans (hk r hr)
  let H := B + R * B
  have hH : 0 < H := by dsimp [H]; positivity
  have hf (r) (hr : r ∈ Icc 0 R) (t) : |h t + (r - R) * b t| ≤ H :=
    quadraticDomination_affine_bound hR.le hB.le hr (hbh t) (hbb t)
  have hf2 (r) (hr : r ∈ Icc 0 R) (t) :
      |deriv (deriv h) t + (r - R) * deriv (deriv b) t| ≤ H :=
    quadraticDomination_affine_bound hR.le hB.le hr (hbh2 t) (hbb2 t)
  refine ⟨K * H + 2 * K * B, K * H + R * (K * H + K * B), 2 * B,
    by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · intro r hr t
    calc
      _ ≤ |deriv (deriv chi) r| * |h t + (r - R) * b t| +
          2 * |deriv chi r| * |b t| := by
        dsimp [dualQuadraticRadialError]
        simpa [abs_mul] using abs_add_le (deriv (deriv chi) r * (h t + (r - R) * b t)) (2 * deriv chi r * b t)
      _ ≤ K * H + 2 * K * B := add_le_add
        (mul_le_mul (hkc2 r hr) (hf r hr t) (abs_nonneg _) hK.le)
        (mul_le_mul (mul_le_mul_of_nonneg_left (hkc1 r hr) (by norm_num)) (hbb t) (abs_nonneg _) (by positivity))
  · intro r hr t
    have hinner : |deriv chi r * (h t + (r - R) * b t) + chi r * b t| ≤ K * H + K * B := by
      calc
        _ ≤ |deriv chi r| * |h t + (r - R) * b t| + |chi r| * |b t| := by
          simpa [abs_mul] using abs_add_le (deriv chi r * (h t + (r - R) * b t)) (chi r * b t)
        _ ≤ K * H + K * B := add_le_add
          (mul_le_mul (hkc1 r hr) (hf r hr t) (abs_nonneg _) hK.le)
          (mul_le_mul (hkc r hr) (hbb t) (abs_nonneg _) hK.le)
    calc
      _ ≤ |chi r| * |deriv (deriv h) t + (r - R) * deriv (deriv b) t| +
          |r| * |deriv chi r * (h t + (r - R) * b t) + chi r * b t| := by
        dsimp [dualQuadraticAngularError]
        simpa [abs_mul] using abs_add_le (chi r * (deriv (deriv h) t + (r - R) * deriv (deriv b) t)) (r * (deriv chi r * (h t + (r - R) * b t) + chi r * b t))
      _ ≤ K * H + R * (K * H + K * B) := add_le_add
        (mul_le_mul (hkc r hr) (hf2 r hr t) (abs_nonneg _) hK.le)
        (mul_le_mul (by simpa [abs_of_nonneg hr.1] using hr.2) hinner (abs_nonneg _) hR.le)
  · intro t
    exact (abs_add_le _ _).trans (by linarith [hbb t, hbb2 t])

end
end TightVer401
