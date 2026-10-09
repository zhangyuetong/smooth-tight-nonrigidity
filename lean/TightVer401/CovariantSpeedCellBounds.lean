import TightVer401.CovariantSpeedPrimitive

namespace TightVer401
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem periodic_cellIntegral_nat_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {T : ℝ}
    (hf : Continuous f) (hp : Function.Periodic f T) (N : ℕ) :
    (∫ r in 0..(N : ℝ) * T, f r) = (N : ℤ) • ∫ r in 0..T, f r := by
  simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast] using
    hp.intervalIntegral_add_zsmul_eq (N : ℤ) 0 (fun a b => hf.intervalIntegrable a b)

theorem periodic_speed_L1_nat_mul {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (haT : Function.Periodic a T) (hbT : Function.Periodic b T) (N : ℕ) :
    (∫ r in 0..(N : ℝ) * T, |a r - b r|) = (N : ℝ) * ∫ r in 0..T, |a r - b r| := by
  have hp : Function.Periodic (fun r => |a r - b r|) T := by
    intro r
    change |a (r + T) - b (r + T)| = |a r - b r|
    rw [haT r, hbT r]
  simpa only [zsmul_eq_mul, Int.cast_natCast, Pi.sub_apply] using
    periodic_cellIntegral_nat_mul (ha.sub hb).abs hp N

theorem exists_covariantSpeedCurve_cell_L1_uniform_threshold {T : ℝ} {ξ : ℂ}
    {b : ℝ → ℝ} {P : ℝ → ℂ} (hb : Continuous b) (hP : Continuous P)
    (hbT : Function.Periodic b T) (hT : 0 < T) (N : ℕ) (hN : N ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ a : ℝ → ℝ, Continuous a → Function.Periodic a T →
      (∫ r in 0..T, |a r - b r|) < η →
      ∀ t ∈ Icc 0 ((N : ℝ) * T),
        ‖covariantSpeedCurve T ξ a P t - covariantSpeedCurve T ξ b P t‖ < ε := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hcell : T ∈ Icc 0 ((N : ℝ) * T) := ⟨hT.le, by nlinarith⟩
  obtain ⟨θ, hθ, hthreshold⟩ := exists_covariantSpeedCurve_L1_uniform_threshold hb hP hcell hε
  refine ⟨θ / N, div_pos hθ hNr, fun a ha haT hsmall => ?_⟩
  apply hthreshold a ha
  rw [periodic_speed_L1_nat_mul ha hb haT hbT N]
  have he := (lt_div_iff₀ hNr).mp hsmall
  simpa only [mul_comm] using he

end
end TightVer401
