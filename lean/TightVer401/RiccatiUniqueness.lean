import TightVer401.RiccatiFlow

/-! Uniqueness uses an integrating factor constructed by OpenAI's actual
primitive. Compact-interval coefficients are extended continuously by clamping
the time parameter; no global solution or global Lipschitz bound is assumed. -/
namespace TightVer401
noncomputable section
open Set OAI.ClosedSurfaceR4.PeriodicPrimitive

theorem riccati_solutions_unique {q₁ q₂ u v : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (h₁ : ContinuousOn q₁ (Icc 0 L)) (h₂ : ContinuousOn q₂ (Icc 0 L))
    (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hud : ∀ t ∈ Icc 0 L, HasDerivAt u (q₁ t * u t + q₂ t * (u t)^2) t)
    (hvd : ∀ t ∈ Icc 0 L, HasDerivAt v (q₁ t * v t + q₂ t * (v t)^2) t)
    (hinitial : u 0 = v 0) : EqOn u v (Icc 0 L) := by
  let clamp : ℝ → ℝ := fun s => max 0 (min L s)
  have hclamp : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ s, clamp s ∈ Icc 0 L := by
    intro s
    exact ⟨le_max_left _ _, max_le hL (min_le_left _ _)⟩
  have hclamp_id : ∀ s ∈ Icc 0 L, clamp s = s := by
    intro s hs
    dsimp only [clamp]
    rw [min_eq_right hs.2, max_eq_right hs.1]
  let a : ℝ → ℝ := fun s => q₁ (clamp s) + q₂ (clamp s) * (u (clamp s) + v (clamp s))
  have ha : Continuous a := (h₁.comp_continuous hclamp hclamp_mem).add
    ((h₂.comp_continuous hclamp hclamp_mem).mul
      ((hu.comp_continuous hclamp hclamp_mem).add (hv.comp_continuous hclamp hclamp_mem)))
  let A : ℝ → ℝ := rawPrimitive a
  let f : ℝ → ℝ := fun t => (u t - v t) * Real.exp (-A t)
  have hfd : ∀ t ∈ Icc 0 L, HasDerivAt f 0 t := by
    intro t ht
    have hd := ((hud t ht).sub (hvd t ht)).mul
      ((rawPrimitive_hasDerivAt ha t).neg.exp)
    convert! hd using 1
    dsimp only [a, Pi.sub_apply, Pi.neg_apply]
    rw [hclamp_id t ht]
    ring
  intro t ht
  have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f' := fun _ => (0 : ℝ)) (fun s hs => hfd s (by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩))
    (continuous_const.intervalIntegrable 0 t)
  have hf0 : f 0 = 0 := by simp [f, hinitial]
  simp only [intervalIntegral.integral_zero, hf0, sub_zero] at hz
  have hprod : (u t - v t) * Real.exp (-A t) = 0 := hz.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (Real.exp_ne_zero _))

end
end TightVer401
