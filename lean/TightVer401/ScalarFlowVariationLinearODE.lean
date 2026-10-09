import TightVer401.RuledPrimitives

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem scalarLinearODE_endpoint {b j : ℝ → ℝ} {P : ℝ} (hP : 0 ≤ P)
    (hb : ContinuousOn b (Icc (0 : ℝ) P))
    (hj : ∀ r ∈ Icc (0 : ℝ) P, HasDerivAt j (b r * j r) r) (hj0 : j 0 = 1) :
    j P = Real.exp (∫ r in 0..P, b r) := by
  let clamp : ℝ → ℝ := fun r => max 0 (min P r)
  have hc : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hm (r : ℝ) : clamp r ∈ Icc (0 : ℝ) P :=
    ⟨le_max_left _ _, max_le hP (min_le_left _ _)⟩
  have he (r : ℝ) (hr : r ∈ Icc (0 : ℝ) P) : clamp r = r := by
    simp only [clamp, min_eq_right hr.2, max_eq_right hr.1]
  let B := b ∘ clamp
  have hB : Continuous B := continuousOn_univ.mp
    (hb.comp hc.continuousOn (fun r _ => hm r))
  have hBe (r : ℝ) (hr : r ∈ Icc (0 : ℝ) P) : B r = b r := by
    simp only [B, Function.comp_apply, he r hr]
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) P) :
      HasDerivAt (fun s => j s * Real.exp (-rawPrimitive B s)) 0 r := by
    convert! (hj r hr).mul ((rawPrimitive_hasDerivAt hB r).neg.exp) using 1
    rw [hBe r hr]
    ring
  have hconst := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := P) (f' := fun _ => (0 : ℝ))
    (fun r hr => hd r (by simpa only [uIcc_of_le hP] using hr)) intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, rawPrimitive, intervalIntegral.integral_same,
    neg_zero, Real.exp_zero, hj0, mul_one] at hconst
  have hprod : j P * Real.exp (-(∫ r in 0..P, B r)) = 1 := by linarith
  have hendpoint : j P = Real.exp (∫ r in 0..P, B r) := by
    calc
      j P = (j P * Real.exp (-(∫ r in 0..P, B r))) * Real.exp (∫ r in 0..P, B r) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ = Real.exp (∫ r in 0..P, B r) := by rw [hprod, one_mul]
  have hi : (∫ r in 0..P, B r) = ∫ r in 0..P, b r :=
    intervalIntegral.integral_congr (fun r hr => hBe r (by simpa only [uIcc_of_le hP] using hr))
  rwa [hi] at hendpoint

end
end TightVer401
