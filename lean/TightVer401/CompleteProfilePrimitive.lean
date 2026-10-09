import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false

def completeProfilePrimitive (H v : ℝ) (b : ℝ → ℝ) (z : ℝ) : ℝ :=
  v + rawPrimitive b z - rawPrimitive b H

theorem completeProfilePrimitive_contDiff (H v : ℝ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (completeProfilePrimitive H v b) :=
  (contDiff_const.add (rawPrimitive_contDiff hb)).sub contDiff_const

theorem completeProfilePrimitive_hasDerivAt (H v : ℝ) {b : ℝ → ℝ}
    (hb : Continuous b) (z : ℝ) : HasDerivAt (completeProfilePrimitive H v b) (b z) z := by
  have hraw : HasDerivAt (rawPrimitive b) (b z) z := rawPrimitive_hasDerivAt hb z
  unfold completeProfilePrimitive
  exact (hraw.const_add v).sub_const (rawPrimitive b H)

theorem completeProfilePrimitive_deriv (H v : ℝ) {b : ℝ → ℝ}
    (hb : Continuous b) : deriv (completeProfilePrimitive H v b) = b := by
  ext z
  exact (completeProfilePrimitive_hasDerivAt H v hb z).deriv

theorem completeProfilePrimitive_at (H v : ℝ) (b : ℝ → ℝ) :
    completeProfilePrimitive H v b H = v := by simp [completeProfilePrimitive]

theorem completeProfilePrimitive_eq_integral (H v : ℝ) {b : ℝ → ℝ}
    (hb : Continuous b) (z : ℝ) :
    completeProfilePrimitive H v b z = v + ∫ s in H..z, b s := by
  have h := intervalIntegral.integral_interval_sub_left (μ := volume)
    (hb.intervalIntegrable 0 z) (hb.intervalIntegrable 0 H)
  change rawPrimitive b z - rawPrimitive b H = _ at h
  dsimp [completeProfilePrimitive]
  linarith

theorem completeProfilePrimitive_germ {H : ℝ} {b F : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : H ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hb : Continuous b) (heq : b =ᶠ[𝓝 H] deriv F) :
    completeProfilePrimitive H (F H) b =ᶠ[𝓝 H] F := by
  have hmem : U ∩ {z | b z = deriv F z} ∈ 𝓝 H := inter_mem (hU.mem_nhds hH) heq
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  filter_upwards [Metric.ball_mem_nhds H hr] with z hz
  have hseg : uIcc H z ⊆ Metric.ball H r := by
    rw [Real.ball_eq_Ioo]
    exact ordConnected_Ioo.uIcc_subset (by constructor <;> linarith) (by simpa [Real.ball_eq_Ioo] using hz)
  have hder (s) (hs : s ∈ uIcc H z) : HasDerivAt F (b s) s := by
    have hm := hball (hseg hs)
    rw [hm.2]
    exact ((hF.contDiffAt (hU.mem_nhds hm.1)).differentiableAt (by simp)).hasDerivAt
  rw [completeProfilePrimitive_eq_integral H (F H) hb z,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hb.intervalIntegrable H z)]
  ring

theorem completeProfilePrimitive_pos {H v : ℝ} {b : ℝ → ℝ}
    (hb : Continuous b) (hbpos : ∀ z ∈ Ici H, 0 < b z) (hv : 0 < v) :
    ∀ z ∈ Ici H, 0 < completeProfilePrimitive H v b z := by
  have hc : Continuous (completeProfilePrimitive H v b) :=
    (show Differentiable ℝ (completeProfilePrimitive H v b) from
      fun z => (completeProfilePrimitive_hasDerivAt H v hb z).differentiableAt).continuous
  have hmono : StrictMonoOn (completeProfilePrimitive H v b) (Ici H) :=
    strictMonoOn_of_deriv_pos (convex_Ici H) hc.continuousOn (by
      intro z hz
      rw [completeProfilePrimitive_deriv H v hb]
      exact hbpos z (interior_subset hz))
  intro z hz
  have hm := hmono.monotoneOn (show H ∈ Ici H by simp) hz hz
  rw [completeProfilePrimitive_at] at hm
  exact hv.trans_le hm

theorem completeProfilePrimitive_tendsto {H v β : ℝ} {b : ℝ → ℝ}
    (hb : Continuous b) (hβ : 0 < β) (hevent : ∀ᶠ z in atTop, b z = β) :
    Tendsto (completeProfilePrimitive H v b) atTop atTop := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp hevent
  have heq : completeProfilePrimitive H v b =ᶠ[atTop]
      (fun z => β * z + (completeProfilePrimitive H v b A - β * A)) := by
    filter_upwards [eventually_ge_atTop A] with z hz
    have hdiff := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_ : s ∈ uIcc A z) => completeProfilePrimitive_hasDerivAt H v hb s)
      (hb.intervalIntegrable A z)
    have hint : (∫ s in A..z, b s) = β * (z - A) := by
      calc
        (∫ s in A..z, b s) = ∫ s in A..z, β := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hz] at hs
          exact hA s hs.1
        _ = _ := by simp [intervalIntegral.integral_const]; ring
    rw [hint] at hdiff
    linarith
  exact (tendsto_atTop_add_const_right atTop _ (tendsto_id.const_mul_atTop hβ)).congr' heq.symm

end
end TightVer401
