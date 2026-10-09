import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace TightVer401
noncomputable section
open OAI.ClosedSurfaceR4.PeriodicPrimitive Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def jetPrimitive (c : ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  fun r => rawPrimitive h r - rawPrimitive h c

def jetDoublePrimitive (c : ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  jetPrimitive c (jetPrimitive c h)

def concaveJetReconstruction (c value slope : ℝ) (h : ℝ → ℝ) : ℝ → ℝ :=
  fun r => value + slope * (r - c) - jetDoublePrimitive c h r

theorem jetPrimitive_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (c : ℝ) :
    ContDiff ℝ ∞ (jetPrimitive c h) := (rawPrimitive_contDiff hh).sub contDiff_const

theorem jetPrimitive_hasDerivAt {h : ℝ → ℝ} (hh : Continuous h) (c r : ℝ) :
    HasDerivAt (jetPrimitive c h) (h r) r := (rawPrimitive_hasDerivAt hh r).sub_const _

theorem jetPrimitive_eq_interval {h : ℝ → ℝ} (hh : Continuous h) (c r : ℝ) :
    jetPrimitive c h r = ∫ t in c..r, h t := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hh.intervalIntegrable (μ := volume) 0 c) (hh.intervalIntegrable (μ := volume) c r)
  unfold jetPrimitive rawPrimitive
  linarith

theorem jetDoublePrimitive_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (c : ℝ) :
    ContDiff ℝ ∞ (jetDoublePrimitive c h) := jetPrimitive_contDiff (jetPrimitive_contDiff hh c) c

theorem jetDoublePrimitive_moments {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (c r : ℝ) :
    jetDoublePrimitive c h r =
      r * (∫ t in c..r, h t) - (∫ t in c..r, t * h t) := by
  have hp := (jetPrimitive_contDiff hh c).continuous
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => x) (v := jetPrimitive c h) (u' := fun _ => (1 : ℝ)) (v' := h)
    continuous_id.continuousOn hp.continuousOn (fun x _ => hasDerivAt_id x)
    (fun x _ => jetPrimitive_hasDerivAt hh.continuous c x)
    intervalIntegrable_const (hh.continuous.intervalIntegrable c r)
  simp only [jetPrimitive, sub_self, mul_zero, sub_zero, one_mul] at he
  have hfirst := jetPrimitive_eq_interval hh.continuous c r
  have hsecond := jetPrimitive_eq_interval hp c r
  change jetDoublePrimitive c h r = ∫ t in c..r, jetPrimitive c h t at hsecond
  change (∫ x in c..r, x * h x) = r * jetPrimitive c h r -
    (∫ x in c..r, jetPrimitive c h x) at he
  rw [hfirst] at he
  linarith

theorem concaveJetReconstruction_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (c value slope : ℝ) : ContDiff ℝ ∞ (concaveJetReconstruction c value slope h) :=
  (contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))).sub
    (jetDoublePrimitive_contDiff hh c)

theorem concaveJetReconstruction_hasDerivAt {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (c value slope r : ℝ) : HasDerivAt (concaveJetReconstruction c value slope h)
      (slope - jetPrimitive c h r) r := by
  have hd := ((hasDerivAt_id r).sub_const c).const_mul slope
  have hp := jetPrimitive_hasDerivAt (jetPrimitive_contDiff hh c).continuous c r
  convert! (hd.const_add value).sub hp using 1 <;> first | rfl | ring

theorem concaveJetReconstruction_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (c value slope r : ℝ) : deriv (concaveJetReconstruction c value slope h) r =
      slope - jetPrimitive c h r := (concaveJetReconstruction_hasDerivAt hh c value slope r).deriv

theorem concaveJetReconstruction_second_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (c value slope r : ℝ) : deriv (deriv (concaveJetReconstruction c value slope h)) r = -h r := by
  have he : deriv (concaveJetReconstruction c value slope h) =
      fun r => slope - jetPrimitive c h r := funext (concaveJetReconstruction_deriv hh c value slope)
  rw [he]
  exact ((jetPrimitive_hasDerivAt hh.continuous c r).const_sub slope).deriv

theorem concaveJetReconstruction_first_jet {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (c value slope : ℝ) : concaveJetReconstruction c value slope h c = value ∧
      deriv (concaveJetReconstruction c value slope h) c = slope := by
  simp [concaveJetReconstruction, jetDoublePrimitive, jetPrimitive,
    concaveJetReconstruction_deriv hh]

theorem concaveJetReconstruction_two_moment_match {h k : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k) (c value slope r : ℝ)
    (hmass : (∫ t in c..r, h t) = ∫ t in c..r, k t)
    (hfirst : (∫ t in c..r, t * h t) = ∫ t in c..r, t * k t) :
    concaveJetReconstruction c value slope h r = concaveJetReconstruction c value slope k r ∧
      deriv (concaveJetReconstruction c value slope h) r =
        deriv (concaveJetReconstruction c value slope k) r := by
  constructor
  · simp only [concaveJetReconstruction, jetDoublePrimitive_moments hh,
      jetDoublePrimitive_moments hk, hmass, hfirst]
  · simp only [concaveJetReconstruction_deriv hh, concaveJetReconstruction_deriv hk,
      jetPrimitive_eq_interval hh.continuous, jetPrimitive_eq_interval hk.continuous, hmass]

end
end TightVer401
