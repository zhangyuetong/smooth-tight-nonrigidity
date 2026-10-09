import TightVer401.AdvectionTransport
import TightVer401.RuledProfiles

/-! Actual zero extension after reciprocal change of transverse coordinate.
Support away from the upper edge makes the extension locally zero at r = 0. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def reciprocalChart (ρ : ℝ → ℝ) (p : Coord) : Coord :=
  ![p 0, 1 / (ρ (p 0) * p 1)]

def reciprocalExtension (ρ : ℝ → ℝ) (f : Coord → ℝ) (p : Coord) : ℝ :=
  if 0 < p 1 then f (reciprocalChart ρ p) else 0

theorem reciprocalChart_differentiableAt {ρ : ℝ → ℝ} {p : Coord}
    (hρ : DifferentiableAt ℝ ρ (p 0)) (hρ0 : ρ (p 0) ≠ 0) (hr0 : p 1 ≠ 0) :
    DifferentiableAt ℝ (reciprocalChart ρ) p := by
  have hs := ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
    (x := p)).differentiableAt
  have hr := ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
    (x := p)).differentiableAt
  have hc : DifferentiableAt ℝ (fun q : Coord => ρ (q 0)) p := hρ.comp p hs
  have hu : DifferentiableAt ℝ (fun q : Coord => 1 / (ρ (q 0) * q 1)) p :=
    scalar_coord_div_differentiableAt (differentiableAt_const 1) (hc.mul hr)
      (mul_ne_zero hρ0 hr0)
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · convert! hs using 1
  · convert! hu using 1

theorem reciprocalExtension_eventually_eq_positive {ρ : ℝ → ℝ} {f : Coord → ℝ}
    {p : Coord} (hr : 0 < p 1) :
    reciprocalExtension ρ f =ᶠ[𝓝 p] (fun q => f (reciprocalChart ρ q)) := by
  have hs : ∀ᶠ q : Coord in 𝓝 p, 0 < q 1 :=
    continuousAt_const.eventually_lt (continuous_apply 1).continuousAt hr
  filter_upwards [hs] with q hq
  exact if_pos hq

theorem reciprocalExtension_eventually_zero {ρ : ℝ → ℝ} {f : Coord → ℝ}
    {p : Coord} {upper : ℝ} (hupper : 0 < upper)
    (hρ : ContinuousAt ρ (p 0)) (hρpos : ∀ s, 0 < ρ s)
    (hsupport : ∀ q : Coord, upper < q 1 → f q = 0) (hr : p 1 ≤ 0) :
    reciprocalExtension ρ f =ᶠ[𝓝 p] (fun _ => 0) := by
  rcases hr.lt_or_eq with hneg | hzero
  · have hs : ∀ᶠ q : Coord in 𝓝 p, q 1 < 0 :=
      (continuous_apply 1).continuousAt.eventually_lt continuousAt_const hneg
    filter_upwards [hs] with q hq
    exact if_neg (by linarith)
  · have hc : ContinuousAt (fun q : Coord => ρ (q 0) * q 1) p :=
      (hρ.comp (f := fun q : Coord => q 0) (x := p)
        (continuous_apply 0).continuousAt).mul (continuous_apply 1).continuousAt
    have hs : ∀ᶠ q : Coord in 𝓝 p, ρ (q 0) * q 1 < 1 / upper :=
      hc.eventually_lt continuousAt_const (by rw [hzero, mul_zero]; positivity)
    filter_upwards [hs] with q hq
    by_cases hpos : 0 < q 1
    · rw [reciprocalExtension, if_pos hpos]
      apply hsupport
      change upper < 1 / (ρ (q 0) * q 1)
      have hm : 0 < ρ (q 0) * q 1 := mul_pos (hρpos _) hpos
      apply (lt_div_iff₀ hm).mpr
      have hb := (lt_div_iff₀ hupper).mp hq
      nlinarith
    · exact if_neg hpos

theorem reciprocalExtension_differentiable {ρ : ℝ → ℝ} {f : Coord → ℝ} {upper : ℝ}
    (hρ : Differentiable ℝ ρ) (hρpos : ∀ s, 0 < ρ s) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ f p)
    (hsupport : ∀ p : Coord, upper < p 1 → f p = 0) :
    Differentiable ℝ (reciprocalExtension ρ f) := by
  intro p
  by_cases hp : 0 < p 1
  · have hu : 0 < (reciprocalChart ρ p) 1 := by
      exact one_div_pos.mpr (mul_pos (hρpos _) hp)
    exact ((hf _ hu).comp p (reciprocalChart_differentiableAt (hρ _) (ne_of_gt (hρpos _))
      (ne_of_gt hp))).congr_of_eventuallyEq (reciprocalExtension_eventually_eq_positive hp)
  · exact (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (reciprocalExtension_eventually_zero hupper (hρ _).continuousAt hρpos hsupport
        (le_of_not_gt hp))

end
end TightVer401
