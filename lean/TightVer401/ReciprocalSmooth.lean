import TightVer401.ReciprocalExtension

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem reciprocalChart_contDiffAt {ρ : ℝ → ℝ} {p : Coord}
    (hρ : ContDiffAt ℝ ∞ ρ (p 0)) (hρ0 : ρ (p 0) ≠ 0) (hr0 : p 1 ≠ 0) :
    ContDiffAt ℝ ∞ (reciprocalChart ρ) p := by
  have hs : ContDiffAt ℝ ∞ (fun q : Coord => q 0) p := (contDiff_apply ℝ ℝ 0).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun q : Coord => q 1) p := (contDiff_apply ℝ ℝ 1).contDiffAt
  have hc : ContDiffAt ℝ ∞ (fun q : Coord => ρ (q 0)) p := hρ.comp p hs
  have hu : ContDiffAt ℝ ∞ (fun q : Coord => 1 / (ρ (q 0) * q 1)) p :=
    contDiffAt_const.div (hc.mul hr) (mul_ne_zero hρ0 hr0)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · convert! hs using 1
  · convert! hu using 1

theorem reciprocalExtension_contDiff {ρ : ℝ → ℝ} {f : Coord → ℝ} {upper : ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρpos : ∀ s, 0 < ρ s) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → ContDiffAt ℝ ∞ f p)
    (hsupport : ∀ p : Coord, upper < p 1 → f p = 0) :
    ContDiff ℝ ∞ (reciprocalExtension ρ f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : 0 < p 1
  · have hu : 0 < (reciprocalChart ρ p) 1 := one_div_pos.mpr (mul_pos (hρpos _) hp)
    exact ((hf _ hu).comp p (reciprocalChart_contDiffAt hρ.contDiffAt
      (ne_of_gt (hρpos _)) (ne_of_gt hp))).congr_of_eventuallyEq
        (reciprocalExtension_eventually_eq_positive hp)
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (reciprocalExtension_eventually_zero hupper hρ.continuous.continuousAt hρpos hsupport
        (le_of_not_gt hp))

end
end TightVer401
