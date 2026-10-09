import TightVer401.ReciprocalSmooth
import TightVer401.ReciprocalTransport
import TightVer401.ReciprocalSupport

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def reciprocalProfile (ρ : ℝ → ℝ) (f : Coord → ℝ) : ℝ → ℝ :=
  fun r => reciprocalExtension ρ f (![0, r] : Coord)

theorem reciprocalExtension_chart {ρ : ℝ → ℝ} {f : Coord → ℝ} {p : Coord}
    (hρpos : ∀ s, 0 < ρ s) (hp : 0 < p 1) :
    reciprocalExtension ρ f (reciprocalChart ρ p) = f p := by
  have hr : 0 < (reciprocalChart ρ p) 1 := one_div_pos.mpr (mul_pos (hρpos _) hp)
  rw [reciprocalExtension, if_pos hr,
    reciprocalChart_involution (ne_of_gt (hρpos _)) (ne_of_gt hp)]

theorem reciprocalProfile_contDiff {ρ : ℝ → ℝ} {f : Coord → ℝ} {upper : ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρpos : ∀ s, 0 < ρ s) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → ContDiffAt ℝ ∞ f p)
    (hsupport : ∀ p : Coord, upper < p 1 → f p = 0) :
    ContDiff ℝ ∞ (reciprocalProfile ρ f) := by
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (![0, r] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · convert! (contDiff_const (c := (0 : ℝ))) using 1
    · convert! (contDiff_id : ContDiff ℝ ∞ (fun r : ℝ => r)) using 1
  exact (reciprocalExtension_contDiff hρ hρpos hupper hf hsupport).comp hs

theorem reciprocalProfile_hasCompactSupport {ρ : ℝ → ℝ} {f : Coord → ℝ} {lower : ℝ}
    (hρpos : ∀ s, 0 < ρ s) (hlower : 0 < lower)
    (hsupport : ∀ p : Coord, p 1 < lower → f p = 0) :
    HasCompactSupport (reciprocalProfile ρ f) :=
  reciprocalExtension_slice_hasCompactSupport hρpos hlower hsupport 0

theorem reciprocalProfile_reconstruction {ρ lam D W : ℝ → ℝ} {f : Coord → ℝ} {upper : ℝ}
    (hρ : ∀ s, HasDerivAt ρ (lam s * ρ s / 2) s)
    (hρpos : ∀ s, 0 < ρ s) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ f p)
    (hsupport : ∀ p : Coord, upper < p 1 → f p = 0)
    (hpde : ∀ p : Coord, 0 < p 1 → coordPartial 0 f p -
      p 1 / 2 * (lam (p 0) + p 1 * D (p 0)) * coordPartial 1 f p = 0)
    (hW : ∀ s, HasDerivAt W (D s / (2 * ρ s)) s) (hW0 : W 0 = 0)
    {p : Coord} (hp : 0 < p 1) :
    f p = reciprocalProfile ρ f (1 / (ρ (p 0) * p 1) - W (p 0)) := by
  have hg := reciprocalExtension_differentiable (fun s => (hρ s).differentiableAt)
    hρpos hupper hf hsupport
  have he := advection_first_integral_formula hg hW hW0
    (reciprocalExtension_transport hρ hρpos hupper hf hsupport hpde)
    (p 0) (1 / (ρ (p 0) * p 1))
  change reciprocalExtension ρ f (reciprocalChart ρ p) = _ at he
  rw [reciprocalExtension_chart hρpos hp] at he
  exact he

end
end TightVer401
