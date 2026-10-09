import TightVer401.AmbientCross
import Mathlib.Analysis.Calculus.ContDiff.WithLp

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem ambientCross_contDiff {f g : ℝ → Ambient}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun t => ambientCross (f t) (g t)) := by
  have hfc := (contDiff_piLp 2).mp hf
  have hgc := (contDiff_piLp 2).mp hg
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t => f t 1 * g t 2 - f t 2 * g t 1)
    exact ((hfc 1).mul (hgc 2)).sub ((hfc 2).mul (hgc 1))
  · change ContDiff ℝ ∞ (fun t => f t 2 * g t 0 - f t 0 * g t 2)
    exact ((hfc 2).mul (hgc 0)).sub ((hfc 0).mul (hgc 2))
  · change ContDiff ℝ ∞ (fun t => f t 0 * g t 1 - f t 1 * g t 0)
    exact ((hfc 0).mul (hgc 1)).sub ((hfc 1).mul (hgc 0))

end
end TightVer401
