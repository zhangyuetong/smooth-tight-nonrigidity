import TightVer401.PeriodicComplexJordan
import TightVer401.CorrugatedSeedJordan
import Schoenflies.JordanClosed

/-! Actual Jordan separation, using the exact external theorem selected by
OpenAI's pinned topology foundation. This proves separation of genuine curve
ranges; membership of a specified disk in the bounded component is separate. -/
namespace TightVer401
noncomputable section
open Set Function
open scoped ContDiff Topology

theorem periodicComplexCurve_separates {L : ℝ} [Fact (0 < L)]
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (hi : InjOn f (Ico 0 L)) :
    Schoenflies.IsSeparating (range (jordanComplexCoordinates.symm ∘ f)) :=
  Schoenflies.jordan_curve_theorem (periodicComplexCurve_isJordanCurve hf hp hi)

theorem corrugatedSeedBeta_separates {N : ℕ} (hN : 2 ≤ N) :
    Schoenflies.IsSeparating
      (range (jordanComplexCoordinates.symm ∘ corrugatedSeedBeta (N : ℝ))) :=
  Schoenflies.jordan_curve_theorem (corrugatedSeedBeta_isJordanCurve hN)

end
end TightVer401
