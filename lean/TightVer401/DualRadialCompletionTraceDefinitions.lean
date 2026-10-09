import OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Ordinary positive trace input for the completion producer. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology

/-- Ordinary initial trace fields from the pinned OpenAI positive Jordan
interface, expanded to avoid its unrelated Green/selection import closure. -/
def DualRadialCompletionPositiveTrace (H : ℂ ≃ₜ ℂ) (gamma : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ gamma ∧ Function.Periodic gamma 1 ∧ Set.InjOn gamma (Ico 0 1) ∧
    (∀ t, deriv gamma t ≠ 0) ∧
    gamma '' Icc 0 1 = frontier (H '' ball (0 : ℂ) 1) ∧
    ∀ z ∈ H '' ball (0 : ℂ) 1, ∃ u : C(unitInterval, ℝ),
      (∀ t, (u t : UnitAddCircle) = normalizedArgument (gamma t - z)) ∧ u 1 = u 0 + 1

end
end TightVer401
