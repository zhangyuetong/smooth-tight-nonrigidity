import TightVer401.DualRadialCompletionTraceDefinitions
import TightVer401.CorrugatedSeedVisiblePairs
import TightVer401.QuadraticFillerCartesianLegendreBoundaryDefinitions
import TightVer401.SeamNormalCoordinates

/-! PENDING CONSUMER CONTRACT ONLY. There is no inhabitant/theorem of this
proposition here, no admission and no custom axiom. This file is deliberately
outside the audited root. Owner: domination parent. Production dependencies:
visible connector (descent), full incoming filling (smoothing), annular global
inverse (degree), and the completion assembly described in the handoff.

The boundary inputs expand the pinned OpenAI positive regular Jordan fields,
not a package granting a completed potential or continued gradient image. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology RealInnerProductSpace

/-- Frozen ordinary-input type for the future actual two-sided completion.
Defining this proposition does not prove `exists_dual_radial_support_completion`. -/
def DualRadialCompletionClaim : Prop :=
  ∀ (G : Coord → ℝ) (e0 : OpenPartialHomeomorph Coord Coord)
    (HpPlus HpMinus HgPlus HgMinus : ℂ ≃ₜ ℂ)
    (pPlus pMinus gammaPlus gammaMinus : ℝ → ℂ)
    (RPlus RMinus : ℝ) (K : Set Coord),
    ContDiffOn ℝ ∞ G e0.source →
    (∀ p ∈ e0.source, (planarHessian G p).det < 0) →
    (∀ p ∈ e0.source, e0 p = planarGradient G p) →
    ContDiffOn ℝ ∞ e0.symm e0.target →
    DualRadialCompletionPositiveTrace HpPlus pPlus →
    DualRadialCompletionPositiveTrace HpMinus pMinus →
    DualRadialCompletionPositiveTrace HgPlus gammaPlus →
    DualRadialCompletionPositiveTrace HgMinus gammaMinus →
    closure ((HpMinus '' ball (0 : ℂ) 1)) ⊆ (HpPlus '' ball (0 : ℂ) 1) →
    closure ((HgPlus '' ball (0 : ℂ) 1)) ⊆ (HgMinus '' ball (0 : ℂ) 1) →
    (0 : ℂ) ∈ (HpMinus '' ball (0 : ℂ) 1) →
    (0 : ℂ) ∈ (HgPlus '' ball (0 : ℂ) 1) →
    seamComplexCoord '' (closure ((HpPlus '' ball (0 : ℂ) 1)) \ (HpMinus '' ball (0 : ℂ) 1)) ⊆ e0.source →
    (∀ t, e0 (seamComplexCoord (pPlus t)) = seamComplexCoord (gammaPlus t)) →
    (∀ t, e0 (seamComplexCoord (pMinus t)) = seamComplexCoord (gammaMinus t)) →
    (∀ t, 0 < inner ℝ (deriv pPlus t) (deriv gammaPlus t)) →
    (∀ t, 0 < inner ℝ (deriv pMinus t) (deriv gammaMinus t)) →
    0 < RPlus → 0 < RMinus →
    ComplexVisiblePair RPlus pPlus (fun t => Complex.I * gammaPlus t) →
    ComplexVisiblePair RMinus (corrugatedReverseReflect gammaMinus)
      (fun t => Complex.I * corrugatedReverseReflect pMinus t) →
    IsCompact K →
    K ⊆ seamComplexCoord '' ((HpPlus '' ball (0 : ℂ) 1) \ closure ((HpMinus '' ball (0 : ℂ) 1))) →
    ∃ (A RN mu B d0 dInfinity epsilon L : ℝ) (Gtilde : Coord → ℝ)
      (W : Set Coord) (e : OpenPartialHomeomorph Coord Coord),
      0 < A ∧ A < RN ∧ 0 < mu ∧ 0 < B ∧ 0 < epsilon ∧ epsilon < L ∧
      ContDiffOn ℝ ∞ Gtilde {p | 0 < planarRadius p} ∧
      (∀ p, 0 < planarRadius p → (planarHessian Gtilde p).det < 0) ∧
      IsOpen W ∧ K ⊆ W ∧ W ⊆ e0.source ∧ W ⊆ {p | 0 < planarRadius p} ∧
      EqOn Gtilde G W ∧
      (∀ p, 0 < planarRadius p → planarRadius p < epsilon →
        Gtilde p = RN * planarRadius p - mu * planarRadius p ^ 2 / 2 + d0) ∧
      (∀ p, L < planarRadius p →
        Gtilde p = A * planarRadius p - B / planarRadius p + dInfinity) ∧
      e.source = {p | 0 < planarRadius p} ∧
      e.target = {y | A < planarRadius y ∧ planarRadius y < RN} ∧
      (∀ p ∈ e.source, e p = planarGradient Gtilde p) ∧
      ContDiffOn ℝ ∞ e.symm e.target

end
end TightVer401
