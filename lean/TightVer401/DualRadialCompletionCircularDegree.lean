import TightVer401.QuadraticFillerCartesianGradientAnnulusSmooth

/-! Ordinary circular boundary specialization required from the degree producer.
This file only defines the local producer proposition. It asserts no theorem,
assumes no global completion package, and imports no pending invocation.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The reversed-boundary, negative-Jacobian annular degree specialization.
All boundary maps are literal actual gradients on circles. The source has an
ordinary smooth ambient collar containing the entire closed annulus. -/
def DualRadialCompletionCircularDegreeClaim : Prop :=
  ∀ (G : Coord → ℝ) (U : Set Coord) (epsilon L a b : ℝ),
    0 < epsilon → epsilon < L → 0 < a → a < b → IsOpen U →
    ContDiffOn ℝ ∞ G U →
    {p : Coord | epsilon ≤ planarRadius p ∧ planarRadius p ≤ L} ⊆ U →
    (∀ p, epsilon < planarRadius p → planarRadius p < L →
      (planarHessian G p).det < 0) →
    (∀ theta : ℝ, planarGradient G (saddlePolarChart ![epsilon, theta]) =
      b • (![Real.cos theta, Real.sin theta] : Coord)) →
    (∀ theta : ℝ, planarGradient G (saddlePolarChart ![L, theta]) =
      a • (![Real.cos theta, Real.sin theta] : Coord)) →
    BijOn (planarGradient G)
      {p : Coord | epsilon < planarRadius p ∧ planarRadius p < L}
      {y : Coord | a < planarRadius y ∧ planarRadius y < b}

end
end TightVer401
