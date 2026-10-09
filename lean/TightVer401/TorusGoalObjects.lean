import TightVer401.PeriodCircleInstances
import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Connected.Basic

/-! Actual target predicates for the ver500 nonrigid-torus route.
These are definitions, with no existence or tightness conclusions supplied. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

/-- The genuine product of two periodic circles. -/
abbrev NonrigidTorusSource :=
  AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi)

/-- Every open affine half-space cuts the image in a preconnected set.
Empty cuts are permitted by the definition of preconnectedness. -/
def IsTightImage {M : Type*} (X : M → Ambient) : Prop :=
  ∀ (ell : Ambient →L[ℝ] ℝ) (a : ℝ),
    IsPreconnected (range X ∩ ell ⁻¹' Ioi a)

/-- No affine Euclidean isometry carries one entire image to the other. -/
def ImageNoncongruent {M : Type*} (X Y : M → Ambient) : Prop :=
  ∀ A : Ambient ≃ᵃⁱ[ℝ] Ambient, A '' range X ≠ range Y

/-- No nonempty open part of the source maps into an affine plane. -/
def HasNoOpenPlanarPatch {M : Type*} [TopologicalSpace M] (X : M → Ambient) : Prop :=
  ∀ U : Set M, IsOpen U → U.Nonempty →
    ∀ ell : Ambient →L[ℝ] ℝ, ell ≠ 0 →
      ∀ c : ℝ, ¬ (∀ p ∈ U, ell (X p) = c)

end
end TightVer401
