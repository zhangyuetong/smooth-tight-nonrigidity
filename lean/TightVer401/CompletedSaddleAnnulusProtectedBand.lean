import TightVer401.CorrugatedIdentityBendingBand
import TightVer401.ProtectedTorusMapDefinitions

/-! Ordinary coordinate-level output for a protected band in an actual saddle
cylinder. This defines a producer specification and asserts no existence. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual smooth coordinates on a protected open neighborhood, with literal
ambient affine equality. The completed annulus producer must construct this
object; it is not a premise granting a completed annulus. -/
structure CompletedSaddleAnnulusProtectedBand {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient)
    (K : Set (AddCircle T × Ioo (0 : ℝ) w)) (a : ℝ) where
  coordinates : OpenPartialHomeomorph
    (AddCircle T × Ioo (0 : ℝ) w) (AddCircle (2 * Real.pi) × ℝ)
  protected_source : K ⊆ coordinates.source
  interior_target : coordinates.target ⊆ univ ×ˢ Ioo (0 : ℝ) Real.pi
  coordinates_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
    (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ coordinates coordinates.source
  inverse_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
    (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ coordinates.symm coordinates.target
  affine_eq : ∀ p ∈ coordinates.source,
    S (coordinates p) = -d.bandMap p + a • revolutionAxis

/-- The actual completed-cylinder output and its protected coordinate map.
No existence is asserted by defining this ordinary producer output type. -/
structure CompletedSaddleAnnulusOutput {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (K : Set (AddCircle T × Ioo (0 : ℝ) w))
    (RN μ h : ℝ) where
  cylinder : ProtectedSaddleCylinderInput RN μ h
  verticalOffset : ℝ
  protectedBand : CompletedSaddleAnnulusProtectedBand d cylinder.saddle K verticalOffset

end
end TightVer401
