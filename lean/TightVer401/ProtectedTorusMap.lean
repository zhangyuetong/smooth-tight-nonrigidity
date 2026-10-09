import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.ProtectedTorusMapTopology
import TightVer401.ProtectedTorusMapSeams

/-! Actual smooth embedded literal torus assembly from ordinary annulus/meridian data.
Constructing these producer data remains a separate existence obligation. Producers
import only ProtectedTorusMapDefinitions, preventing circular discharge imports. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual local seam representatives give smoothness and injective native derivatives. -/
theorem protectedTorusMap_contMDiff_and_immersion {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (protectedTorusMap d.saddle d.meridian h) ∧
      ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
        (protectedTorusMap d.saddle d.meridian h) p) := by
  exact protectedTorusMap_contMDiff_and_immersion_from_data d

/-- Global injection derived from producer injection,
monotone cosine height and strict interior radius separation. -/
theorem protectedTorusMap_injective {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    Function.Injective (protectedTorusMap d.saddle d.meridian h) :=
  protectedTorusMap_injective_from_data d

/-- The two literal closed cylinder images join at the actual seams. -/
theorem protectedTorusMap_range {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    range (protectedTorusMap d.saddle d.meridian h) =
      d.saddle '' (univ ×ˢ Icc (0 : ℝ) Real.pi) ∪
      protectedTorusConvexCylinder d.meridian h ''
        (univ ×ˢ Icc Real.pi (2 * Real.pi)) :=
  protectedTorusMap_range_from_data d

/-- The actual assembled map is an embedding by compactness and global injection. -/
theorem protectedTorusMap_embedding_of_annulus_and_meridian {RN μ h : ℝ}
    (d : ProtectedTorusAssemblyInput RN μ h) :
    Topology.IsEmbedding (protectedTorusMap d.saddle d.meridian h) := by
  letI : CompactSpace NonrigidTorusSource := nonrigidTorusSource_compact
  exact ((protectedTorusMap_contMDiff_and_immersion d).1.continuous.isClosedEmbedding
    (protectedTorusMap_injective d)).isEmbedding

end
end TightVer401
