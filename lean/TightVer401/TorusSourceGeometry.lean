import TightVer401.TorusGoalObjects
import Mathlib.Topology.Instances.AddCircle.Real

/-! Derived topology and the actual native smooth structure of the torus source.
No embedding or nonrigidity result is asserted. -/
namespace TightVer401
noncomputable section
open scoped Manifold ContDiff

private theorem nonrigidTorusSource_period_pos : 0 < 2 * Real.pi :=
  mul_pos (by norm_num) Real.pi_pos

theorem nonrigidTorusSource_compact : CompactSpace NonrigidTorusSource := by
  letI : Fact (0 < 2 * Real.pi) := ⟨nonrigidTorusSource_period_pos⟩
  dsimp only [NonrigidTorusSource]
  infer_instance

theorem nonrigidTorusSource_connected : ConnectedSpace NonrigidTorusSource := by
  dsimp only [NonrigidTorusSource]
  infer_instance

/-- The chart structure is a constructed object, so this declaration is a
`def` rather than a theorem. It is the product of the audited period charts. -/
@[instance_reducible]
def nonrigidTorusSource_chartedSpace : ChartedSpace (ModelProd ℝ ℝ) NonrigidTorusSource := by
  letI : Fact (0 < 2 * Real.pi) := ⟨nonrigidTorusSource_period_pos⟩
  dsimp only [NonrigidTorusSource]
  infer_instance

attribute [instance] nonrigidTorusSource_chartedSpace

/-- Mathlib's native product model is a type tag for the ordinary real product.
This object also exposes the literal real-product chart-space type. -/
def nonrigidTorusSource_realProductChartedSpace :
    ChartedSpace (ℝ × ℝ) NonrigidTorusSource := nonrigidTorusSource_chartedSpace

theorem nonrigidTorusSource_isManifold :
    IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ NonrigidTorusSource := by
  letI : Fact (0 < 2 * Real.pi) := ⟨nonrigidTorusSource_period_pos⟩
  dsimp only [NonrigidTorusSource, nonrigidTorusSource_chartedSpace]
  infer_instance

end
end TightVer401
