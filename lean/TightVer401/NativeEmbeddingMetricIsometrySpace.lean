import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic

/-! Compatible finite intrinsic distance on connected Riemannian manifolds.
The distance is Mathlib's actual C1 path-length infimum. The constructions
retain the original topology definitionally; no ambient or product distance
is used. These are opt-in structures rather than global instances.
-/
open Manifold Bundle Set
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section

/-- All extended distances in a connected emetric space are finite. -/
theorem connected_emetric_edist_ne_top {M : Type*} [PseudoEMetricSpace M]
    [PreconnectedSpace M] (x y : M) : edist x y ≠ ⊤ := by
  have hball : Metric.eball x ⊤ = (Set.univ : Set M) :=
    (show IsClopen (Metric.eball x ⊤) from
      ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩).eq_univ
      ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hball]; trivial
  have hxy : edist x y < ⊤ := by simpa only [Metric.mem_eball, edist_comm] using hy
  exact hxy.ne

section Intrinsic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [t : TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (fun p : M => TangentSpace I p)]
  [IsContinuousRiemannianBundle E (fun p : M => TangentSpace I p)]
  [T3Space M] [PreconnectedSpace M]

/-- The genuine intrinsic distance is finite on a connected source. -/
theorem riemannianEDist_ne_top_connected (x y : M) :
    Manifold.riemannianEDist I x y ≠ ⊤ := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  exact connected_emetric_edist_ne_top x y

/-- Opt-in metric structure from the actual Riemannian C1 path infimum. -/
@[reducible] def connectedRiemannianMetricSpace : MetricSpace M :=
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y => connected_emetric_edist_ne_top x y)

/-- The constructed intrinsic metric has exactly the preexisting topology. -/
theorem connectedRiemannianMetricSpace_topology :
    (connectedRiemannianMetricSpace I M).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      t := rfl

/-- Its extended distance is the actual Riemannian path-length infimum. -/
theorem connectedRiemannianMetricSpace_edist (x y : M) :
    letI : MetricSpace M := connectedRiemannianMetricSpace I M
    edist x y = Manifold.riemannianEDist I x y := rfl

/-- Required compatibility predicate for the intrinsic rigidity consumer. -/
theorem connectedRiemannianMetricSpace_isRiemannian :
    letI : MetricSpace M := connectedRiemannianMetricSpace I M
    IsRiemannianManifold I M := by
  letI : MetricSpace M := connectedRiemannianMetricSpace I M
  exact ⟨fun _ _ => rfl⟩

end Intrinsic
end
end TightVer401

