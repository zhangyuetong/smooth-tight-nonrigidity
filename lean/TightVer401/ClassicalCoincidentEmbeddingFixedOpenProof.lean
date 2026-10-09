import TightVer401.ClassicalCoincidentEmbeddingDifferential
import TightVer401.NativeEmbeddingMetricIsometrySpace
import TightVer401.NativeEmbeddingMetricIsometryDistance
import TightVer401.NativeProductPlaneIntrinsicDistance
import TightVer401.FixedOpenCompact

/-! Closed rigidity of equal-image smooth embeddings with common induced form.
The intrinsic metric is built from the actual immersion Y, and its distance is
Mathlib's actual C1-path infimum with the original torus topology. -/
open Manifold Bundle
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4

/-- The exact fixed-open background statement, without an external premise. -/
theorem classicalCoincidentEmbeddingFixedOpen_proved :
    ClassicalCoincidentEmbeddingFixedOpenClaim := by
  intro X Y hX hY hmetric himage U hU hne hagree
  letI : IsManifold nativeProductModel ∞ NonrigidTorusSource :=
    nonrigidTorusSource_isManifold
  letI : CompactSpace NonrigidTorusSource := nonrigidTorusSource_compact
  letI : ConnectedSpace NonrigidTorusSource := nonrigidTorusSource_connected
  obtain ⟨e, he, hi, heq⟩ :=
    classicalEmbeddedImageReparametrization_proved X Y hX hY himage
  have hfix : EqOn e id U := classicalCoincident_reparam_fixedOn hY heq hagree
  have hdNative (p q : NonrigidTorusSource) :
      nativeProductImmersionEDist Y hY.1 hY.2.1 (e p) (e q) =
        nativeProductImmersionEDist Y hY.1 hY.2.1 p q := by
    letI := nativeProductImmersionRiemannianBundle Y hY.1 hY.2.1
    exact riemannianEDist_homeomorph_eq_of_tangent_enorm e
      (he.of_le (by simp)) (hi.of_le (by simp))
      (classicalCoincident_native_enorm hY he heq hmetric) p q
  have hdPlane (p q : NonrigidTorusSource) :
      nativeProductPlaneImmersionEDist Y hY.1 hY.2.1 (e p) (e q) =
        nativeProductPlaneImmersionEDist Y hY.1 hY.2.1 p q := by
    rw [← nativeProductPlaneImmersionEDist_transport Y hY.1 hY.2.1,
      ← nativeProductPlaneImmersionEDist_transport Y hY.1 hY.2.1]
    exact hdNative p q
  letI : ChartedSpace Plane NonrigidTorusSource :=
    nativeProductPlaneChartedSpace NonrigidTorusSource
  letI : IsManifold planeModel ∞ NonrigidTorusSource :=
    nativeProductPlane_isManifold NonrigidTorusSource
  let g := nativeProductPlaneImmersionMetric Y hY.1 hY.2.1
  letI : RiemannianBundle (fun p : NonrigidTorusSource => TangentSpace planeModel p) :=
    nativeProductPlaneImmersionRiemannianBundle Y hY.1 hY.2.1
  letI : IsContMDiffRiemannianBundle planeModel ∞ Plane
      (fun p : NonrigidTorusSource => TangentSpace planeModel p) :=
    ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  letI : IsContinuousRiemannianBundle Plane
      (fun p : NonrigidTorusSource => TangentSpace planeModel p) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let intrinsicMetric : MetricSpace NonrigidTorusSource :=
    connectedRiemannianMetricSpace planeModel NonrigidTorusSource
  letI : MetricSpace NonrigidTorusSource := intrinsicMetric
  letI : EMetricSpace NonrigidTorusSource := intrinsicMetric.toEMetricSpace
  letI : PseudoMetricSpace NonrigidTorusSource := intrinsicMetric.toPseudoMetricSpace
  letI : PseudoEMetricSpace NonrigidTorusSource :=
    intrinsicMetric.toEMetricSpace.toPseudoEMetricSpace
  letI : IsRiemannianManifold planeModel NonrigidTorusSource :=
    connectedRiemannianMetricSpace_isRiemannian planeModel NonrigidTorusSource
  have hiso : Isometry (e : NonrigidTorusSource → NonrigidTorusSource) := by
    intro p q
    exact hdPlane p q
  have hid : (e : NonrigidTorusSource → NonrigidTorusSource) = id :=
    isometry_eq_id_of_fixed_open_compact (n := 2) hiso
      (classicalCoincident_plane_contMDiff he) hU hne hfix
  funext p
  have hp : e p = p := congrFun hid p
  exact (heq p).symm.trans (congrArg Y hp)

end
end TightVer401

