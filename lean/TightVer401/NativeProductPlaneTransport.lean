import TightVer401.NativeProductPlaneFormsApplications
import TightVer401.NativeProductPlaneBandCurvature
import TightVer401.NormalLoopCriterionImmersion

/-! Reusable geometry bridge for the native band and actual torus source.
The atlas is explicit and opt-in. This does not supply a torus embedding,
an extended bending, an intrinsic distance, or global curvature integration. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open OAI.ClosedSurfaceR4 OAI.SmoothLocal.Geometry

/-- The transported atlas on the registered native torus source. -/
@[instance_reducible]
def nonrigidTorusSource_planeChartedSpace : ChartedSpace Plane NonrigidTorusSource :=
  nativeProductPlaneChartedSpace NonrigidTorusSource

/-- Genuine infinity smooth plane-model torus, retaining the registered native atlas. -/
theorem nonrigidTorusSource_plane_isManifold :
    letI := nonrigidTorusSource_planeChartedSpace
    IsManifold planeModel ∞ NonrigidTorusSource := by
  letI : IsManifold nativeProductModel ∞ NonrigidTorusSource := nonrigidTorusSource_isManifold
  exact nativeProductPlane_isManifold NonrigidTorusSource

section Band
variable {L b : ℝ} [Fact (0 < L)]
local instance nativeProductPlaneTransportBandChartedSpace : ChartedSpace Plane (AddCircle L × Set.Ioo (0 : ℝ) b) :=
  nativeProductPlaneChartedSpace _

/-- Direct actual native-band application: smooth plane structure, smooth actual
map, injective manifold differential, and negative chart intrinsic curvature. -/
theorem nativeProductPlane_band_geometry (d : PeriodicRuledFrame L) :
    IsManifold planeModel ∞ (AddCircle L × Set.Ioo (0 : ℝ) b) ∧
    ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := b)) ∧
    ∀ p : AddCircle L × Set.Ioo (0 : ℝ) b,
      Function.Injective (surfaceDifferential d.bandMap p) ∧
      gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap d.bandMap p))
        (![0, (p.2 : ℝ)] : Coord) < 0 := by
  refine ⟨nativeProductPlane_isManifold _,
    (nativeProductPlane_contMDiff_iff _ _).mpr d.bandMap_contMDiff, ?_⟩
  intro p
  exact ⟨(nativeProductPlane_immersion_iff
    ((d.bandMap_contMDiff p).mdifferentiableAt (by simp))).mpr
      (periodicRuledFrame_bandMap_immersion d p), nativeProductPlane_band_curvature_neg d p⟩

end Band

section
variable (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]
local instance nativeProductPlaneTransportChartedSpace : ChartedSpace Plane M := nativeProductPlaneChartedSpace M

/-- Actual model/atlas/differential/induced-form/local-curvature transport.
The native smooth manifold is the only geometric source input. -/
theorem native_product_plane_geometry_transport [IsManifold nativeProductModel ∞ M] :
    IsManifold planeModel ∞ M ∧
    ∀ F : M → Ambient, ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ F →
      ContMDiff planeModel 𝓘(ℝ, Ambient) ∞ F ∧
      (∀ (p : M) (v w : ℝ × ℝ),
        surfaceDifferential F p (nativeProductPlaneEquiv v) =
          mfderiv nativeProductModel 𝓘(ℝ, Ambient) F p v ∧
        inducedForm F p (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
          nativeProductInducedForm F p v w) ∧
      (∀ (p : M) (q : Coord),
        gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap F p)) q =
          gaussianCurvature (inducedMetric (nativeProductCoordinateMap F p)) q) := by
  refine ⟨nativeProductPlane_isManifold M, ?_⟩
  intro F hF
  refine ⟨(nativeProductPlane_contMDiff_iff M F).mpr hF, ?_, ?_⟩
  · intro p v w
    have hd := (hF p).mdifferentiableAt (by simp)
    exact ⟨nativeProductPlane_mfderiv_apply hd v, nativeProductPlane_inducedForm hd v w⟩
  · exact nativeProductPlane_coordinate_curvature F

end
end
end TightVer401


