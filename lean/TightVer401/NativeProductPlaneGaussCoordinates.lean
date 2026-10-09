import TightVer401.NativeProductPlaneAtlas

/-! Explicit coordinate atlas adapter for the retained Gauss inverse APIs.

Those APIs use `Coord = Fin 2 → ℝ`, whereas the manifold metric API uses the
Euclidean `Plane`. For a native product-charted carrier, this file constructs
the actual Coord atlas using `finTwoArrow.symm`, proves its smooth compatibility,
and identifies its manifold differential with the native differential composed
with `finTwoArrow`. The identity from this atlas to the transported Plane atlas
is smooth. No global chart instance or norm-isometry identification is introduced.
-/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def nativeProductGaussCoordinateEquiv : (ℝ × ℝ) ≃L[ℝ] Coord :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

section
variable (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]

@[instance_reducible]
def nativeProductGaussChartedSpace : ChartedSpace Coord M where
  atlas := (fun c : OpenPartialHomeomorph M (ModelProd ℝ ℝ) =>
    c.trans nativeProductGaussCoordinateEquiv.toHomeomorph.toOpenPartialHomeomorph) ''
      atlas (ModelProd ℝ ℝ) M
  chartAt p := (chartAt (ModelProd ℝ ℝ) p).trans
    nativeProductGaussCoordinateEquiv.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source p := by simp [mem_chart_source]
  chart_mem_atlas p := ⟨chartAt (ModelProd ℝ ℝ) p, chart_mem_atlas _ _, rfl⟩

local instance nativeProductGaussCoordinatesChartedSpace : ChartedSpace Coord M :=
  nativeProductGaussChartedSpace M
local instance nativeProductGaussCoordinatesPlaneChartedSpace :
    ChartedSpace OAI.ClosedSurfaceR4.Plane M := nativeProductPlaneChartedSpace M

private theorem nativeProductGauss_identity_germ (p : M) :
    writtenInExtChartAt nativeProductModel 𝓘(ℝ, Coord) p (id : M → M)
      =ᶠ[𝓝 (extChartAt nativeProductModel p p)] nativeProductGaussCoordinateEquiv := by
  have h := (chartAt (ModelProd ℝ ℝ) p).eventually_right_inverse' (mem_chart_source _ p)
  filter_upwards [h] with q hq
  change nativeProductGaussCoordinateEquiv (chartAt (ModelProd ℝ ℝ) p
    ((chartAt (ModelProd ℝ ℝ) p).symm q)) = nativeProductGaussCoordinateEquiv q
  rw [hq]

private theorem nativeProductGauss_inverse_germ (p : M) :
    writtenInExtChartAt 𝓘(ℝ, Coord) nativeProductModel p (id : M → M)
      =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Coord) p p)] nativeProductGaussCoordinateEquiv.symm := by
  have h := (chartAt Coord p).eventually_right_inverse' (mem_chart_source _ p)
  filter_upwards [h] with q hq
  apply nativeProductGaussCoordinateEquiv.injective
  exact hq.trans (nativeProductGaussCoordinateEquiv.apply_symm_apply q).symm

theorem nativeProductGauss_identity_contMDiff :
    ContMDiff nativeProductModel 𝓘(ℝ, Coord) ∞ (id : M → M) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  exact (nativeProductGaussCoordinateEquiv.contDiff.contDiffAt.congr_of_eventuallyEq
    (nativeProductGauss_identity_germ M p)).contDiffWithinAt

theorem nativeProductGauss_inverse_contMDiff :
    ContMDiff 𝓘(ℝ, Coord) nativeProductModel ∞ (id : M → M) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  exact (nativeProductGaussCoordinateEquiv.symm.contDiff.contDiffAt.congr_of_eventuallyEq
    (nativeProductGauss_inverse_germ M p)).contDiffWithinAt

theorem nativeProductGauss_inverse_hasMFDerivAt (p : M) :
    HasMFDerivAt 𝓘(ℝ, Coord) nativeProductModel (id : M → M) p
      nativeProductGaussCoordinateEquiv.symm.toContinuousLinearMap := by
  refine ⟨continuousAt_id, ?_⟩
  exact (nativeProductGaussCoordinateEquiv.symm.hasFDerivAt.congr_of_eventuallyEq
    (nativeProductGauss_inverse_germ M p)).hasFDerivWithinAt

theorem nativeProductGauss_mfderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : M → V} {p : M} (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, V) F p) :
    mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, V) F p =
      (mfderiv nativeProductModel 𝓘(ℝ, V) F p).comp
        nativeProductGaussCoordinateEquiv.symm.toContinuousLinearMap := by
  have h := mfderiv_comp p hF (nativeProductGauss_inverse_hasMFDerivAt M p).mdifferentiableAt
  rw [(nativeProductGauss_inverse_hasMFDerivAt M p).mfderiv] at h
  exact h

theorem nativeProductGauss_isManifold [IsManifold nativeProductModel ∞ M] :
    IsManifold 𝓘(ℝ, Coord) ∞ M := by
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have hd : ContDiffOn (E := ℝ × ℝ) (F := ℝ × ℝ) ℝ ∞
      (fun q : ℝ × ℝ => ((a.symm.trans b) q : ℝ × ℝ))
      (show Set (ℝ × ℝ) from (a.symm.trans b).source) := by
    have h := ((contDiffGroupoid ∞ nativeProductModel).compatible ha hb).1
    dsimp [contDiffPregroupoid] at h
    convert! h using 1 <;> simp [nativeProductModel, Function.comp_def]
  have hcomp := nativeProductGaussCoordinateEquiv.contDiff.comp_contDiffOn
    (hd.comp nativeProductGaussCoordinateEquiv.symm.contDiff.contDiffOn
      (mapsTo_preimage _ _))
  convert! hcomp using 1 <;> simp [preimage_preimage, Function.comp_def]
  rfl

/-- Output of a checked Coord inverse can be read smoothly in the actual Plane atlas. -/
theorem nativeProductGauss_to_plane_contMDiff :
    ContMDiff 𝓘(ℝ, Coord) OAI.ClosedSurfaceR4.planeModel ∞ (id : M → M) :=
  (nativeProductPlane_identity_contMDiff M).comp (nativeProductGauss_inverse_contMDiff M)

end
end
end TightVer401
