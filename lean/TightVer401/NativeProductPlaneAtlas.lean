import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import TightVer401.ManifoldBranching
import TightVer401.TorusSourceGeometry

/-! Explicit atlas transport from the native real product to OpenAI's plane.
The plane atlas is opt-in, never a replacement global instance. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
abbrev nativeProductModel := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)

/-- Reuse the pinned OpenAI coordinate equivalence, with its actual inverse. -/
def nativeProductPlaneEquiv : (ℝ × ℝ) ≃L[ℝ] OAI.ClosedSurfaceR4.Plane :=
  OAI.CircleDomainRigidity.euclideanPlaneCoordinates.symm

@[simp] theorem nativeProductPlaneEquiv_symm_apply (v : OAI.ClosedSurfaceR4.Plane) :
    nativeProductPlaneEquiv.symm v = (v 0, v 1) := rfl

@[simp] theorem nativeProductPlaneEquiv_apply_zero (v : ℝ × ℝ) :
    nativeProductPlaneEquiv v 0 = v.1 := rfl

@[simp] theorem nativeProductPlaneEquiv_apply_one (v : ℝ × ℝ) :
    nativeProductPlaneEquiv v 1 = v.2 := rfl

/-- The Euclidean pairing pulls back to the sum of the two coordinate products.
No isometry for the product's max norm is asserted. -/
theorem nativeProductPlaneEquiv_inner (v w : ℝ × ℝ) :
    inner ℝ (nativeProductPlaneEquiv v) (nativeProductPlaneEquiv w) =
      v.1 * w.1 + v.2 * w.2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]

section Atlas
variable (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]

/-- Compose each native chart with the actual plane homeomorphism. -/
@[instance_reducible]
def nativeProductPlaneChartedSpace : ChartedSpace OAI.ClosedSurfaceR4.Plane M where
  atlas := (fun c : OpenPartialHomeomorph M (ModelProd ℝ ℝ) =>
    c.trans nativeProductPlaneEquiv.toHomeomorph.toOpenPartialHomeomorph) ''
      atlas (ModelProd ℝ ℝ) M
  chartAt p := (chartAt (ModelProd ℝ ℝ) p).trans
    nativeProductPlaneEquiv.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source p := by simp [mem_chart_source]
  chart_mem_atlas p := ⟨chartAt (ModelProd ℝ ℝ) p, chart_mem_atlas _ _, rfl⟩

local instance : ChartedSpace OAI.ClosedSurfaceR4.Plane M := nativeProductPlaneChartedSpace M

@[simp] theorem nativeProductPlane_chartAt_apply (p q : M) :
    chartAt OAI.ClosedSurfaceR4.Plane p q =
      nativeProductPlaneEquiv (chartAt (ModelProd ℝ ℝ) p q) := rfl

@[simp] theorem nativeProductPlane_chartAt_symm_apply (p : M)
    (q : OAI.ClosedSurfaceR4.Plane) :
    (chartAt OAI.ClosedSurfaceR4.Plane p).symm q =
      (chartAt (ModelProd ℝ ℝ) p).symm (nativeProductPlaneEquiv.symm q) := rfl

@[simp] theorem nativeProductPlane_extChartAt_apply (p q : M) :
    extChartAt OAI.ClosedSurfaceR4.planeModel p q =
      nativeProductPlaneEquiv (extChartAt nativeProductModel p q) := rfl

@[simp] theorem nativeProductPlane_extChartAt_symm_apply (p : M)
    (q : OAI.ClosedSurfaceR4.Plane) :
    (extChartAt OAI.ClosedSurfaceR4.planeModel p).symm q =
      (extChartAt nativeProductModel p).symm (nativeProductPlaneEquiv.symm q) := rfl

/-- The identity of the underlying carrier is smooth between the two atlases. -/
theorem nativeProductPlane_identity_contMDiff :
    ContMDiff nativeProductModel OAI.ClosedSurfaceR4.planeModel ∞ (id : M → M) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  have he : (extChartAt OAI.ClosedSurfaceR4.planeModel p ∘ id ∘
      (extChartAt nativeProductModel p).symm) =ᶠ[𝓝 (extChartAt nativeProductModel p p)]
      nativeProductPlaneEquiv := by
    have h := (chartAt (ModelProd ℝ ℝ) p).eventually_right_inverse'
      (mem_chart_source _ p)
    filter_upwards [h] with q hq
    change nativeProductPlaneEquiv (chartAt (ModelProd ℝ ℝ) p
      ((chartAt (ModelProd ℝ ℝ) p).symm q)) = nativeProductPlaneEquiv q
    rw [hq]
  exact (nativeProductPlaneEquiv.contDiff.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt

/-- The inverse identity is smooth as well. -/
theorem nativeProductPlane_inverse_contMDiff :
    ContMDiff OAI.ClosedSurfaceR4.planeModel nativeProductModel ∞ (id : M → M) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  have he : (extChartAt nativeProductModel p ∘ id ∘
      (extChartAt OAI.ClosedSurfaceR4.planeModel p).symm) =ᶠ[
        𝓝 (extChartAt OAI.ClosedSurfaceR4.planeModel p p)] nativeProductPlaneEquiv.symm := by
    have h := (chartAt OAI.ClosedSurfaceR4.Plane p).eventually_right_inverse'
      (mem_chart_source _ p)
    filter_upwards [h] with q hq
    apply nativeProductPlaneEquiv.injective
    change nativeProductPlaneEquiv (chartAt (ModelProd ℝ ℝ) p
      ((chartAt (ModelProd ℝ ℝ) p).symm (nativeProductPlaneEquiv.symm q))) =
        nativeProductPlaneEquiv (nativeProductPlaneEquiv.symm q)
    exact hq.trans (nativeProductPlaneEquiv.apply_symm_apply q).symm
  exact (nativeProductPlaneEquiv.symm.contDiff.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt

/-- Actual derivative of the atlas-changing identity, not a formal tangent tag identification. -/
theorem nativeProductPlane_identity_hasMFDerivAt (p : M) :
    HasMFDerivAt nativeProductModel OAI.ClosedSurfaceR4.planeModel (id : M → M) p
      nativeProductPlaneEquiv.toContinuousLinearMap := by
  refine ⟨continuousAt_id, ?_⟩
  have he : writtenInExtChartAt nativeProductModel OAI.ClosedSurfaceR4.planeModel p
      (id : M → M) =ᶠ[𝓝 (extChartAt nativeProductModel p p)] nativeProductPlaneEquiv := by
    have h := (chartAt (ModelProd ℝ ℝ) p).eventually_right_inverse'
      (mem_chart_source _ p)
    filter_upwards [h] with q hq
    change nativeProductPlaneEquiv (chartAt (ModelProd ℝ ℝ) p
      ((chartAt (ModelProd ℝ ℝ) p).symm q)) = nativeProductPlaneEquiv q
    rw [hq]
  exact (nativeProductPlaneEquiv.hasFDerivAt.congr_of_eventuallyEq he).hasFDerivWithinAt

theorem nativeProductPlane_inverse_hasMFDerivAt (p : M) :
    HasMFDerivAt OAI.ClosedSurfaceR4.planeModel nativeProductModel (id : M → M) p
      nativeProductPlaneEquiv.symm.toContinuousLinearMap := by
  refine ⟨continuousAt_id, ?_⟩
  have he : writtenInExtChartAt OAI.ClosedSurfaceR4.planeModel nativeProductModel p
      (id : M → M) =ᶠ[𝓝 (extChartAt OAI.ClosedSurfaceR4.planeModel p p)]
        nativeProductPlaneEquiv.symm := by
    have h := (chartAt OAI.ClosedSurfaceR4.Plane p).eventually_right_inverse'
      (mem_chart_source _ p)
    filter_upwards [h] with q hq
    apply nativeProductPlaneEquiv.injective
    exact hq.trans (nativeProductPlaneEquiv.apply_symm_apply q).symm
  exact (nativeProductPlaneEquiv.symm.hasFDerivAt.congr_of_eventuallyEq he).hasFDerivWithinAt

/-- Smoothness of any map out of the native source is unchanged by the atlas transport. -/
theorem nativeProductPlane_contMDiff_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : M → V) :
    ContMDiff OAI.ClosedSurfaceR4.planeModel 𝓘(ℝ, V) ∞ F ↔
      ContMDiff nativeProductModel 𝓘(ℝ, V) ∞ F := by
  constructor
  · intro h
    exact h.comp (nativeProductPlane_identity_contMDiff M)
  · intro h
    exact h.comp (nativeProductPlane_inverse_contMDiff M)

/-- The native smooth atlas gives a genuine smooth plane atlas. -/
theorem nativeProductPlane_isManifold [IsManifold nativeProductModel ∞ M] :
    IsManifold OAI.ClosedSurfaceR4.planeModel ∞ M := by
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have hd : ContDiffOn (E := ℝ × ℝ) (F := ℝ × ℝ) ℝ ∞ (fun q : ℝ × ℝ => ((a.symm.trans b) q : ℝ × ℝ))
      (show Set (ℝ × ℝ) from (a.symm.trans b).source) := by
    have h := ((contDiffGroupoid ∞ nativeProductModel).compatible ha hb).1
    dsimp [contDiffPregroupoid] at h
    convert! h using 1 <;> simp [nativeProductModel, Function.comp_def]
  have hcomp := nativeProductPlaneEquiv.contDiff.comp_contDiffOn
    (hd.comp nativeProductPlaneEquiv.symm.contDiff.contDiffOn
      (mapsTo_preimage _ _))
  convert! hcomp using 1 <;>
    simp [preimage_preimage, Function.comp_def]
  rfl

end Atlas
end
end TightVer401








