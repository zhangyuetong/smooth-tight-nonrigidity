import TightVer401.AngularDescentCharts
import TightVer401.PlanarSupportCurvature

/-! A derived open saddle neighborhood for a Cartesian filler.
The input is the actual determinant inequality on the closed punctured disk;
no exterior collar or curvature conclusion is assumed. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- The canonical saddle locus inside the smooth positive-radius domain. -/
def quadraticFillerCartesianSaddleNeighborhood (F : Coord → ℝ) : Set Coord :=
  {p | 0 < planarRadius p} ∩ (fun p => (planarHessian F p).det) ⁻¹' Iio 0

/-- Strict actual Hessian sign supplies an open neighborhood of the whole closed
punctured disk, including every point of its outer seam. -/
theorem quadraticFillerCartesian_exists_open_saddle_neighborhood
    {F : Coord → ℝ} {R : ℝ}
    (hF : ContDiffOn ℝ ∞ F {p | 0 < planarRadius p})
    (hdet : ∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R →
      (planarHessian F p).det < 0) :
    ∃ U : Set Coord, IsOpen U ∧ U ⊆ {p | 0 < planarRadius p} ∧
      (∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R → p ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧
      (∀ p ∈ U, (planarHessian F p).det < 0) ∧
      (∀ p ∈ U, gaussianCurvature (inducedMetric (planarSupportMap F)) p < 0) := by
  have hrad : Continuous planarRadius := by
    simpa only [angularDescentComplex_norm] using angularDescentComplex_contDiff.continuous.norm
  have hpos : IsOpen ({p | 0 < planarRadius p} : Set Coord) :=
    isOpen_lt continuous_const hrad
  let U := quadraticFillerCartesianSaddleNeighborhood F
  have hU : IsOpen U :=
    (planarHessian_det_contDiffOn hF hpos).continuousOn.isOpen_inter_preimage hpos isOpen_Iio
  have hsub : U ⊆ {p | 0 < planarRadius p} := inter_subset_left
  have hFU : ContDiffOn ℝ ∞ F U := hF.mono hsub
  refine ⟨U, hU, hsub, ?_, hFU, ?_, ?_⟩
  · intro p hp hpR
    exact ⟨hp, hdet p hp hpR⟩
  · intro p hp
    exact hp.2
  · intro p hp
    exact (planarSupportMap_negative_curvature_iff hFU hU hp hp.2.ne).mpr hp.2

end
end TightVer401
