import TightVer401.ProtectedTorusBandPhase
import TightVer401.CompletedSaddleAnnulusGeometryOutput
import TightVer401.ProtectedTorusMap

/-! The constructed protected cylinder coordinates followed by the literal
saddle phase chart. This connects the same actual band to the same torus map;
no support completion, curvature, or protected-coordinate conclusion is assumed. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

variable {T w RN μ h : ℝ} [Fact (0 < T)]
variable {d : PeriodicRuledFrame T} {K : Set (AddCircle T × Ioo (0 : ℝ) w)}
variable (Q : CompletedSaddleAnnulusGeometryOutput d K RN μ h)

/-- Actual protected band coordinates in the native quotient torus. -/
def completedSaddleTorusBandChart :
    OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource :=
  Q.protectedBand.coordinates.trans protectedTorusPhaseChart

/-- All original protected coordinates already land in the saddle phase,
so composing with the quotient chart discards no original source point. -/
theorem completedSaddleTorusBandChart_source :
    (completedSaddleTorusBandChart Q).source = Q.protectedBand.coordinates.source := by
  change Q.protectedBand.coordinates.source ∩
    Q.protectedBand.coordinates ⁻¹' protectedTorusPhaseChart.source =
      Q.protectedBand.coordinates.source
  ext p
  constructor
  · exact fun hp => hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    rw [protectedTorusPhaseChart_source]
    exact Q.protectedBand.interior_target (Q.protectedBand.coordinates.map_source hp)

/-- The same supplied protected compact support remains in the actual source. -/
theorem completedSaddleTorusBandChart_protected_source :
    K ⊆ (completedSaddleTorusBandChart Q).source := by
  rw [completedSaddleTorusBandChart_source]
  exact Q.protectedBand.protected_source

/-- The actual native composed coordinate map is smooth on its actual source. -/
theorem completedSaddleTorusBandChart_forward_smooth :
    ContMDiffOn nativeProductModel nativeProductModel ∞
      (completedSaddleTorusBandChart Q) (completedSaddleTorusBandChart Q).source := by
  change ContMDiffOn nativeProductModel nativeProductModel ∞
    (protectedTorusPhaseChart ∘ Q.protectedBand.coordinates)
    (Q.protectedBand.coordinates.source ∩
      Q.protectedBand.coordinates ⁻¹' protectedTorusPhaseChart.source)
  exact protectedTorusPhaseChart_forward_smooth.contMDiffOn.comp
    (Q.protectedBand.coordinates_smooth.mono inter_subset_left) (fun _ hp => hp.2)

/-- Actual inverse smoothness is the composition of the two audited inverse maps. -/
theorem completedSaddleTorusBandChart_inverse_smooth :
    ContMDiffOn nativeProductModel nativeProductModel ∞
      (completedSaddleTorusBandChart Q).symm (completedSaddleTorusBandChart Q).target := by
  change ContMDiffOn nativeProductModel nativeProductModel ∞
    (Q.protectedBand.coordinates.symm ∘ protectedTorusPhaseChart.symm)
    (protectedTorusPhaseChart.target ∩
      protectedTorusPhaseChart.symm ⁻¹' Q.protectedBand.coordinates.target)
  exact Q.protectedBand.inverse_smooth.comp
    (protectedTorusPhaseChart_inverse_smooth.mono inter_subset_left) (fun _ hp => hp.2)

/-- The protected image lies in the actual open saddle phase of the quotient torus. -/
theorem completedSaddleTorusBandChart_target_subset :
    (completedSaddleTorusBandChart Q).target ⊆ protectedTorusPhaseChart.target := by
  change protectedTorusPhaseChart.target ∩
    protectedTorusPhaseChart.symm ⁻¹' Q.protectedBand.coordinates.target ⊆
      protectedTorusPhaseChart.target
  exact inter_subset_left

/-- Literal affine placement for any meridian and height parameter: on the
actual saddle chart the torus map uses this same cylinder saddle. -/
theorem completedSaddleTorusBandChart_placement (r : ℝ → ℝ) (height : ℝ)
    {p : AddCircle T × Ioo (0 : ℝ) w}
    (hp : p ∈ (completedSaddleTorusBandChart Q).source) :
    protectedTorusMap Q.cylinder.saddle r height (completedSaddleTorusBandChart Q p) =
      -d.bandMap p + Q.verticalOffset • revolutionAxis := by
  have hpOld : p ∈ Q.protectedBand.coordinates.source := by
    rwa [completedSaddleTorusBandChart_source] at hp
  have hpPhase : Q.protectedBand.coordinates p ∈ protectedTorusPhaseChart.source := by
    rw [protectedTorusPhaseChart_source]
    exact Q.protectedBand.interior_target (Q.protectedBand.coordinates.map_source hpOld)
  change protectedTorusMap Q.cylinder.saddle r height
    (protectedTorusPhaseChart (Q.protectedBand.coordinates p)) = _
  rw [protectedTorusPhaseChart_map_source Q.cylinder.saddle r height hpPhase]
  exact Q.protectedBand.affine_eq p hpOld

private theorem saddlePhase_zero_not_mem_target :
    (0 : NonrigidTorusSource) ∉ protectedTorusPhaseChart.target := by
  intro hp
  have hsource := protectedTorusPhaseChart.map_target hp
  rw [protectedTorusPhaseChart_source] at hsource
  have hpositive := hsource.2.1
  change 0 < (periodChart (2 * Real.pi)).symm
    (0 : AddCircle (2 * Real.pi)) at hpositive
  have hinverse : (periodChart (2 * Real.pi)).symm
      (0 : AddCircle (2 * Real.pi)) = 0 := by
    have hz : periodChart (2 * Real.pi) (0 : ℝ) = 0 := rfl
    rw [← hz, (periodChart (2 * Real.pi)).left_inv (periodChart_zero_source _)]
  rw [hinverse] at hpositive
  exact (lt_irrefl (0 : ℝ)) hpositive

/-- A literal seam point lies outside the protected chart target. -/
theorem completedSaddleTorusBandChart_zero_not_mem_target :
    (0 : NonrigidTorusSource) ∉ (completedSaddleTorusBandChart Q).target := by
  intro hp
  exact saddlePhase_zero_not_mem_target
    (completedSaddleTorusBandChart_target_subset Q hp)

/-- The protected torus image is proper, without a supplied exterior-point premise. -/
theorem completedSaddleTorusBandChart_exists_outside :
    ∃ p : NonrigidTorusSource, p ∉ (completedSaddleTorusBandChart Q).target :=
  ⟨0, completedSaddleTorusBandChart_zero_not_mem_target Q⟩

/-- In particular the same protected support's image misses that actual seam point. -/
theorem completedSaddleTorusBandChart_zero_not_mem_protected_image :
    (0 : NonrigidTorusSource) ∉ (completedSaddleTorusBandChart Q) '' K := by
  rintro ⟨p, hp, he⟩
  apply completedSaddleTorusBandChart_zero_not_mem_target Q
  rw [← he]
  exact (completedSaddleTorusBandChart Q).map_source
    (completedSaddleTorusBandChart_protected_source Q hp)

end
end TightVer401
