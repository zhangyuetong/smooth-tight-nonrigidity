import TightVer401.QuadraticRadialFillingGradientJordan
import Mathlib.Topology.Homeomorph.Lemmas

/-! The actual complex gradient restriction gives a boundary component
homeomorphism from ordinary smoothness, injectivity and trace-image data. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem quadraticRadialFilling_complexSphere_coord_radius
    {S : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) S) :
    planarRadius (seamComplexCoord z) = S := by
  rw [quadraticRadialFillingRadius_complex]
  simpa only [Metric.mem_sphere, dist_zero_right] using hz

/-- Actual polar representatives identify the complex gradient image of the
source circle with the range of its actual complex angular trace. -/
theorem quadraticRadialFilling_complexGradient_image_sphere
    (H : Coord → ℝ) {S : ℝ} (hS : 0 < S) :
    (fun z : ℂ => angularDescentComplex (planarGradient H (seamComplexCoord z))) ''
        Metric.sphere (0 : ℂ) S =
      range (quadraticRadialFillingGradientComplexTrace H S) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ range (quadraticRadialFillingCircle S) := by
      change z ∈ range (circleMap 0 S)
      rw [range_circleMap]
      simpa only [abs_of_pos hS] using hz
    obtain ⟨s, hs⟩ := hz'
    refine ⟨s, ?_⟩
    change angularDescentComplex (planarGradient H (saddlePolarChart ![S,s])) =
      angularDescentComplex (planarGradient H (seamComplexCoord z))
    rw [← quadraticRadialFillingCircle_coord, hs]
  · rintro ⟨s, rfl⟩
    have hs : quadraticRadialFillingCircle S s ∈ Metric.sphere (0 : ℂ) S := by
      have hs' : circleMap 0 S s ∈ range (circleMap 0 S) := mem_range_self s
      rw [range_circleMap] at hs'
      simpa only [quadraticRadialFillingCircle, abs_of_pos hS] using hs'
    refine ⟨quadraticRadialFillingCircle S s, hs, ?_⟩
    change angularDescentComplex
        (planarGradient H (seamComplexCoord (quadraticRadialFillingCircle S s))) =
      angularDescentComplex (planarGradient H (saddlePolarChart ![S,s]))
    rw [quadraticRadialFillingCircle_coord]

/-- Ordinary injectivity of the actual Cartesian gradient on the radius
level transfers to its actual complex restriction on the complex sphere. -/
theorem quadraticRadialFilling_complexGradient_injOn_sphere
    {H : Coord → ℝ} {S : ℝ}
    (hinj : InjOn (planarGradient H) {x : Coord | planarRadius x = S}) :
    InjOn (fun z : ℂ => angularDescentComplex (planarGradient H (seamComplexCoord z)))
      (Metric.sphere (0 : ℂ) S) := by
  intro z hz w hw heq
  apply seamComplexCoord.injective
  exact hinj (quadraticRadialFilling_complexSphere_coord_radius hz)
    (quadraticRadialFilling_complexSphere_coord_radius hw)
    (quadraticRadialFillingComplex_injective heq)

/-- The actual complex gradient is continuous on the source circle because
the given potential is smooth on an actual open neighborhood of that circle. -/
theorem quadraticRadialFilling_complexGradient_continuousOn_sphere
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord}
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircleV : {x : Coord | planarRadius x = S} ⊆ V) :
    ContinuousOn
      (fun z : ℂ => angularDescentComplex (planarGradient H (seamComplexCoord z)))
      (Metric.sphere (0 : ℂ) S) := by
  apply angularDescentComplex_contDiff.continuous.comp_continuousOn'
  apply (planarGradient_contDiffOn hH hV).continuousOn.comp'
    seamComplexCoord.continuous.continuousOn
  intro z hz
  exact hCircleV (quadraticRadialFilling_complexSphere_coord_radius hz)

/-- Construct a boundary component homeomorphism to the stated actual trace
image by compactness and actual gradient injectivity. No boundary
homeomorphism, degree or interior image is an input. -/
def quadraticRadialFillingGradientComponentHomeomorph
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord} {Γ : ℂ → ℂ}
    (hS : 0 < S) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircleV : {x : Coord | planarRadius x = S} ⊆ V)
    (hinj : InjOn (planarGradient H) {x : Coord | planarRadius x = S})
    (hTrace : range (quadraticRadialFillingGradientComplexTrace H S) =
      Γ '' Metric.sphere (0 : ℂ) 1) :
    Metric.sphere (0 : ℂ) S ≃ₜ Γ '' Metric.sphere (0 : ℂ) 1 := by
  let G : ℂ → ℂ := fun z =>
    angularDescentComplex (planarGradient H (seamComplexCoord z))
  letI : CompactSpace (Metric.sphere (0 : ℂ) S) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) S)
  let e : Metric.sphere (0 : ℂ) S ≃ G '' Metric.sphere (0 : ℂ) S :=
    Equiv.Set.imageOfInjOn G (Metric.sphere (0 : ℂ) S)
      (quadraticRadialFilling_complexGradient_injOn_sphere hinj)
  have he : Continuous e :=
    (quadraticRadialFilling_complexGradient_continuousOn_sphere hV hH hCircleV).domRestrict.subtype_mk
      (fun z => mem_image_of_mem G z.property)
  have htarget : G '' Metric.sphere (0 : ℂ) S = Γ '' Metric.sphere (0 : ℂ) 1 :=
    (quadraticRadialFilling_complexGradient_image_sphere H hS).trans hTrace
  exact (e.toHomeomorphOfContinuousClosed he he.isClosedMap).trans
    (Homeomorph.setCongr htarget)

theorem quadraticRadialFillingGradientComponentHomeomorph_apply
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord} {Γ : ℂ → ℂ}
    (hS : 0 < S) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircleV : {x : Coord | planarRadius x = S} ⊆ V)
    (hinj : InjOn (planarGradient H) {x : Coord | planarRadius x = S})
    (hTrace : range (quadraticRadialFillingGradientComplexTrace H S) =
      Γ '' Metric.sphere (0 : ℂ) 1)
    (z : Metric.sphere (0 : ℂ) S) :
    (quadraticRadialFillingGradientComponentHomeomorph hS hV hH hCircleV hinj hTrace z : ℂ) =
      angularDescentComplex (planarGradient H (seamComplexCoord z)) := rfl

theorem quadraticRadialFilling_exists_gradient_component_homeomorph
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord} {Γ : ℂ → ℂ}
    (hS : 0 < S) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircleV : {x : Coord | planarRadius x = S} ⊆ V)
    (hinj : InjOn (planarGradient H) {x : Coord | planarRadius x = S})
    (hTrace : range (quadraticRadialFillingGradientComplexTrace H S) =
      Γ '' Metric.sphere (0 : ℂ) 1) :
    ∃ Φ : Metric.sphere (0 : ℂ) S ≃ₜ Γ '' Metric.sphere (0 : ℂ) 1,
      ∀ z : Metric.sphere (0 : ℂ) S,
        (Φ z : ℂ) = angularDescentComplex (planarGradient H (seamComplexCoord z)) :=
  ⟨quadraticRadialFillingGradientComponentHomeomorph hS hV hH hCircleV hinj hTrace,
    quadraticRadialFillingGradientComponentHomeomorph_apply hS hV hH hCircleV hinj hTrace⟩

end
end TightVer401
