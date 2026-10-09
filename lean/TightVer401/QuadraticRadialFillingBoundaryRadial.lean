import TightVer401.QuadraticRadialFillingExteriorCollar
import TightVer401.QuadraticRadialFillingCircle
import TightVer401.QuadraticRadialFillingTraces

/-! Actual positive radial pairing persists on an incoming boundary collar. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology BigOperators

/-- Every point of the actual positive radius level has a real polar angle.
The underlying circle and coordinate maps are retained actual constructions. -/
theorem quadraticRadialFilling_radiusLevel_exists_polar {R : ℝ} (hR : 0 < R)
    {x : Coord} (hx : x ∈ quadraticRadialFillingRadiusLevel R) :
    ∃ θ : ℝ, saddlePolarChart ![R, θ] = x := by
  change planarRadius x = R at hx
  have hz : angularDescentComplex x ∈ range (circleMap 0 R) := by
    rw [range_circleMap]
    simpa only [Metric.mem_sphere, dist_zero_right, angularDescentComplex_norm,
      abs_of_pos hR] using hx
  obtain ⟨θ, hθ⟩ := hz
  refine ⟨θ, ?_⟩
  rw [← quadraticRadialFillingCircle_coord]
  change seamComplexCoord (circleMap 0 R θ) = x
  rw [hθ, quadraticRadialFillingCoord_complex]

/-- The physical circle position is exactly `R` times its outward radial
unit vector; this converts the given geometric radial-gradient condition. -/
theorem quadraticRadialFilling_polar_radial_pairing (F : Coord → ℝ) (R θ : ℝ) :
    planarGradient F (saddlePolarChart ![R, θ]) ⬝ᵥ saddlePolarChart ![R, θ] =
      R * (planarGradient F (saddlePolarChart ![R, θ]) ⬝ᵥ
        quadraticRadialFillingRadialUnit θ) := by
  simp [saddlePolarChart, quadraticRadialFillingRadialUnit, dotProduct, Fin.sum_univ_two]
  ring

/-- Actual incoming radial positivity gives an actual open positive
neighborhood of the entire seam circle. -/
theorem quadraticRadialFilling_positive_radial_neighborhood
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    (hCircleU : quadraticRadialFillingRadiusLevel R ⊆ U)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R, θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ) :
    ∃ W : Set Coord, IsOpen W ∧ W ⊆ U ∧
      quadraticRadialFillingRadiusLevel R ⊆ W ∧
      ∀ x ∈ W, 0 < planarGradient F x ⬝ᵥ x := by
  let a : Coord → ℝ := fun x => planarGradient F x ⬝ᵥ x
  let W : Set Coord := U ∩ a ⁻¹' Ioi 0
  have hgrad : ContinuousOn (planarGradient F) U :=
    (planarGradient_contDiffOn hF hU).continuousOn
  have ha : ContinuousOn a U := by
    unfold a dotProduct
    exact continuousOn_finsetSum _ (fun i _ =>
      ((continuousOn_pi.mp hgrad) i).mul (continuous_apply i).continuousOn)
  have hW : IsOpen W := ha.isOpen_inter_preimage hU isOpen_Ioi
  refine ⟨W, hW, inter_subset_left, ?_, fun _ hx => hx.2⟩
  intro x hx
  refine ⟨hCircleU hx, ?_⟩
  obtain ⟨θ, hθ⟩ := quadraticRadialFilling_radiusLevel_exists_polar hR hx
  change 0 < planarGradient F x ⬝ᵥ x
  rw [← hθ, quadraticRadialFilling_polar_radial_pairing]
  exact mul_pos hR (hRadial θ)

/-- The positive seam trace supplies a uniform radial collar on which the
actual incoming gradient remains positively radial and never vanishes. -/
theorem quadraticRadialFilling_exists_positive_radial_collar
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    (hCircleU : quadraticRadialFillingRadiusLevel R ⊆ U)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R, θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ x : Coord, |planarRadius x - R| < δ →
      x ∈ U ∧ 0 < planarGradient F x ⬝ᵥ x ∧ planarGradient F x ≠ 0 := by
  obtain ⟨W, hW, hWU, hCircleW, hpositive⟩ :=
    quadraticRadialFilling_positive_radial_neighborhood hF hU hR hCircleU hRadial
  obtain ⟨δ, hδ, hδR, hcollar⟩ :=
    quadraticRadialFilling_exists_radial_collar hR hW hCircleW
  refine ⟨δ, hδ, hδR, ?_⟩
  intro x hx
  have hxW : x ∈ W := hcollar x hx
  have hp : 0 < planarGradient F x ⬝ᵥ x := hpositive x hxW
  refine ⟨hWU hxW, hp, ?_⟩
  intro hzero
  simpa [hzero, dotProduct] using hp

end
end TightVer401
