import TightVer401.SphereHemisphere
import TightVer401.RegularLocalInverse

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def gaussCoordinate (w : Ambient) (hw : w ≠ 0) (N : Coord → Ambient) : Coord → Coord :=
  fun p => sphereHemisphereInverse w hw (N p)

theorem gaussCoordinate_differential_injective {N : Coord → Ambient} {U : Set Coord}
    (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U) (hunit : ∀ q ∈ U, ‖N q‖ = 1)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {p : Coord} (hp : p ∈ U)
    (hpos : 0 < inner ℝ w (N p)) (hi : Function.Injective (fderiv ℝ N p)) :
    Function.Injective (fderiv ℝ (gaussCoordinate w hw N) p) := by
  have hNa := (hN p hp).contDiffAt (hU.mem_nhds hp)
  have hC := (sphereHemisphereInverse_contDiffAt w hw hpos).comp p hNa
  have hV : IsOpen (U ∩ N ⁻¹' {u | 0 < inner ℝ w u}) :=
    hN.continuousOn.isOpen_inter_preimage hU
      (isOpen_lt continuous_const (continuous_const.inner continuous_id))
  have he : N =ᶠ[𝓝 p] (fun q => sphereHemisphere w hw (gaussCoordinate w hw N q)) := by
    filter_upwards [hV.mem_nhds ⟨hp, hpos⟩] with q hq
    exact (sphereHemisphere_right_inverse w hw hu (hunit q hq.1) hq.2).symm
  have hd : fderiv ℝ N p = (fderiv ℝ (sphereHemisphere w hw) (gaussCoordinate w hw N p)).comp
      (fderiv ℝ (gaussCoordinate w hw N) p) := by
    rw [he.fderiv_eq]
    exact fderiv_comp p ((sphereHemisphere_contDiff w hw hu).contDiffAt.differentiableAt (by simp))
      (hC.differentiableAt (by simp))
  intro v z hvz
  apply hi
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, hvz]

theorem gaussMap_exists_smooth_inverse_coordinates {N : Coord → Ambient} {U : Set Coord}
    (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U) (hunit : ∀ q ∈ U, ‖N q‖ = 1)
    (hi : ∀ q ∈ U, Function.Injective (fderiv ℝ N q))
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {p : Coord} (hp : p ∈ U)
    (hpos : 0 < inner ℝ w (N p)) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ U ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (e : Coord → Coord) = gaussCoordinate w hw N ∧
      (∀ q ∈ e.source, N q = sphereHemisphere w hw (e q)) := by
  let V := U ∩ N ⁻¹' {u | 0 < inner ℝ w u}
  have hV : IsOpen V := hN.continuousOn.isOpen_inter_preimage hU
    (isOpen_lt continuous_const (continuous_const.inner continuous_id))
  have hC : ContDiffOn ℝ ∞ (gaussCoordinate w hw N) V := by
    intro q hq
    exact ((sphereHemisphereInverse_contDiffAt w hw hq.2).comp q
      ((hN q hq.1).contDiffAt (hU.mem_nhds hq.1))).contDiffWithinAt
  have hCi : ∀ q ∈ V, Function.Injective (fderiv ℝ (gaussCoordinate w hw N) q) := by
    intro q hq
    exact gaussCoordinate_differential_injective hN hU hunit w hw hu hq.1 hq.2 (hi q hq.1)
  obtain ⟨e, hep, hes, hef, hei⟩ := exists_smooth_local_inverse hV hC hCi (p := p) ⟨hp, hpos⟩
  refine ⟨e, hep, (fun q hq => (hes hq).1), hei, hef, ?_⟩
  intro q hq
  rw [hef]
  exact (sphereHemisphere_right_inverse w hw hu (hunit q (hes hq).1) (hes hq).2).symm

end
end TightVer401
