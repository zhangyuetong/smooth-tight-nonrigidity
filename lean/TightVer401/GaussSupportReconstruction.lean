import TightVer401.GaussInverseCoordinates
import TightVer401.GaussMapDifferential

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem support_reconstruction_from_inverse_coordinates {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) (e : OpenPartialHomeomorph Coord Coord)
    (heU : e.source ⊆ U) (he : ContDiffOn ℝ ∞ e.symm e.target)
    (heN : ∀ q ∈ e.source, N q = sphereHemisphere w hw (e q)) :
    ∀ y ∈ e.target, X (e.symm y) =
      sphereSupportMap (inducedMetric (sphereHemisphere w hw)) (sphereHemisphere w hw)
        (fun z => inner ℝ (X (e.symm z)) (sphereHemisphere w hw z)) y := by
  let Q := sphereHemisphere w hw
  have hmaps : MapsTo e.symm e.target U := fun y hy => heU (e.map_target hy)
  have hX' : ContDiffOn ℝ ∞ (fun y => X (e.symm y)) e.target := hX.comp he hmaps
  have hN' : ∀ y ∈ e.target, N (e.symm y) = Q y := by
    intro y hy
    rw [heN _ (e.map_target hy), e.right_inv hy]
  have hn' : ∀ y ∈ e.target, IsUnitNormalAt (fun z => X (e.symm z)) (Q y) y := by
    intro y hy
    have hx := hmaps hy
    have hnormal := hn _ hx
    rw [hN' y hy] at hnormal
    refine ⟨hnormal.1, ?_⟩
    intro v
    have hdX := ((hX _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdI := ((he _ hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
    have hd := fderiv_comp y hdX hdI
    change fderiv ℝ (fun z => X (e.symm z)) y =
      (fderiv ℝ X (e.symm y)).comp (fderiv ℝ e.symm y) at hd
    rw [hd]
    exact hnormal.2 _
  have hg := sphereHemisphere_metric w hw hu
  have hg' : SmoothPositiveOn (inducedMetric Q) e.target :=
    ⟨fun i j => (hg.1.1 i j).mono (subset_univ _), fun y _ => hg.1.2 y (mem_univ y)⟩
  have hQ' : IsometricOn (inducedMetric Q) Q e.target :=
    ⟨hg.2.1.mono (subset_univ _), fun y _ => hg.2.2 y (mem_univ y)⟩
  exact sphereSupportMap_converse_local hg' hQ' hX' e.open_target hn'

theorem gaussSupport_reconstruction_local {g : MetricField} {X N : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hX : IsometricOn g X U) (hN : ContDiffOn ℝ ∞ N U)
    (hU : IsOpen U) (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q)
    (hK : ∀ q ∈ U, gaussianCurvature g q ≠ 0) {p : Coord} (hp : p ∈ U) :
    ∃ (hw : N p ≠ 0) (hu : ‖N p‖ = 1) (e : OpenPartialHomeomorph Coord Coord),
      p ∈ e.source ∧ e.source ⊆ U ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ q ∈ e.source, N q = sphereHemisphere (N p) hw (e q)) ∧
      (∀ y ∈ e.target, X (e.symm y) =
        sphereSupportMap (inducedMetric (sphereHemisphere (N p) hw)) (sphereHemisphere (N p) hw)
          (fun z => inner ℝ (X (e.symm z)) (sphereHemisphere (N p) hw z)) y) := by
  have hunit : ∀ q ∈ U, ‖N q‖ = 1 := by
    intro q hq
    have hh := (hn q hq).1
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (N q)]
  have hw : N p ≠ 0 := norm_ne_zero_iff.mp (by rw [hunit p hp]; exact one_ne_zero)
  have hpos : 0 < inner ℝ (N p) (N p) := by rw [(hn p hp).1]; exact zero_lt_one
  have hi : ∀ q ∈ U, Function.Injective (fderiv ℝ N q) :=
    fun q hq => gaussMap_differential_injective hg hX hN hU hn hq (hK q hq)
  obtain ⟨e, hep, heU, he, _, heN⟩ := gaussMap_exists_smooth_inverse_coordinates
    hN hU hunit hi (N p) hw (hunit p hp) hp hpos
  exact ⟨hw, hunit p hp, e, hep, heU, he, heN,
    support_reconstruction_from_inverse_coordinates hX.1 hU hn (N p) hw (hunit p hp) e heU he heN⟩

end
end TightVer401
