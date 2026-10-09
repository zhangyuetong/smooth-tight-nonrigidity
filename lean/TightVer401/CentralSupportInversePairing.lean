import TightVer401.CentralSupportBilinear
import TightVer401.GaussSupportReconstruction

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The Hessian-plus-metric support tensor is evaluated through the actual
smooth Gauss inverse and the actual support height. -/
theorem supportInverse_bilinear_pairing {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1)
    (e : OpenPartialHomeomorph Coord Coord) (heU : e.source ⊆ U)
    (heI : ContDiffOn ℝ ∞ e.symm e.target)
    (heN : ∀ q ∈ e.source, N q = sphereHemisphere w hw (e q))
    {p : Coord} (hp : p ∈ e.source) (heD : DifferentiableAt ℝ e p) (v z : Coord) :
    sphereSupportTensorBilinear (inducedMetric (sphereHemisphere w hw))
      (fun y => inner ℝ (X (e.symm y)) (sphereHemisphere w hw y)) (e p)
      (fderiv ℝ e p v) (fderiv ℝ e p z) =
      inner ℝ (fderiv ℝ X p v) (fderiv ℝ N p z) := by
  let Q := sphereHemisphere w hw
  let H : Coord → ℝ := fun y => inner ℝ (X (e.symm y)) (Q y)
  let A := sphereSupportMap (inducedMetric Q) Q H
  have hQ := sphereHemisphere_contDiff w hw hu
  have hg := sphereHemisphere_metric w hw hu
  have hX' : ContDiffOn ℝ ∞ (X ∘ e.symm) e.target :=
    hX.comp heI (fun y hy => heU (e.map_target hy))
  have hH : ContDiffOn ℝ ∞ H e.target := hX'.inner ℝ hQ.contDiffOn
  have hmetric : SmoothPositiveOn (inducedMetric Q) e.target :=
    ⟨fun i j => (hg.1.1 i j).mono (subset_univ _), fun y _ => hg.1.2 y (mem_univ y)⟩
  have hQmetric : IsometricOn (inducedMetric Q) Q e.target :=
    ⟨hg.2.1.mono (subset_univ _), fun y _ => hg.2.2 y (mem_univ y)⟩
  have hunit : ∀ y ∈ e.target, inner ℝ (Q y) (Q y) = 1 := by
    intro y _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w hw hu, one_pow]
  have hep : e p ∈ e.target := e.map_source hp
  have hA : DifferentiableAt ℝ A (e p) :=
    ((sphereSupportMap_contDiffOn hmetric hQ.contDiffOn hH e.open_target) _ hep).contDiffAt
      (e.open_target.mem_nhds hep) |>.differentiableAt (by simp)
  have hreconstruction := support_reconstruction_from_inverse_coordinates
    hX hU hn w hw hu e heU heI heN
  have hXA : X =ᶠ[𝓝 p] (A ∘ e) := by
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    have h := hreconstruction (e q) (e.map_source hq)
    simpa only [e.left_inv hq, Function.comp_apply, A, H, Q] using h
  have hNQ : N =ᶠ[𝓝 p] (Q ∘ e) := by
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact heN q hq
  have hDX : fderiv ℝ X p = (fderiv ℝ A (e p)).comp (fderiv ℝ e p) := by
    rw [hXA.fderiv_eq]
    exact fderiv_comp p hA heD
  have hDN : fderiv ℝ N p = (fderiv ℝ Q (e p)).comp (fderiv ℝ e p) := by
    rw [hNQ.fderiv_eq]
    exact fderiv_comp p (hQ.differentiable (by simp) _) heD
  have hv : fderiv ℝ A (e p) (fderiv ℝ e p v) = fderiv ℝ X p v :=
    (congrArg (fun D : Coord →L[ℝ] Ambient => D v) hDX).symm
  have hz : fderiv ℝ Q (e p) (fderiv ℝ e p z) = fderiv ℝ N p z :=
    (congrArg (fun D : Coord →L[ℝ] Ambient => D z) hDN).symm
  change sphereSupportTensorBilinear (inducedMetric Q) H (e p)
    (fderiv ℝ e p v) (fderiv ℝ e p z) = _
  rw [sphereSupportTensorBilinear_eq_differential hmetric hQmetric hH e.open_target hep hunit,
    hv, hz]

end
end TightVer401
