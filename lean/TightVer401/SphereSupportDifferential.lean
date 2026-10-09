import TightVer401.SphereSupportConverse

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem coordPartial_inner {F G : Coord → Ambient} {p : Coord}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (i : Fin 2) :
    coordPartial i (fun q => inner ℝ (F q) (G q)) p =
      inner ℝ (F p) (coordPartial i G p) + inner ℝ (coordPartial i F p) (G p) := by
  unfold coordPartial
  rw [fderiv_inner_apply ℝ hF hG]

theorem coordPartial_eventuallyEq {f h : Coord → ℝ} {p : Coord}
    (he : f =ᶠ[𝓝 p] h) (i : Fin 2) : coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [he.fderiv_eq]

theorem sphereGradient_derivative_normal {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (i : Fin 2) :
    inner ℝ (coordPartial i (sphereGradient g Q H) p) (Q p) = -coordPartial i H p := by
  have hG := sphereGradient_contDiffOn hg hQ.1 hH hU
  have hdG := ((hG p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdQ := ((hQ.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have he : (fun q => inner ℝ (sphereGradient g Q H q) (Q q)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact sphereGradient_normal_pairing hQ.1 hU hq hunit
  have hi := coordPartial_eventuallyEq he i
  rw [coordPartial_inner hdG hdQ, sphereGradient_pairing hg hQ hp] at hi
  have hz : coordPartial i (fun _ : Coord => (0 : ℝ)) p = 0 := by
    unfold coordPartial
    rw [(hasFDerivAt_const (c := (0 : ℝ)) p).fderiv]
    rfl
  rw [hz] at hi
  linarith

theorem sphereGradient_derivative_tangent {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (i j : Fin 2) :
    inner ℝ (coordPartial i (sphereGradient g Q H) p) (coordPartial j Q p) = covHessian g H p i j := by
  have hG := sphereGradient_contDiffOn hg hQ.1 hH hU
  have hdG := ((hG p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdj := (((partial_contDiffOn hQ.1 hU j) p hp).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have he : (fun q => inner ℝ (sphereGradient g Q H q) (coordPartial j Q q)) =ᶠ[𝓝 p]
      (coordPartial j H) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact sphereGradient_pairing hg hQ hq j
  have hi := coordPartial_eventuallyEq he i
  rw [coordPartial_inner hdG hdj, sphere_gauss_decomposition hg hQ hU hp hunit,
    inner_sub_right, inner_sum] at hi
  simp only [real_inner_smul_right, sphereGradient_pairing hg hQ hp,
    sphereGradient_normal_pairing hQ.1 hU hp hunit, mul_zero, sub_zero] at hi
  unfold covHessian
  linarith

theorem sphereSupportMap_partial {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i : Fin 2) :
    coordPartial i (sphereSupportMap g Q H) p =
      coordPartial i (sphereGradient g Q H) p +
        coordPartial i H p • Q p + H p • coordPartial i Q p := by
  have hG := sphereGradient_contDiffOn hg hQ.1 hH hU
  have hdG := ((hG p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdQ := ((hQ.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdH := ((hH p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  change (fderiv ℝ (sphereGradient g Q H + H • Q) p) (Pi.single i 1) =
    (fderiv ℝ (sphereGradient g Q H) p) (Pi.single i 1) +
      (fderiv ℝ H p) (Pi.single i 1) • Q p + H p • (fderiv ℝ Q p) (Pi.single i 1)
  rw [fderiv_add hdG (hdH.smul hdQ), fderiv_smul hdH hdQ]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  module

theorem sphereSupportMap_differential_pairings {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (i j : Fin 2) :
    inner ℝ (coordPartial i (sphereSupportMap g Q H) p) (Q p) = 0 ∧
    inner ℝ (coordPartial i (sphereSupportMap g Q H) p) (coordPartial j Q p) =
      covHessian g H p i j + H p * g p i j := by
  have horth (k : Fin 2) : inner ℝ (coordPartial k Q p) (Q p) = 0 :=
    sphere_differential_orthogonal hQ.1 hU hp hunit _
  have horth' (k : Fin 2) : inner ℝ (Q p) (coordPartial k Q p) = 0 := by
    rw [real_inner_comm]; exact horth k
  have hind : inner ℝ (coordPartial i Q p) (coordPartial j Q p) = g p i j :=
    congrFun (congrFun (inducedMetric_eq_of_isometric hQ hp) i) j
  rw [sphereSupportMap_partial hg hQ hH hU hp]
  simp only [inner_add_left, real_inner_smul_left,
    sphereGradient_derivative_normal hg hQ hH hU hp hunit,
    sphereGradient_derivative_tangent hg hQ hH hU hp hunit,
    hunit p hp, horth, horth', hind, mul_zero, mul_one, add_zero, neg_add_cancel, zero_add, and_self]

end
end TightVer401
