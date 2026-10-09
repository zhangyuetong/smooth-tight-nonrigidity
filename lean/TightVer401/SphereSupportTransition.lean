import TightVer401.SphereSupportCurvature

/-! Coordinate invariance follows from the actual chain rule and the gradient's
duality characterization. No Hessian transformation law is assumed. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem sphereGradient_differential_pairing {g : MetricField} {Q : Coord → Ambient}
    {H : Coord → ℝ} {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    {p : Coord} (hp : p ∈ U) (v : Coord) :
    inner ℝ (sphereGradient g Q H p) (fderiv ℝ Q p v) = fderiv ℝ H p v := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  rw [fderiv_two_coordinates]
  simp only [inner_add_right, real_inner_smul_right, sphereGradient_pairing hg hQ hp]
  conv_rhs => rw [hv]
  simp only [map_add, map_smul, coordPartial, smul_eq_mul]

theorem sphereGradient_coordinate_change {g₁ g₂ : MetricField}
    {Q₁ Q₂ : Coord → Ambient} {H₁ H₂ : Coord → ℝ} {C : Coord → Coord}
    {U₁ U₂ : Set Coord} (hg₁ : SmoothPositiveOn g₁ U₁) (hg₂ : SmoothPositiveOn g₂ U₂)
    (hQ₁ : IsometricOn g₁ Q₁ U₁) (hQ₂ : IsometricOn g₂ Q₂ U₂)
    (hH₂ : ContDiffOn ℝ ∞ H₂ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {p : Coord} (hp : p ∈ U₁) (hCp : C p ∈ U₂) (hC : DifferentiableAt ℝ C p)
    (hQeq : Q₁ =ᶠ[𝓝 p] (fun q => Q₂ (C q)))
    (hHeq : H₁ =ᶠ[𝓝 p] (fun q => H₂ (C q)))
    (hunit₁ : ∀ q ∈ U₁, inner ℝ (Q₁ q) (Q₁ q) = 1)
    (hunit₂ : ∀ q ∈ U₂, inner ℝ (Q₂ q) (Q₂ q) = 1) :
    sphereGradient g₁ Q₁ H₁ p = sphereGradient g₂ Q₂ H₂ (C p) := by
  have hdQ₂ := ((hQ₂.1 _ hCp).contDiffAt (hU₂.mem_nhds hCp)).differentiableAt (by simp)
  have hdH₂ := ((hH₂ _ hCp).contDiffAt (hU₂.mem_nhds hCp)).differentiableAt (by simp)
  have hdQ : fderiv ℝ Q₁ p = (fderiv ℝ Q₂ (C p)).comp (fderiv ℝ C p) := by
    rw [hQeq.fderiv_eq]
    exact fderiv_comp p hdQ₂ hC
  have hdH : fderiv ℝ H₁ p = (fderiv ℝ H₂ (C p)).comp (fderiv ℝ C p) := by
    rw [hHeq.fderiv_eq]
    exact fderiv_comp p hdH₂ hC
  have hpQ : Q₁ p = Q₂ (C p) := hQeq.eq_of_nhds
  let G₁ := sphereGradient g₁ Q₁ H₁ p
  let G₂ := sphereGradient g₂ Q₂ H₂ (C p)
  have hwt (i : Fin 2) : inner ℝ (coordPartial i Q₁ p) (G₁ - G₂) = 0 := by
    rw [real_inner_comm, inner_sub_left, sphereGradient_pairing hg₁ hQ₁ hp]
    have hpair : inner ℝ G₂ (coordPartial i Q₁ p) = coordPartial i H₁ p := by
      change inner ℝ G₂ (fderiv ℝ Q₁ p (Pi.single i 1)) = fderiv ℝ H₁ p (Pi.single i 1)
      rw [hdQ, hdH]
      exact sphereGradient_differential_pairing hg₂ hQ₂ hCp _
    rw [hpair, sub_self]
  have hnormal : inner ℝ (Q₁ p) (G₁ - G₂) = 0 := by
    rw [inner_sub_right, real_inner_comm G₁ (Q₁ p), real_inner_comm G₂ (Q₁ p)]
    rw [sphereGradient_normal_pairing hQ₁.1 hU₁ hp hunit₁, hpQ,
      sphereGradient_normal_pairing hQ₂.1 hU₂ hCp hunit₂, sub_self]
  have hn := sphere_isUnitNormal hQ₁.1 hU₁ hp hunit₁
  have he := normal_eq_inner_smul_of_independent_tangents
    (fun i => coordPartial i Q₁ p) (isometric_tangents_independent hg₁ hQ₁ hp)
    (Q₁ p) (G₁ - G₂) (hunit₁ p hp) (fun i => hn.2 _) hwt
  rw [hnormal, zero_smul] at he
  exact sub_eq_zero.mp he

theorem sphereSupportMap_coordinate_change {g₁ g₂ : MetricField}
    {Q₁ Q₂ : Coord → Ambient} {H₁ H₂ : Coord → ℝ} {C : Coord → Coord}
    {U₁ U₂ : Set Coord} (hg₁ : SmoothPositiveOn g₁ U₁) (hg₂ : SmoothPositiveOn g₂ U₂)
    (hQ₁ : IsometricOn g₁ Q₁ U₁) (hQ₂ : IsometricOn g₂ Q₂ U₂)
    (hH₂ : ContDiffOn ℝ ∞ H₂ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {p : Coord} (hp : p ∈ U₁) (hCp : C p ∈ U₂) (hC : DifferentiableAt ℝ C p)
    (hQeq : Q₁ =ᶠ[𝓝 p] (fun q => Q₂ (C q)))
    (hHeq : H₁ =ᶠ[𝓝 p] (fun q => H₂ (C q)))
    (hunit₁ : ∀ q ∈ U₁, inner ℝ (Q₁ q) (Q₁ q) = 1)
    (hunit₂ : ∀ q ∈ U₂, inner ℝ (Q₂ q) (Q₂ q) = 1) :
    sphereSupportMap g₁ Q₁ H₁ p = sphereSupportMap g₂ Q₂ H₂ (C p) := by
  unfold sphereSupportMap
  rw [sphereGradient_coordinate_change hg₁ hg₂ hQ₁ hQ₂ hH₂ hU₁ hU₂ hp hCp hC
    hQeq hHeq hunit₁ hunit₂, hQeq.eq_of_nhds, hHeq.eq_of_nhds]

end
end TightVer401
