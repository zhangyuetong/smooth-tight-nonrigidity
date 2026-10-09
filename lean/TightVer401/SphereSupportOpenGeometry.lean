import TightVer401.SphereSupportOpen
import TightVer401.CurvatureLocality

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Matrix

theorem sphereSupportMap_curvature_at {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) {p : Coord} (hp : p ∈ U)
    (hdet : (sphereSupportTensor g H p).det ≠ 0) :
    gaussianCurvature (inducedMetric (sphereSupportMap g Q H)) p =
      1 / (sphereSupportEndomorphism g H p).det := by
  have hb (i j : Fin 2) : ContDiffOn ℝ ∞ (fun q => sphereSupportTensor g H q i j) U :=
    (covHessian_contDiffOn hg hU hH i j).add (hH.mul (hg.1 i j))
  have hd : ContDiffOn ℝ ∞ (fun q => (sphereSupportTensor g H q).det) U := by
    simp only [Matrix.det_fin_two]
    exact ((hb 0 0).mul (hb 1 1)).sub ((hb 0 1).mul (hb 1 0))
  let V := U ∩ {q | (sphereSupportTensor g H q).det ≠ 0}
  have hV : IsOpen V := hd.continuousOn.isOpen_inter_preimage hU
    (isOpen_ne : IsOpen {x : ℝ | x ≠ 0})
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono inter_subset_left, fun q hq => hg.2 q hq.1⟩
  have hQV : IsometricOn g Q V :=
    ⟨hQ.1.mono inter_subset_left, fun q hq => hQ.2 q hq.1⟩
  exact sphereSupportMap_curvature hgV hQV (hH.mono inter_subset_left) hV
    (fun q hq => hunit q hq.1) (fun _ hq => hq.2) (p := p) ⟨hp, hdet⟩

open scoped Manifold
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem globalSphereSupport_chart_geometryOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) :
    let Q := sphereHemisphere w hw
    let P := sphereHemispherePoint w hw hu
    let g := inducedMetric Q
    let h := hemisphereHeight w hw hu H
    let A := fun z => globalSphereSupport H (P z)
    let V := hemisphereDomain w hw hu Ω
    ∀ p ∈ V,
      (∀ i, coordPartial i A p = sphereTangentLift g Q p (sphereSupportTensor g h p i)) ∧
      IsUnitNormalAt A (Q p) p ∧
      inducedMetric A p = sphereSupportTensor g h p * (g p)⁻¹ * (sphereSupportTensor g h p).transpose ∧
      secondFundamental A (Q p) p = -sphereSupportTensor g h p ∧
      ((sphereSupportTensor g h p).det ≠ 0 →
        Function.Injective (fderiv ℝ A p) ∧
        gaussianCurvature (inducedMetric A) p = 1 / (sphereSupportEndomorphism g h p).det) := by
  let Q := sphereHemisphere w hw
  let P := sphereHemispherePoint w hw hu
  let g := inducedMetric Q
  let h := hemisphereHeight w hw hu H
  let A := fun z => globalSphereSupport H (P z)
  let V := hemisphereDomain w hw hu Ω
  dsimp only
  intro p hp
  have hV : IsOpen V := hemisphereDomain_isOpen w hw hu hΩ
  have hg := sphereHemisphere_metric w hw hu
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1.1 i j).mono (subset_univ _), fun z _ => hg.1.2 z (mem_univ z)⟩
  have hQV : IsometricOn g Q V :=
    ⟨hg.2.1.mono (subset_univ _), fun z _ => hg.2.2 z (mem_univ z)⟩
  have hh : ContDiffOn ℝ ∞ h V := hemisphereHeight_contDiffOn hH w hw hu
  have hunit : ∀ z ∈ V, inner ℝ (Q z) (Q z) = 1 := by
    intro z _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w hw hu, one_pow]
  have he : A =ᶠ[𝓝 p] sphereSupportMap g Q h := by
    filter_upwards [hV.mem_nhds hp] with z hz
    exact globalSphereSupport_chartOn hH hΩ w hw hu hz
  have hparts (i : Fin 2) : coordPartial i A p = coordPartial i (sphereSupportMap g Q h) p := by
    unfold coordPartial
    rw [he.fderiv_eq]
  have hmetric := (inducedMetric_eventuallyEq he).eq_of_nhds
  have hsecond : secondFundamental A (Q p) p = secondFundamental (sphereSupportMap g Q h) (Q p) p := by
    ext i j
    have hej : coordPartial j A =ᶠ[𝓝 p] coordPartial j (sphereSupportMap g Q h) := by
      filter_upwards [he.eventuallyEq_nhds] with z hz
      unfold coordPartial
      rw [hz.fderiv_eq]
    change inner ℝ (fderiv ℝ (coordPartial j A) p (Pi.single i 1)) (Q p) =
      inner ℝ (fderiv ℝ (coordPartial j (sphereSupportMap g Q h)) p (Pi.single i 1)) (Q p)
    rw [hej.fderiv_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hparts]
    exact sphereSupportMap_differential hgV hQV hh hV hp hunit i
  · have hn := sphereSupportMap_isUnitNormal hgV hQV hh hV hp hunit
    exact ⟨hn.1, fun v => by rw [he.fderiv_eq]; exact hn.2 v⟩
  · rw [hmetric]
    exact sphereSupportMap_inducedMetric hgV hQV hh hV hp hunit
  · rw [hsecond]
    exact sphereSupportMap_secondFundamental hgV hQV hh hV hp hunit
  · intro hdet
    constructor
    · rw [he.fderiv_eq]
      exact sphereSupportMap_differential_injective hgV hQV hh hV hp hunit hdet
    · rw [gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq he)]
      exact sphereSupportMap_curvature_at hgV hQV hh hV hunit hp hdet

end
end TightVer401
