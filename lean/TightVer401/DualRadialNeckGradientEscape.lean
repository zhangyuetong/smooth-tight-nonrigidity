import TightVer401.DualRadialNeckSmoothingGeometry
import TightVer401.PlanarGradientInverse

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The planar radius used in the scalar calculations is exactly the
Euclidean norm, with its actual L2 structure rather than the coordinate max norm. -/
theorem planarRadius_eq_euclidean_norm (p : Coord) :
    planarRadius p = ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 2))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rfl

theorem radialPlanarGradient_radius {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U) :
    planarRadius (planarGradient (radialPlanarPotential F) p) =
      |deriv F (planarRadius p)| := by
  have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp.1).ne'
  have hsq : planarRadius (planarGradient (radialPlanarPotential F) p) ^ 2 =
      (deriv F (planarRadius p)) ^ 2 := by
    rw [planarRadius_sq]
    simp only [planarGradient, radialPlanarPotential_coordPartial hF hU hp]
    calc
      (deriv F (planarRadius p) * p 0 / planarRadius p) ^ 2 +
          (deriv F (planarRadius p) * p 1 / planarRadius p) ^ 2 =
          deriv F (planarRadius p) ^ 2 * (p 0 ^ 2 + p 1 ^ 2) / planarRadius p ^ 2 := by
        field_simp [hr]
      _ = deriv F (planarRadius p) ^ 2 := by
        rw [← planarRadius_sq p]
        field_simp [hr]
  have hrad : 0 ≤ planarRadius (planarGradient (radialPlanarPotential F) p) :=
    Real.sqrt_nonneg _
  nlinarith [sq_abs (deriv F (planarRadius p)), abs_nonneg (deriv F (planarRadius p))]

theorem radialPlanarGradient_norm_eq_abs_deriv {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U) :
    ‖(WithLp.toLp 2 (planarGradient (radialPlanarPotential F) p) :
      EuclideanSpace ℝ (Fin 2))‖ = |deriv F (planarRadius p)| := by
  rw [← planarRadius_eq_euclidean_norm]
  exact radialPlanarGradient_radius hF hU hp

def dualRadialPlanarRay (θ r : ℝ) : Coord := ![r * Real.cos θ, r * Real.sin θ]

theorem dualRadialPlanarRay_sq (θ r : ℝ) :
    dualRadialPlanarRay θ r 0 ^ 2 + dualRadialPlanarRay θ r 1 ^ 2 = r ^ 2 := by
  dsimp [dualRadialPlanarRay]
  have hh := congrArg (fun x : ℝ => r ^ 2 * x) (Real.sin_sq_add_cos_sq θ)
  nlinarith [hh]

theorem dualRadialPlanarRay_radius (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    planarRadius (dualRadialPlanarRay θ r) = r := by
  rw [planarRadius, dualRadialPlanarRay_sq, Real.sqrt_sq hr.le]

theorem radialPlanarGradient_ray_radius {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (θ : ℝ) {r : ℝ}
    (hr : 0 < r) (hrU : r ∈ U) (hd : 0 < deriv F r) :
    planarRadius (planarGradient (radialPlanarPotential F) (dualRadialPlanarRay θ r)) =
      deriv F r := by
  have hp : dualRadialPlanarRay θ r ∈ radialPlanarDomain U := by
    refine ⟨?_, ?_⟩
    · change 0 < dualRadialPlanarRay θ r 0 ^ 2 + dualRadialPlanarRay θ r 1 ^ 2
      rw [dualRadialPlanarRay_sq]
      exact sq_pos_of_pos hr
    · change planarRadius (dualRadialPlanarRay θ r) ∈ U
      rwa [dualRadialPlanarRay_radius θ hr]
  rw [radialPlanarGradient_radius hF hU hp, dualRadialPlanarRay_radius θ hr, abs_of_pos hd]

theorem radialPlanarGradient_ray_norm {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (θ : ℝ) {r : ℝ}
    (hr : 0 < r) (hrU : r ∈ U) (hd : 0 < deriv F r) :
    ‖(WithLp.toLp 2 (planarGradient (radialPlanarPotential F) (dualRadialPlanarRay θ r)) :
      EuclideanSpace ℝ (Fin 2))‖ = deriv F r := by
  rw [← planarRadius_eq_euclidean_norm]
  exact radialPlanarGradient_ray_radius hF hU θ hr hrU hd

/-- Escape of the actual Euclidean gradient along every ray follows from
actual slope escape, not from a norm assigned to a symbolic radial coefficient. -/
theorem radialPlanarGradient_ray_norm_tendsto_atTop {F : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hF : ContDiffOn ℝ ∞ F (Ioo a b))
    (hpos : ∀ r ∈ Ioo a b, 0 < deriv F r)
    (hescape : Tendsto (deriv F) (𝓝[>] a) atTop) (θ : ℝ) :
    Tendsto (fun r =>
      ‖(WithLp.toLp 2 (planarGradient (radialPlanarPotential F) (dualRadialPlanarRay θ r)) :
        EuclideanSpace ℝ (Fin 2))‖) (𝓝[>] a) atTop := by
  have heq : (fun r =>
      ‖(WithLp.toLp 2 (planarGradient (radialPlanarPotential F) (dualRadialPlanarRay θ r)) :
        EuclideanSpace ℝ (Fin 2))‖) =ᶠ[𝓝[>] a] deriv F := by
    have hupper : ∀ᶠ r in 𝓝[>] a, r < b :=
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hupper] with r hr hrupper
    exact radialPlanarGradient_ray_norm hF isOpen_Ioo θ (ha.trans hr)
      ⟨hr, hrupper⟩ (hpos r ⟨hr, hrupper⟩)
  exact hescape.congr' heq.symm

/-- Complete ver500 neck attachment including its actual planar gradient
norm escape, retained germs, and actual saddle geometry. -/
theorem exists_dualRadialNeck_gradient_adapter {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) {j a : ℝ}
    (ha : 0 < a) (haj : a < j) (hjU : j ∈ U)
    (hpos : 0 < deriv f j) (hneg : ∀ x ∈ U, deriv (deriv f) x < 0) :
    let B := dualRadialNeckCoefficient (deriv f j) j a
    let C := dualRadialNeckConstant (f j) (deriv f j) j a
    ∃ (b c d : ℝ) (F : ℝ → ℝ), j < b ∧ b ∈ U ∧ c ∈ Ioo a j ∧ d ∈ Ioo j b ∧
      Ioo d b ⊆ U ∧ ContDiffOn ℝ ∞ F (Ioo a b) ∧
      (∀ r ∈ Ioo a b, 0 < deriv F r ∧ deriv (deriv F) r < 0) ∧
      EqOn F (dualRadialNeck C B a) (Ioo a c) ∧ EqOn F f (Ioo d b) ∧
      Tendsto (deriv F) (𝓝[>] a) atTop ∧ Tendsto F (𝓝[>] a) (𝓝 C) ∧
      (∀ p ∈ radialPlanarDomain (Ioo a b),
        (planarHessian (radialPlanarPotential F) p).det < 0 ∧
        Function.Injective (fderiv ℝ (planarSupportMap (radialPlanarPotential F)) p) ∧
        gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential F))) p < 0) ∧
      ∀ θ : ℝ, Tendsto (fun r =>
        ‖(WithLp.toLp 2 (planarGradient (radialPlanarPotential F) (dualRadialPlanarRay θ r)) :
          EuclideanSpace ℝ (Fin 2))‖) (𝓝[>] a) atTop := by
  dsimp only
  obtain ⟨b, c, d, F, hjb, hbU, hc, hd, hcollarU, hF, hsigns, hneck, hincoming,
    hescape, hvalue, hgeometry⟩ :=
    exists_dualRadialNeck_saddle_adapter hU hf ha haj hjU hpos hneg
  refine ⟨b, c, d, F, hjb, hbU, hc, hd, hcollarU, hF, hsigns, hneck, hincoming,
    hescape, hvalue, hgeometry, ?_⟩
  intro θ
  exact radialPlanarGradient_ray_norm_tendsto_atTop ha (haj.trans hjb) hF
    (fun r hr => (hsigns r hr).1) hescape θ

end
end TightVer401
