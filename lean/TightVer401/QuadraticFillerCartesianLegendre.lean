import TightVer401.QuadraticFillerCartesianLegendreGerm

/-! Actual local Legendre calculus for the retained inner gradient annulus. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The local transform is smooth by the generic actual Legendre calculus. -/
theorem quadraticFillerCartesianLegendre_contDiffOn {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianLegendrePotential hR hM h b)
      (quadraticFillerCartesianGradientAnnulus R M) :=
  planarLegendre_contDiffOn (quadraticFillerCartesianGradientEquiv hR hM h b)
    (quadraticFillerCartesianGradient_potential_contDiffOn hR M h b)
    (quadraticFillerCartesianGradientEquiv_smooth hR hM h b).2

/-- Its actual gradient is precisely the constructed inverse of the filler gradient. -/
theorem quadraticFillerCartesianLegendre_gradient {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) {y : Coord} (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    planarGradient (quadraticFillerCartesianLegendrePotential hR hM h b) y =
      quadraticFillerCartesianGradientInverse R M y :=
  planarLegendre_gradient (quadraticFillerCartesianGradientEquiv hR hM h b)
    (quadraticFillerCartesianGradient_potential_contDiffOn hR M h b)
    (quadraticFillerCartesianGradientEquiv_smooth hR hM h b).2 (fun _ _ => rfl) hy

/-- The actual Hessian is the inverse of the actual filler Hessian at the inverse point. -/
theorem quadraticFillerCartesianLegendre_hessian {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) {y : Coord} (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    planarHessian (quadraticFillerCartesianLegendrePotential hR hM h b) y =
      (planarHessian (quadraticFillerCartesianPotential R M h b)
        (quadraticFillerCartesianGradientInverse R M y))⁻¹ :=
  planarLegendre_hessian (quadraticFillerCartesianGradientEquiv hR hM h b)
    (quadraticFillerCartesianGradient_potential_contDiffOn hR M h b)
    (quadraticFillerCartesianGradientEquiv_smooth hR hM h b).2 (fun _ _ => rfl) hy

/-- The exact radial germ supplies strict actual Hessian determinant negativity. -/
theorem quadraticFillerCartesianLegendre_hessian_det_neg {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    (planarHessian (quadraticFillerCartesianLegendrePotential hR hM h b) y).det < 0 := by
  rw [quadraticFillerCartesianLegendre_hessian_eq_radial hR hM h b hy]
  exact quadraticFillerCartesianLegendreRadialPotential_hessian_det_neg hR hM hy

/-- Actual induced support curvature is negative throughout the exact dual annulus. -/
theorem quadraticFillerCartesianLegendre_gaussianCurvature_neg {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    gaussianCurvature (inducedMetric (planarSupportMap
      (quadraticFillerCartesianLegendrePotential hR hM h b))) y < 0 := by
  have hdet := quadraticFillerCartesianLegendre_hessian_det_neg hR hM h b hy
  exact (planarSupportMap_negative_curvature_iff
    (quadraticFillerCartesianLegendre_contDiffOn hR hM h b)
    (quadraticFillerCartesianGradient_annulus_isOpen R M) hy hdet.ne).mpr hdet

/-- The actual support differential of the local dual germ is injective. -/
theorem quadraticFillerCartesianLegendre_differential_injective {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    Function.Injective (fderiv ℝ (planarSupportMap
      (quadraticFillerCartesianLegendrePotential hR hM h b)) y) :=
  planarSupportMap_differential_injective (quadraticFillerCartesianLegendre_contDiffOn hR hM h b)
    (quadraticFillerCartesianGradient_annulus_isOpen R M) hy
    (quadraticFillerCartesianLegendre_hessian_det_neg hR hM h b hy).ne

/-- The two actual gradients compose to the identity on the dual annulus. -/
theorem quadraticFillerCartesianLegendre_gradient_right_inverse {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    planarGradient (quadraticFillerCartesianPotential R M h b)
      (planarGradient (quadraticFillerCartesianLegendrePotential hR hM h b) y) = y := by
  rw [quadraticFillerCartesianLegendre_gradient hR hM h b hy]
  exact (quadraticFillerCartesianGradientEquiv hR hM h b).right_inv hy

/-- The two actual gradients compose to the identity on the retained inner source. -/
theorem quadraticFillerCartesianLegendre_gradient_left_inverse {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (h b : ℝ → ℝ) {p : Coord}
    (hp : p ∈ quadraticFillerCartesianGradientInner R) :
    planarGradient (quadraticFillerCartesianLegendrePotential hR hM h b)
      (planarGradient (quadraticFillerCartesianPotential R M h b) p) = p := by
  rw [quadraticFillerCartesianLegendre_gradient hR hM h b
    (quadraticFillerCartesianGradient_actual_mapsTo hR hM h b hp)]
  exact (quadraticFillerCartesianGradientEquiv hR hM h b).left_inv hp

end
end TightVer401
