import TightVer401.CorrugatedSeedCellArclength

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace

theorem corrugated_complex_covariant_deriv {f : ℝ → ℂ} {T : ℝ} {ξ : ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : ∀ t, f (t + T) = ξ * f t) (t : ℝ) :
    deriv f (t + T) = ξ * deriv f t := by
  have hd := hf.differentiable (by simp)
  have hs := (hd (t + T)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const T)
  have hr := (hd t).hasDerivAt.const_mul ξ
  have he := hs.congr_of_eventuallyEq (f₁ := fun s => ξ * f s)
    (Filter.Eventually.of_forall (fun s => (hc s).symm))
  simpa only [one_smul] using he.unique hr

theorem corrugatedSeedSphereScale_periodic {N : ℝ} (hN : N ≠ 0) :
    Function.Periodic (corrugatedSeedSphereScale N) (corrugatedSeedCell N) := by
  intro t
  unfold corrugatedSeedSphereScale
  rw [corrugatedSeedBeta_cell hN, corrugatedComplexCoord_weight,
    corrugatedComplexCoord_weight, norm_mul]
  simp only [corrugatedSeedRotation, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem corrugatedSeedSphere_geodesic_curvature_periodic {N : ℝ} (hN : N ≠ 0) :
    Function.Periodic (sphericalCurveGeodesicCurvature (corrugatedSeedSphere N))
      (corrugatedSeedCell N) := by
  have hv := corrugated_complex_covariant_deriv (corrugatedSeedBeta_contDiff N)
    (corrugatedSeedBeta_cell hN)
  have ha := corrugated_complex_covariant_deriv
    (contDiff_infty_iff_deriv.mp (corrugatedSeedBeta_contDiff N)).2 hv
  intro t
  rw [corrugatedSeedSphere_geodesic_curvature, corrugatedSeedSphere_geodesic_curvature,
    corrugatedSeedSphereScale_periodic hN t, hv t, ha t]
  have hd : corrugatedSeedPlaneDet (corrugatedSeedRotation N * deriv (corrugatedSeedBeta N) t)
      (corrugatedSeedRotation N * deriv (deriv (corrugatedSeedBeta N)) t) =
      corrugatedSeedPlaneDet (deriv (corrugatedSeedBeta N) t)
        (deriv (deriv (corrugatedSeedBeta N)) t) := corrugatedSeedPlaneDet_rotate _ _ _
  rw [hd]
  change _ / (corrugatedSeedSphericalSpeed N (t + corrugatedSeedCell N))^3 =
    _ / (corrugatedSeedSphericalSpeed N t)^3
  rw [corrugatedSeedSphericalSpeed_periodic hN t]

theorem corrugatedSeedFrame_curvature_periodic {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) :
    Function.Periodic (normalLoopCurvature (corrugatedSeedSphere N ∘ ψ)) ell := by
  intro r
  rw [normalLoopCurvature_arclength_comp (corrugatedSeedSphere_contDiff N) hψ hi,
    normalLoopCurvature_arclength_comp (corrugatedSeedSphere_contDiff N) hψ hi,
    hcell r, corrugatedSeedSphere_geodesic_curvature_periodic (ne_of_gt (by linarith : 0 < N))]

theorem corrugatedSeedFrame_curvature_both_signs {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hs : Function.Surjective ψ) :
    (∃ r, 0 < normalLoopCurvature (corrugatedSeedSphere N ∘ ψ) r) ∧
      ∃ r, normalLoopCurvature (corrugatedSeedSphere N ∘ ψ) r < 0 := by
  obtain ⟨r, hr⟩ := hs 0
  obtain ⟨s, hs⟩ := hs (Real.pi / N)
  constructor
  · refine ⟨r, ?_⟩
    rw [normalLoopCurvature_arclength_comp (corrugatedSeedSphere_contDiff N) hψ hi, hr]
    exact corrugatedSeedSphere_curvature_positive hN
  · refine ⟨s, ?_⟩
    rw [normalLoopCurvature_arclength_comp (corrugatedSeedSphere_contDiff N) hψ hi, hs]
    exact corrugatedSeedSphere_curvature_negative hN

theorem corrugatedSeedFrame_curvature_nonconstant {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hs : Function.Surjective ψ) :
    ¬ ∃ c : ℝ, ∀ r, normalLoopCurvature (corrugatedSeedSphere N ∘ ψ) r = c := by
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := corrugatedSeedFrame_curvature_both_signs hN hψ hi hs
  rintro ⟨c, hc⟩
  rw [hc r] at hr
  rw [hc s] at hs
  linarith

end
end TightVer401
