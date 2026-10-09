import TightVer401.SmoothingChartTransfer

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem seam_coordPartial_comp_at {F : Coord → ℝ} {Φ : Coord → Coord} {p : Coord}
    (hF : DifferentiableAt ℝ F (Φ p)) (hΦ : DifferentiableAt ℝ Φ p) (i : Fin 2) :
    coordPartial i (fun q => F (Φ q)) p =
      coordPartial 0 F (Φ p)*(coordPartial i Φ p) 0+
        coordPartial 1 F (Φ p)*(coordPartial i Φ p) 1 := by
  have hd := hF.hasFDerivAt.comp p hΦ.hasFDerivAt
  have hd' := hd.congr_of_eventuallyEq (f₁ := fun q => F (Φ q))
    (Filter.Eventually.of_forall (fun _ => rfl))
  change fderiv ℝ (fun q => F (Φ q)) p (Pi.single i 1)=_
  rw [hd'.fderiv]
  change fderiv ℝ F (Φ p) (coordPartial i Φ p)=_
  exact seam_fderiv_coordinate_apply F (Φ p) (coordPartial i Φ p)

/-- An actual inverse-chart derivative bound controls the actual transported
planar gradient error. -/
theorem smoothing_gradient_comp_bound {F G : Coord → ℝ} {Φ : Coord → Coord}
    {p : Coord} (hF : DifferentiableAt ℝ F (Φ p)) (hG : DifferentiableAt ℝ G (Φ p))
    (hΦ : DifferentiableAt ℝ Φ p) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hB : ∀ i a : Fin 2, |coordPartial i Φ p a| ≤ M)
    (hclose : ‖planarGradient F (Φ p)-planarGradient G (Φ p)‖ ≤ η) :
    ‖planarGradient (fun q => F (Φ q)) p-planarGradient (fun q => G (Φ q)) p‖ ≤ 2*M*η := by
  have hg (a : Fin 2) : |coordPartial a F (Φ p)-coordPartial a G (Φ p)| ≤ η := by
    exact (norm_le_pi_norm (planarGradient F (Φ p)-planarGradient G (Φ p)) a).trans hclose
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*M*η)).mpr
  intro i
  change |coordPartial i (fun q => F (Φ q)) p-coordPartial i (fun q => G (Φ q)) p| ≤ _
  rw [seam_coordPartial_comp_at hF hΦ,seam_coordPartial_comp_at hG hΦ]
  have he : coordPartial 0 F (Φ p)*coordPartial i Φ p 0+
      coordPartial 1 F (Φ p)*coordPartial i Φ p 1-
      (coordPartial 0 G (Φ p)*coordPartial i Φ p 0+
        coordPartial 1 G (Φ p)*coordPartial i Φ p 1)=
      (coordPartial 0 F (Φ p)-coordPartial 0 G (Φ p))*coordPartial i Φ p 0+
        (coordPartial 1 F (Φ p)-coordPartial 1 G (Φ p))*coordPartial i Φ p 1 := by ring
  rw [he]
  calc
    _ ≤ |(coordPartial 0 F (Φ p)-coordPartial 0 G (Φ p))*coordPartial i Φ p 0|+
        |(coordPartial 1 F (Φ p)-coordPartial 1 G (Φ p))*coordPartial i Φ p 1| := abs_add_le _ _
    _ ≤ η*M+η*M := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul (hg 0) (hB i 0) (abs_nonneg _) hη)
        (mul_le_mul (hg 1) (hB i 1) (abs_nonneg _) hη)
    _ = 2*M*η := by ring

end
end TightVer401
