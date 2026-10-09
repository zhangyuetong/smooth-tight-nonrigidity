import TightVer401.SmoothingCutoff

namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff Topology BigOperators

def seamCoordinateJacobian (Φ : Coord → Coord) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a i => coordPartial i (fun q => Φ q a) p

theorem seam_fderiv_coordinate_apply (F : Coord → ℝ) (p v : Coord) :
    fderiv ℝ F p v = coordPartial 0 F p*v 0+coordPartial 1 F p*v 1 := by
  have hv : v=v 0 • (Pi.single 0 1 : Coord)+v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  rw [hv]
  simp [coordPartial]
  ring

theorem seam_coordPartial_component {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ)
    (p : Coord) (a i : Fin 2) :
    coordPartial i (fun q => Φ q a) p = coordPartial i Φ p a := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) a (Φ p)).comp p
    (hΦ.differentiable (by simp) p).hasFDerivAt
  have hd' := hd.congr_of_eventuallyEq (f₁ := fun q => Φ q a)
    (Eventually.of_forall (fun _ => rfl))
  unfold coordPartial
  rw [hd'.fderiv]
  rfl

theorem seam_coordPartial_comp {F : Coord → ℝ} {Φ : Coord → Coord}
    (hF : ContDiff ℝ ∞ F) (hΦ : ContDiff ℝ ∞ Φ) (p : Coord) (i : Fin 2) :
    coordPartial i (fun q => F (Φ q)) p =
      ∑ a : Fin 2, coordPartial a F (Φ p)*coordPartial i (fun q => Φ q a) p := by
  have hd := (hF.differentiable (by simp) (Φ p)).hasFDerivAt.comp p
    (hΦ.differentiable (by simp) p).hasFDerivAt
  have hd' := hd.congr_of_eventuallyEq (f₁ := fun q => F (Φ q))
    (Eventually.of_forall (fun _ => rfl))
  change fderiv ℝ (fun q => F (Φ q)) p (Pi.single i 1) = _
  rw [hd'.fderiv]
  change fderiv ℝ F (Φ p) (coordPartial i Φ p) = _
  rw [seam_fderiv_coordinate_apply]
  simp only [Fin.sum_univ_two,seam_coordPartial_component hΦ]

/-- The actual second-derivative chain rule includes the chart's second
derivatives. Those terms must be controlled in curved-seam smoothing. -/
theorem seam_planarHessian_comp {F : Coord → ℝ} {Φ : Coord → Coord}
    (hF : ContDiff ℝ ∞ F) (hΦ : ContDiff ℝ ∞ Φ) (p : Coord) (i j : Fin 2) :
    planarHessian (fun q => F (Φ q)) p i j =
      ((seamCoordinateJacobian Φ p).transpose * planarHessian F (Φ p) *
        seamCoordinateJacobian Φ p) i j +
      ∑ a : Fin 2, coordPartial a F (Φ p)*planarHessian (fun q => Φ q a) p i j := by
  have hΦa (a : Fin 2) : ContDiff ℝ ∞ (fun q => Φ q a) := (contDiff_apply ℝ ℝ a).comp hΦ
  have hF₁ (a : Fin 2) : ContDiff ℝ ∞ (fun q => coordPartial a F (Φ q)) :=
    (smoothing_partial_contDiff hF a).comp hΦ
  have hΦ₁ (a : Fin 2) := smoothing_partial_contDiff (hΦa a) j
  have hprod (a : Fin 2) : DifferentiableAt ℝ
      (fun q => coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q) p :=
    ((hF₁ a).mul (hΦ₁ a)).differentiable (by simp) p
  have he : coordPartial j (fun q => F (Φ q)) =
      fun q => ∑ a : Fin 2, coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q := by
    funext q
    exact seam_coordPartial_comp hF hΦ q j
  change coordPartial i (coordPartial j (fun q => F (Φ q))) p = _
  rw [he,coordPartial_sum_two _ hprod]
  have hm (a : Fin 2) : coordPartial i
      (fun q => coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q) p =
      (∑ b : Fin 2, planarHessian F (Φ p) b a*coordPartial i (fun q => Φ q b) p)*
        coordPartial j (fun q => Φ q a) p +
      coordPartial a F (Φ p)*planarHessian (fun q => Φ q a) p i j := by
    rw [coordPartial_mul_at ((hF₁ a).differentiable (by simp) p)
      ((hΦ₁ a).differentiable (by simp) p),
      seam_coordPartial_comp (smoothing_partial_contDiff hF a) hΦ]
    rfl
  simp only [hm,Fin.sum_univ_two]
  simp [Matrix.mul_apply,Matrix.transpose_apply,seamCoordinateJacobian,Fin.sum_univ_two]
  ring

end
end TightVer401
