import TightVer401.PolarSaddleSign

/-! Open-domain polar saddle criterion, suitable for punctured-disk fillings. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

theorem polarLocal_coordPartial_comp {F : Coord → ℝ} {Φ : Coord → Coord} {p : Coord}
    (hF : DifferentiableAt ℝ F (Φ p)) (hΦ : ContDiff ℝ ∞ Φ)
    (i : Fin 2) :
    coordPartial i (fun q => F (Φ q)) p =
      ∑ a : Fin 2, coordPartial a F (Φ p)*coordPartial i (fun q => Φ q a) p := by
  have hd := hF.hasFDerivAt.comp p (hΦ.differentiable (by simp) p).hasFDerivAt
  change HasFDerivAt (fun q => F (Φ q)) _ p at hd
  change fderiv ℝ (fun q => F (Φ q)) p (Pi.single i 1) = _
  rw [hd.fderiv]
  change fderiv ℝ F (Φ p) (coordPartial i Φ p) = _
  rw [seam_fderiv_coordinate_apply]
  simp only [Fin.sum_univ_two,seam_coordPartial_component hΦ]

/-- A local second-derivative chain rule: the Cartesian potential need only
be smooth on its actual open source domain. -/
theorem polarLocal_planarHessian_comp {F : Coord → ℝ} {Φ : Coord → Coord}
    {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hΦ : ContDiff ℝ ∞ Φ) {p : Coord} (hp : Φ p ∈ U) (i j : Fin 2) :
    planarHessian (fun q => F (Φ q)) p i j =
      ((seamCoordinateJacobian Φ p).transpose * planarHessian F (Φ p) *
        seamCoordinateJacobian Φ p) i j +
      ∑ a : Fin 2, coordPartial a F (Φ p)*planarHessian (fun q => Φ q a) p i j := by
  have hF₁ (a : Fin 2) : DifferentiableAt ℝ (fun q => coordPartial a F (Φ q)) p :=
    (((partial_contDiffOn hF hU a).contDiffAt (hU.mem_nhds hp)).differentiableAt
      (by simp)).comp p (hΦ.differentiable (by simp) p)
  have hΦa (a : Fin 2) : ContDiff ℝ ∞ (fun q => Φ q a) :=
    (contDiff_apply ℝ ℝ a).comp hΦ
  have hΦ₁ (a : Fin 2) := smoothing_partial_contDiff (hΦa a) j
  have hprod (a : Fin 2) : DifferentiableAt ℝ
      (fun q => coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q) p :=
    (hF₁ a).mul ((hΦ₁ a).differentiable (by simp) p)
  have he : coordPartial j (fun q => F (Φ q)) =ᶠ[𝓝 p]
      (fun q => ∑ a : Fin 2, coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q) := by
    filter_upwards [(hU.preimage hΦ.continuous).mem_nhds hp] with q hq
    exact polarLocal_coordPartial_comp ((hF.contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by simp)) hΦ j
  change fderiv ℝ (coordPartial j (fun q => F (Φ q))) p (Pi.single i 1) = _
  rw [he.fderiv_eq]
  change coordPartial i (fun q => ∑ a : Fin 2,
      coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q) p = _
  rw [coordPartial_sum_two _ hprod]
  have hm (a : Fin 2) : coordPartial i
      (fun q => coordPartial a F (Φ q)*coordPartial j (fun x => Φ x a) q) p =
      (∑ b : Fin 2, planarHessian F (Φ p) b a*coordPartial i (fun q => Φ q b) p)*
        coordPartial j (fun q => Φ q a) p +
      coordPartial a F (Φ p)*planarHessian (fun q => Φ q a) p i j := by
    rw [coordPartial_mul_at (hF₁ a) ((hΦ₁ a).differentiable (by simp) p),
      polarLocal_coordPartial_comp (((partial_contDiffOn hF hU a).contDiffAt
        (hU.mem_nhds hp)).differentiableAt (by simp)) hΦ]
    rfl
  simp only [hm,Fin.sum_univ_two]
  simp [Matrix.mul_apply,Matrix.transpose_apply,seamCoordinateJacobian,Fin.sum_univ_two]
  ring

theorem polarLocal_correctedHessian_comp {F : Coord → ℝ} {Φ : Coord → Coord}
    {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hΦ : ContDiff ℝ ∞ Φ) {p : Coord} (hp : Φ p ∈ U)
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    seamCorrectedHessian Φ (fun q => F (Φ q)) p =
      (seamCoordinateJacobian Φ p).transpose * planarHessian F (Φ p) * seamCoordinateJacobian Φ p := by
  have hgrad (i j : Fin 2) :
      (∑ k : Fin 2, seamChartConnection Φ k i j p*coordPartial k (fun q => F (Φ q)) p) =
      ∑ a : Fin 2, coordPartial a F (Φ p)*planarHessian (fun q => Φ q a) p i j := by
    have hc := seamChartConnection_cancel hJ i j
    have h₀ := congrFun hc 0
    have h₁ := congrFun hc 1
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,seamCoordinateJacobian] at h₀ h₁
    simp only [Fin.sum_univ_two,polarLocal_coordPartial_comp
      ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) hΦ]
    linear_combination coordPartial 0 F (Φ p)*h₀+coordPartial 1 F (Φ p)*h₁
  ext i j
  unfold seamCorrectedHessian
  rw [polarLocal_planarHessian_comp hF hU hΦ hp,hgrad]
  ring

end
end TightVer401
