import TightVer401.GnomonicCoordinates
import TightVer401.AmbientCross
import TightVer401.ScalarCoordinateCalculus
import TightVer401.SeamCoordinateChain
import TightVer401.AnnularDegreeLocal

/-! Exact projected source orientation. The quotient determinant identity
requires only differentiability and a nonzero third coordinate; no unit or
tangent assumptions and no desired Cartesian orientation are supplied. -/
namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry
open scoped Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

private theorem selectedProjection_ambient_component_partial
    {N : Coord → Ambient} {q : Coord} (hN : DifferentiableAt ℝ N q)
    (i : Fin 2) (k : Fin 3) :
    coordPartial i (fun x => N x k) q = coordPartial i N q k := by
  have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).hasFDerivAt.comp
    q hN.hasFDerivAt
  have hc' := hc.congr_of_eventuallyEq (f₁ := fun x => N x k)
    (Eventually.of_forall (fun _ => rfl))
  unfold coordPartial
  rw [hc'.fderiv]
  rfl

private theorem selectedProjection_coord_component_partial
    {F : Coord → Coord} {q : Coord} (hF : DifferentiableAt ℝ F q)
    (i a : Fin 2) :
    coordPartial i (fun x => F x a) q = coordPartial i F q a := by
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) a (F q)).comp q hF.hasFDerivAt
  have hc' := hc.congr_of_eventuallyEq (f₁ := fun x => F x a)
    (Eventually.of_forall (fun _ => rfl))
  unfold coordPartial
  rw [hc'.fderiv]
  rfl

/-- Every scalar entry of the actual projected differential is computed
by the quotient derivative of the SAME ambient map. -/
theorem positiveExitSelected_gnomonic_component_partial
    {N : Coord → Ambient} {q : Coord} (hN : DifferentiableAt ℝ N q)
    (hN2 : N q 2 ≠ 0) (a i : Fin 2) :
    coordPartial i (fun x => gnomonicInverse (N x) a) q =
      (coordPartial i N q a.castSucc * N q 2 -
        N q a.castSucc * coordPartial i N q 2) / (N q 2)^2 := by
  have hd (k : Fin 3) : DifferentiableAt ℝ (fun x => N x k) q :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).differentiableAt.comp q hN
  fin_cases a
  · change coordPartial i (fun x => N x 0 / N x 2) q = _
    rw [coordPartial_scalar_div (hd 0) (hd 2) hN2,
      selectedProjection_ambient_component_partial hN,
      selectedProjection_ambient_component_partial hN]
    rfl
  · change coordPartial i (fun x => N x 1 / N x 2) q = _
    rw [coordPartial_scalar_div (hd 1) (hd 2) hN2,
      selectedProjection_ambient_component_partial hN,
      selectedProjection_ambient_component_partial hN]
    rfl

/-- Exact gnomonic Jacobian formula for an arbitrary actual ambient map.
The familiar sphere formula needs no unit or tangent premises. -/
theorem positiveExitSelected_gnomonic_seam_jacobian
    {N : Coord → Ambient} {q : Coord} (hN : DifferentiableAt ℝ N q)
    (hN2 : N q 2 ≠ 0) :
    (seamCoordinateJacobian (gnomonicInverse ∘ N) q).det =
      inner ℝ (N q) (ambientCross (coordPartial 0 N q) (coordPartial 1 N q)) /
        (N q 2)^3 := by
  rw [Matrix.det_fin_two]
  simp only [seamCoordinateJacobian, Function.comp_apply,
    positiveExitSelected_gnomonic_component_partial hN hN2]
  simp [ambient_inner_dot, dotProduct, Fin.sum_univ_succ, ambientCross, cross_apply,
    Fin.succ_zero_eq_one, show (1 : Fin 2).succ = (2 : Fin 3) from rfl]
  field_simp [hN2]
  <;> ring

/-- The source-order consumer's intrinsic Frechet determinant is literally
the computed scalar-coordinate determinant of the same projected map. -/
theorem positiveExitSelected_gnomonic_annular_jacobian
    {N : Coord → Ambient} {q : Coord} (hN : DifferentiableAt ℝ N q)
    (hN2 : N q 2 ≠ 0) :
    annularJacobian (gnomonicInverse ∘ N) q =
      inner ℝ (N q) (ambientCross (coordPartial 0 N q) (coordPartial 1 N q)) /
        (N q 2)^3 := by
  have hF : DifferentiableAt ℝ (gnomonicInverse ∘ N) q :=
    ((gnomonicInverse_contDiffAt hN2).differentiableAt (by simp)).comp q hN
  have hJ : annularJacobian (gnomonicInverse ∘ N) q =
      (seamCoordinateJacobian (gnomonicInverse ∘ N) q).det := by
    rw [annularJacobian, ← LinearMap.det_toMatrix', Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix'_apply, seamCoordinateJacobian,
      selectedProjection_coord_component_partial hF, ContinuousLinearMap.coe_coe]
    rfl
  exact hJ.trans (positiveExitSelected_gnomonic_seam_jacobian hN hN2)

/-- Northern gnomonic projection preserves the actual signed cross area. -/
theorem positiveExitSelected_gnomonic_annular_jacobian_neg
    {N : Coord → Ambient} {q : Coord} (hN : DifferentiableAt ℝ N q)
    (hnorth : 0 < N q 2)
    (hcross : inner ℝ (N q) (ambientCross (coordPartial 0 N q) (coordPartial 1 N q)) < 0) :
    annularJacobian (gnomonicInverse ∘ N) q < 0 := by
  rw [positiveExitSelected_gnomonic_annular_jacobian hN hnorth.ne']
  exact div_neg_of_neg_of_pos hcross (pow_pos hnorth 3)

end
end TightVer401



