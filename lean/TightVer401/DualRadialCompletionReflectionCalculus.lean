import TightVer401.DualRadialCompletionLegendreGerms
import TightVer401.SeamNormalCoordinates
import TightVer401.PolarSaddleSignLocal
import TightVer401.PolarSupportGerm

/-! Actual conjugation reflection and its scalar calculus. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The existing complex conjugation, transported through the existing
complex-to-coordinate continuous linear equivalence. -/
def dualRadialCompletionReflection : Coord ≃L[ℝ] Coord :=
  (seamComplexCoord.symm.trans Complex.conjCLE).trans seamComplexCoord

@[simp] theorem dualRadialCompletionReflection_apply (p : Coord) :
    dualRadialCompletionReflection p = ![p 0, -p 1] := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem dualRadialCompletionReflection_involutive (p : Coord) :
    dualRadialCompletionReflection (dualRadialCompletionReflection p) = p := by
  ext i
  fin_cases i <;> simp

@[simp] theorem dualRadialCompletionReflection_radius (p : Coord) :
    planarRadius (dualRadialCompletionReflection p) = planarRadius p := by
  simp [planarRadius]

@[simp] theorem dualRadialCompletionReflection_dot (p q : Coord) :
    dualRadialCompletionReflection p ⬝ᵥ dualRadialCompletionReflection q = p ⬝ᵥ q := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The chain rule for the actual reflection of a scalar potential. -/
theorem dualRadialCompletionReflection_fderiv {F : Coord → ℝ} {p : Coord}
    (hF : DifferentiableAt ℝ F (dualRadialCompletionReflection p)) :
    fderiv ℝ (fun q => F (dualRadialCompletionReflection q)) p =
      (fderiv ℝ F (dualRadialCompletionReflection p)).comp
        dualRadialCompletionReflection.toContinuousLinearMap :=
  (hF.hasFDerivAt.comp p dualRadialCompletionReflection.hasFDerivAt).fderiv

private theorem reflection_component_partial (p : Coord) (a i : Fin 2) :
    coordPartial i (fun q => dualRadialCompletionReflection q a) p =
      (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) a i := by
  rw [seam_coordPartial_component dualRadialCompletionReflection.contDiff]
  change (fderiv ℝ dualRadialCompletionReflection p (Pi.single i 1)) a = _
  rw [dualRadialCompletionReflection.hasFDerivAt.fderiv]
  fin_cases a <;> fin_cases i <;> simp

private theorem reflection_component_hessian (p : Coord) (a i j : Fin 2) :
    planarHessian (fun q => dualRadialCompletionReflection q a) p i j = 0 := by
  have he : coordPartial j (fun q => dualRadialCompletionReflection q a) =
      fun _ => (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) a j := by
    funext q
    exact reflection_component_partial q a j
  change coordPartial i (coordPartial j (fun q => dualRadialCompletionReflection q a)) p = _
  rw [he, coordPartial_scalar_const]

/-- The actual Cartesian gradient transforms by conjugation reflection. -/
theorem dualRadialCompletionReflection_gradient {F : Coord → ℝ} {p : Coord}
    (hF : DifferentiableAt ℝ F (dualRadialCompletionReflection p)) :
    planarGradient (fun q => F (dualRadialCompletionReflection q)) p =
      dualRadialCompletionReflection (planarGradient F (dualRadialCompletionReflection p)) := by
  ext i
  change coordPartial i (fun q => F (dualRadialCompletionReflection q)) p = _
  rw [polarLocal_coordPartial_comp hF dualRadialCompletionReflection.contDiff]
  simp only [reflection_component_partial]
  fin_cases i <;> simp [Fin.sum_univ_two, planarGradient]

/-- Smoothness transfers on the literal reflected open domain. -/
theorem dualRadialCompletionReflection_contDiffOn {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun q => F (dualRadialCompletionReflection q))
      (dualRadialCompletionReflection ⁻¹' U) :=
  hF.comp dualRadialCompletionReflection.contDiff.contDiffOn (fun _ hq => hq)

/-- Actual Hessian conjugation, requiring smoothness only on the actual open
incoming domain. Component second derivatives of the linear reflection vanish. -/
theorem dualRadialCompletionReflection_hessian {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : dualRadialCompletionReflection p ∈ U) :
    planarHessian (fun q => F (dualRadialCompletionReflection q)) p =
      (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).transpose *
        planarHessian F (dualRadialCompletionReflection p) * !![1, 0; 0, -1] := by
  ext i j
  rw [polarLocal_planarHessian_comp hF hU dualRadialCompletionReflection.contDiff hp]
  have hJ : seamCoordinateJacobian dualRadialCompletionReflection p =
      (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext a b
    exact reflection_component_partial p a b
  simp only [hJ, reflection_component_hessian, mul_zero, Finset.sum_const_zero, add_zero]

/-- Conjugation reflection preserves the actual Cartesian Hessian determinant. -/
theorem dualRadialCompletionReflection_hessian_det {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : dualRadialCompletionReflection p ∈ U) :
    (planarHessian (fun q => F (dualRadialCompletionReflection q)) p).det =
      (planarHessian F (dualRadialCompletionReflection p)).det := by
  rw [dualRadialCompletionReflection_hessian hF hU hp,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp [Matrix.det_fin_two]

/-- Audited double-dual recovery pulled back through the actual reflection.
The ordinary incoming equality is the only overlap hypothesis. -/
theorem dualRadialCompletionReflection_recovery
    (G H : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    (hH : EqOn H (planarLegendre G e) e.target) :
    EqOn (fun p => planarLegendre H e.symm (dualRadialCompletionReflection p))
      (fun p => G (dualRadialCompletionReflection p))
      (dualRadialCompletionReflection ⁻¹' e.source) := by
  intro p hp
  exact dualRadialCompletionLegendre_recovery G H e hH hp

/-- Recovery is also an actual ambient scalar germ on the reflected source. -/
theorem dualRadialCompletionReflection_recovery_germ
    (G H : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    (hH : EqOn H (planarLegendre G e) e.target) {p : Coord}
    (hp : dualRadialCompletionReflection p ∈ e.source) :
    (fun q => planarLegendre H e.symm (dualRadialCompletionReflection q)) =ᶠ[𝓝 p]
      (fun q => G (dualRadialCompletionReflection q)) := by
  filter_upwards [(e.open_source.preimage dualRadialCompletionReflection.continuous).mem_nhds hp]
    with q hq
  exact dualRadialCompletionReflection_recovery G H e hH hq

end
end TightVer401
