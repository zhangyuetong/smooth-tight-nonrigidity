import TightVer401.SeamCoordinateChain
import TightVer401.GaussBridge

/-! Actual local curvature under a smooth change of the physical Coord model.

Inputs are open domains, ordinary local smoothness, actual derivative ranks,
MapsTo, and a unit vector orthogonal to the actual surface differential at
the point. The first form and normal second form both transform by the same
Jacobian congruence. The extra coordinate Hessian term vanishes by actual
normal orthogonality, so their determinant factors cancel in the retained
OpenAI Gauss equation. No curvature or metric compatibility is assumed.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem component_partial {κ : Coord → Coord} {p : Coord}
    (hκ : DifferentiableAt ℝ κ p) (a i : Fin 2) :
    coordPartial i (fun q => κ q a) p = coordPartial i κ p a := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) a (κ p)).comp p hκ.hasFDerivAt
  change HasFDerivAt (fun q => κ q a) _ p at hd
  change fderiv ℝ (fun q => κ q a) p (Pi.single i 1) = _
  rw [hd.fderiv]
  rfl

private theorem scalar_partial_comp {f : Coord → ℝ} {κ : Coord → Coord} {p : Coord}
    (hf : DifferentiableAt ℝ f (κ p)) (hκ : DifferentiableAt ℝ κ p) (i : Fin 2) :
    coordPartial i (f ∘ κ) p =
      ∑ a : Fin 2, coordPartial a f (κ p) * coordPartial i (fun q => κ q a) p := by
  change fderiv ℝ (f ∘ κ) p (Pi.single i 1) = _
  rw [fderiv_comp p hf hκ]
  change fderiv ℝ f (κ p) (coordPartial i κ p) = _
  rw [seam_fderiv_coordinate_apply]
  simp only [Fin.sum_univ_two, component_partial hκ]

/-- Local second coordinate chain rule, including the genuine coordinate
Hessians. Smoothness is required only on the indicated open domains. -/
theorem protectedTorus_curvature_planarHessian_comp
    {f : Coord → ℝ} {κ : Coord → Coord} {U V : Set Coord}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f U) (hκ : ContDiffOn ℝ ∞ κ V)
    (hmap : MapsTo κ V U) {p : Coord} (hp : p ∈ V) (i j : Fin 2) :
    planarHessian (f ∘ κ) p i j =
      ((seamCoordinateJacobian κ p).transpose * planarHessian f (κ p) *
        seamCoordinateJacobian κ p) i j +
      ∑ a : Fin 2, coordPartial a f (κ p) * planarHessian (fun q => κ q a) p i j := by
  have hκa (a : Fin 2) : ContDiffOn ℝ ∞ (fun q => κ q a) V :=
    (contDiff_apply ℝ ℝ a).contDiffOn.comp hκ (mapsTo_univ _ _)
  have hf₁ (a : Fin 2) : ContDiffOn ℝ ∞ (fun q => coordPartial a f (κ q)) V :=
    (partial_contDiffOn hf hU a).comp hκ hmap
  have hκ₁ (a : Fin 2) := partial_contDiffOn (hκa a) hV j
  have hdκ : DifferentiableAt ℝ κ p := ((hκ p hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hdf₁ (a : Fin 2) : DifferentiableAt ℝ (fun q => coordPartial a f (κ q)) p :=
    (((hf₁ a) p hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hdκ₁ (a : Fin 2) : DifferentiableAt ℝ (coordPartial j (fun q => κ q a)) p :=
    (((hκ₁ a) p hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hprod (a : Fin 2) : DifferentiableAt ℝ
      (fun q => coordPartial a f (κ q) * coordPartial j (fun x => κ x a) q) p :=
    (hdf₁ a).mul (hdκ₁ a)
  have he : coordPartial j (f ∘ κ) =ᶠ[𝓝 p]
      (fun q => ∑ a : Fin 2, coordPartial a f (κ q) * coordPartial j (fun x => κ x a) q) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact scalar_partial_comp
      (((hf (κ q) (hmap hq)).contDiffAt (hU.mem_nhds (hmap hq))).differentiableAt (by simp))
      (((hκ q hq).contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)) j
  have he' : coordPartial i (coordPartial j (f ∘ κ)) p =
      coordPartial i (fun q => ∑ a : Fin 2,
        coordPartial a f (κ q) * coordPartial j (fun x => κ x a) q) p :=
    congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) he.fderiv_eq
  change coordPartial i (coordPartial j (f ∘ κ)) p = _
  rw [he', coordPartial_sum_two _ hprod]
  have hm (a : Fin 2) : coordPartial i
      (fun q => coordPartial a f (κ q) * coordPartial j (fun x => κ x a) q) p =
      (∑ b : Fin 2, planarHessian f (κ p) b a * coordPartial i (fun q => κ q b) p) *
        coordPartial j (fun x => κ x a) p +
      coordPartial a f (κ p) * planarHessian (fun q => κ q a) p i j := by
    rw [coordPartial_mul_at (hdf₁ a) (hdκ₁ a)]
    have hchain := scalar_partial_comp
      ((((partial_contDiffOn hf hU a) (κ p) (hmap hp)).contDiffAt
        (hU.mem_nhds (hmap hp))).differentiableAt (by simp)) hdκ i
    exact congrArg (fun t : ℝ => t * coordPartial j (fun x => κ x a) p +
      coordPartial a f (κ p) * coordPartial i (coordPartial j (fun q => κ q a)) p) hchain
  simp only [hm, Fin.sum_univ_two]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, seamCoordinateJacobian,
    Fin.sum_univ_two]
  ring

private theorem vector_partial_comp {X : Coord → Ambient} {κ : Coord → Coord} {p : Coord}
    (hX : DifferentiableAt ℝ X (κ p)) (hκ : DifferentiableAt ℝ κ p) (i : Fin 2) :
    coordPartial i (X ∘ κ) p =
      ∑ a : Fin 2, coordPartial i (fun q => κ q a) p • coordPartial a X (κ p) := by
  have hv : coordPartial i κ p =
      (coordPartial i κ p 0) • (Pi.single 0 (1 : ℝ) : Coord) +
      (coordPartial i κ p 1) • (Pi.single 1 (1 : ℝ) : Coord) := by
    ext a
    fin_cases a <;> simp
  change fderiv ℝ (X ∘ κ) p (Pi.single i 1) = _
  rw [fderiv_comp p hX hκ]
  change fderiv ℝ X (κ p) (coordPartial i κ p) = _
  rw [hv]
  simp only [map_add, map_smul, Fin.sum_univ_two]
  rw [component_partial hκ 0 i, component_partial hκ 1 i]
  rfl

/-- The actual induced first form changes by Jacobian congruence. -/
theorem protectedTorus_curvature_inducedMetric_comp
    {X : Coord → Ambient} {κ : Coord → Coord} {p : Coord}
    (hX : DifferentiableAt ℝ X (κ p)) (hκ : DifferentiableAt ℝ κ p) :
    inducedMetric (X ∘ κ) p =
      (seamCoordinateJacobian κ p).transpose * inducedMetric X (κ p) *
        seamCoordinateJacobian κ p := by
  ext i j
  change inner ℝ (coordPartial i (X ∘ κ) p) (coordPartial j (X ∘ κ) p) = _
  rw [vector_partial_comp hX hκ i, vector_partial_comp hX hκ j]
  simp only [Fin.sum_univ_two, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, Matrix.mul_apply,
    Matrix.transpose_apply, seamCoordinateJacobian, inducedMetric]
  ring

/-- Actual differential orthogonality survives composition by the chain rule. -/
theorem protectedTorus_curvature_unitNormal_comp
    {X : Coord → Ambient} {κ : Coord → Coord} {p : Coord} {n : Ambient}
    (hX : DifferentiableAt ℝ X (κ p)) (hκ : DifferentiableAt ℝ κ p)
    (hn : IsUnitNormalAt X n (κ p)) : IsUnitNormalAt (X ∘ κ) n p := by
  refine ⟨hn.1, fun v => ?_⟩
  rw [fderiv_comp p hX hκ]
  change inner ℝ (fderiv ℝ X (κ p) (fderiv ℝ κ p v)) n = 0
  exact hn.2 (fderiv ℝ κ p v)

/-- The actual normal second form changes by the same Jacobian congruence.
Coordinate second derivatives cancel because the actual normal height has
zero differential, rather than by a supplied second-form identity. -/
theorem protectedTorus_curvature_secondFundamental_comp
    {X : Coord → Ambient} {κ : Coord → Coord} {U V : Set Coord}
    (hU : IsOpen U) (hV : IsOpen V)
    (hX : ContDiffOn ℝ ∞ X U) (hκ : ContDiffOn ℝ ∞ κ V)
    (hmap : MapsTo κ V U) {p : Coord} (hp : p ∈ V) {n : Ambient}
    (hn : IsUnitNormalAt X n (κ p)) :
    secondFundamental (X ∘ κ) n p =
      (seamCoordinateJacobian κ p).transpose * secondFundamental X n (κ p) *
        seamCoordinateJacobian κ p := by
  have hcomp : ContDiffOn ℝ ∞ (X ∘ κ) V := hX.comp hκ hmap
  have hz (a : Fin 2) : coordPartial a (height X n) (κ p) = 0 := by
    simp only [coordPartial, height_derivative_at_normal hX hU (hmap hp) hn, zero_apply]
  ext i j
  have he := protectedTorus_curvature_planarHessian_comp hU hV (height_smooth hX n) hκ hmap hp i j
  have hh : height X n ∘ κ = height (X ∘ κ) n := rfl
  rw [hh] at he
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero] at he
  change coordPartial i (coordPartial j (height (X ∘ κ) n)) p = _ at he
  have hH : planarHessian (height X n) (κ p) = secondFundamental X n (κ p) := by
    ext a b
    exact second_partial_height hX hU (hmap hp) n a b
  calc
    secondFundamental (X ∘ κ) n p i j =
        coordPartial i (coordPartial j (height (X ∘ κ) n)) p :=
      (second_partial_height hcomp hV hp n i j).symm
    _ = ((seamCoordinateJacobian κ p).transpose * planarHessian (height X n) (κ p) *
        seamCoordinateJacobian κ p) i j := he
    _ = _ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      ((seamCoordinateJacobian κ p).transpose * A * seamCoordinateJacobian κ p) i j) hH

/-- Genuine Gaussian curvature is invariant under an ordinary local smooth
coordinate reparametrization with actual derivative rank. -/
theorem protectedTorus_curvature_reparam
    {X : Coord → Ambient} {κ : Coord → Coord} {U V : Set Coord}
    (hU : IsOpen U) (hV : IsOpen V)
    (hX : ContDiffOn ℝ ∞ X U) (hκ : ContDiffOn ℝ ∞ κ V)
    (hmap : MapsTo κ V U)
    (hXinj : ∀ q ∈ U, Function.Injective (fderiv ℝ X q))
    (hκinj : ∀ q ∈ V, Function.Injective (fderiv ℝ κ q))
    {p : Coord} (hp : p ∈ V) {n : Ambient} (hn : IsUnitNormalAt X n (κ p)) :
    gaussianCurvature (inducedMetric (X ∘ κ)) p =
      gaussianCurvature (inducedMetric X) (κ p) := by
  have hcomp : ContDiffOn ℝ ∞ (X ∘ κ) V := hX.comp hκ hmap
  have hdX : DifferentiableAt ℝ X (κ p) :=
    ((hX (κ p) (hmap hp)).contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by simp)
  have hdκ : DifferentiableAt ℝ κ p :=
    ((hκ p hp).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hinj : ∀ q ∈ V, Function.Injective (fderiv ℝ (X ∘ κ) q) := by
    intro q hq v w he
    rw [fderiv_comp q
      (((hX (κ q) (hmap hq)).contDiffAt (hU.mem_nhds (hmap hq))).differentiableAt (by simp))
      (((hκ q hq).contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp))] at he
    change fderiv ℝ X (κ q) (fderiv ℝ κ q v) = fderiv ℝ X (κ q) (fderiv ℝ κ q w) at he
    exact hκinj q hq (hXinj (κ q) (hmap hq) he)
  have hg := inducedMetric_smoothPositiveOn hX hU hXinj
  have hgcomp := inducedMetric_smoothPositiveOn hcomp hV hinj
  have hncomp := protectedTorus_curvature_unitNormal_comp hdX hdκ hn
  have hm := protectedTorus_curvature_inducedMetric_comp hdX hdκ
  have hs := protectedTorus_curvature_secondFundamental_comp hU hV hX hκ hmap hp hn
  have hdet : (inducedMetric (X ∘ κ) p).det =
      (seamCoordinateJacobian κ p).det^2 * (inducedMetric X (κ p)).det := by
    rw [hm]
    simp only [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hJ : (seamCoordinateJacobian κ p).det ≠ 0 := by
    intro hz
    have hc := metricDet_ne_zero hgcomp hp
    rw [hdet, hz, zero_pow (by norm_num), zero_mul] at hc
    exact hc rfl
  rw [curvature_eq_second_form_det_div_metric_det hgcomp
      (inducedMetric_isometricOn hcomp) hV hp hncomp,
    curvature_eq_second_form_det_div_metric_det hg
      (inducedMetric_isometricOn hX) hU (hmap hp) hn, hs, hdet]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  field_simp [hJ, metricDet_ne_zero hg (hmap hp)]

end
end TightVer401
