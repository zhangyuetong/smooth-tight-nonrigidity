import TightVer401.CompletedSaddleAnnulusGraphs
import TightVer401.GaussBridge
import TightVer401.SurfaceMetric
import TightVer401.ScalarCoordinateCalculus

/-! Negative actual intrinsic curvature for the same upper and lower graphs.
The true unit normal and actual second-form entries are computed here;
neither curvature nor an independently realized metric is assumed. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

private theorem completedSaddleAnnulusGraph_component_partial
    {F : Coord → Ambient} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {y : Coord} (hy : y ∈ U) (i : Fin 2) (k : Fin 3) :
    coordPartial i F y k = coordPartial i (fun x => F x k) y := by
  have hd := ((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).hasFDerivAt.comp
    y hd.hasFDerivAt
  unfold coordPartial
  have hh : fderiv ℝ (fun x => F x k) y =
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).comp (fderiv ℝ F y) := hc.fderiv
  rw [hh]
  rfl

private theorem completedSaddleAnnulusGraph_first_partial
    {F : Coord → Ambient} {z : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hCoords : ∀ x ∈ U, F x = WithLp.toLp 2 ![-x 0,-x 1,z x])
    {y : Coord} (hy : y ∈ U) (j : Fin 2) :
    coordPartial j F y = WithLp.toLp 2
      ![-(Pi.single j 1 : Coord) 0,-(Pi.single j 1 : Coord) 1,coordPartial j z y] := by
  have he₀ : (fun x => F x 0) =ᶠ[𝓝 y] (fun x => -x 0) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    rw [hCoords x hx]
    rfl
  have he₁ : (fun x => F x 1) =ᶠ[𝓝 y] (fun x => -x 1) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    rw [hCoords x hx]
    rfl
  have he₂ : (fun x => F x 2) =ᶠ[𝓝 y] z := by
    filter_upwards [hU.mem_nhds hy] with x hx
    rw [hCoords x hx]
    rfl
  ext k
  fin_cases k
  · change coordPartial j F y 0 = -(Pi.single j 1 : Coord) 0
    rw [completedSaddleAnnulusGraph_component_partial hF hU hy j 0,
      coordPartial_eventuallyEq he₀ j]
    change fderiv ℝ (fun x : Coord => -x 0) y (Pi.single j 1) = _
    have hn : HasFDerivAt (fun x : Coord => -x 0)
        (-(ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ)) y :=
      ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ).hasFDerivAt (x := y)).neg
    rw [hn.fderiv]
    rfl
  · change coordPartial j F y 1 = -(Pi.single j 1 : Coord) 1
    rw [completedSaddleAnnulusGraph_component_partial hF hU hy j 1,
      coordPartial_eventuallyEq he₁ j]
    change fderiv ℝ (fun x : Coord => -x 1) y (Pi.single j 1) = _
    have hn : HasFDerivAt (fun x : Coord => -x 1)
        (-(ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ)) y :=
      ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ).hasFDerivAt (x := y)).neg
    rw [hn.fderiv]
    rfl
  · change coordPartial j F y 2 = coordPartial j z y
    rw [completedSaddleAnnulusGraph_component_partial hF hU hy j 2,
      coordPartial_eventuallyEq he₂ j]

private theorem completedSaddleAnnulusGraph_second_partial
    {F : Coord → Ambient} {z : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hCoords : ∀ x ∈ U, F x = WithLp.toLp 2 ![-x 0,-x 1,z x])
    {y : Coord} (hy : y ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) y = WithLp.toLp 2
      ![0,0,planarHessian z y i j] := by
  have hD : ContDiffOn ℝ ∞ (coordPartial j F) U := partial_contDiffOn hF hU j
  have he₀ : (fun x => coordPartial j F x 0) =ᶠ[𝓝 y]
      (fun _ => -(Pi.single j 1 : Coord) 0) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    rw [completedSaddleAnnulusGraph_first_partial hF hU hCoords hx j]
    rfl
  have he₁ : (fun x => coordPartial j F x 1) =ᶠ[𝓝 y]
      (fun _ => -(Pi.single j 1 : Coord) 1) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    rw [completedSaddleAnnulusGraph_first_partial hF hU hCoords hx j]
    rfl
  have he₂ : (fun x => coordPartial j F x 2) =ᶠ[𝓝 y] coordPartial j z := by
    filter_upwards [hU.mem_nhds hy] with x hx
    rw [completedSaddleAnnulusGraph_first_partial hF hU hCoords hx j]
    rfl
  ext k
  fin_cases k
  · change coordPartial i (coordPartial j F) y 0 = 0
    rw [completedSaddleAnnulusGraph_component_partial hD hU hy i 0,
      coordPartial_eventuallyEq he₀ i,coordPartial_scalar_const]
  · change coordPartial i (coordPartial j F) y 1 = 0
    rw [completedSaddleAnnulusGraph_component_partial hD hU hy i 1,
      coordPartial_eventuallyEq he₁ i,coordPartial_scalar_const]
  · change coordPartial i (coordPartial j F) y 2 = planarHessian z y i j
    rw [completedSaddleAnnulusGraph_component_partial hD hU hy i 2,
      coordPartial_eventuallyEq he₂ i]
    rfl

private theorem completedSaddleAnnulusGraph_unit_normal
    {F : Coord → Ambient} {z : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hCoords : ∀ x ∈ U, F x = WithLp.toLp 2 ![-x 0,-x 1,z x])
    {y : Coord} (hy : y ∈ U) :
    IsUnitNormalAt F (planarUnitNormal (planarGradient z y)) y := by
  refine ⟨planarUnitNormal_unit _,?_⟩
  have hp (i : Fin 2) :
      inner ℝ (coordPartial i F y) (planarUnitNormal (planarGradient z y)) = 0 := by
    rw [completedSaddleAnnulusGraph_first_partial hF hU hCoords hy i]
    simp only [planarUnitNormal,EuclideanSpace.inner_toLp_toLp]
    fin_cases i <;> simp [dotProduct,Fin.sum_univ_succ,planarGradient] <;> ring
  intro v
  rw [fderiv_two_coordinates,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    hp 0,hp 1]
  simp

private theorem completedSaddleAnnulusGraph_second_form
    {F : Coord → Ambient} {z : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hCoords : ∀ x ∈ U, F x = WithLp.toLp 2 ![-x 0,-x 1,z x])
    {y : Coord} (hy : y ∈ U) :
    secondFundamental F (planarUnitNormal (planarGradient z y)) y =
      (planarWeight (planarGradient z y))⁻¹ • planarHessian z y := by
  ext i j
  change inner ℝ (coordPartial i (coordPartial j F) y)
    (planarUnitNormal (planarGradient z y)) = _
  rw [completedSaddleAnnulusGraph_second_partial hF hU hCoords hy i j]
  simp only [planarUnitNormal,EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct,Fin.sum_univ_succ,div_eq_mul_inv]
  <;> ring

private theorem completedSaddleAnnulusGraph_saddle_curvature
    {F : Coord → Ambient} {z : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hCoords : ∀ x ∈ U, F x = WithLp.toLp 2 ![-x 0,-x 1,z x])
    (hRank : ∀ x ∈ U, Function.Injective (fderiv ℝ F x))
    {y : Coord} (hy : y ∈ U) (hdet : (planarHessian z y).det < 0) :
    gaussianCurvature (inducedMetric F) y < 0 := by
  apply (negative_curvature_iff_second_form_det_neg
    (inducedMetric_smoothPositiveOn hF hU hRank) (inducedMetric_isometricOn hF) hU hy
    (completedSaddleAnnulusGraph_unit_normal hF hU hCoords hy)).mpr
  rw [completedSaddleAnnulusGraph_second_form hF hU hCoords hy,Matrix.det_smul]
  simp only [Fintype.card_fin]
  exact mul_neg_of_pos_of_neg
    (sq_pos_of_pos (inv_pos.mpr (planarWeight_pos (planarGradient z y)))) hdet

private theorem completedSaddleAnnulusGraph_affine_hessian
    {f : Coord → ℝ} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (c σ : ℝ) {y : Coord} (hy : y ∈ U) :
    planarHessian (fun x => c+σ*f x) y = σ • planarHessian f y := by
  have hFirst {x : Coord} (hx : x ∈ U) (j : Fin 2) :
      coordPartial j (fun x => c+σ*f x) x = σ*coordPartial j f x := by
    have hd := ((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    unfold coordPartial
    rw [((hd.hasFDerivAt.const_mul σ).const_add c).fderiv]
    rfl
  ext i j
  have he : coordPartial j (fun x => c+σ*f x) =ᶠ[𝓝 y]
      (fun x => σ*coordPartial j f x) := by
    filter_upwards [hU.mem_nhds hy] with x hx using hFirst hx j
  change coordPartial i (coordPartial j (fun x => c+σ*f x)) y =
    σ*coordPartial i (coordPartial j f) y
  rw [coordPartial_eventuallyEq he i]
  have hd := (((partial_contDiffOn hf hU j) y hy).contDiffAt
    (hU.mem_nhds hy)).differentiableAt (by simp)
  change fderiv ℝ (fun x => σ * coordPartial j f x) y (Pi.single i 1) =
    σ * fderiv ℝ (coordPartial j f) y (Pi.single i 1)
  rw [(hd.hasFDerivAt.const_mul σ).fderiv]
  rfl

/-- Both same-object actual completed support graphs have strictly negative
intrinsic Gaussian curvature, from the actual completed potential Hessian. -/
theorem completedSaddleAnnulusGraphs_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    {y : Coord} (hy : y ∈ e.target) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusUpperGraph G e dInfinity)) y < 0 ∧
    gaussianCurvature (inducedMetric (completedSaddleAnnulusLowerGraph G e dInfinity)) y < 0 := by
  have hL := planarLegendre_contDiffOn e hG hi
  have hdet := planarLegendre_saddle e hG hi heG hy (hNeg _ (e.map_target hy))
  have hGraphs := completedSaddleAnnulusGraphs_contDiffOn e dInfinity hG hi
  constructor
  · apply completedSaddleAnnulusGraph_saddle_curvature hGraphs.1 e.open_target
      (z := fun x => dInfinity+(1:ℝ)*planarLegendre G e x)
      (fun x _ => by
        ext k
        fin_cases k <;> simp [completedSaddleAnnulusUpperGraph,
          completedSaddleAnnulusGraphHeight] <;> ring)
      (fun x hx => (completedSaddleAnnulusGraphs_differential_injective e dInfinity hG hi hx).1) hy
    rw [completedSaddleAnnulusGraph_affine_hessian hL e.open_target dInfinity 1 hy]
    simpa only [one_smul] using hdet
  · apply completedSaddleAnnulusGraph_saddle_curvature hGraphs.2 e.open_target
      (z := fun x => -dInfinity+(-1:ℝ)*planarLegendre G e x)
      (fun x _ => by
        ext k
        fin_cases k <;> simp [completedSaddleAnnulusLowerGraph,
          completedSaddleAnnulusGraphHeight] <;> ring)
      (fun x hx => (completedSaddleAnnulusGraphs_differential_injective e dInfinity hG hi hx).2) hy
    rw [completedSaddleAnnulusGraph_affine_hessian hL e.open_target (-dInfinity) (-1) hy,
      Matrix.det_smul]
    simpa using hdet

theorem completedSaddleAnnulusUpperGraph_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    {y : Coord} (hy : y ∈ e.target) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusUpperGraph G e dInfinity)) y < 0 :=
  (completedSaddleAnnulusGraphs_gaussianCurvature_neg e dInfinity hG hi heG hNeg hy).1

theorem completedSaddleAnnulusLowerGraph_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    {y : Coord} (hy : y ∈ e.target) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusLowerGraph G e dInfinity)) y < 0 :=
  (completedSaddleAnnulusGraphs_gaussianCurvature_neg e dInfinity hG hi heG hNeg hy).2

end
end TightVer401
