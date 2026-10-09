import TightVer401.CompletedSaddleAnnulusUpperChart
import TightVer401.CompletedSaddleAnnulusGraphCurvatureTransfer
import TightVer401.CompletedSaddleAnnulusCollarImmersion
import TightVer401.CompletedSaddleAnnulusCylinderRank
import TightVer401.RevolutionEndCurvature

/-! Actual preferred-chart germs and intrinsic curvature of the same cylinder.
All geometric germs below are derived from the literal cylinder definition. -/
open Manifold
open scoped Manifold ContDiff Topology Matrix RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter Function OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem cylinderCurvature_chart_symm (q : AddCircle (2 * Real.pi)) (u : ℝ)
    (x : Coord) :
    (chartAt (ModelProd ℝ ℝ) (q,u)).symm (x 0,x 1) =
      (q+periodProjection (2 * Real.pi) (x 0),x 1) := by
  apply Prod.ext
  · change (OAI.RawQuotientLie.addLeftChart (periodChart (2 * Real.pi)) q).symm (x 0) = _
    simpa [periodChart,periodProjection] using
      OAI.RawQuotientLie.addLeftChart_symm_apply (periodChart (2 * Real.pi)) q (x 0)
  · rfl

private theorem cylinderCurvature_chart_center (q : AddCircle (2 * Real.pi)) (u : ℝ) :
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
      (chartAt (ModelProd ℝ ℝ) (q,u) (q,u)) = (![0,u] : Coord) := by
  apply (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).injective
  change (chartAt (ModelProd ℝ ℝ) (q,u) (q,u) : ℝ × ℝ) = (0,u)
  apply Prod.ext
  · change (periodChart (2 * Real.pi)).symm (-q+q) = 0
    rw [neg_add_cancel]
    have h0 : periodChart (2 * Real.pi) (0:ℝ) = (0:AddCircle (2 * Real.pi)) := rfl
    simpa only [h0] using
      (periodChart (2 * Real.pi)).left_inv (periodChart_zero_source (2 * Real.pi))
  · rfl

private theorem cylinderCurvature_parameter_mem {β : ℝ → ℝ} {A RN v : ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hv : v ∈ Ioo (Real.pi/2) Real.pi) : β v ∈ Ioo A RN := by
  have hm : Real.pi/2 ∈ Icc (Real.pi/2) Real.pi :=
    ⟨le_rfl,by linarith [Real.pi_pos]⟩
  have he : Real.pi ∈ Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [Real.pi_pos],le_rfl⟩
  constructor
  · rw [← hβA]; exact hMono hm (Ioo_subset_Icc_self hv) hv.1
  · rw [← hβRN]; exact hMono (Ioo_subset_Icc_self hv) he hv.2

/-- The literal lower sheet is the same actual reflected graph, at every
ordinary lower-strip point. -/
theorem completedSaddleAnnulusCylinderMap_lowerGraph
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN : ℝ} (hA : 0 < A) (d0 dInfinity : ℝ) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    {p : AddCircle (2 * Real.pi) × ℝ} (hp : p ∈ univ ×ˢ Ioo (0:ℝ) (Real.pi/2)) :
    completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β p =
      completedSaddleAnnulusLowerGraph G e dInfinity
        (completedSaddleAnnulusCylinderPlanePoint (β (Real.pi-p.2)) p.1) := by
  have hv : Real.pi-p.2 ∈ Ioo (Real.pi/2) Real.pi := by
    constructor <;> linarith [hp.2.1,hp.2.2]
  have hr := cylinderCurvature_parameter_mem hMono hβA hβRN hv
  have hy : completedSaddleAnnulusCylinderPlanePoint (β (Real.pi-p.2)) p.1 ∈
      quadraticRadialFillingOpenAnnulus A RN := by
    change A < planarRadius _ ∧ planarRadius _ < RN
    rwa [completedSaddleAnnulusCylinderPlanePoint_radius (hA.trans hr.1)]
  rw [completedSaddleAnnulusCylinderMap,completedSaddleAnnulusCylinderPhase_lower hp.2.2.le,
    if_pos hp.2.2.le,completedSaddleAnnulusHeightResolved_eq_interior hy]
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective p.1
  rw [← hθ]
  change β (Real.pi-p.2) • revolutionCircleRadial (periodProjection (2 * Real.pi) θ) +
    (completedSaddleAnnulusGraphHeight G e
      (completedSaddleAnnulusCylinderPlanePoint (β (Real.pi-p.2))
        (periodProjection (2 * Real.pi) θ))-dInfinity) • revolutionAxis =
      completedSaddleAnnulusLowerGraph G e dInfinity
        (completedSaddleAnnulusCylinderPlanePoint (β (Real.pi-p.2))
          (periodProjection (2 * Real.pi) θ))
  rw [completedSaddleAnnulusCylinderPlanePoint_representative,
    revolutionCircleRadial_representative]
  ext i
  fin_cases i <;> simp [completedSaddleAnnulusLowerGraph,
    completedSaddleAnnulusPolarPoint,quadraticRadialFillingCircle_coord,
    saddlePolarChart,revolutionRadial,revolutionAxis]

/-- Actual upper graph germ in the actual preferred native coordinates. -/
theorem completedSaddleAnnulusCylinderMap_upper_coordinate_germ
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN : ℝ} (hA : 0 < A) (d0 dInfinity : ℝ) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (Real.pi/2) Real.pi)
    (θ : ℝ) (hθ : periodProjection (2 * Real.pi) θ = q) :
    nativeProductCoordinateMap (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (q,u) =ᶠ[𝓝 (![0,u] : Coord)]
        (completedSaddleAnnulusUpperGraph G e dInfinity ∘
          fun x : Coord => completedSaddleAnnulusPolarPoint (β (x 1)) (θ+x 0)) := by
  have hv : ∀ᶠ x : Coord in 𝓝 (![0,u] : Coord), x 1 ∈ Ioo (Real.pi/2) Real.pi :=
    (continuous_apply 1).continuousAt.eventually (isOpen_Ioo.mem_nhds hu)
  filter_upwards [hv] with x hx
  unfold nativeProductCoordinateMap
  rw [cylinderCurvature_chart_symm,
    completedSaddleAnnulusCylinderMap_upperGraph hA hβ hMono hβA hβRN G e d0 dInfinity
      (show (q+periodProjection (2 * Real.pi) (x 0),x 1) ∈
        univ ×ˢ Ioo (Real.pi/2) Real.pi from ⟨mem_univ _,hx⟩),
    ← hθ,← map_add,completedSaddleAnnulusCylinderPlanePoint_representative]
  rfl

/-- Actual reflected lower graph germ in the same preferred native atlas. -/
theorem completedSaddleAnnulusCylinderMap_lower_coordinate_germ
    (G : Coord → ℝ) (e : OpenPartialHomeomorph Coord Coord)
    {A RN : ℝ} (hA : 0 < A) (d0 dInfinity : ℝ) {β : ℝ → ℝ}
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) (Real.pi/2))
    (θ : ℝ) (hθ : periodProjection (2 * Real.pi) θ = q) :
    nativeProductCoordinateMap (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (q,u) =ᶠ[𝓝 (![0,u] : Coord)]
        (completedSaddleAnnulusLowerGraph G e dInfinity ∘
          fun x : Coord => completedSaddleAnnulusPolarPoint (β (Real.pi-x 1)) (θ+x 0)) := by
  have hv : ∀ᶠ x : Coord in 𝓝 (![0,u] : Coord), x 1 ∈ Ioo (0:ℝ) (Real.pi/2) :=
    (continuous_apply 1).continuousAt.eventually (isOpen_Ioo.mem_nhds hu)
  filter_upwards [hv] with x hx
  unfold nativeProductCoordinateMap
  rw [cylinderCurvature_chart_symm,
    completedSaddleAnnulusCylinderMap_lowerGraph G e hA d0 dInfinity hMono hβA hβRN
      (show (q+periodProjection (2 * Real.pi) (x 0),x 1) ∈
        univ ×ˢ Ioo (0:ℝ) (Real.pi/2) from ⟨mem_univ _,hx⟩),
    ← hθ,← map_add,completedSaddleAnnulusCylinderPlanePoint_representative]
  rfl

/-- The actual square parameter germ and actual infinity scalar formula
derive the polynomial neck in the preferred native chart. -/
theorem completedSaddleAnnulusCylinderMap_neck_coordinate_germ
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A*planarRadius p-B/planarRadius p+dInfinity)
    {β : ℝ → ℝ} (hβ : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2))
    (q : AddCircle (2 * Real.pi)) (θ : ℝ) (hθ : periodProjection (2 * Real.pi) θ = q) :
    nativeProductCoordinateMap (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β)
      (q,Real.pi/2) =ᶠ[𝓝 (![0,Real.pi/2] : Coord)]
        completedSaddleAnnulusMeridianRepresentative
          (fun v => A+B*(v-Real.pi/2)^2) (fun v => 2*B*(v-Real.pi/2)) θ := by
  have hg := completedSaddleAnnulusCylinderMap_neck_germ (d0 := d0) e hA hARN hB hL
    hSource hTarget heG hInfinity hβ
  have ht : Tendsto (fun x : Coord => x 1)
      (𝓝 (![0,Real.pi/2] : Coord)) (𝓝 (Real.pi/2)) :=
    (continuous_apply 1).tendsto _
  filter_upwards [ht.eventually hg] with x hx
  unfold nativeProductCoordinateMap
  rw [cylinderCurvature_chart_symm,hx (q+periodProjection (2 * Real.pi) (x 0)),← hθ,← map_add,
    revolutionCircleRadial_representative]
  rfl

private def cylinderCurvature_neckRadius (A B : ℝ) (v : ℝ) : ℝ :=
  A+B*(v-Real.pi/2)^2

private def cylinderCurvature_neckHeight (B : ℝ) (v : ℝ) : ℝ :=
  2*B*(v-Real.pi/2)

private theorem cylinderCurvature_neckRadius_deriv (A B v : ℝ) :
    HasDerivAt (cylinderCurvature_neckRadius A B) (2*B*(v-Real.pi/2)) v := by
  convert! (hasDerivAt_const v A).add
    (((hasDerivAt_id v).sub_const (Real.pi/2)).pow 2 |>.const_mul B) using 1 <;>
    simp [cylinderCurvature_neckRadius] <;> ring

private theorem cylinderCurvature_neckHeight_deriv (B v : ℝ) :
    HasDerivAt (cylinderCurvature_neckHeight B) (2*B) v := by
  convert! ((hasDerivAt_id v).sub_const (Real.pi/2)).const_mul (2*B) using 1 <;>
    simp [cylinderCurvature_neckHeight] <;> ring

private theorem cylinderCurvature_neck_smooth (A B θ : ℝ) :
    ContDiff ℝ ∞ (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ) := by
  have hr : ContDiff ℝ ∞ (fun p : Coord => cylinderCurvature_neckRadius A B (p 1)) :=
    contDiff_const.add (contDiff_const.mul (((contDiff_apply ℝ ℝ 1).sub contDiff_const).pow 2))
  have hz : ContDiff ℝ ∞ (fun p : Coord => cylinderCurvature_neckHeight B (p 1)) :=
    contDiff_const.mul ((contDiff_apply ℝ ℝ 1).sub contDiff_const)
  exact (hr.smul (revolutionRadial_contDiff.comp
    (contDiff_const.add (contDiff_apply ℝ ℝ 0)))).add (hz.smul contDiff_const)

private theorem cylinderCurvature_neck_fderiv (A B θ : ℝ) (p v : Coord) :
    fderiv ℝ (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ) p v =
      (v 1*(2*B*(p 1-Real.pi/2))) • revolutionRadial (θ+p 0) +
      ((A+B*(p 1-Real.pi/2)^2)*v 0) • revolutionAngular (θ+p 0) +
      (v 1*(2*B)) • revolutionAxis := by
  exact completedSaddleAnnulusMeridianRepresentative_fderiv
    (cylinderCurvature_neckRadius_deriv A B (p 1))
    (cylinderCurvature_neckHeight_deriv B (p 1)) θ v

private theorem cylinderCurvature_neck_rank {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (θ : ℝ) (p : Coord) :
    Injective (fderiv ℝ (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ) p) := by
  have hr : 0 < A+B*(p 1-Real.pi/2)^2 := by positivity
  rcases revolution_frame (θ+p 0) with ⟨hrr,haa,hzz,hra,hrz,haz⟩
  have har : inner ℝ (revolutionAngular (θ+p 0)) (revolutionRadial (θ+p 0)) = 0 := by
    rw [real_inner_comm,hra]
  have hza : inner ℝ revolutionAxis (revolutionAngular (θ+p 0)) = 0 := by
    rw [real_inner_comm,haz]
  intro v w hvw
  have hz : fderiv ℝ (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ) p (v-w) = 0 := by
    simp [map_sub,hvw]
  have h1 : (v-w) 1 = 0 := by
    have he := congrArg (fun a : Ambient => inner ℝ a revolutionAxis) hz
    simp only [cylinderCurvature_neck_fderiv,inner_add_left,real_inner_smul_left,
      inner_zero_left,hrz,haz,hzz,mul_zero,mul_one,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_right (by positivity : 2*B ≠ 0)
  have h0 : (v-w) 0 = 0 := by
    have he := congrArg (fun a : Ambient => inner ℝ a (revolutionAngular (θ+p 0))) hz
    simp only [cylinderCurvature_neck_fderiv,inner_add_left,real_inner_smul_left,
      inner_zero_left,hra,haa,hza,mul_zero,mul_one,zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hr.ne'
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

private theorem cylinderCurvature_neck_partial_zero (A B θ : ℝ) :
    coordPartial 0 (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ) =
      fun p => cylinderCurvature_neckRadius A B (p 1) • revolutionAngular (θ+p 0) := by
  funext p
  simp only [coordPartial,cylinderCurvature_neck_fderiv,Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),zero_mul,one_mul,mul_one,
    zero_smul,zero_add,add_zero,cylinderCurvature_neckRadius]

private theorem cylinderCurvature_neck_partial_one (A B θ : ℝ) :
    coordPartial 1 (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ) =
      fun p => cylinderCurvature_neckHeight B (p 1) • revolutionRadial (θ+p 0) +
        (2*B) • revolutionAxis := by
  funext p
  simp only [coordPartial,cylinderCurvature_neck_fderiv,Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),zero_mul,one_mul,mul_zero,
    zero_smul,add_zero,cylinderCurvature_neckHeight]

private theorem cylinderCurvature_neck_second_zero (A B θ : ℝ) (i : Fin 2) :
    coordPartial i (coordPartial 0 (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ))
        (![0,Real.pi/2] : Coord) =
      if i = 0 then (-A) • revolutionRadial θ else 0 := by
  rw [cylinderCurvature_neck_partial_zero]
  have ha : HasDerivAt (fun s => revolutionAngular (θ+s)) (-revolutionRadial θ) (0:ℝ) := by
    convert! (revolutionAngular_hasDerivAt (θ+(0:ℝ))).scomp 0
      ((hasDerivAt_id 0).const_add θ) using 1 <;>
      simp only [Function.comp_def,add_zero,one_smul]
  have hh := revolution_curve_product_partial
    (p := (![0,Real.pi/2] : Coord))
    (cylinderCurvature_neckRadius_deriv A B (Real.pi/2)) ha i
  fin_cases i <;> simpa [cylinderCurvature_neckRadius] using hh

private theorem cylinderCurvature_neck_second_one (A B θ : ℝ) (i : Fin 2) :
    coordPartial i (coordPartial 1 (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ))
        (![0,Real.pi/2] : Coord) =
      if i = 1 then (2*B) • revolutionRadial θ else 0 := by
  rw [cylinderCurvature_neck_partial_one]
  have hp : DifferentiableAt ℝ (fun p : Coord =>
      cylinderCurvature_neckHeight B (p 1) • revolutionRadial (θ+p 0))
        (![0,Real.pi/2] : Coord) := by
    have hSmooth : ContDiff ℝ ∞ (fun p : Coord =>
        cylinderCurvature_neckHeight B (p 1) • revolutionRadial (θ+p 0)) :=
      ((contDiff_const.mul ((contDiff_apply ℝ ℝ 1).sub contDiff_const)).smul
      (revolutionRadial_contDiff.comp (contDiff_const.add (contDiff_apply ℝ ℝ 0))))
    exact hSmooth.differentiable (by simp) _
  simp only [coordPartial,fderiv_fun_add hp (differentiableAt_const (c := (2*B) • revolutionAxis)),
    add_apply,fderiv_const_apply,zero_apply,add_zero]
  change coordPartial i (fun p : Coord =>
    cylinderCurvature_neckHeight B (p 1) • revolutionRadial (θ+p 0)) (![0,Real.pi/2] : Coord) = _
  have ha : HasDerivAt (fun s => revolutionRadial (θ+s)) (revolutionAngular θ) (0:ℝ) := by
    convert! (revolutionRadial_hasDerivAt (θ+(0:ℝ))).scomp 0
      ((hasDerivAt_id 0).const_add θ) using 1 <;>
      simp only [Function.comp_def,add_zero,one_smul]
  have hh := revolution_curve_product_partial
    (p := (![0,Real.pi/2] : Coord)) (cylinderCurvature_neckHeight_deriv B (Real.pi/2)) ha i
  fin_cases i <;> simpa [cylinderCurvature_neckHeight] using hh

private theorem cylinderCurvature_neck_negative {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (θ : ℝ) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusMeridianRepresentative
      (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ))
        (![0,Real.pi/2] : Coord) < 0 := by
  let X := completedSaddleAnnulusMeridianRepresentative
    (cylinderCurvature_neckRadius A B) (cylinderCurvature_neckHeight B) θ
  have hX := (cylinderCurvature_neck_smooth A B θ).contDiffOn (s := univ)
  have hg := inducedMetric_smoothPositiveOn hX isOpen_univ
    (fun p _ => cylinderCurvature_neck_rank hA hB θ p)
  rcases revolution_frame θ with ⟨hrr,haa,hzz,hra,hrz,haz⟩
  have har : inner ℝ (revolutionAngular θ) (revolutionRadial θ) = 0 := by
    rw [real_inner_comm,hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial θ) = 0 := by
    rw [real_inner_comm,hrz]
  have hrrNorm : ‖revolutionRadial θ‖^2 = 1 := by
    simpa only [real_inner_self_eq_norm_sq] using hrr
  have hn : IsUnitNormalAt X (revolutionRadial θ) (![0,Real.pi/2] : Coord) := by
    refine ⟨hrr,?_⟩
    intro v
    simp only [X,cylinderCurvature_neck_fderiv,Matrix.cons_val_zero,Matrix.cons_val_one,
      sub_self,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero,zero_smul,zero_add,
      inner_add_left,real_inner_smul_left,har,hzr,mul_zero,add_zero]
  have hBForm : secondFundamental X (revolutionRadial θ) (![0,Real.pi/2] : Coord) =
      !![-A,0;0,2*B] := by
    ext i j
    fin_cases j <;> fin_cases i <;>
      simp [secondFundamental,X,cylinderCurvature_neck_second_zero,
        cylinderCurvature_neck_second_one,real_inner_smul_left,hrrNorm]
  apply (negative_curvature_iff_second_form_det_neg hg (inducedMetric_isometricOn hX)
    isOpen_univ (mem_univ _) hn).mpr
  rw [hBForm,Matrix.det_fin_two]
  with_unfolding_all change (-A)*(2*B)-0*0 < 0
  rw [mul_zero,sub_zero]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hA) (mul_pos (by norm_num) hB)

/-- Strict negative actual intrinsic curvature at every actual native neck point. -/
theorem completedSaddleAnnulusCylinderMap_neck_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A*planarRadius p-B/planarRadius p+dInfinity)
    {β : ℝ → ℝ} (hβ : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2))
    (q : AddCircle (2 * Real.pi)) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) (q,Real.pi/2)))
        (![0,Real.pi/2] : Coord) < 0 := by
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective q
  rw [nativeProductPlane_curvature_of_chart_germ
    (completedSaddleAnnulusCylinderMap_neck_coordinate_germ e hA hARN hB hL
      hSource hTarget heG hInfinity hβ q θ hθ)]
  exact cylinderCurvature_neck_negative hA hB θ

private theorem cylinderCurvature_polar_eq (r : ℝ → ℝ) (θ : ℝ) :
    (fun p : Coord => completedSaddleAnnulusPolarPoint (r (p 1)) (θ+p 0)) =
      completedSaddleAnnulusCylinderPolarCoordinate r θ := by
  funext p
  rw [completedSaddleAnnulusCylinderPolarCoordinate,
    completedSaddleAnnulusCylinderPlanePoint_representative]

private theorem cylinderCurvature_polar_smooth {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (θ : ℝ) :
    ContDiff ℝ ∞ (fun p : Coord => completedSaddleAnnulusPolarPoint (r (p 1)) (θ+p 0)) := by
  rw [cylinderCurvature_polar_eq]
  exact completedSaddleAnnulusCylinderPolarCoordinate_contDiff hr θ

private theorem cylinderCurvature_polar_rank {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) {p : Coord} {r₁ : ℝ} (hd : HasDerivAt r r₁ (p 1))
    (hrpos : 0 < r (p 1)) (hr₁ : r₁ ≠ 0) (θ : ℝ) :
    Injective (fderiv ℝ (fun x : Coord =>
      completedSaddleAnnulusPolarPoint (r (x 1)) (θ+x 0)) p) := by
  rw [cylinderCurvature_polar_eq]
  exact completedSaddleAnnulusCylinderPolarCoordinate_fderiv_injective hr θ p hrpos.ne'
    (by rwa [hd.deriv])

/-- Actual intrinsic negative curvature of the same cylinder above the neck,
in its native preferred chart; polar regularity is derived from actual beta'. -/
theorem completedSaddleAnnulusCylinderMap_upper_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hPositive : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (Real.pi/2) Real.pi) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) (q,u)))
        (![0,u] : Coord) < 0 := by
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective q
  let φ : Coord → Coord := fun x => completedSaddleAnnulusPolarPoint (β (x 1)) (θ+x 0)
  let V : Set Coord := {x | x 1 ∈ Ioo (Real.pi/2) Real.pi}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_apply 1)
  have hφ := cylinderCurvature_polar_smooth hβ θ
  have hMaps : MapsTo φ V e.target := by
    intro x hx
    rw [hTarget]
    have hr := cylinderCurvature_parameter_mem hMono hβA hβRN hx
    change A < planarRadius (completedSaddleAnnulusPolarPoint (β (x 1)) (θ+x 0)) ∧
      planarRadius (completedSaddleAnnulusPolarPoint (β (x 1)) (θ+x 0)) < RN
    rwa [completedSaddleAnnulusPolarPoint_radius (hA.trans hr.1)]
  have hpV : (![0,u] : Coord) ∈ V := hu
  have hRank : Injective (fderiv ℝ φ (![0,u] : Coord)) :=
    cylinderCurvature_polar_rank hβ (hβ.differentiable (by simp) u).hasDerivAt
      (hA.trans (cylinderCurvature_parameter_mem hMono hβA hβRN hu).1)
      (hPositive u hu).ne' θ
  rw [nativeProductPlane_curvature_of_chart_germ
    (completedSaddleAnnulusCylinderMap_upper_coordinate_germ G e hA d0 dInfinity
      hβ hMono hβA hβRN q hu θ hθ)]
  exact completedSaddleAnnulusUpperGraph_chart_gaussianCurvature_neg e dInfinity hG hi heG
    hNeg hV hφ.contDiffOn hMaps hpV hRank

/-- The actual reflected lower sheet has the same intrinsic sign, derived
from the reflected beta derivative and actual lower graph. -/
theorem completedSaddleAnnulusCylinderMap_lower_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN d0 dInfinity : ℝ} (hA : 0 < A)
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hPositive : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) (Real.pi/2)) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) (q,u)))
        (![0,u] : Coord) < 0 := by
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective q
  let r : ℝ → ℝ := fun v => β (Real.pi-v)
  have hr : ContDiff ℝ ∞ r := hβ.comp (contDiff_const.sub contDiff_id)
  let φ : Coord → Coord := fun x => completedSaddleAnnulusPolarPoint (r (x 1)) (θ+x 0)
  let V : Set Coord := {x | x 1 ∈ Ioo (0:ℝ) (Real.pi/2)}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_apply 1)
  have hφ := cylinderCurvature_polar_smooth hr θ
  have hReflect (v : ℝ) (hv : v ∈ Ioo (0:ℝ) (Real.pi/2)) :
      Real.pi-v ∈ Ioo (Real.pi/2) Real.pi := by
    constructor <;> linarith [hv.1,hv.2]
  have hMaps : MapsTo φ V e.target := by
    intro x hx
    rw [hTarget]
    have hm := cylinderCurvature_parameter_mem hMono hβA hβRN (hReflect (x 1) hx)
    change A < planarRadius (completedSaddleAnnulusPolarPoint (r (x 1)) (θ+x 0)) ∧
      planarRadius (completedSaddleAnnulusPolarPoint (r (x 1)) (θ+x 0)) < RN
    rwa [completedSaddleAnnulusPolarPoint_radius (hA.trans hm.1)]
  have hd : HasDerivAt r (-deriv β (Real.pi-u)) u := by
    convert! ((hβ.differentiable (by simp) (Real.pi-u)).hasDerivAt).comp u
      ((hasDerivAt_const u Real.pi).sub (hasDerivAt_id u)) using 1 <;> simp [r]
  have hRank : Injective (fderiv ℝ φ (![0,u] : Coord)) :=
    cylinderCurvature_polar_rank hr hd
      (hA.trans (cylinderCurvature_parameter_mem hMono hβA hβRN (hReflect u hu)).1)
      (neg_ne_zero.mpr (hPositive _ (hReflect u hu)).ne') θ
  rw [nativeProductPlane_curvature_of_chart_germ
    (completedSaddleAnnulusCylinderMap_lower_coordinate_germ G e hA d0 dInfinity
      hMono hβA hβRN q hu θ hθ)]
  exact completedSaddleAnnulusLowerGraph_chart_gaussianCurvature_neg e dInfinity hG hi heG
    hNeg hV hφ.contDiffOn hMaps (show (![0,u] : Coord) ∈ V from hu) hRank

/-- Negative actual intrinsic curvature throughout the SAME native open cylinder strip. -/
theorem completedSaddleAnnulusCylinderMap_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A*planarRadius p-B/planarRadius p+dInfinity)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hPositive : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (hβNeck : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2))
    (q : AddCircle (2 * Real.pi)) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) Real.pi) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) (q,u)))
        (![0,u] : Coord) < 0 := by
  rcases lt_trichotomy u (Real.pi/2) with hLower | hNeck | hUpper
  · exact completedSaddleAnnulusCylinderMap_lower_gaussianCurvature_neg e hA hTarget
      hG hi heG hNeg hβ hMono hβA hβRN hPositive q ⟨hu.1,hLower⟩
  · subst u
    exact completedSaddleAnnulusCylinderMap_neck_gaussianCurvature_neg e hA hARN hB hL
      hSource hTarget heG hInfinity hβNeck q
  · exact completedSaddleAnnulusCylinderMap_upper_gaussianCurvature_neg e hA hTarget
      hG hi heG hNeg hβ hMono hβA hβRN hPositive q ⟨hUpper,hu.2⟩

/-- The same sign evaluated at the actual preferred-chart center, without
requiring a supplied coordinate-center identification. -/
theorem completedSaddleAnnulusCylinderMap_preferred_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    {A RN B L d0 dInfinity : ℝ} (hA : 0 < A) (hARN : A < RN) (hB : 0 < B) (hL : 0 < L)
    (hSource : e.source = {p : Coord | 0 < planarRadius p})
    (hTarget : e.target = quadraticRadialFillingOpenAnnulus A RN)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    (hNeg : ∀ p ∈ e.source, (planarHessian G p).det < 0)
    (hInfinity : ∀ p : Coord, L < planarRadius p →
      G p = A*planarRadius p-B/planarRadius p+dInfinity)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hMono : StrictMonoOn β (Icc (Real.pi/2) Real.pi))
    (hβA : β (Real.pi/2) = A) (hβRN : β Real.pi = RN)
    (hPositive : ∀ u ∈ Ioo (Real.pi/2) Real.pi, 0 < deriv β u)
    (hβNeck : β =ᶠ[𝓝 (Real.pi/2)] (fun u => A+B*(u-Real.pi/2)^2))
    (p : AddCircle (2 * Real.pi) × ℝ) (hp : p ∈ univ ×ˢ Ioo (0:ℝ) Real.pi) :
    gaussianCurvature (inducedMetric (nativeProductPlaneCoordinateMap
      (completedSaddleAnnulusCylinderMap G e A RN d0 dInfinity β) p))
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
        (chartAt (ModelProd ℝ ℝ) p p)) < 0 := by
  rw [cylinderCurvature_chart_center p.1 p.2]
  exact completedSaddleAnnulusCylinderMap_gaussianCurvature_neg e hA hARN hB hL
    hSource hTarget hG hi heG hNeg hInfinity hβ hMono hβA hβRN hPositive hβNeck p.1 hp.2

end
end TightVer401
