import TightVer401.AnnularDegreeGradient
import TightVer401.AnnularDegreeJordanWinding
import TightVer401.QuadraticRadialFillingGradientComponentMap
import TightVer401.QuadraticRadialFillingImageAssembly
import TightVer401.QuadraticRadialFillingRoundAnnulus
import TightVer401.QuadraticRadialFillingRoundUnitTurn
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

/-! Actual ordinary annular degree data for the same smoothed quadratic
filling. Source positivity and actual angular integrals are derived from
literal circles and scalar germs. No count or inverse package is an input. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem quadraticRadialFillingDegree_coord_symm (x : Coord) :
    seamComplexCoord.symm x = angularDescentComplex x := by
  apply seamComplexCoord.injective
  rw [seamComplexCoord.apply_symm_apply,quadraticRadialFillingCoord_complex]

private theorem quadraticRadialFillingDegree_round_eq (r : ℝ) (hr : 0 < r) :
    roundDiskChart r hr = quadraticRadialFillingRoundFilling r hr := by
  ext z
  change (r : ℂ) * z = r • z
  rw [Complex.real_smul]

/-- Positive actual round source parametrization: the regular circuit is
pinned and its positive turn is supplied by the explicit round angle. -/
theorem quadraticRadialFillingDegree_positive_round (r : ℝ) (hr : 0 < r) :
    PositiveJordanParametrization (roundDiskChart r hr) (unitCircleParam 0 r) := by
  have h := unitCircleParam_regular r hr
  refine ⟨h.smooth,h.periodic,h.injective,h.regular,h.boundary,?_⟩
  intro z hz
  rw [roundDiskChart_interior] at hz
  have hzn : ‖z‖ < r := by simpa only [mem_ball,dist_zero_right] using hz
  obtain ⟨u,hu,hturn⟩ := quadraticRadialFillingRound_exists_normalized_argument_unit_turn hr hzn
  exact ⟨u,fun t => (hu t).symm,hturn⟩

private theorem quadraticRadialFillingDegree_complex_smooth
    {H : Coord → ℝ} {V : Set Coord} (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V) :
    ContDiffOn ℝ ∞ (annularComplexConjugate (planarGradient H))
      (seamComplexCoord ⁻¹' V) := by
  exact seamComplexCoord.symm.contDiff.comp_contDiffOn
    ((planarGradient_contDiffOn hH hV).comp seamComplexCoord.contDiff.contDiffOn
      (fun _ hz => hz))

private theorem quadraticRadialFillingDegree_complex_trace (H : Coord → ℝ) (r s : ℝ) :
    annularComplexConjugate (planarGradient H) (circleMap 0 r s) =
      quadraticRadialFillingGradientComplexTrace H r s := by
  change seamComplexCoord.symm (planarGradient H
      (seamComplexCoord (quadraticRadialFillingCircle r s))) = _
  rw [quadraticRadialFillingCircle_coord,quadraticRadialFillingDegree_coord_symm] <;> rfl

/-- The ordinary positive position pairing on the actual source circle
implies the unit radial pairing used by the explicit actual direction lift. -/
theorem quadraticRadialFillingDegree_radial_unit_positive
    {H : Coord → ℝ} {S : ℝ} (hS : 0 < S)
    (hPosition : ∀ s, 0 < planarGradient H (saddlePolarChart ![S,s]) ⬝ᵥ
      saddlePolarChart ![S,s]) :
    ∀ s, 0 < quadraticRadialFillingGradientTrace H S s ⬝ᵥ ![Real.cos s,Real.sin s] := by
  intro s
  have hs := hPosition s
  have hpair : planarGradient H (saddlePolarChart ![S,s]) ⬝ᵥ
      saddlePolarChart ![S,s] =
      S * (quadraticRadialFillingGradientTrace H S s ⬝ᵥ ![Real.cos s,Real.sin s]) := by
    simp only [quadraticRadialFillingGradientTrace, saddlePolarChart, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hpair] at hs
  exact pos_of_mul_pos_right hs hS.le
/-- The actual retained scalar germ fixes the entire actual inner gradient
trace, including its orientation; no winding or image premise is supplied. -/
theorem quadraticRadialFillingDegree_inner_trace
    {R M ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ < R/2)
    {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) (s : ℝ) :
    quadraticRadialFillingGradientComplexTrace H ρ s = circleMap 0 (M*(R-ρ)) s := by
  change angularDescentComplex (planarGradient H (saddlePolarChart ![ρ,s])) = _
  rw [quadraticRadialFilling_inner_gradient_circle hR M (fun _ => 0) (fun _ => 0)
    hInner hρ hρR,quadraticFillerCartesianGradientCircle_eq hR M (fun _ => 0)
      (fun _ => 0) hρ hρR]
  apply Complex.ext <;> simp [angularDescentComplex, circleMap_zero_re, circleMap_zero_im,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem quadraticRadialFillingDegree_integral_from_unit_lift
    {F : ℂ → ℂ} {O : Set ℂ} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (hγO : ∀ t, γ t ∈ O)
    {y : ℂ} (hAvoid : ∀ t, F (γ t) ≠ y)
    (u : C(unitInterval, ℝ))
    (hu : ∀ t : unitInterval, normalizedArgument (F (γ t)-y) = (u t : UnitAddCircle))
    (hturn : u 1 = u 0 + 1) :
    planarFormIntegral (annularAngularFormP F y) (annularAngularFormQ F y) γ = 1 := by
  rw [annularAngularForm_integral_eq_pathIncrement hO hF hγ hγO y hAvoid]
  unfold pathArgumentIncrement
  rw [circlePathIncrement_eq_lift _ u (fun t => (hu t).symm),hturn]
  ring

/-- The actual radial-positive outer gradient has angular integral one
around zero, derived from its explicit actual real direction lift. -/
theorem quadraticRadialFillingDegree_outer_integral_zero
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord}
    (hS : 0 < S) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircle : quadraticRadialFillingRadiusLevel S ⊆ V)
    (hRadial : ∀ s, 0 < quadraticRadialFillingGradientTrace H S s ⬝ᵥ
      ![Real.cos s,Real.sin s]) :
    planarFormIntegral (annularAngularFormP (annularComplexConjugate (planarGradient H)) 0)
      (annularAngularFormQ (annularComplexConjugate (planarGradient H)) 0)
      (unitCircleParam 0 S) = 1 := by
  have hγ := quadraticRadialFillingDegree_positive_round S hS
  have hCircleO : ∀ t, unitCircleParam 0 S t ∈ seamComplexCoord ⁻¹' V := by
    intro t
    apply hCircle
    rw [show unitCircleParam 0 S t = quadraticRadialFillingCircle S (2*Real.pi*t) from rfl,
      quadraticRadialFillingCircle_coord]
    exact quadraticRadialFilling_radiusLevel_polar hS _
  obtain ⟨u,hu,hturn⟩ := quadraticRadialFillingGradient_exists_normalized_argument_unit_turn
    hS hV hH hCircle hRadial
  apply quadraticRadialFillingDegree_integral_from_unit_lift
    (hV.preimage seamComplexCoord.continuous) (quadraticRadialFillingDegree_complex_smooth hV hH)
    hγ.smooth hCircleO (u := u)
  · intro t
    rw [show unitCircleParam 0 S t = circleMap 0 S (2*Real.pi*t) from rfl,
      quadraticRadialFillingDegree_complex_trace]
    exact quadraticRadialFillingGradientComplexTrace_ne_zero hRadial _
  · intro t
    simpa only [unitCircleParam,quadraticRadialFillingDegree_complex_trace,sub_zero] using hu t
  · exact hturn

/-- Actual Jordan interior constancy moves the independently derived outer
integral at zero to the precise Gamma-center test required by degree. -/
theorem quadraticRadialFillingDegree_outer_integral_center
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord} (Γ : ℂ ≃ₜ ℂ)
    (hS : 0 < S) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircle : quadraticRadialFillingRadiusLevel S ⊆ V)
    (hRadial : ∀ s, 0 < quadraticRadialFillingGradientTrace H S s ⬝ᵥ
      ![Real.cos s,Real.sin s])
    (hTrace : range (quadraticRadialFillingGradientComplexTrace H S) = Γ '' sphere (0:ℂ) 1)
    (hOrigin : (0:ℂ) ∈ Γ '' ball (0:ℂ) 1) :
    planarFormIntegral (annularAngularFormP (annularComplexConjugate (planarGradient H)) (Γ 0))
      (annularAngularFormQ (annularComplexConjugate (planarGradient H)) (Γ 0))
      (unitCircleParam 0 S) = 1 := by
  have hγ := quadraticRadialFillingDegree_positive_round S hS
  have hCircleO : ∀ t, unitCircleParam 0 S t ∈ seamComplexCoord ⁻¹' V := by
    intro t
    apply hCircle
    rw [show unitCircleParam 0 S t = quadraticRadialFillingCircle S (2*Real.pi*t) from rfl,
      quadraticRadialFillingCircle_coord]
    exact quadraticRadialFilling_radiusLevel_polar hS _
  have hImage : range (annularComplexConjugate (planarGradient H) ∘ unitCircleParam 0 S) ⊆
      frontier (jordanInterior Γ) := by
    rintro z ⟨t,rfl⟩
    rw [frontier_jordanInterior,← hTrace]
    exact ⟨2*Real.pi*t,(quadraticRadialFillingDegree_complex_trace H S _).symm⟩
  have hClosed : unitCircleParam 0 S 1 = unitCircleParam 0 S 0 := by
    simpa using hγ.periodic 0
  have hCenter : Γ 0 ∈ jordanInterior Γ := ⟨0,mem_ball_self zero_lt_one,rfl⟩
  have he := annularAngularForm_integral_eq_interior
    (hV.preimage seamComplexCoord.continuous) (quadraticRadialFillingDegree_complex_smooth hV hH)
    hγ.smooth hCircleO hClosed Γ hImage (Γ 0) 0 hCenter hOrigin
  exact he.trans (quadraticRadialFillingDegree_outer_integral_zero hS hV hH hCircle hRadial)

/-- The actual radial inner scalar germ gives the actual raw inner angular
integral one around zero. -/
theorem quadraticRadialFillingDegree_inner_integral_zero
    {R M ρ : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ) (hρR : ρ < R/2)
    {H : Coord → ℝ} {V : Set Coord} (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircle : quadraticRadialFillingRadiusLevel ρ ⊆ V)
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) :
    planarFormIntegral (annularAngularFormP (annularComplexConjugate (planarGradient H)) 0)
      (annularAngularFormQ (annularComplexConjugate (planarGradient H)) 0)
      (unitCircleParam 0 ρ) = 1 := by
  have hC : 0 < M*(R-ρ) := mul_pos hM (by linarith)
  have hγ := quadraticRadialFillingDegree_positive_round ρ hρ
  have hCircleO : ∀ t, unitCircleParam 0 ρ t ∈ seamComplexCoord ⁻¹' V := by
    intro t
    apply hCircle
    rw [show unitCircleParam 0 ρ t = quadraticRadialFillingCircle ρ (2*Real.pi*t) from rfl,
      quadraticRadialFillingCircle_coord]
    exact quadraticRadialFilling_radiusLevel_polar hρ _
  obtain ⟨u,hu,hturn⟩ := quadraticRadialFillingRound_exists_normalized_argument_unit_turn hC
    (z := 0) (by simpa using hC)
  apply quadraticRadialFillingDegree_integral_from_unit_lift
    (hV.preimage seamComplexCoord.continuous) (quadraticRadialFillingDegree_complex_smooth hV hH)
    hγ.smooth hCircleO (u := u)
  · intro t
    rw [show unitCircleParam 0 ρ t = circleMap 0 ρ (2*Real.pi*t) from rfl,
      quadraticRadialFillingDegree_complex_trace,quadraticRadialFillingDegree_inner_trace hR hρ hρR hInner]
    exact circleMap_ne_center hC.ne'
  · intro t
    simpa only [unitCircleParam,quadraticRadialFillingDegree_complex_trace,
      quadraticRadialFillingDegree_inner_trace hR hρ hρR hInner] using hu t
  · exact hturn

private theorem quadraticRadialFillingDegree_round_frontier (r : ℝ) (hr : 0 < r) :
    frontier (jordanInterior (roundDiskChart r hr)) = sphere (0 : ℂ) r := by
  rw [roundDiskChart_interior,frontier_ball _ hr.ne']

private theorem quadraticRadialFillingDegree_source_open
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    annularCoordJordanInterior (roundDiskChart S hS) (roundDiskChart ρ hρ) =
      quadraticRadialFillingOpenAnnulus ρ S := by
  unfold annularCoordJordanInterior annularJordanInterior
  rw [quadraticRadialFillingDegree_round_eq S hS,quadraticRadialFillingDegree_round_eq ρ hρ]
  exact quadraticRadialFillingRoundAnnulus_open_coord hρ hS

private theorem quadraticRadialFillingDegree_source_closed
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) :
    annularCoordJordanClosure (roundDiskChart S hS) (roundDiskChart ρ hρ) =
      quadraticRadialFillingClosedAnnulus ρ S := by
  unfold annularCoordJordanClosure annularJordanClosure
  rw [quadraticRadialFillingDegree_round_eq S hS,quadraticRadialFillingDegree_round_eq ρ hρ]
  change seamComplexCoord '' (closure
    (quadraticRadialFillingRoundFilling S hS '' ball (0 : ℂ) 1) \
      (quadraticRadialFillingRoundFilling ρ hρ '' ball (0 : ℂ) 1)) = _
  rw [quadraticRadialFillingRoundFilling_closure_ball]
  exact quadraticRadialFillingRoundAnnulus_closed_coord hρ hS

private theorem quadraticRadialFillingDegree_source_nested
    {ρ S : ℝ} (hρ : 0 < ρ) (hS : 0 < S) (hρS : ρ < S) :
    closure (jordanInterior (roundDiskChart ρ hρ)) ⊆
      jordanInterior (roundDiskChart S hS) := by
  rw [roundDiskChart_interior,roundDiskChart_interior,closure_ball _ hρ.ne']
  exact closedBall_subset_ball hρS

private theorem quadraticRadialFillingDegree_target_open
    {C : ℝ} (hC : 0 < C) (Γ : ℂ ≃ₜ ℂ) :
    annularCoordJordanInterior (roundDiskChart C hC) Γ =
      seamComplexCoord '' (ball (0 : ℂ) C \ Γ '' closedBall (0 : ℂ) 1) := by
  unfold annularCoordJordanInterior annularJordanInterior
  rw [roundDiskChart_interior,closure_jordanInterior]

private theorem quadraticRadialFillingDegree_target_closed
    {C : ℝ} (hC : 0 < C) (Γ : ℂ ≃ₜ ℂ) :
    annularCoordJordanClosure (roundDiskChart C hC) Γ =
      seamComplexCoord '' (closedBall (0 : ℂ) C \ Γ '' ball (0 : ℂ) 1) := by
  unfold annularCoordJordanClosure annularJordanClosure
  rw [roundDiskChart_interior,closure_ball _ hC.ne'] <;> rfl

/-- Derive the actual closed-band inverse from the SAME scalar filling and
ordinary gradient boundary data. The two raw disk turns are constructed;
negative Hessian sign and the swapped boundary assignment are explicit. -/
theorem quadraticRadialFillingDegree_exists_band_inverse
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hρR : ρ < R/2) (hρS : ρ < S)
    {H : Coord → ℝ} {V : Set Coord} (Γ : ℂ ≃ₜ ℂ)
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hBandV : quadraticRadialFillingClosedAnnulus ρ S ⊆ V)
    (hNeg : ∀ x ∈ quadraticRadialFillingOpenAnnulus ρ S, (planarHessian H x).det < 0)
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    (hOuter : InjOn (planarGradient H) (quadraticRadialFillingRadiusLevel S))
    (hTrace : range (quadraticRadialFillingGradientComplexTrace H S) = Γ '' sphere (0:ℂ) 1)
    (hOrigin : (0:ℂ) ∈ Γ '' ball (0:ℂ) 1)
    (hNested : Γ '' closedBall (0:ℂ) 1 ⊆ ball (0:ℂ) (M*(R-ρ)))
    (hRadial : ∀ s, 0 < quadraticRadialFillingGradientTrace H S s ⬝ᵥ
      ![Real.cos s,Real.sin s]) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      e.source = quadraticRadialFillingOpenAnnulus ρ S ∧
      e.target = seamComplexCoord '' (ball (0:ℂ) (M*(R-ρ)) \ Γ '' closedBall (0:ℂ) 1) ∧
      (e : Coord → Coord) = planarGradient H ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∃ E : quadraticRadialFillingClosedAnnulus ρ S ≃ₜ
          seamComplexCoord '' (closedBall (0:ℂ) (M*(R-ρ)) \ Γ '' ball (0:ℂ) 1),
        ∀ x, (E x : Coord) = planarGradient H x := by
  have hS : 0 < S := hρ.trans hρS
  have hC : 0 < M*(R-ρ) := mul_pos hM (by linarith)
  let Ho := roundDiskChart S hS
  let Hi := roundDiskChart ρ hρ
  let To := roundDiskChart (M*(R-ρ)) hC
  have hCircleS : quadraticRadialFillingRadiusLevel S ⊆ V := by
    intro x hx
    exact hBandV ⟨by rw [hx]; exact hρS.le,by rw [hx]⟩
  have hCircleρ : quadraticRadialFillingRadiusLevel ρ ⊆ V := by
    intro x hx
    exact hBandV ⟨by rw [hx],by rw [hx]; exact hρS.le⟩
  have hInnerInj : InjOn (planarGradient H) (quadraticRadialFillingRadiusLevel ρ) :=
    (quadraticRadialFilling_inner_gradient_injOn hR hM hInner).mono (by
      intro x hx
      exact ⟨by rw [hx]; exact hρ,by rw [hx]; exact hρR⟩)
  have hInnerTrace : range (quadraticRadialFillingGradientComplexTrace H ρ) =
      To '' sphere (0:ℂ) 1 := by
    rw [show quadraticRadialFillingGradientComplexTrace H ρ = circleMap 0 (M*(R-ρ))
      from funext (quadraticRadialFillingDegree_inner_trace hR hρ hρR hInner)]
    rw [range_circleMap,abs_of_pos hC]
    change sphere (0:ℂ) (M*(R-ρ)) = roundDiskChart (M*(R-ρ)) hC '' sphere (0:ℂ) 1
    rw [quadraticRadialFillingDegree_round_eq]
    exact (quadraticRadialFillingRoundFilling_sphere (M*(R-ρ)) hC).symm
  let outerComponent := quadraticRadialFillingGradientComponentHomeomorph
    hS hV hH hCircleS hOuter hTrace
  let innerComponent := quadraticRadialFillingGradientComponentHomeomorph
    hρ hV hH hCircleρ hInnerInj hInnerTrace
  let Bo : frontier (jordanInterior Ho) ≃ₜ frontier (jordanInterior Γ) :=
    ((Homeomorph.setCongr (quadraticRadialFillingDegree_round_frontier S hS)).trans
      outerComponent).trans (Homeomorph.setCongr (frontier_jordanInterior Γ).symm)
  let Bi : frontier (jordanInterior Hi) ≃ₜ frontier (jordanInterior To) :=
    ((Homeomorph.setCongr (quadraticRadialFillingDegree_round_frontier ρ hρ)).trans
      innerComponent).trans (Homeomorph.setCongr (frontier_jordanInterior To).symm)
  have hBo : ∀ x, (Bo x : ℂ) = annularComplexConjugate (planarGradient H) x := by
    intro x
    change angularDescentComplex (planarGradient H (seamComplexCoord x)) =
      seamComplexCoord.symm (planarGradient H (seamComplexCoord x))
    rw [quadraticRadialFillingDegree_coord_symm]
  have hBi : ∀ x, (Bi x : ℂ) = annularComplexConjugate (planarGradient H) x := by
    intro x
    change angularDescentComplex (planarGradient H (seamComplexCoord x)) =
      seamComplexCoord.symm (planarGradient H (seamComplexCoord x))
    rw [quadraticRadialFillingDegree_coord_symm]
  have hnS : closure (jordanInterior Hi) ⊆ jordanInterior Ho :=
    quadraticRadialFillingDegree_source_nested hρ hS hρS
  have hnT : closure (jordanInterior Γ) ⊆ jordanInterior To := by
    rw [closure_jordanInterior,roundDiskChart_interior]
    exact hNested
  have hKO : annularCoordJordanClosure Ho Hi ⊆ V := by
    rw [quadraticRadialFillingDegree_source_closed hρ hS]
    exact hBandV
  have hSign : ∀ x ∈ annularCoordJordanInterior Ho Hi,
      0 < ((-1 : ℤ) : ℝ) * (planarHessian H x).det := by
    intro x hx
    rw [quadraticRadialFillingDegree_source_open hρ hS] at hx
    simpa only [Int.cast_neg,Int.cast_one,neg_one_mul] using neg_pos.mpr (hNeg x hx)
  have hWo := quadraticRadialFillingDegree_outer_integral_center Γ hS hV hH
    hCircleS hRadial hTrace hOrigin
  have hWi := quadraticRadialFillingDegree_inner_integral_zero hR hM hρ hρR hV hH
    hCircleρ hInner
  have hTo0 : To 0 = 0 := by
    dsimp only [To, roundDiskChart]
    change ((M * (R - ρ) : ℝ) : ℂ) * 0 = 0
    exact mul_zero _
  obtain ⟨e,hes,het,hef,hei,E,hE⟩ :=
    annular_degree_planarGradient_global_diffeomorphism Ho Hi To Γ
      (unitCircleParam 0 S) (unitCircleParam 0 ρ)
      (quadraticRadialFillingDegree_positive_round S hS)
      (quadraticRadialFillingDegree_positive_round ρ hρ) hnS hnT H V hV hH hKO
      (-1) (Or.inr rfl) hSign true Bo Bi hBo hBi 1 (by norm_num)
      (by simpa using hWo)
      (by simpa only [ite_true,hTo0] using hWi)
  rw [quadraticRadialFillingDegree_source_open hρ hS] at hes
  rw [quadraticRadialFillingDegree_target_open hC Γ] at het
  have hK : annularCoordJordanClosure Ho Hi = quadraticRadialFillingClosedAnnulus ρ S :=
    quadraticRadialFillingDegree_source_closed hρ hS
  have hL : annularCoordJordanClosure To Γ =
      seamComplexCoord '' (closedBall (0:ℂ) (M*(R-ρ)) \ Γ '' ball (0:ℂ) 1) :=
    quadraticRadialFillingDegree_target_closed hC Γ
  let E' := ((Homeomorph.setCongr hK).symm.trans E).trans (Homeomorph.setCongr hL)
  refine ⟨e,hes,het,hef,hei,E',?_⟩
  intro x
  exact hE ((Homeomorph.setCongr hK).symm x)

private theorem quadraticRadialFillingDegree_closed_target_coord (C : ℝ) (Γ : ℂ ≃ₜ ℂ) :
    seamComplexCoord '' (closedBall (0:ℂ) C \ Γ '' ball (0:ℂ) 1) =
      {y : Coord | planarRadius y ≤ C} \ seamComplexCoord '' (Γ '' ball (0:ℂ) 1) := by
  ext x
  constructor
  · rintro ⟨z,⟨hz,hn⟩,rfl⟩
    refine ⟨?_,?_⟩
    · change planarRadius (seamComplexCoord z) ≤ C
      rw [quadraticRadialFillingRadius_complex]
      simpa only [mem_closedBall,dist_zero_right] using hz
    · rintro ⟨w,hw,he⟩
      rw [seamComplexCoord.injective he] at hw
      exact hn hw
  · rintro ⟨hx,hn⟩
    refine ⟨seamComplexCoord.symm x,⟨?_,?_⟩,seamComplexCoord.apply_symm_apply x⟩
    · rw [mem_closedBall,dist_zero_right,← quadraticRadialFillingRadius_complex,
        seamComplexCoord.apply_symm_apply]
      exact hx
    · intro hz
      exact hn ⟨seamComplexCoord.symm x,hz,seamComplexCoord.apply_symm_apply x⟩

/-- The derived genuine band homeomorphism supplies exactly the ordinary
closed-band image and injection consumed by the retained inner assembly. -/
theorem quadraticRadialFillingDegree_closed_band_image_and_injOn
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M) (hρ : 0 < ρ)
    (hρR : ρ < R/2) (hρS : ρ < S)
    {H : Coord → ℝ} {V : Set Coord} (Γ : ℂ ≃ₜ ℂ)
    (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hBandV : quadraticRadialFillingClosedAnnulus ρ S ⊆ V)
    (hNeg : ∀ x ∈ quadraticRadialFillingOpenAnnulus ρ S, (planarHessian H x).det < 0)
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    (hOuter : InjOn (planarGradient H) (quadraticRadialFillingRadiusLevel S))
    (hTrace : range (quadraticRadialFillingGradientComplexTrace H S) = Γ '' sphere (0:ℂ) 1)
    (hOrigin : (0:ℂ) ∈ Γ '' ball (0:ℂ) 1)
    (hNested : Γ '' closedBall (0:ℂ) 1 ⊆ ball (0:ℂ) (M*(R-ρ)))
    (hRadial : ∀ s, 0 < quadraticRadialFillingGradientTrace H S s ⬝ᵥ
      ![Real.cos s,Real.sin s]) :
    planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
        {y : Coord | planarRadius y ≤ M*(R-ρ)} \ seamComplexCoord '' (Γ '' ball (0:ℂ) 1) ∧
      InjOn (planarGradient H) (quadraticRadialFillingClosedAnnulus ρ S) := by
  obtain ⟨e,hes,het,hef,hei,E,hE⟩ := quadraticRadialFillingDegree_exists_band_inverse
    hR hM hρ hρR hρS Γ hV hH hBandV hNeg hInner hOuter hTrace hOrigin hNested hRadial
  have hImage : planarGradient H '' quadraticRadialFillingClosedAnnulus ρ S =
      seamComplexCoord '' (closedBall (0:ℂ) (M*(R-ρ)) \ Γ '' ball (0:ℂ) 1) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [← hE ⟨x,hx⟩]
      exact (E ⟨x,hx⟩).property
    · intro hy
      obtain ⟨x,hx⟩ := E.surjective ⟨y,hy⟩
      refine ⟨x,x.property,?_⟩
      exact (hE x).symm.trans (congrArg Subtype.val hx)
  refine ⟨hImage.trans (quadraticRadialFillingDegree_closed_target_coord _ Γ),?_⟩
  intro x hx y hy he
  have hEq : E ⟨x,hx⟩ = E ⟨y,hy⟩ := Subtype.ext (by rw [hE,hE]; exact he)
  exact congrArg Subtype.val (E.injective hEq)
end
end TightVer401
