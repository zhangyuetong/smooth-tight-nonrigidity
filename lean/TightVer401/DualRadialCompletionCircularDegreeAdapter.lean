import TightVer401.DualRadialCompletionCircularDegree
import TightVer401.AnnularDegreeDefinitions
import TightVer401.AnnularDegreeAngularForm
import TightVer401.AnnularDegreeLocalOrientation
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization
import OAI.Analysis.CircleDomains.Topology.PeriodicCircleDescent

/-! Literal round-circle specialization of the actual annular-gradient degree claim. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open OAI.CircleDomainRigidity.FiniteTransfer
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

private theorem circular_coord_radius (z : ℂ) : planarRadius (seamComplexCoord z) = ‖z‖ := by
  rw [seamComplexCoord_apply]
  simp only [planarRadius, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_def, Complex.normSq_apply, pow_two]

private theorem circular_coord_inverse_norm (p : Coord) : ‖seamComplexCoord.symm p‖ = planarRadius p := by
  rw [← circular_coord_radius, seamComplexCoord.apply_symm_apply]

private theorem circular_polar_coordinates (r t : ℝ) :
    seamComplexCoord (unitCircleParam 0 r t) = saddlePolarChart ![r, 2 * Real.pi * t] := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, unitCircleParam, circleMap,
    saddlePolarChart, ← Complex.ofReal_mul]

private theorem circular_positive_param (r : ℝ) (hr : 0 < r) :
    PositiveJordanParametrization (roundDiskChart r hr) (unitCircleParam 0 r) := by
  have hreg := unitCircleParam_regular r hr
  refine ⟨hreg.smooth, hreg.periodic, hreg.injective, hreg.regular, hreg.boundary, ?_⟩
  intro y hy
  obtain ⟨v, hv, hproj, hturn⟩ := annular_regular_image_circle_argument_sign
    isOpen_univ contDiff_id.contDiffOn (0 : ℂ) hr (subset_univ _) 1 (by norm_num)
    (fun z _ => by
      simp only [fderiv_id, one_mul]
      change 0 < LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
      rw [LinearMap.det_id]
      norm_num) (roundDiskChart r hr) hreg y hy
  let u : C(unitInterval, ℝ) := ⟨fun t => v t, hv.continuous.comp continuous_subtype_val⟩
  refine ⟨u, fun t => hproj t, ?_⟩
  change v 1 = v 0 + 1
  linarith

private theorem circular_nested {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r < R) :
    closure (jordanInterior (roundDiskChart r hr)) ⊆ jordanInterior (roundDiskChart R hR) := by
  rw [roundDiskChart_interior, roundDiskChart_interior, closure_ball (0 : ℂ) hr.ne']
  intro z hz
  simp only [mem_closedBall, mem_ball, dist_zero_right] at hz ⊢
  exact hz.trans_lt hrR

private theorem circular_coord_interior {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    annularCoordJordanInterior (roundDiskChart R hR) (roundDiskChart r hr) =
      {p : Coord | r < planarRadius p ∧ planarRadius p < R} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ jordanInterior (roundDiskChart R hR) ∧
      z ∉ closure (jordanInterior (roundDiskChart r hr)) at hz
    rw [roundDiskChart_interior, roundDiskChart_interior, closure_ball (0 : ℂ) hr.ne'] at hz
    change r < planarRadius (seamComplexCoord z) ∧ planarRadius (seamComplexCoord z) < R
    simpa only [mem_ball, mem_closedBall, dist_zero_right, not_le,
      circular_coord_radius, and_comm] using hz
  · intro hp
    change r < planarRadius p ∧ planarRadius p < R at hp
    refine ⟨seamComplexCoord.symm p, ?_, seamComplexCoord.apply_symm_apply p⟩
    change seamComplexCoord.symm p ∈ jordanInterior (roundDiskChart R hR) ∧
      seamComplexCoord.symm p ∉ closure (jordanInterior (roundDiskChart r hr))
    rw [roundDiskChart_interior, roundDiskChart_interior, closure_ball (0 : ℂ) hr.ne']
    simpa only [mem_ball, mem_closedBall, dist_zero_right, not_le,
      circular_coord_inverse_norm, and_comm] using hp

private theorem circular_coord_closure {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    annularCoordJordanClosure (roundDiskChart R hR) (roundDiskChart r hr) =
      {p : Coord | r ≤ planarRadius p ∧ planarRadius p ≤ R} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ closure (jordanInterior (roundDiskChart R hR)) ∧
      z ∉ jordanInterior (roundDiskChart r hr) at hz
    rw [roundDiskChart_interior, roundDiskChart_interior, closure_ball (0 : ℂ) hR.ne'] at hz
    change r ≤ planarRadius (seamComplexCoord z) ∧ planarRadius (seamComplexCoord z) ≤ R
    simpa only [mem_ball, mem_closedBall, dist_zero_right, not_lt,
      circular_coord_radius, and_comm] using hz
  · intro hp
    change r ≤ planarRadius p ∧ planarRadius p ≤ R at hp
    refine ⟨seamComplexCoord.symm p, ?_, seamComplexCoord.apply_symm_apply p⟩
    change seamComplexCoord.symm p ∈ closure (jordanInterior (roundDiskChart R hR)) ∧
      seamComplexCoord.symm p ∉ jordanInterior (roundDiskChart r hr)
    rw [roundDiskChart_interior, roundDiskChart_interior, closure_ball (0 : ℂ) hR.ne']
    simpa only [mem_ball, mem_closedBall, dist_zero_right, not_lt,
      circular_coord_inverse_norm, and_comm] using hp

private def circular_boundary_scale {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    frontier (jordanInterior (roundDiskChart r hr)) ≃ₜ
      frontier (jordanInterior (roundDiskChart k hk)) :=
  (Homeomorph.mulLeft₀ ((k / r : ℝ) : ℂ)
    (by exact_mod_cast (div_pos hk hr).ne')).subtype (by
      intro z
      rw [roundDiskChart_interior, roundDiskChart_interior,
        frontier_ball (0 : ℂ) hr.ne', frontier_ball (0 : ℂ) hk.ne']
      simp only [mem_sphere, dist_zero_right]
      change (‖z‖ = r) ↔ ‖((k / r : ℝ) : ℂ) * z‖ = k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hk hr)]
      constructor
      · intro hz
        rw [hz]
        field_simp [hr.ne']
      · intro hz
        have hkr : k / r ≠ 0 := (div_pos hk hr).ne'
        have he : k / r * r = k := by field_simp [hr.ne']
        exact (mul_left_cancel₀ hkr) (hz.trans he.symm))

private theorem circular_gradient_trace {G : Coord → ℝ} {r k : ℝ}
    (hCircle : ∀ theta, planarGradient G (saddlePolarChart ![r, theta]) =
      k • (![Real.cos theta, Real.sin theta] : Coord)) (t : ℝ) :
    annularComplexConjugate (planarGradient G) (unitCircleParam 0 r t) = unitCircleParam 0 k t := by
  apply seamComplexCoord.injective
  simp only [annularComplexConjugate, comp_apply, seamComplexCoord.apply_symm_apply]
  rw [circular_polar_coordinates, hCircle, circular_polar_coordinates]
  ext i
  fin_cases i <;> simp [saddlePolarChart, Pi.smul_apply, smul_eq_mul]

private theorem circular_boundary_actual {G : Coord → ℝ} {r k : ℝ}
    (hr : 0 < r) (hk : 0 < k)
    (hCircle : ∀ theta, planarGradient G (saddlePolarChart ![r, theta]) =
      k • (![Real.cos theta, Real.sin theta] : Coord))
    (x : frontier (jordanInterior (roundDiskChart r hr))) :
    (circular_boundary_scale hr hk x : ℂ) = annularComplexConjugate (planarGradient G) x := by
  have hx : (x : ℂ) ∈ sphere (0 : ℂ) r := by
    simpa only [roundDiskChart_interior, frontier_ball (0 : ℂ) hr.ne'] using x.property
  obtain ⟨t, ht⟩ := (annular_unitCircleParam_range 0 hr).symm ▸ hx
  change ((k / r : ℝ) : ℂ) * (x : ℂ) = _
  rw [← ht, circular_gradient_trace hCircle]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [unitCircleParam, circleMap, zero_add]
  push_cast
  field_simp [hrc]

private theorem circular_normalized_argument {r : ℝ} (hr : 0 < r) (t : ℝ) :
    normalizedArgument (unitCircleParam 0 r t) = (t : UnitAddCircle) := by
  have hscale : unitCircleParam 0 r t = (r : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ) := by
    simp [unitCircleParam, circleMap, Circle.coe_exp]
  rw [hscale]
  have he : normalizedArgument ((r : ℂ) * (Circle.exp (2 * Real.pi * t) : ℂ)) =
      normalizedArgument (Circle.exp (2 * Real.pi * t) : ℂ) := by
    unfold normalizedArgument
    rw [Complex.arg_real_mul _ hr]
  rw [he, normalizedArgument_circleExp]

private theorem circular_gradient_winding {G : Coord → ℝ} {U : Set Coord} {r k : ℝ}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hr : 0 < r) (hk : 0 < k)
    (hIn : ∀ theta, saddlePolarChart ![r, theta] ∈ U)
    (hCircle : ∀ theta, planarGradient G (saddlePolarChart ![r, theta]) =
      k • (![Real.cos theta, Real.sin theta] : Coord)) :
    planarFormIntegral (annularAngularFormP (annularComplexConjugate (planarGradient G)) 0)
      (annularAngularFormQ (annularComplexConjugate (planarGradient G)) 0) (unitCircleParam 0 r) = 1 := by
  let f := annularComplexConjugate (planarGradient G)
  let O : Set ℂ := seamComplexCoord ⁻¹' U ∩ {z | f z ≠ 0}
  have hf : ContDiffOn ℝ ∞ f (seamComplexCoord ⁻¹' U) :=
    seamComplexCoord.symm.contDiff.comp_contDiffOn
      ((planarGradient_contDiffOn hG hU).comp seamComplexCoord.contDiff.contDiffOn (fun _ hz => hz))
  have hZero : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hO : IsOpen O :=
    hf.continuousOn.isOpen_inter_preimage (hU.preimage seamComplexCoord.continuous) hZero
  have hAvoid : ∀ z ∈ O, f z ≠ 0 := fun _ hz => hz.2
  have hTrace (t : ℝ) : f (unitCircleParam 0 r t) = unitCircleParam 0 k t :=
    circular_gradient_trace hCircle t
  have hCurve (t : ℝ) : unitCircleParam 0 r t ∈ O := by
    constructor
    · change seamComplexCoord (unitCircleParam 0 r t) ∈ U
      rw [circular_polar_coordinates]
      exact hIn _
    · change f (unitCircleParam 0 r t) ≠ 0
      rw [hTrace]
      have hx : unitCircleParam 0 k t ∈ sphere (0 : ℂ) k :=
        annular_unitCircleParam_range 0 hk ▸ mem_range_self t
      have hn : ‖unitCircleParam 0 k t‖ = k := by simpa only [mem_sphere, dist_zero_right] using hx
      exact norm_ne_zero_iff.mp (by rw [hn]; exact hk.ne')
  have he := annularAngularForm_integral_eq_lift hO (hf.mono inter_subset_left) hAvoid
    (unitCircleParam_regular r hr).smooth hCurve id continuous_id
    (fun t => by
      rw [hTrace, sub_zero, circular_normalized_argument hk t]
      rfl)
  simpa using he

/-- The actual ordinary-boundary gradient theorem supplies the literal local
circular degree specialization required by the same-potential completion. -/
theorem dualRadialCompletionCircularDegree_of_gradientClaim
    (hDegree : AnnularDegreeGradientClaim) : DualRadialCompletionCircularDegreeClaim := by
  intro G U epsilon L a b hepsilon hepsilonL ha hab hU hG hClosed hneg hInner hOuter
  have hL : 0 < L := hepsilon.trans hepsilonL
  have hb : 0 < b := ha.trans hab
  have hIn (theta : ℝ) : saddlePolarChart ![epsilon, theta] ∈ U := by
    apply hClosed
    have hr : planarRadius (saddlePolarChart ![epsilon, theta]) = epsilon :=
      angularDescent_radius_polar (q := ![epsilon, theta]) hepsilon
    change epsilon ≤ planarRadius (saddlePolarChart ![epsilon, theta]) ∧
      planarRadius (saddlePolarChart ![epsilon, theta]) ≤ L
    rw [hr]
    exact ⟨le_rfl, hepsilonL.le⟩
  have hOut (theta : ℝ) : saddlePolarChart ![L, theta] ∈ U := by
    apply hClosed
    have hr : planarRadius (saddlePolarChart ![L, theta]) = L := angularDescent_radius_polar (q := ![L, theta]) hL
    change epsilon ≤ planarRadius (saddlePolarChart ![L, theta]) ∧
      planarRadius (saddlePolarChart ![L, theta]) ≤ L
    rw [hr]
    exact ⟨hepsilonL.le, le_rfl⟩
  obtain ⟨e, hs, ht, hf, _hi, _hBoundary⟩ := hDegree
    (roundDiskChart L hL) (roundDiskChart epsilon hepsilon)
    (roundDiskChart b hb) (roundDiskChart a ha)
    (unitCircleParam 0 L) (unitCircleParam 0 epsilon)
    (circular_positive_param L hL) (circular_positive_param epsilon hepsilon)
    (circular_nested hepsilon hL hepsilonL) (circular_nested ha hb hab)
    G U hU hG (by rw [circular_coord_closure]; exact hClosed)
    (-1) (Or.inr rfl)
    (fun x hx => by
      rw [circular_coord_interior] at hx
      simpa using neg_pos.mpr (hneg x hx.1 hx.2))
    true (circular_boundary_scale hL ha) (circular_boundary_scale hepsilon hb)
    (circular_boundary_actual hL ha hOuter) (circular_boundary_actual hepsilon hb hInner)
    1 (by norm_num)
    (by simpa [roundDiskChart] using circular_gradient_winding hU hG hL ha hOut hOuter)
    (by simpa [roundDiskChart] using circular_gradient_winding hU hG hepsilon hb hIn hInner)
  have hbij := e.bijOn
  rw [hs, ht, hf, circular_coord_interior, circular_coord_interior] at hbij
  exact hbij

end
end TightVer401
