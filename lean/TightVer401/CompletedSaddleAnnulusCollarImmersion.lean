import TightVer401.CompletedSaddleAnnulusCollars
import TightVer401.NativeProductPlaneCurvature
import TightVer401.RevolutionEndGeometry

/-! Actual native endpoint immersion of the normalized south and north
collars, derived from their actual radial and angular differential columns. -/
open Manifold
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set Filter Function OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- An actual meridian surface in the physical coordinate representative. -/
def completedSaddleAnnulusMeridianRepresentative (r z : ℝ → ℝ) (θ : ℝ)
    (p : Coord) : Ambient :=
  r (p 1) • revolutionRadial (θ + p 0) + z (p 1) • revolutionAxis

private theorem completedSaddleAnnulus_collar_chart_center
    (q : AddCircle (2 * Real.pi)) (u : ℝ) :
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
        (chartAt (ModelProd ℝ ℝ) (q, u) (q, u)) = (![0,u] : Coord) := by
  apply (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).injective
  change (chartAt (ModelProd ℝ ℝ) (q,u) (q,u) : ℝ × ℝ) = (0,u)
  apply Prod.ext
  · change (periodChart (2 * Real.pi)).symm (-q + q) = 0
    rw [neg_add_cancel]
    have h0 : periodChart (2 * Real.pi) (0 : ℝ) = (0 : AddCircle (2 * Real.pi)) := rfl
    simpa only [h0] using
      (periodChart (2 * Real.pi)).left_inv (periodChart_zero_source (2 * Real.pi))
  · rfl

private theorem completedSaddleAnnulus_collar_chart_symm
    (q : AddCircle (2 * Real.pi)) (u : ℝ) (x : Coord) :
    (chartAt (ModelProd ℝ ℝ) (q,u)).symm (x 0, x 1) =
      (q + periodProjection (2 * Real.pi) (x 0), x 1) := by
  apply Prod.ext
  · change (OAI.RawQuotientLie.addLeftChart (periodChart (2 * Real.pi)) q).symm (x 0) = _
    simpa [periodChart, periodProjection] using
      OAI.RawQuotientLie.addLeftChart_symm_apply (periodChart (2 * Real.pi)) q (x 0)
  · rfl

theorem completedSaddleAnnulusSouthCollar_coordinateMap
    (RN : ℝ) {μ h : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (q : AddCircle (2 * Real.pi)) (u θ : ℝ)
    (hθ : periodProjection (2 * Real.pi) θ = q) :
    nativeProductCoordinateMap (completedSaddleAnnulusSouthCollar RN μ h) (q,u) =
      completedSaddleAnnulusMeridianRepresentative
        (fun v => RN + μ * completedSaddleAnnulusSouthTransverse h μ v)
        (fun v => -h * Real.cos v) θ := by
  funext x
  unfold nativeProductCoordinateMap
  rw [completedSaddleAnnulus_collar_chart_symm]
  rw [completedSaddleAnnulusSouthCollar_normalized_formula RN hh hμ]
  rw [← hθ, ← map_add, revolutionCircleRadial_representative]
  rfl

theorem completedSaddleAnnulusNorthCollar_coordinateMap
    (RN : ℝ) {μ h : ℝ} (hh : 0 < h) (hμ : 0 < μ)
    (q : AddCircle (2 * Real.pi)) (u θ : ℝ)
    (hθ : periodProjection (2 * Real.pi) θ = q) :
    nativeProductCoordinateMap (completedSaddleAnnulusNorthCollar RN μ h) (q,u) =
      completedSaddleAnnulusMeridianRepresentative
        (fun v => RN + μ * completedSaddleAnnulusNorthTransverse h μ v)
        (fun v => -h * Real.cos v) θ := by
  funext x
  unfold nativeProductCoordinateMap
  rw [completedSaddleAnnulus_collar_chart_symm]
  rw [completedSaddleAnnulusNorthCollar_normalized_formula RN hh hμ]
  rw [← hθ, ← map_add, revolutionCircleRadial_representative]
  rfl

/-- Differentiate the actual scalar meridian and actual angular frame. -/
theorem completedSaddleAnnulusMeridianRepresentative_fderiv
    {r z : ℝ → ℝ} {p : Coord} {r₁ z₁ : ℝ}
    (hr : HasDerivAt r r₁ (p 1)) (hz : HasDerivAt z z₁ (p 1))
    (θ : ℝ) (v : Coord) :
    fderiv ℝ (completedSaddleAnnulusMeridianRepresentative r z θ) p v =
      (v 1 * r₁) • revolutionRadial (θ + p 0) +
        (r (p 1) * v 0) • revolutionAngular (θ + p 0) +
        (v 1 * z₁) • revolutionAxis := by
  have hrr := hr.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have hangle : HasFDerivAt (fun x : Coord => θ + x 0)
      (ContinuousLinearMap.proj (R := ℝ) 0) p := by
    simpa only [ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)).const_add θ
  have ha := (revolutionRadial_hasDerivAt (θ + p 0)).hasFDerivAt.comp p hangle
  have hzz := hz.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have hd := (hrr.smul ha).add (hzz.smul (hasFDerivAt_const (c := revolutionAxis) p))
  change HasFDerivAt (completedSaddleAnnulusMeridianRepresentative r z θ) _ p at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply,
    zero_apply, smul_zero, zero_add, smul_smul, Function.comp_apply]
  module

private theorem completedSaddleAnnulus_meridian_endpoint_injective
    {r z : ℝ → ℝ} {u r₁ : ℝ} (hr : HasDerivAt r r₁ u)
    (hz : HasDerivAt z 0 u) (hradius : r u ≠ 0) (htransverse : r₁ ≠ 0)
    (θ : ℝ) :
    Injective (fderiv ℝ (completedSaddleAnnulusMeridianRepresentative r z θ) (![0,u] : Coord)) := by
  have hd (v : Coord) :
      fderiv ℝ (completedSaddleAnnulusMeridianRepresentative r z θ) (![0,u] : Coord) v =
        (v 1 * r₁) • revolutionRadial θ + (r u * v 0) • revolutionAngular θ := by
    simpa using completedSaddleAnnulusMeridianRepresentative_fderiv
      (p := (![0,u] : Coord)) hr hz θ v
  rcases revolution_frame θ with ⟨hrr, haa, _, hra, _, _⟩
  have har : inner ℝ (revolutionAngular θ) (revolutionRadial θ) = 0 := by
    rw [real_inner_comm, hra]
  intro v w hvw
  have hzero :
      fderiv ℝ (completedSaddleAnnulusMeridianRepresentative r z θ) (![0,u] : Coord) (v-w) = 0 := by
    simp [map_sub, hvw]
  have h0 : (v-w) 0 = 0 := by
    have hi := congrArg (fun a : Ambient => inner ℝ a (revolutionAngular θ)) hzero
    simp only [hd, inner_add_left, real_inner_smul_left, inner_zero_left,
      hra, haa, mul_zero, mul_one, zero_add] at hi
    exact (mul_eq_zero.mp hi).resolve_left hradius
  have h1 : (v-w) 1 = 0 := by
    have hi := congrArg (fun a : Ambient => inner ℝ a (revolutionRadial θ)) hzero
    simp only [hd, inner_add_left, real_inner_smul_left, inner_zero_left,
      hrr, har, mul_zero, mul_one, add_zero] at hi
    exact (mul_eq_zero.mp hi).resolve_right htransverse
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

private theorem completedSaddleAnnulus_native_injective_of_coordinate
    {F : AddCircle (2 * Real.pi) × ℝ → Ambient}
    {q : AddCircle (2 * Real.pi)} {u : ℝ}
    (hF : MDifferentiableAt nativeProductModel 𝓘(ℝ, Ambient) F (q,u))
    (hi : Injective (fderiv ℝ (nativeProductCoordinateMap F (q,u)) (![0,u] : Coord))) :
    Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (q,u)) := by
  have hc := nativeProductPlane_coordinate_fderiv hF
  rw [completedSaddleAnnulus_collar_chart_center q u] at hc
  let e := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  intro v w hvw
  apply e.symm.injective
  apply hi
  rw [hc]
  change mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (q,u) (e (e.symm v)) =
    mfderiv nativeProductModel 𝓘(ℝ, Ambient) F (q,u) (e (e.symm w))
  simpa only [e.apply_symm_apply] using hvw

/-- Actual native differential injectivity at every south boundary point;
the radial derivative is nonzero even though the height derivative vanishes. -/
theorem completedSaddleAnnulusSouthCollar_mfderiv_injective
    {RN μ h : ℝ} (hRN : 0 < RN) (hμ : 0 < μ) (hh : 0 < h)
    (q : AddCircle (2 * Real.pi)) :
    Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (completedSaddleAnnulusSouthCollar RN μ h) (q, (0 : ℝ))) := by
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective q
  have hr : HasDerivAt
      (fun u => RN + μ * completedSaddleAnnulusSouthTransverse h μ u)
      (μ * (-Real.sqrt (h / μ))) 0 := by
    simpa using ((completedSaddleAnnulusSouthTransverse_hasDerivAt h μ 0).const_mul μ).const_add RN
  have hz : HasDerivAt (fun u => -h * Real.cos u) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).const_mul (-h)
  have hrad : RN + μ * completedSaddleAnnulusSouthTransverse h μ 0 ≠ 0 := by
    simpa using hRN.ne'
  have htrans : μ * (-Real.sqrt (h / μ)) ≠ 0 :=
    mul_ne_zero hμ.ne' (neg_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos hh hμ)).ne')
  apply completedSaddleAnnulus_native_injective_of_coordinate
    ((completedSaddleAnnulusSouthCollar_contMDiff RN μ h (q,0)).mdifferentiableAt (by simp))
  rw [completedSaddleAnnulusSouthCollar_coordinateMap RN hh hμ q 0 θ hθ]
  exact completedSaddleAnnulus_meridian_endpoint_injective hr hz hrad htrans θ

/-- Actual native differential injectivity at every north boundary point. -/
theorem completedSaddleAnnulusNorthCollar_mfderiv_injective
    {RN μ h : ℝ} (hRN : 0 < RN) (hμ : 0 < μ) (hh : 0 < h)
    (q : AddCircle (2 * Real.pi)) :
    Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (completedSaddleAnnulusNorthCollar RN μ h) (q, Real.pi)) := by
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective q
  have hr : HasDerivAt
      (fun u => RN + μ * completedSaddleAnnulusNorthTransverse h μ u)
      (μ * Real.sqrt (h / μ)) Real.pi := by
    simpa using ((completedSaddleAnnulusNorthTransverse_hasDerivAt h μ Real.pi).const_mul μ).const_add RN
  have hz : HasDerivAt (fun u => -h * Real.cos u) 0 Real.pi := by
    simpa using (Real.hasDerivAt_cos Real.pi).const_mul (-h)
  have hrad : RN + μ * completedSaddleAnnulusNorthTransverse h μ Real.pi ≠ 0 := by
    simpa using hRN.ne'
  have htrans : μ * Real.sqrt (h / μ) ≠ 0 :=
    mul_ne_zero hμ.ne' (Real.sqrt_pos.mpr (div_pos hh hμ)).ne'
  apply completedSaddleAnnulus_native_injective_of_coordinate
    ((completedSaddleAnnulusNorthCollar_contMDiff RN μ h (q,Real.pi)).mdifferentiableAt (by simp))
  rw [completedSaddleAnnulusNorthCollar_coordinateMap RN hh hμ q Real.pi θ hθ]
  exact completedSaddleAnnulus_meridian_endpoint_injective hr hz hrad htrans θ

end
end TightVer401
