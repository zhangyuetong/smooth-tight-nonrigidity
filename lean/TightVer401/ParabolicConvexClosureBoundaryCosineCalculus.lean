import TightVer401.ParabolicConvexClosureBoundary
import TightVer401.RevolutionEndNativeNormal
import TightVer401.NativeProductPlaneAtlas
import Mathlib.Geometry.Manifold.Instances.Icc

/-! Calculus interfaces for the exact cosine boundary parametrization.

The source model is the retained real circle model times Mathlib's genuine
interval halfspace model. Its tangent inclusion is proved injective from the
canonical interval tangent vector and its actual manifold differential; the
right endpoint is not treated as a definitionally identical real tangent.
Polynomial collars descend through the retained circle projection, and their
actual differential regularity follows from the checked coordinate collar.
No surface rank, chart compatibility, or boundary smoothness is an input.
-/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

local instance boundaryCosineCalculusPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev parabolicConvexClosureBoundaryModel := 𝓘(ℝ, ℝ).prod (𝓡∂ 1)

def parabolicConvexClosureBoundaryInclusion
    (p : AddCircle (2 * Real.pi) × unitInterval) : AddCircle (2 * Real.pi) × ℝ :=
  (p.1, (p.2 : ℝ))

theorem parabolicConvexClosureBoundaryInclusion_contMDiff :
    ContMDiff parabolicConvexClosureBoundaryModel nativeProductModel ∞
      parabolicConvexClosureBoundaryInclusion :=
  contMDiff_id.prodMap contMDiff_subtypeVal_Icc

theorem parabolicConvexClosure_intervalVal_mfderiv_injective (t : unitInterval) :
    Function.Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) t) := by
  let L := mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) t
  have hone : L (1 : TangentSpace (𝓡∂ 1) t) = 1 := mfderiv_subtypeVal_Icc_one t
  have hne : (1 : TangentSpace (𝓡∂ 1) t) ≠ 0 := by
    intro he
    rw [he, map_zero] at hone
    change (0 : ℝ) = 1 at hone
    norm_num at hone
  have hdim : Module.finrank ℝ (TangentSpace (𝓡∂ 1) t) = 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    simp
  intro v w he
  change L v = L w at he
  have hz : L (v - w) = 0 := by simp [map_sub, he]
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : TangentSpace (𝓡∂ 1) t) hne).mp hdim (v - w)
  rw [← ha, map_smul, hone] at hz
  have ha0 : a = 0 := by simpa using hz
  apply sub_eq_zero.mp
  rw [← ha, ha0, zero_smul]

theorem parabolicConvexClosureBoundaryInclusion_mfderiv_injective
    (p : AddCircle (2 * Real.pi) × unitInterval) :
    Function.Injective (mfderiv parabolicConvexClosureBoundaryModel nativeProductModel
      parabolicConvexClosureBoundaryInclusion p) := by
  change Function.Injective (mfderiv parabolicConvexClosureBoundaryModel nativeProductModel
    (Prod.map id (Subtype.val : unitInterval → ℝ)) p)
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((contMDiff_subtypeVal_Icc (n := ∞) p.2).mdifferentiableAt (by simp)), mfderiv_id]
  intro v w he
  exact Prod.ext (congrArg (fun u : ℝ × ℝ => u.1) he)
    (parabolicConvexClosure_intervalVal_mfderiv_injective p.2
      (congrArg (fun u : ℝ × ℝ => u.2) he))

def parabolicConvexClosureCircleCollar (σ RN mu h : ℝ)
    (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  (RN + mu * p.2) • revolutionCircleRadial p.1 +
    (σ * (h - mu * p.2^2 / 2)) • revolutionAxis

theorem parabolicConvexClosureCircleCollar_contMDiff (σ RN mu h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞
      (parabolicConvexClosureCircleCollar σ RN mu h) := by
  exact ((contMDiff_const.add (contMDiff_const.mul contMDiff_snd)).smul
    (revolutionCircleRadial_contMDiff.comp contMDiff_fst)).add
    ((contMDiff_const.mul (contMDiff_const.sub
      ((contMDiff_const.mul (contMDiff_snd.pow 2)).div_const 2))).smul contMDiff_const)

theorem parabolicConvexClosureCircleCollar_representative (σ RN mu h θ t : ℝ) :
    parabolicConvexClosureCircleCollar σ RN mu h (periodProjection (2 * Real.pi) θ, t) =
      parabolicConvexClosureCollar σ RN mu h (![θ, t] : Coord) := by
  simp [parabolicConvexClosureCircleCollar, parabolicConvexClosureCollar,
    revolutionCircleRadial_representative]

theorem parabolicConvexClosureCircleCollar_mfderiv_injective {σ RN mu h : ℝ}
    (hmu : mu ≠ 0) (p : AddCircle (2 * Real.pi) × ℝ) (hr : RN + mu * p.2 ≠ 0) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCircleCollar σ RN mu h) p) := by
  obtain ⟨θ, hθ⟩ := QuotientAddGroup.mk_surjective p.1
  let u : ℝ × ℝ := (θ, p.2)
  have hu : revolutionCylinderProjection u = p := Prod.ext hθ rfl
  have heq : parabolicConvexClosureCircleCollar σ RN mu h ∘ revolutionCylinderProjection =
      parabolicConvexClosureCollar σ RN mu h ∘ revolutionProductCoordinates := by
    funext x
    exact parabolicConvexClosureCircleCollar_representative σ RN mu h x.1 x.2
  have hraw : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCircleCollar σ RN mu h ∘ revolutionCylinderProjection) u) := by
    rw [heq]
    change Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCollar σ RN mu h ∘ revolutionProductCoordinates) u)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv]
    rw [fderiv_comp u
      ((parabolicConvexClosureCollar_contDiff σ RN mu h).differentiable (by simp) _)
      revolutionProductCoordinates.differentiableAt,
      revolutionProductCoordinates.hasFDerivAt.fderiv]
    exact (parabolicConvexClosureCollar_differential_injective hmu hr).comp
      revolutionProductCoordinates.injective
  have hd := mfderiv_comp u
    ((parabolicConvexClosureCircleCollar_contMDiff σ RN mu h _).mdifferentiableAt (by simp))
    ((revolutionCylinderProjection_contMDiff u).mdifferentiableAt (by simp))
  intro v w he
  obtain ⟨v', hv⟩ := revolutionCylinderProjection_mfderiv_surjective u v
  obtain ⟨w', hw⟩ := revolutionCylinderProjection_mfderiv_surjective u w
  have he' : mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCircleCollar σ RN mu h ∘ revolutionCylinderProjection) u v' =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCircleCollar σ RN mu h ∘ revolutionCylinderProjection) u w' := by
    rw [hd]
    change mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCircleCollar σ RN mu h) (revolutionCylinderProjection u)
      (mfderiv nativeProductModel nativeProductModel revolutionCylinderProjection u v') =
      mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (parabolicConvexClosureCircleCollar σ RN mu h) (revolutionCylinderProjection u)
      (mfderiv nativeProductModel nativeProductModel revolutionCylinderProjection u w')
    rw [hv, hw, hu]
    exact he
  rw [← hv, ← hw, hraw he']

theorem parabolicConvexClosure_scalarReparam_mfderiv_injective {s : ℝ → ℝ}
    {d : ℝ} (p : AddCircle (2 * Real.pi) × ℝ) (hs : HasDerivAt s d p.2) (hd : d ≠ 0) :
    Function.Injective (mfderiv nativeProductModel nativeProductModel (Prod.map id s) p) := by
  rw [mfderiv_prodMap mdifferentiableAt_id hs.differentiableAt.mdifferentiableAt,
    mfderiv_id, mfderiv_eq_fderiv, hs.hasFDerivAt.fderiv]
  intro v w he
  change (v.1, v.2 * d) = (w.1, w.2 * d) at he
  apply Prod.ext
  · have h1 := congrArg (fun u : ℝ × ℝ => u.1) he
    exact h1
  · have h2 := congrArg (fun u : ℝ × ℝ => u.2) he
    change v.2 * d = w.2 * d at h2
    exact mul_right_cancel₀ hd h2

end
end TightVer401
