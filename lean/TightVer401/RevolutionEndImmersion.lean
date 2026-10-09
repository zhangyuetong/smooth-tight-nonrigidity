import TightVer401.RevolutionEndCircleSmooth
import TightVer401.RevolutionEndGeometry
import TightVer401.PeriodProjectionDifferential
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 def revolutionProductCoordinates : (ℝ × ℝ) ≃L[ℝ] Coord :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

 theorem revolutionProductCoordinates_apply (p : ℝ × ℝ) :
    revolutionProductCoordinates p = ![p.1, p.2] := rfl

 def revolutionCylinderProjection : ℝ × ℝ → AddCircle (2 * Real.pi) × ℝ :=
  Prod.map (periodProjection (2 * Real.pi)) id

 theorem revolutionCylinderProjection_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      revolutionCylinderProjection := (periodProjection_contMDiff _).prodMap contMDiff_id

 theorem revolutionCylinderProjection_mfderiv_surjective (p : ℝ × ℝ) :
    Function.Surjective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) revolutionCylinderProjection p) := by
  intro v
  obtain ⟨s, hs⟩ := periodProjection_mfderiv_surjective (2 * Real.pi) p.1 v.1
  refine ⟨(s, v.2), ?_⟩
  rw [revolutionCylinderProjection, mfderiv_prodMap
    ((periodProjection_contMDiff _ p.1).mdifferentiableAt (by simp)) mdifferentiableAt_id,
    mfderiv_id]
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection _) p.1 s, v.2) = v
  rw [hs]
  exact Prod.eta v

 theorem revolutionEndCircleFull_raw_mfderiv_injective {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (p : ℝ × ℝ) (hqp : q p.2 ≠ 0) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q ∘ revolutionCylinderProjection) p) := by
  have heq : revolutionEndCircleFull q ∘ revolutionCylinderProjection =
      revolutionEnd q ∘ revolutionProductCoordinates := by
    funext s
    exact revolutionEndCircleFull_representative q s.1 s.2
  rw [heq, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod, mfderiv_eq_fderiv]
  have hd : fderiv ℝ (revolutionEnd q ∘ revolutionProductCoordinates) p =
      (fderiv ℝ (revolutionEnd q) (revolutionProductCoordinates p)).comp
        revolutionProductCoordinates.toContinuousLinearMap := by
    rw [fderiv_comp p ((revolutionEnd_contDiff hq).differentiable (by simp) _)
      revolutionProductCoordinates.differentiableAt]
    congr 1
    exact revolutionProductCoordinates.hasFDerivAt.fderiv
  rw [hd]
  exact (revolutionEnd_differential_injective hq hqp).comp revolutionProductCoordinates.injective

 theorem revolutionEndCircleFull_mfderiv_injective {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (p : AddCircle (2 * Real.pi) × ℝ) (hqp : q p.2 ≠ 0) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q) p) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let u : ℝ × ℝ := (s, p.2)
  have hu : revolutionCylinderProjection u = p := Prod.ext hs rfl
  have hd := mfderiv_comp u
    ((revolutionEndCircleFull_contMDiff hq (revolutionCylinderProjection u)).mdifferentiableAt (by simp))
    ((revolutionCylinderProjection_contMDiff u).mdifferentiableAt (by simp))
  intro v w hvw
  obtain ⟨v', hv⟩ := revolutionCylinderProjection_mfderiv_surjective u v
  obtain ⟨w', hw⟩ := revolutionCylinderProjection_mfderiv_surjective u w
  have he : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q ∘ revolutionCylinderProjection) u v' =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q ∘ revolutionCylinderProjection) u w' := by
    rw [hd]
    change mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) (revolutionCylinderProjection u)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) revolutionCylinderProjection u v') =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) (revolutionCylinderProjection u)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) revolutionCylinderProjection u w')
    rw [hv, hw, hu]
    exact hvw
  have hvw' := revolutionEndCircleFull_raw_mfderiv_injective hq u hqp he
  rw [← hv, ← hw, hvw']

end
end TightVer401

