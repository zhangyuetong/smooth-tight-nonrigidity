import TightVer401.RevolutionEndImmersion
import TightVer401.RevolutionEndGauss

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolutionEndCircleFull_raw_mfderiv_apply {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (p v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q ∘ revolutionCylinderProjection) p v =
    fderiv ℝ (revolutionEnd q) (revolutionProductCoordinates p) (revolutionProductCoordinates v) := by
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
  rfl

 theorem revolutionEndCircleNormal_orthogonal {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : AddCircle (2 * Real.pi) × ℝ) (v : ℝ × ℝ) :
    inner ℝ (show Ambient from mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q) p v) (revolutionEndCircleNormal q p) = 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let u : ℝ × ℝ := (s, p.2)
  have hu : revolutionCylinderProjection u = p := Prod.ext hs rfl
  obtain ⟨v', hv⟩ := revolutionCylinderProjection_mfderiv_surjective u v
  have hd := mfderiv_comp u
    ((revolutionEndCircleFull_contMDiff hq (revolutionCylinderProjection u)).mdifferentiableAt (by simp))
    ((revolutionCylinderProjection_contMDiff u).mdifferentiableAt (by simp))
  have he : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q) p v =
    mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q ∘ revolutionCylinderProjection) u v' := by
    rw [hd]
    change mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p v =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) (revolutionCylinderProjection u)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) revolutionCylinderProjection u v')
    rw [hv, hu]
  have hn : revolutionEndCircleNormal q p = revolutionEndNormal q (revolutionProductCoordinates u) := by
    rw [← hu]
    exact revolutionEndCircleNormal_representative q s p.2
  rw [he, revolutionEndCircleFull_raw_mfderiv_apply hq, hn]
  exact (revolutionEnd_isUnitNormal hq _).2 _

 theorem revolutionEndCircle_isUnitNormal {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : AddCircle (2 * Real.pi) × ℝ) :
    inner ℝ (revolutionEndCircleNormal q p) (revolutionEndCircleNormal q p) = 1 ∧
    ∀ v : ℝ × ℝ, inner ℝ (show Ambient from mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient)
      (revolutionEndCircleFull q) p v) (revolutionEndCircleNormal q p) = 0 :=
  ⟨revolutionEndCircleNormal_unit q p, revolutionEndCircleNormal_orthogonal hq p⟩

 theorem revolutionEndCircleNormal_contMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (revolutionEndCircleNormal q) := by
  have hqd := (contDiff_infty_iff_deriv.mp hq).2
  have hw : ContDiff ℝ ∞ (fun z => revolutionWeight (deriv q z)) :=
    (contDiff_const.add (hqd.pow 2)).sqrt (fun z => ne_of_gt (by positivity : 0 < 1 + deriv q z ^ 2))
  have ha : ContDiff ℝ ∞ (fun z => -1 / revolutionWeight (deriv q z)) :=
    contDiff_const.div hw (fun z => ne_of_gt (revolutionWeight_pos _))
  have hb : ContDiff ℝ ∞ (revolutionNormalHeight q) :=
    hqd.div hw (fun z => ne_of_gt (revolutionWeight_pos _))
  exact ((ha.contMDiff.comp contMDiff_snd).smul
    (revolutionCircleRadial_contMDiff.comp contMDiff_fst)).add
    ((hb.contMDiff.comp contMDiff_snd).smul contMDiff_const)

end
end TightVer401

