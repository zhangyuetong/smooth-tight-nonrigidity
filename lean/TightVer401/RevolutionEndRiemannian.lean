import TightVer401.RevolutionEndImmersion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Bounded

namespace TightVer401
noncomputable section
open Set Bundle Bornology OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 abbrev RevolutionCylinder := AddCircle (2 * Real.pi) × ℝ
 abbrev revolutionCylinderModel := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)

local instance (p : RevolutionCylinder) : NormedAddCommGroup (TangentSpace revolutionCylinderModel p) :=
  inferInstanceAs (NormedAddCommGroup (ℝ × ℝ))
local instance (p : RevolutionCylinder) : NormedSpace ℝ (TangentSpace revolutionCylinderModel p) :=
  inferInstanceAs (NormedSpace ℝ (ℝ × ℝ))

 def revolutionEndInducedInner (q : ℝ → ℝ) (p : RevolutionCylinder) :
    TangentSpace revolutionCylinderModel p →L[ℝ]
      TangentSpace revolutionCylinderModel p →L[ℝ] ℝ :=
  (innerSL ℝ (E := Ambient) : Ambient →L[ℝ] Ambient →L[ℝ] ℝ).bilinearComp
    (show TangentSpace revolutionCylinderModel p →L[ℝ] Ambient from
      mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p)
    (show TangentSpace revolutionCylinderModel p →L[ℝ] Ambient from
      mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p)

 theorem revolutionEndInducedInner_apply (q : ℝ → ℝ) (p : RevolutionCylinder)
    (v w : TangentSpace revolutionCylinderModel p) :
    revolutionEndInducedInner q p v w =
      inner ℝ (show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p v)
      (show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p w) := rfl

 theorem revolutionEndInducedInner_pos {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : RevolutionCylinder) (hp : q p.2 ≠ 0)
    (v : TangentSpace revolutionCylinderModel p) (hv : v ≠ 0) :
    0 < revolutionEndInducedInner q p v v := by
  rw [revolutionEndInducedInner_apply]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  exact (revolutionEndCircleFull_mfderiv_injective hq p hp) (by simpa using h)

 theorem revolutionEndInducedInner_bounded {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : RevolutionCylinder) (hp : q p.2 ≠ 0) :
    IsVonNBounded ℝ {v : TangentSpace revolutionCylinderModel p | revolutionEndInducedInner q p v v < 1} := by
  let D : TangentSpace revolutionCylinderModel p →L[ℝ] Ambient :=
    mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p
  letI : FiniteDimensional ℝ (TangentSpace revolutionCylinderModel p) :=
    inferInstanceAs (FiniteDimensional ℝ (ℝ × ℝ))
  have hi : Function.Injective D := revolutionEndCircleFull_mfderiv_injective hq p hp
  have hiL : Function.Injective D.toLinearMap := hi
  obtain ⟨K, _, hK⟩ := (LinearMap.injective_iff_antilipschitz D.toLinearMap).mp hiL
  have hb : Bornology.IsBounded (D ⁻¹' Metric.ball (0 : Ambient) 1) :=
    hK.isBounded_preimage Metric.isBounded_ball
  apply NormedSpace.isVonNBounded_of_isBounded ℝ (hb.subset ?_)
  intro v hv
  change ‖D v - 0‖ < 1
  rw [sub_zero]
  change revolutionEndInducedInner q p v v < 1 at hv
  rw [revolutionEndInducedInner_apply, real_inner_self_eq_norm_sq] at hv
  change ‖D v‖^2 < 1 at hv
  nlinarith [norm_nonneg (D v)]

 def revolutionEndRiemannianMetric {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) :
    RiemannianMetric (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) where
  inner := revolutionEndInducedInner q
  symm p v w := by
    rw [revolutionEndInducedInner_apply, revolutionEndInducedInner_apply]
    exact real_inner_comm _ _
  pos p v hv := revolutionEndInducedInner_pos hq p (ne_of_gt (hpos p.2)) v hv
  continuousAt p := by
    let D : TangentSpace revolutionCylinderModel p →L[ℝ] Ambient :=
      mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p
    exact (D.continuous.inner (𝕜 := ℝ) D.continuous).continuousAt
  isVonNBounded p := revolutionEndInducedInner_bounded hq p (ne_of_gt (hpos p.2))

end
end TightVer401



