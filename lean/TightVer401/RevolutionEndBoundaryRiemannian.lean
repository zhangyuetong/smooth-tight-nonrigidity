import TightVer401.RevolutionEndBoundaryImmersion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Bounded

namespace TightVer401
noncomputable section
open Set Bundle Bornology OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

local instance (H : ℝ) (p : RevolutionClosedEnd H) : NormedAddCommGroup (TangentSpace revolutionEndBoundaryModel p) :=
  inferInstanceAs (NormedAddCommGroup (ℝ × EuclideanSpace ℝ (Fin 1)))
local instance (H : ℝ) (p : RevolutionClosedEnd H) : NormedSpace ℝ (TangentSpace revolutionEndBoundaryModel p) :=
  inferInstanceAs (NormedSpace ℝ (ℝ × EuclideanSpace ℝ (Fin 1)))

 def revolutionEndBoundaryInducedInner (q : ℝ → ℝ) (p : RevolutionClosedEnd H) :
    TangentSpace revolutionEndBoundaryModel p →L[ℝ]
      TangentSpace revolutionEndBoundaryModel p →L[ℝ] ℝ :=
  (innerSL ℝ (E := Ambient) : Ambient →L[ℝ] Ambient →L[ℝ] ℝ).bilinearComp
    (show TangentSpace revolutionEndBoundaryModel p →L[ℝ] Ambient from
      mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p)
    (show TangentSpace revolutionEndBoundaryModel p →L[ℝ] Ambient from
      mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p)

 theorem revolutionEndBoundaryInducedInner_apply (q : ℝ → ℝ) (p : RevolutionClosedEnd H)
    (v w : TangentSpace revolutionEndBoundaryModel p) :
    revolutionEndBoundaryInducedInner q p v w =
      inner ℝ (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p v)
      (show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p w) := rfl

 theorem revolutionEndBoundaryInducedInner_pos {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : RevolutionClosedEnd H) (hp : q p.2 ≠ 0)
    (v : TangentSpace revolutionEndBoundaryModel p) (hv : v ≠ 0) :
    0 < revolutionEndBoundaryInducedInner q p v v := by
  rw [revolutionEndBoundaryInducedInner_apply]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  exact (revolutionEndCircle_boundary_mfderiv_injective hq p hp) (by simpa using h)

 theorem revolutionEndBoundaryInducedInner_bounded {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : RevolutionClosedEnd H) (hp : q p.2 ≠ 0) :
    IsVonNBounded ℝ {v : TangentSpace revolutionEndBoundaryModel p | revolutionEndBoundaryInducedInner q p v v < 1} := by
  let D : TangentSpace revolutionEndBoundaryModel p →L[ℝ] Ambient :=
    mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p
  letI : FiniteDimensional ℝ (TangentSpace revolutionEndBoundaryModel p) :=
    inferInstanceAs (FiniteDimensional ℝ (ℝ × EuclideanSpace ℝ (Fin 1)))
  have hi : Function.Injective D := revolutionEndCircle_boundary_mfderiv_injective hq p hp
  have hiL : Function.Injective D.toLinearMap := hi
  obtain ⟨K, _, hK⟩ := (LinearMap.injective_iff_antilipschitz D.toLinearMap).mp hiL
  have hb : Bornology.IsBounded (D ⁻¹' Metric.ball (0 : Ambient) 1) :=
    hK.isBounded_preimage Metric.isBounded_ball
  apply NormedSpace.isVonNBounded_of_isBounded ℝ (hb.subset ?_)
  intro v hv
  change ‖D v - 0‖ < 1
  rw [sub_zero]
  change revolutionEndBoundaryInducedInner q p v v < 1 at hv
  rw [revolutionEndBoundaryInducedInner_apply, real_inner_self_eq_norm_sq] at hv
  change ‖D v‖^2 < 1 at hv
  nlinarith [norm_nonneg (D v)]

 def revolutionEndBoundaryRiemannianMetric {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) :
    RiemannianMetric (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) where
  inner := revolutionEndBoundaryInducedInner q
  symm p v w := by
    rw [revolutionEndBoundaryInducedInner_apply, revolutionEndBoundaryInducedInner_apply]
    exact real_inner_comm _ _
  pos p v hv := revolutionEndBoundaryInducedInner_pos hq p (ne_of_gt (hpos p.2 p.2.property)) v hv
  continuousAt p := by
    let D : TangentSpace revolutionEndBoundaryModel p →L[ℝ] Ambient :=
      mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p
    exact (D.continuous.inner (𝕜 := ℝ) D.continuous).continuousAt
  isVonNBounded p := revolutionEndBoundaryInducedInner_bounded hq p (ne_of_gt (hpos p.2 p.2.property))

end
end TightVer401




