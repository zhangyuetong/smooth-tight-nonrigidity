import TightVer401.RevolutionEndRiemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace TightVer401
noncomputable section
open Set Bundle ContinuousLinearMap OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
 def revolutionEndDerivativeCoordinates (q : ℝ → ℝ) (p₀ : RevolutionCylinder) :
    RevolutionCylinder → (ℝ × ℝ) →L[ℝ] Ambient :=
  inTangentCoordinates revolutionCylinderModel 𝓘(ℝ, Ambient) id (revolutionEndCircleFull q)
    (mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q)) p₀

 theorem revolutionEndDerivativeCoordinates_contMDiffAt {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p₀ : RevolutionCylinder) :
    ContMDiffAt revolutionCylinderModel 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] Ambient) ∞
      (revolutionEndDerivativeCoordinates q p₀) p₀ :=
  (revolutionEndCircleFull_contMDiff hq p₀).mfderiv_const (by simp)

 def revolutionEndInnerCoordinates (q : ℝ → ℝ) (p₀ p : RevolutionCylinder) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (E := Ambient) : Ambient →L[ℝ] Ambient →L[ℝ] ℝ).bilinearComp
    (revolutionEndDerivativeCoordinates q p₀ p) (revolutionEndDerivativeCoordinates q p₀ p)

 theorem revolutionEndInnerCoordinates_contMDiffAt {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p₀ : RevolutionCylinder) :
    ContMDiffAt revolutionCylinderModel 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) ∞
      (revolutionEndInnerCoordinates q p₀) p₀ := by
  have hA := revolutionEndDerivativeCoordinates_contMDiffAt hq p₀
  let B : Ambient →L[ℝ] Ambient →L[ℝ] ℝ := innerSL ℝ
  have hBc : ContMDiffAt revolutionCylinderModel 𝓘(ℝ, Ambient →L[ℝ] Ambient →L[ℝ] ℝ) ∞
      (fun _ : RevolutionCylinder => B) p₀ := contMDiffAt_const
  have hB := hBc.clm_comp hA
  let P : ((ℝ × ℝ) →L[ℝ] Ambient) →L[ℝ] Ambient →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.precompL (ℝ × ℝ) B
  have hP : ContDiff ℝ ∞ P := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (n := ∞) (E := (ℝ × ℝ) →L[ℝ] Ambient)
    (F := Ambient →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) P
  have hC := hP.contMDiff.contMDiffAt.comp p₀ hA
  have hD := hC.clm_comp hA
  have heq : revolutionEndInnerCoordinates q p₀ =
      fun p => (P (revolutionEndDerivativeCoordinates q p₀ p)).comp
        (revolutionEndDerivativeCoordinates q p₀ p) := by
    funext p
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change inner ℝ (revolutionEndDerivativeCoordinates q p₀ p v)
      (revolutionEndDerivativeCoordinates q p₀ p w) =
      inner ℝ (revolutionEndDerivativeCoordinates q p₀ p w)
        (revolutionEndDerivativeCoordinates q p₀ p v)
    exact (real_inner_comm
      (revolutionEndDerivativeCoordinates q p₀ p v)
      (revolutionEndDerivativeCoordinates q p₀ p w)).symm
  rw [heq]
  exact hD
end
end TightVer401









