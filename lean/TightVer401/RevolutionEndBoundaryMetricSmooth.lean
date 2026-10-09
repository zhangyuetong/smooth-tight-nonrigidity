import TightVer401.RevolutionEndBoundaryRiemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace TightVer401
noncomputable section
open Set Bundle ContinuousLinearMap OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
 def revolutionEndBoundaryDerivativeCoordinates (q : ℝ → ℝ) (p₀ : RevolutionClosedEnd H) :
    RevolutionClosedEnd H → (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] Ambient :=
  inTangentCoordinates revolutionEndBoundaryModel 𝓘(ℝ, Ambient) id (revolutionEndCircle q H)
    (mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H)) p₀

 theorem revolutionEndBoundaryDerivativeCoordinates_contMDiffAt {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p₀ : RevolutionClosedEnd H) :
    ContMDiffAt revolutionEndBoundaryModel 𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] Ambient) ∞
      (revolutionEndBoundaryDerivativeCoordinates q p₀) p₀ :=
  (revolutionEndCircle_boundary_contMDiff hq H p₀).mfderiv_const (by simp)

 def revolutionEndBoundaryInnerCoordinates (q : ℝ → ℝ) (p₀ p : RevolutionClosedEnd H) :
    (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
  (innerSL ℝ (E := Ambient) : Ambient →L[ℝ] Ambient →L[ℝ] ℝ).bilinearComp
    (revolutionEndBoundaryDerivativeCoordinates q p₀ p) (revolutionEndBoundaryDerivativeCoordinates q p₀ p)

 theorem revolutionEndBoundaryInnerCoordinates_contMDiffAt {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (p₀ : RevolutionClosedEnd H) :
    ContMDiffAt revolutionEndBoundaryModel 𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ) ∞
      (revolutionEndBoundaryInnerCoordinates q p₀) p₀ := by
  have hA := revolutionEndBoundaryDerivativeCoordinates_contMDiffAt hq p₀
  let B : Ambient →L[ℝ] Ambient →L[ℝ] ℝ := innerSL ℝ
  have hBc : ContMDiffAt revolutionEndBoundaryModel 𝓘(ℝ, Ambient →L[ℝ] Ambient →L[ℝ] ℝ) ∞
      (fun _ : RevolutionClosedEnd H => B) p₀ := contMDiffAt_const
  have hB := hBc.clm_comp hA
  let P : ((ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] Ambient) →L[ℝ] Ambient →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
    ContinuousLinearMap.precompL (ℝ × EuclideanSpace ℝ (Fin 1)) B
  have hP : ContDiff ℝ ∞ P := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (n := ∞) (E := (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] Ambient)
    (F := Ambient →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ) P
  have hC := hP.contMDiff.contMDiffAt.comp p₀ hA
  have hD := hC.clm_comp hA
  have heq : revolutionEndBoundaryInnerCoordinates q p₀ =
      fun p => (P (revolutionEndBoundaryDerivativeCoordinates q p₀ p)).comp
        (revolutionEndBoundaryDerivativeCoordinates q p₀ p) := by
    funext p
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change inner ℝ (revolutionEndBoundaryDerivativeCoordinates q p₀ p v)
      (revolutionEndBoundaryDerivativeCoordinates q p₀ p w) =
      inner ℝ (revolutionEndBoundaryDerivativeCoordinates q p₀ p w)
        (revolutionEndBoundaryDerivativeCoordinates q p₀ p v)
    exact (real_inner_comm
      (revolutionEndBoundaryDerivativeCoordinates q p₀ p v)
      (revolutionEndBoundaryDerivativeCoordinates q p₀ p w)).symm
  rw [heq]
  exact hD
end
end TightVer401










