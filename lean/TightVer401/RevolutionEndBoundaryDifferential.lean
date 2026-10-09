import TightVer401.RevolutionEndBoundarySmooth
import TightVer401.RevolutionEndImmersion
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

namespace TightVer401
noncomputable section
open Set Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEndBoundaryCoordinate_mfderiv_apply (H : ℝ) (z : Ici H)
    (v : TangentSpace (𝓡∂ 1) z) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (revolutionEndBoundaryCoordinate H) z v = v := by
  have hd := mfderiv_chartAt_eq_tangentCoordChange (I := 𝓡∂ 1) (x := z) (y := z)
    (mem_chart_source (EuclideanHalfSpace 1) z)
  change mfderiv (𝓡∂ 1) (𝓡∂ 1) (revolutionEndBoundaryCoordinate H) z =
    tangentCoordChange (𝓡∂ 1) z z z at hd
  rw [hd]
  change tangentCoordChange (𝓡∂ 1) z z z
    (show EuclideanSpace ℝ (Fin 1) from v) = (show EuclideanSpace ℝ (Fin 1) from v)
  exact tangentCoordChange_self (mem_extChartAt_source z)

theorem revolutionEndBoundaryVal_hasMFDerivAt (H : ℝ) (z : Ici H) :
    HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Ici H => (z : ℝ)) z
      (show TangentSpace (𝓡∂ 1) z →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (z : ℝ) from
        EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) := by
  have hd := hasMFDerivAt_extChartAt (I := 𝓡∂ 1) (x := z) (y := z)
    (mem_chart_source (EuclideanHalfSpace 1) z)
  change HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
    (extChartAt (𝓡∂ 1) z) z
    (mfderiv (𝓡∂ 1) (𝓡∂ 1) (revolutionEndBoundaryCoordinate H) z) at hd
  have hc : mfderiv (𝓡∂ 1) (𝓡∂ 1) (revolutionEndBoundaryCoordinate H) z =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
    apply ContinuousLinearMap.ext
    intro v
    exact revolutionEndBoundaryCoordinate_mfderiv_apply H z v
  rw [hc] at hd
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)
  have hF : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℝ)
      (fun v => P v + H) (extChartAt (𝓡∂ 1) z z) P :=
    (P.hasFDerivAt.add_const H).hasMFDerivAt
  have he := hF.comp z hd
  change HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ)
    ((fun v => P v + H) ∘ (extChartAt (𝓡∂ 1) z)) z P at he
  convert he using 1
  funext x
  change (x : ℝ) = (x : ℝ) - H + H
  ring

theorem revolutionEndBoundaryVal_mfderiv_injective (H : ℝ) (z : Ici H) :
    Function.Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Ici H => (z : ℝ)) z) := by
  rw [(revolutionEndBoundaryVal_hasMFDerivAt H z).mfderiv]
  intro v w hvw
  apply PiLp.ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact hvw

end
end TightVer401
