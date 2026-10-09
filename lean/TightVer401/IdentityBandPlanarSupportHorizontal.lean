import TightVer401.IdentityBandPlanarSupportGradient
import TightVer401.CorrugatedSeedFrameHorizontal

/-! The retained complex horizontal projection and the actual Cartesian
horizontal coordinates are related by the pinned real linear equivalences. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold

/-- Actual real Cartesian coordinates of a complex horizontal projection. -/
def identityBandPlanarComplexCoordinates : ℂ ≃L[ℝ] Coord :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp] theorem identityBandPlanarComplexCoordinates_apply (z : ℂ) :
    identityBandPlanarComplexCoordinates z = ![z.re, z.im] := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem identityBandPlanarHorizontalCLM_complex (u : Ambient) :
    identityBandPlanarComplexCoordinates (corrugatedAmbientHorizontalCLM u) =
      identityBandPlanarHorizontalCLM u := by
  ext i
  fin_cases i <;>
    simp [identityBandPlanarComplexCoordinates_apply, corrugatedAmbientHorizontalCLM,
      identityBandPlanarHorizontalCLM, ContinuousLinearMap.pi_apply, PiLp.proj_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Coord M]
  [IsManifold 𝓘(ℝ, Coord) ∞ M]

/-- Actual retained horizontal injectivity supplies Cartesian injectivity. -/
theorem identityBandPlanarHorizontalCLM_injective {X : M → Ambient}
    (hi : Function.Injective (corrugatedAmbientHorizontalCLM ∘ X)) :
    Function.Injective (fun p => identityBandPlanarHorizontalCLM (X p)) := by
  intro p q hpq
  apply hi
  apply identityBandPlanarComplexCoordinates.injective
  simpa only [Function.comp_apply, identityBandPlanarHorizontalCLM_complex] using hpq

/-- The horizontal regularity premise is transported by the actual derivative
of the fixed complex-to-Cartesian linear equivalence. -/
theorem identityBandPlanarHorizontalCLM_differential_injective {X : M → Ambient}
    (hX : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, ℂ) ∞ (corrugatedAmbientHorizontalCLM ∘ X))
    (hi : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, ℂ)
      (corrugatedAmbientHorizontalCLM ∘ X) p)) (p : M) :
    Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Coord)
      (fun p => identityBandPlanarHorizontalCLM (X p)) p) := by
  have heq : (fun p => identityBandPlanarHorizontalCLM (X p)) =
      identityBandPlanarComplexCoordinates ∘ (corrugatedAmbientHorizontalCLM ∘ X) := by
    funext p
    exact (identityBandPlanarHorizontalCLM_complex (X p)).symm
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Coord) ∞ identityBandPlanarComplexCoordinates :=
    identityBandPlanarComplexCoordinates.contDiff.contMDiff
  rw [heq, mfderiv_comp p
    (hc.mdifferentiable
      (by simp) _) (hX.mdifferentiable (by simp) p), mfderiv_eq_fderiv,
    identityBandPlanarComplexCoordinates.fderiv]
  exact identityBandPlanarComplexCoordinates.injective.comp (hi p)

end
end TightVer401