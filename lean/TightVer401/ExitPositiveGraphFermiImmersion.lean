import TightVer401.ExitPositiveGraphFermiEmbedding
import TightVer401.ExitPositiveGraphFermiRegularity
import TightVer401.NormalLoopEmbeddingPeriod

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem fermiGraph_raw_periodic {L : ℝ} {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hvL : Function.Periodic v L) (δ : ℝ) :
    Function.Periodic (fermiNormalMap ζ ∘ exitGraphCurve v δ) L := by
  intro r
  simp only [Function.comp_apply, fermiNormalMap, exitGraphCurve, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, hvL r, hζL r, (normalLoop_actual_periodic hζ hζL).1 r]

theorem fermiNativeGraph_mfderiv_injective {L : ℝ} [Fact (0 < L)]
    {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v L) (δ : ℝ)
    (hderiv : ∀ r, deriv (fermiNormalMap ζ ∘ exitGraphCurve v δ) r ≠ 0)
    (q : AddCircle L) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (fermiNativeGraph hζ hζL hvL δ) q) := by
  have hp := fermiGraph_raw_periodic hζ hζL hvL δ
  have he : fermiNativeGraph hζ hζL hvL δ = hp.lift :=
    periodicLift_unique hp _ (fermiNativeGraph_coe hζ hζL hvL δ)
  rw [he]
  exact periodicCurve_lift_mfderiv_injective
    ((fermiNormalMap_contDiff hζ).comp (exitGraphCurve_contDiff hv δ)) hp hderiv q

theorem fermiNativeSphereGraph_mfderiv_injective {L : ℝ} [Fact (0 < L)]
    {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v L) (δ : ℝ)
    (hderiv : ∀ r, deriv (fermiNormalMap ζ ∘ exitGraphCurve v δ) r ≠ 0)
    (q : AddCircle L) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      (fermiNativeSphereGraph hζ hζL hunit hspeed hvL δ) q) := by
  have hi := fermiNativeGraph_mfderiv_injective hζ hζL hv hvL δ hderiv q
  have hs := fermiNativeSphereGraph_contMDiff hζ hζL hunit hspeed hv hvL δ
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞ ((↑) : RoundSphere → Ambient) :=
    contMDiff_coe_sphere
  have hchain := mfderiv_comp q
    ((hc (fermiNativeSphereGraph hζ hζL hunit hspeed hvL δ q)).mdifferentiableAt (by simp))
    ((hs q).mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (fermiNativeGraph hζ hζL hvL δ) q = _ at hchain
  intro x y he
  apply hi
  rw [hchain]
  exact congrArg (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) ((↑) : RoundSphere → Ambient)
    (fermiNativeSphereGraph hζ hζL hunit hspeed hvL δ q)) he

end
end TightVer401
