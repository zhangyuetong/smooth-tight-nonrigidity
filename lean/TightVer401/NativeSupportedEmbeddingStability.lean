import TightVer401.NativeCompactEmbeddingStability
import TightVer401.NativeSupportedEmbeddingTopology
import Mathlib.Topology.Algebra.Support

/-! Actual smooth compactly supported bending preserves a native embedding,
including on a noncompact source such as the open identity-holonomy band. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- A compactly supported smooth native perturbation has a genuine embedding
threshold. Both local injection and exterior localization are proved. -/
theorem nativeSupportedEmbedding_exists_amplitude_threshold
    {M : Type*} [MetricSpace M] [WeaklyLocallyCompactSpace M]
    [ChartedSpace (ModelProd ℝ ℝ) M]
    {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y)
    (hemb : Topology.IsEmbedding X)
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p))
    (hcompact : IsCompact (tsupport Y)) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → Topology.IsEmbedding (fun p => X p + a • Y p) := by
  have hc : Continuous (fun z : M × ℝ => X z.1 + z.2 • Y z.1) :=
    (hX.continuous.comp continuous_fst).add
      (continuous_snd.smul (hY.continuous.comp continuous_fst))
  apply nativeSupportedEmbedding_exists_parameter_threshold hemb hc
    (fun p => by simp) hcompact
  · intro p hp a
    simp only [image_eq_zero_of_notMem_tsupport hp, smul_zero, add_zero]
  · intro p
    exact nativeCompactEmbedding_parameterGraph_locally_injective hX hY p (himm p)

end
end TightVer401
